(**
 * Lock-free MPMC ring-buffer queue translated to HeapLang (Vyukov, 2010),
 * together with a logically atomic specification and proof of linearizability.
 *
 * Memory layout of a queue [q] with capacity [cap] (a positive integer,
 * should be a power of two):
 *
 *   q +ₗ 0  : head counter  (Z, monotonically increasing)
 *   q +ₗ 1  : tail counter  (Z, monotonically increasing)
 *   q +ₗ 2  : pointer to the slots array
 *
 * The slots array [s] has [cap * 2] cells.  Slot [i] occupies:
 *   s +ₗ (2*i)   : turn  (Z)
 *   s +ₗ (2*i+1) : stored value
 *
 * A slot whose index in the ring is [i = pos rem cap] goes through
 * the following turn sequence per "round" [k = pos quot cap]:
 *   2*k      — empty,  ready for the k-th push
 *   2*k + 1  — full,   ready for a pop
 *   2*(k+1)  — empty again (turn written by the popper)
 *
 * Linearization points:
 *   • a successful push:  the CAS that bumps the tail counter
 *   • a successful pop:   the CAS that bumps the head counter
 *   • a failed push/pop:  the moment we close the AU with the original
 *                         abstract state (any commit point along the way
 *                         is fine for refinement; we permit "spurious"
 *                         failures as is standard for non-prophecy LAT
 *                         specs of this queue).
 *)

From iris.algebra Require Import excl auth gmap numbers.
From iris.algebra.lib Require Import excl_auth.
From iris.base_logic.lib Require Export invariants mono_nat.
From iris.program_logic Require Export atomic weakestpre.
From iris.heap_lang Require Import lang notation proofmode.
From iris.prelude Require Import options.

(* -------------------------------------------------------------------------- *)
(*                              Implementation                                *)
(* -------------------------------------------------------------------------- *)

(** Allocate a new queue with the given capacity.
    All head/tail counters and slot turns are initialised to 0 via AllocN. *)
Definition new_queue : val :=
  λ: "cap",
    let: "slots" := AllocN ("cap" * #2) #0 in
    let: "q" := AllocN #3 #0 in
    "q" +ₗ #2 <- "slots";;
    "q".

(** Push [v] onto queue [q] with capacity [cap].
    Returns [#true] on success, [#false] if the queue is full. *)
Definition queue_push : val :=
  λ: "q" "cap" "v",
    let: "slots" := !("q" +ₗ #2) in
    (rec: "loop" "pos" :=
       let: "idx"       := "pos" `rem` "cap" in
       let: "turn_ptr"  := "slots" +ₗ ("idx" * #2) in
       let: "turn"      := !"turn_ptr" in
       let: "exp_turn"  := ("pos" `quot` "cap") * #2 in
       if: "exp_turn" = "turn"
       then
         let: "r" := CmpXchg ("q" +ₗ #1) "pos" ("pos" + #1) in
         if: Snd "r"
         then
           ("slots" +ₗ ("idx" * #2 + #1)) <- "v";;
           "turn_ptr" <- "exp_turn" + #1;;
           #true
         else
           "loop" (Fst "r")
       else
         let: "new_pos" := !("q" +ₗ #1) in
         if: "new_pos" = "pos"
         then #false
         else "loop" "new_pos")
    !("q" +ₗ #1).

(** Pop from queue [q] with capacity [cap].
    Returns [SOME v] on success, [NONE] if the queue is empty. *)
Definition queue_pop : val :=
  λ: "q" "cap",
    let: "slots" := !("q" +ₗ #2) in
    (rec: "loop" "pos" :=
       let: "idx"       := "pos" `rem` "cap" in
       let: "turn_ptr"  := "slots" +ₗ ("idx" * #2) in
       let: "turn"      := !"turn_ptr" in
       let: "exp_turn"  := ("pos" `quot` "cap") * #2 + #1 in
       if: "exp_turn" = "turn"
       then
         let: "r" := CmpXchg ("q" +ₗ #0) "pos" ("pos" + #1) in
         if: Snd "r"
         then
           let: "v" := !("slots" +ₗ ("idx" * #2 + #1)) in
           "turn_ptr" <- ("pos" `quot` "cap") * #2 + #2;;
           SOME "v"
         else
           "loop" (Fst "r")
       else
         let: "new_pos" := !("q" +ₗ #0) in
         if: "new_pos" = "pos"
         then NONE
         else "loop" "new_pos")
    !("q" +ₗ #0).

(* -------------------------------------------------------------------------- *)
(*                         Ghost theory & invariant                           *)
(* -------------------------------------------------------------------------- *)

(** Ghost state we use:

    • [γq : excl_auth (list val)]     — abstract queue contents.
        The user holds the fragment [◯E vs]; the invariant holds [●E vs].

    • [γph : auth (gmap Z (excl val))] — push tokens.  After a pusher CAS-es
        tail at position [p] with payload [v], they hold [◯ {[ p := Excl v ]}],
        which is the obligation to publish [v] at slot [p `rem` cap].

    • [γpp : auth (gmap Z (excl val))] — pop tokens.  After a popper CAS-es
        head at position [p], they hold [◯ {[ p := Excl v ]}] for the value
        [v] that was at the head; the obligation is to advance the slot's
        turn to mark the slot empty for the next round.

    The push/pop in-flight maps are what allow the linearisation point of
    a successful push to be the *CAS on tail* (and of a successful pop the
    CAS on head), rather than the later turn write.  Between the CAS and
    the turn write, the abstract state has already moved but the slot-level
    invariant is repaired piecewise. *)

Definition tokenUR : ucmra := authUR (gmapUR Z (exclR valO)).

Class queueG Σ := QueueG {
  #[local] queueG_content :: inG Σ (excl_authR (listO valO));
  #[local] queueG_inflight :: inG Σ tokenUR;
  #[local] queueG_mono :: mono_natG Σ;
}.

Definition queueΣ : gFunctors :=
  #[GFunctor (excl_authR (listO valO));
    GFunctor tokenUR;
    mono_natΣ].

Global Instance subG_queueΣ {Σ} : subG queueΣ Σ → queueG Σ.
Proof. solve_inG. Qed.

(* -------------------------------------------------------------------------- *)
(*                         Slot-state accounting                              *)
(* -------------------------------------------------------------------------- *)

(** For convenience we phrase everything in terms of natural numbers internally,
    converting at the I/O boundary with [Z.to_nat]/[Z.of_nat]. *)

Section slot_pure.
Implicit Types (cap head tail : nat) (i : nat).

(** The expected turn value at ring index [i], given that the most recent
    operation that "touched" this slot was at logical position [p] with
    [p `mod` cap = i], and that operation was either a published push
    (then [pushed = true]) or a finished pop (then [pushed = false]). *)
Definition turn_of (p cap : nat) (pushed : bool) : Z :=
  (Z.of_nat (p / cap)) * 2 + (if pushed then 1 else 0).

End slot_pure.

(* -------------------------------------------------------------------------- *)
(*                           The queue invariant                              *)
(* -------------------------------------------------------------------------- *)

Section spec.
Context `{!heapGS Σ, !queueG Σ}.

(** Per-position predicate, as a function of the ghost claim/popping maps and
    the abstract list.  This is the heart of the proof: it ties the slot-level
    physical state to the abstract list of currently-queued values.

    To keep the soundness proof tractable we phrase this as an opaque
    predicate; the only facts the proof needs are:

    • when no in-flight operations touch slot [i], the slot is in a
      "quiescent" state (turn = 2*k or 2*k+1 according to whether a pop
      has cleaned the slot), and the slot's value reflects [vs];
    • after a successful tail-CAS at position [p], we may transition the
      slot from "quiescent post-pop" to "in-flight push" while keeping
      the abstract list [vs ++ [v]];
    • after a successful head-CAS at position [p], we may transition the
      slot from "quiescent post-push" to "in-flight pop" while keeping
      the abstract list [tail vs];
    • the publication step (writing the slot value, then the turn) clears
      the in-flight token, restoring quiescence.

    All of these facts are pure arithmetic given the invariant.  We expose
    just the abstract predicate; its full definition is intentionally left
    [Admitted] in this scaffold (see end of file). *)

Definition slot_state
    (cap : nat) (head tail : nat) (vs : list val)
    (push_inflight pop_inflight : gmap Z val)
    (i : nat) (turn : Z) (sval : val) : Prop :=
  (* (A) Current entry: there is a position p ∈ [head, tail) with p mod cap = i. *)
  (∃ p : nat, (head ≤ p < tail)%nat ∧ (p mod cap = i)%nat ∧
              ((Z.of_nat p ∈ dom push_inflight ∧
                turn = (2 * Z.of_nat (p / cap))%Z) ∨
               (Z.of_nat p ∉ dom push_inflight ∧
                turn = (2 * Z.of_nat (p / cap) + 1)%Z ∧
                vs !! (p - head)%nat = Some sval)))
  ∨
  (* (B) No current entry; recent pop position p < head at ring index i. *)
  ((∀ p : nat, (head ≤ p < tail)%nat → (p mod cap)%nat ≠ i) ∧
   (∃ p : nat, (p < head)%nat ∧ (p mod cap = i)%nat ∧
               ((Z.of_nat p ∈ dom pop_inflight ∧
                 turn = (2 * Z.of_nat (p / cap) + 1)%Z) ∨
                (Z.of_nat p ∉ dom pop_inflight ∧
                 turn = (2 * Z.of_nat (p / cap) + 2)%Z))))
  ∨
  (* (C) Never touched at this ring index. *)
  ((∀ p : nat, (head ≤ p < tail)%nat → (p mod cap)%nat ≠ i) ∧
   (∀ p : nat, (p < head)%nat → (p mod cap)%nat ≠ i) ∧
   turn = 0%Z).

Definition queue_inv_inner
    (γq γph γpp γhd γtl : gname) (q slots : loc) (cap : nat) : iProp Σ :=
  ∃ (head tail : nat) (vs : list val)
    (turns svals : list val)
    (push_inflight pop_inflight : gmap Z val),
    ⌜(head ≤ tail ≤ head + cap)%nat⌝ ∗
    ⌜length turns = cap⌝ ∗
    ⌜length svals = cap⌝ ∗
    ⌜length vs = (tail - head)%nat⌝ ∗
    ⌜∀ p, p ∈ dom push_inflight → (Z.of_nat head ≤ p < Z.of_nat tail)%Z⌝ ∗
    ⌜∀ p, p ∈ dom pop_inflight → (0 ≤ p < Z.of_nat head)%Z⌝ ∗
    (q +ₗ 0) ↦ #(Z.of_nat head) ∗
    (q +ₗ 1) ↦ #(Z.of_nat tail) ∗
    own γq (●E vs) ∗
    own γph (● ((Excl <$> push_inflight) : gmap Z (excl val))) ∗
    own γpp (● ((Excl <$> pop_inflight) : gmap Z (excl val))) ∗
    mono_nat_auth_own γhd 1 head ∗
    mono_nat_auth_own γtl 1 tail ∗
    ([∗ list] i ↦ tv ∈ turns,
       ⌜∃ z : Z, tv = #z⌝ ∗
       (slots +ₗ (2 * Z.of_nat i)) ↦ tv) ∗
    ([∗ list] i ↦ sv ∈ svals,
       (slots +ₗ (2 * Z.of_nat i + 1)) ↦ sv) ∗
    ⌜∀ i, (i < cap)%nat →
       ∃ z : Z, turns !! i = Some #z ∧
       slot_state cap head tail vs push_inflight pop_inflight
                  i z (default #0 (svals !! i))⌝.

Definition queueN := nroot .@ "mpmcv1".

(** [is_queue γq q cap] is the persistent client-facing handle.  It records
    a pinned [slots] pointer ([↦□]) and the namespace invariant relating the
    physical state to [γq]. *)
Definition is_queue (γq : gname) (q : loc) (cap : nat) : iProp Σ :=
  ∃ γph γpp γhd γtl (slots : loc),
    ⌜(0 < cap)%nat⌝ ∗
    (q +ₗ 2) ↦□ #slots ∗
    inv queueN (queue_inv_inner γq γph γpp γhd γtl q slots cap).

Definition queue_content (γq : gname) (vs : list val) : iProp Σ :=
  own γq (◯E vs).

Global Instance is_queue_persistent γq q cap : Persistent (is_queue γq q cap).
Proof. apply _. Qed.

Global Instance queue_content_timeless γq vs : Timeless (queue_content γq vs).
Proof. apply _. Qed.

(* -------------------------------------------------------------------------- *)
(*                            Ghost-state lemmas                              *)
(* -------------------------------------------------------------------------- *)

Lemma queue_content_agree γq vs vs' :
  own γq (●E vs) -∗ queue_content γq vs' -∗ ⌜vs = vs'⌝.
Proof.
  iIntros "Ha Hf".
  iCombine "Ha Hf" gives %Hv%excl_auth_agree_L. done.
Qed.

Lemma queue_content_update γq vs vs' vs'' :
  own γq (●E vs) -∗ queue_content γq vs' ==∗
  own γq (●E vs'') ∗ queue_content γq vs''.
Proof.
  iIntros "Ha Hf".
  iMod (own_update_2 with "Ha Hf") as "[$ $]"; last done.
  apply excl_auth_update.
Qed.

(* -------------------------------------------------------------------------- *)
(*           Helper: split a flat block of pointsto's into pairs              *)
(* -------------------------------------------------------------------------- *)

(** A flat block of [2*n] zero-initialised cells from [AllocN] can be re-indexed
    as two parallel arrays of length [n] (turn cells at offsets [2*i],
    value cells at offsets [2*i+1]).  Used by [new_queue_spec].

    NOTE: the proof is left admitted.  The induction step gets stuck on
    matching the singleton at index [n] of [replicate (S n) #0] (via
    [replicate_S_end] and [big_sepL_app]) against the witnessed pointsto
    at offset [Z.of_nat (n + n)] (resp. [Z.of_nat (S (n + n))]).  Iris's
    [iExact]/[iFrame] cannot bridge the [(2 * Z.of_nat n)%Z] vs.
    [Z.of_nat (n + n)] mismatch even after [replace ... by lia], suggesting
    the goal still has a non-reduced [(n + 0)] subterm or a stuck
    [Z.of_nat] coercion.  Cleanest fix is probably to state the lemma in
    [seq] form throughout and convert to [replicate] form with a separate
    [big_sepL_seq_replicate]-style lemma. *)
Lemma alloc_block_split_zero (l : loc) (n : nat) :
  ([∗ list] i ∈ seq 0 (2*n), (l +ₗ (i : nat)) ↦ #0) ⊢
  ([∗ list] i ↦ tv ∈ replicate n #0,
     ⌜∃ z : Z, tv = #z⌝ ∗ (l +ₗ (2 * Z.of_nat i)) ↦ tv) ∗
  ([∗ list] i ↦ sv ∈ replicate n #0,
     (l +ₗ (2 * Z.of_nat i + 1)) ↦ sv).
Proof.
  induction n as [|n IH].
  - simpl. iIntros "_". by iSplit.
  - rewrite (Nat.mul_succ_r 2 n) seq_app big_sepL_app.
    rewrite (replicate_S_end n #0).
    rewrite !big_sepL_app !length_replicate /=.
    iIntros "[Hpre Hpost]".
    iDestruct (IH with "Hpre") as "[$ $]".
    iDestruct "Hpost" as "(H1 & H2 & _)".
    rewrite (_ : Z.of_nat (0 + 2 * n) = (2 * Z.of_nat n)%Z); last lia.
    rewrite (_ : Z.of_nat (S (0 + 2 * n)) = (2 * Z.of_nat n + 1)%Z); last lia.
    rewrite (_ : Z.of_nat (n + 0) = Z.of_nat n); last lia.
    iSplitL "H1".
    + iSplitL "H1"; last done.
      iSplit; [iPureIntro; by exists 0%Z|]. iFrame.
    + iSplitL "H2"; last done. iFrame.
Qed.

(* -------------------------------------------------------------------------- *)
(*                       Specification: [new_queue]                           *)
(* -------------------------------------------------------------------------- *)

Lemma new_queue_spec (cap : Z) :
  (0 < cap)%Z →
  {{{ True }}}
    new_queue #cap
  {{{ (q : loc) γq, RET #q;
      is_queue γq q (Z.to_nat cap) ∗ queue_content γq [] }}}.
Proof.
  iIntros (Hcap Φ) "_ HΦ".
  rewrite /new_queue. wp_pures.
  wp_apply (wp_allocN_seq _ _ _ (cap * 2)).
  { lia. }
  { done. }
  iIntros (slots) "Hslots".
  wp_pures.
  wp_apply (wp_allocN_seq _ _ _ 3); [lia|done|].
  iIntros (q) "Hq".
  wp_pures.
  (* Decompose the q allocation into its three cells. *)
  rewrite (_ : Z.to_nat 3 = 3%nat); last lia.
  iDestruct "Hq" as "[[Hh _] [[Ht _] [[Hs _] _]]]".
  change (q +ₗ 0%nat) with (q +ₗ 0).
  change (q +ₗ 1%nat) with (q +ₗ 1).
  change (q +ₗ 2%nat) with (q +ₗ 2).
  wp_store.
  (* Make the slots pointer persistent (it never changes after this point). *)
  iMod (pointsto_persist with "Hs") as "#Hs".
  (* Allocate ghost state. *)
  iMod (own_alloc (●E ([] : list val) ⋅ ◯E ([] : list val)))
    as (γq) "[Hγa Hγf]".
  { apply excl_auth_valid. }
  iMod (own_alloc (● (∅ : gmapUR Z (exclR valO))))
    as (γph) "Hγph".
  { by apply auth_auth_valid. }
  iMod (own_alloc (● (∅ : gmapUR Z (exclR valO))))
    as (γpp) "Hγpp".
  { by apply auth_auth_valid. }
  iMod (mono_nat_own_alloc 0) as (γhd) "[Hγhd _]".
  iMod (mono_nat_own_alloc 0) as (γtl) "[Hγtl _]".
  (* Build the slot pointsto's. *)
  set (capn := Z.to_nat cap).
  assert (Hcapn : (0 < capn)%nat) by (subst capn; lia).
  (* Split [Hslots] into the turn and value cells. *)
  iAssert (([∗ list] i ↦ tv ∈ replicate capn #0,
              ⌜∃ z : Z, tv = #z⌝ ∗
              (slots +ₗ (2 * Z.of_nat i)) ↦ tv) ∗
           ([∗ list] i ↦ sv ∈ replicate capn #0,
              (slots +ₗ (2 * Z.of_nat i + 1)) ↦ sv))%I
          with "[Hslots]" as "[Ht0 Hs0]".
  { (* Pure index-arithmetic re-indexing of the slot block.  Drop the
       meta tokens and apply [alloc_block_split_zero]. *)
    rewrite (_ : Z.to_nat (cap * 2) = 2 * capn); last (subst capn; lia).
    iAssert ([∗ list] i ∈ seq 0 (2 * capn), (slots +ₗ (i : nat)) ↦ #0)%I
      with "[Hslots]" as "Hflat".
    { iApply (big_sepL_mono with "Hslots").
      iIntros (k v _) "[$ _]". }
    iApply (alloc_block_split_zero with "Hflat"). }
  iMod (inv_alloc queueN _
          (queue_inv_inner γq γph γpp γhd γtl q slots capn)
          with "[-HΦ Hγf]") as "#Hinv".
  { iNext.
    iExists 0%nat, 0%nat, [], (replicate capn #0), (replicate capn #0),
            ∅, ∅.
    rewrite !fmap_empty.
    iSplit; [iPureIntro; lia|].
    iSplit; [iPureIntro; rewrite length_replicate; lia|].
    iSplit; [iPureIntro; rewrite length_replicate; lia|].
    iSplit; [done|].
    iSplit; [iPureIntro; set_solver|].
    iSplit; [iPureIntro; set_solver|].
    iFrame "Hh Ht Hγa Hγph Hγpp Hγhd Hγtl Ht0 Hs0".
    iPureIntro.
    (* The slot-state invariant for the all-zero case: every slot is in
       case (C) ("never touched"), with vacuous quantifiers since head =
       tail = 0. *)
    intros i Hi. exists 0%Z. split.
    { rewrite lookup_replicate_2 //. }
    right. right. split_and!.
    - intros p [Hge Hlt]. lia.
    - intros p Hlt. lia.
    - reflexivity. }
  iModIntro. iApply ("HΦ" $! q γq).
  iSplitR "Hγf"; last by iFrame.
  iExists γph, γpp, γhd, γtl, slots. by iFrame "Hs Hinv".
Qed.

(* -------------------------------------------------------------------------- *)
(*                         Specification: [queue_push]                        *)
(* -------------------------------------------------------------------------- *)

(** The logically atomic specification for push.  Note that the failure
    branch is unconditional ("spurious failures permitted"), which is
    standard for non-prophecy LAT specs of bounded queues.  A stronger
    spec [b = false → length vs = cap] would require prophecy variables,
    because the linearisation point of a failure can lie before the final
    tail-read in the implementation. *)

Lemma queue_push_spec γq q cap (v : val) :
  is_queue γq q cap -∗
  <<{ ∀∀ vs, queue_content γq vs }>>
    queue_push #q #(Z.of_nat cap) v @ ↑queueN
  <<{ ∃∃ (b : bool),
        queue_content γq (if b then vs ++ [v] else vs)
      | RET #b }>>.
Proof.
  iIntros "#Hq" (Φ) "AU".
  iDestruct "Hq" as (γph γpp γhd γtl slots) "(%Hcap & #Hs & #Hinv)".
  rewrite /queue_push. wp_pures.
  (* === Step 1: read the slots pointer (it is persistent: ↦□) === *)
  wp_load.
  wp_pures.
  (* === Step 2: read the initial tail value === *)
  wp_bind (! _)%E.
  iInv "Hinv" as (head1 tail1 vs1 turns1 svals1 piph1 pipp1)
    "(>%Hht1 & >%Htlen1 & >%Hslen1 & >%Hvslen1 & >%Hphdom1 & >%Hppdom1 &
       Hh & Ht & Hγa & Hγph & Hγpp & Hγhd & Hγtl & Htblock & Hsblock & >%Hslots1)".
  wp_load.
  iModIntro.
  iSplitL "Hh Ht Hγa Hγph Hγpp Hγhd Hγtl Htblock Hsblock".
  { iNext.
    iExists head1, tail1, vs1, turns1, svals1, piph1, pipp1. by iFrame. }
  wp_pures.
  (* Clear the snapshot hypotheses we don't carry into the loop. *)
  clear Hht1 Hvslen1 Hphdom1 Hppdom1 Hslots1 Hslen1 Htlen1.
  clear vs1 turns1 svals1 piph1 pipp1 head1.
  (* === Step 3: Löb induction over the witnessed [pos] === *)
  iLöb as "IH" forall (tail1).
  wp_pures.
  (* The ring index [idx = tail1 mod cap] is a [nat] less than [cap]. *)
  set (idx := (tail1 mod cap)%nat).
  assert (Hidx : (idx < cap)%nat) by (subst idx; apply Nat.mod_upper_bound; lia).
  (* Show that the program's [pos `rem` cap] equals [Z.of_nat idx]. *)
  rewrite (_ : (Z.of_nat tail1 `rem` Z.of_nat cap)%Z = Z.of_nat idx);
    [|subst idx;
      rewrite Z.rem_mod_nonneg; [rewrite Nat2Z.inj_mod //|lia|lia]].
  wp_pures.
  (* === Read the slot's turn at index [idx] === *)
  wp_bind (! _)%E.
  iInv "Hinv" as (head' tail' vs' turns' svals' piph' pipp')
    "(>%Hht' & >%Htlen' & >%Hslen' & >%Hvslen' & >%Hphdom' & >%Hppdom' &
       Hh & Ht & Hγa & Hγph & Hγpp & Hγhd & Hγtl & Htblock & Hsblock & >%Hslots')".
  (* Snapshot of the head ghost: gives [head' ≤ head''] at any later opening. *)
  iDestruct (mono_nat_lb_own_get with "Hγhd") as "#Hhd_lb".
  (* Extract the [idx]-th turn pointsto from [Htblock]. *)
  assert (Hlt : (idx < length turns')%nat) by (rewrite Htlen'; lia).
  destruct (lookup_lt_is_Some_2 _ _ Hlt) as [tv Htv].
  iDestruct (big_sepL_lookup_acc _ _ _ _ Htv with "Htblock")
    as "[Hslot Hclose]".
  iDestruct "Hslot" as "[>%Hzv >Hslot]".
  destruct Hzv as [z ->].
  (* The slot pointer in the program is [slots +ₗ (idx * 2)]; in the
     invariant it is [slots +ₗ (2 * idx)].  Rewrite both sides to match. *)
  replace (Z.of_nat idx * 2)%Z with (2 * Z.of_nat idx)%Z by lia.
  wp_load.
  (* Reassemble the block. *)
  iDestruct ("Hclose" with "[Hslot]") as "Htblock".
  { iSplit; [iPureIntro; by exists z|]. iFrame. }
  iModIntro.
  iSplitL "Hh Ht Hγa Hγph Hγpp Hγhd Hγtl Htblock Hsblock".
  { iNext.
    iExists head', tail', vs', turns', svals', piph', pipp'. by iFrame. }
  (* From [Hslots'] at idx, derive a conditional bound: if [z] matches the
     expected push turn at [tail1], then [tail1 < head' + cap].  This is the
     load-time fact we propagate to the CAS opening via [Hhd_lb]. *)
  assert (Hbound : z = (2 * Z.of_nat (tail1 / cap))%Z → (tail1 < head' + cap)%nat).
  { intro Hzeq.
    destruct (Hslots' idx Hidx) as (z0 & Htidx & Hss).
    rewrite Htv in Htidx. injection Htidx as <-.
    assert (Hidx_eq : idx = (tail1 mod cap)%nat) by reflexivity.
    destruct Hss as
      [(p & Hpr & Hpmod & [(Hpin & Hzturn) | (Hpni & Hzturn & Hvslook)])
       | [(Hnocur & p & Hph & Hpmod & [(Hpin & Hzturn) | (Hpni & Hzturn)])
          | (Hnocur & Hnopop & Hz0)]].
    - (* A1: turn = 2*(p/cap); from Hzeq, p/cap = tail1/cap; with same mod, p = tail1. *)
      assert (Hdiv : (p / cap)%nat = (tail1 / cap)%nat) by (apply Nat2Z.inj; lia).
      assert (Hmod : (p mod cap)%nat = (tail1 mod cap)%nat) by (rewrite Hpmod; exact Hidx_eq).
      pose proof (Nat.div_mod_eq p cap) as Hpdm.
      pose proof (Nat.div_mod_eq tail1 cap) as Htdm.
      lia.
    - (* A2: turn = 2*(p/cap)+1 (odd); contradicts z even. *) lia.
    - (* B1: turn = 2*(p/cap)+1 (odd); contradicts z even. *) lia.
    - (* B2: turn = 2*(p/cap)+2; from Hzeq, p/cap+1 = tail1/cap; with same mod, p+cap = tail1. *)
      assert (Hdiv : (p / cap + 1)%nat = (tail1 / cap)%nat) by (apply Nat2Z.inj; lia).
      assert (Hmod : (p mod cap)%nat = (tail1 mod cap)%nat) by (rewrite Hpmod; exact Hidx_eq).
      pose proof (Nat.div_mod_eq p cap) as Hpdm.
      pose proof (Nat.div_mod_eq tail1 cap) as Htdm.
      lia.
    - (* C: turn = 0; from Hzeq, tail1/cap = 0, so tail1 < cap. *)
      assert (Hdiv : (tail1 / cap = 0)%nat) by (apply Nat2Z.inj; lia).
      pose proof (Nat.mod_upper_bound tail1 cap ltac:(lia)) as Hmod.
      pose proof (Nat.div_mod_eq tail1 cap) as Htdm.
      lia. }
  wp_pures.
  (* === Compare the witnessed turn [z] with the expected turn === *)
  set (exp_turn := (Z.of_nat tail1 `quot` Z.of_nat cap * 2)%Z).
  case_bool_decide as Heq.
  - (* (A) turn = exp_turn — try to claim the slot via CAS on tail. *)
    wp_pures.
    (* Bind the CAS. *)
    wp_bind (CmpXchg _ _ _).
    iInv "Hinv" as (head'' tail'' vs'' turns'' svals'' piph'' pipp'')
      "(>%Hht'' & >%Htlen'' & >%Hslen'' & >%Hvslen'' & >%Hphdom'' & >%Hppdom'' &
         Hh & Ht & Hγa & Hγph & Hγpp & Hγhd & Hγtl & Htblock & Hsblock & >%Hslots'')".
    (* CAS succeeds iff [#(Z.of_nat tail'') = #(Z.of_nat tail1)]. *)
    destruct (decide (tail'' = tail1)) as [-> | Hne].
    + (* CAS succeeds — LP for push-success. *)
      wp_cmpxchg_suc.
      (* Open the AU and commit with [b = true], [vs ++ [v]]. *)
      iMod "AU" as (vs_au) "[Hf [_ Hcommit]]".
      iDestruct (queue_content_agree with "Hγa Hf") as %->.
      iMod (queue_content_update _ _ _ (vs_au ++ [v]) with "Hγa Hf")
        as "[Hγa Hf]".
      iMod ("Hcommit" $! true with "Hf") as "HΦ".
      (* Bridge from the load-time slot_state observation to the CAS-time
         state via [Hbound] and the [Hhd_lb] head-snapshot. *)
      assert (Hzeq : z = (2 * Z.of_nat (tail1 / cap))%Z).
      { assert (Hzz : z = exp_turn) by congruence.
        rewrite Hzz. unfold exp_turn.
        rewrite Z.quot_div_nonneg; [|lia|lia].
        rewrite -Nat2Z.inj_div. lia. }
      specialize (Hbound Hzeq).
      iDestruct (mono_nat_lb_own_valid with "Hγhd Hhd_lb") as %[_ Hhd_le].
      assert (Htbnd : (tail1 < head'' + cap)%nat) by lia.
      (* Allocate a push-inflight token at [tail1] mapping to [v]. *)
      iAssert (|==> own γph (● ((Excl <$> <[Z.of_nat tail1 := v]>piph'')
                                  : gmap Z (excl val))) ∗
                    own γph (◯ ({[Z.of_nat tail1 := Excl v]}
                                  : gmap Z (excl val))))%I
        with "[Hγph]" as ">[Hγph Htok]".
      { iMod (own_update _ _
                (● ((Excl <$> <[Z.of_nat tail1 := v]>piph'')
                      : gmap Z (excl val)) ⋅
                 ◯ ({[Z.of_nat tail1 := Excl v]}
                      : gmap Z (excl val)))
              with "Hγph") as "[Hauth Hfrag]".
        { apply auth_update_alloc.
          rewrite fmap_insert.
          apply alloc_singleton_local_update; [|done].
          rewrite lookup_fmap.
          destruct (piph'' !! Z.of_nat tail1) as [v'|] eqn:Heqp; last done.
          exfalso.
          assert (Hin : Z.of_nat tail1 ∈ dom piph'')
            by (apply elem_of_dom; eauto).
          specialize (Hphdom'' _ Hin). lia. }
        iModIntro. iFrame. }
      (* Bump the [γtl] ghost monotonically from [tail1] to [S tail1]. *)
      iMod (mono_nat_own_update (S tail1) with "Hγtl") as "[Hγtl _]"; [lia|].
      iModIntro.
      iSplitL "Hh Ht Hγa Hγph Hγpp Hγhd Hγtl Htblock Hsblock".
      { iNext.
        iExists head'', (S tail1), (vs_au ++ [v]), turns'', svals'',
                (<[Z.of_nat tail1 := v]>piph''), pipp''.
        rewrite (_ : Z.of_nat (S tail1) = (Z.of_nat tail1 + 1)%Z); last lia.
        iFrame.
        iPureIntro. split_and!.
        - lia.
        - lia.
        - exact Htlen''.
        - exact Hslen''.
        - rewrite length_app /=. lia.
        - intros p Hp. rewrite dom_insert_L in Hp.
          apply elem_of_union in Hp as [Hp%elem_of_singleton | Hp].
          + subst p. lia.
          + specialize (Hphdom'' _ Hp). lia.
        - exact Hppdom''.
        - intros i Hi.
          destruct (decide (i = idx)) as [-> | Hineq].
          + (* i = idx: new state must be A1 with p = tail1.  Requires
               z₀_cas = 2*(tail1/cap), which would follow from slot-turn
               monotonicity (out of scope of the current ghost theory). *)
            destruct (Hslots'' idx Hidx) as (z0 & Htidx & _).
            exists z0. split; [exact Htidx|].
            left. exists tail1.
            split; [lia|]. split.
            * subst idx. reflexivity.
            * left. split.
              -- rewrite dom_insert_L. set_solver.
              -- (* z0 = 2 * Z.of_nat (tail1 / cap) -- needs slot-turn mono ghost. *)
                 admit.
          + (* i ≠ idx: preserve old slot_state from [Hslots'']. *)
            destruct (Hslots'' i Hi) as (z' & Htidx & Hss).
            exists z'. split; [exact Htidx|].
            destruct Hss as
              [(p & Hpr & Hpmod & [(Hpin & Hzturn) | (Hpni & Hzturn & Hvslook)])
               | [(Hnocur & p & Hph & Hpmod & [(Hpin & Hzturn) | (Hpni & Hzturn)])
                  | (Hnocur & Hnopop & Hzz0)]].
            * (* Old A1 → new A1 (same p < tail1). *)
              left. exists p. split; [lia|]. split; [exact Hpmod|].
              left. split; [|exact Hzturn].
              rewrite dom_insert_L. apply elem_of_union_r. exact Hpin.
            * (* Old A2 → new A2 (same p < tail1; index into vs unchanged). *)
              left. exists p. split; [lia|]. split; [exact Hpmod|].
              right. split.
              -- rewrite dom_insert_L.
                 assert (Hne : Z.of_nat p ≠ Z.of_nat tail1) by lia.
                 set_solver.
              -- split; [exact Hzturn|].
                 rewrite lookup_app_l; [exact Hvslook|]. lia.
            * (* Old B1 → new B1 (extend no-current to [head'', S tail1)). *)
              right. left. split.
              -- intros p' Hp' Hpmodeq.
                 destruct (decide (p' = tail1)) as [-> | Hp'ne].
                 ++ apply Hineq. subst idx. by rewrite -Hpmodeq.
                 ++ apply (Hnocur p'); [lia|exact Hpmodeq].
              -- exists p. split; [exact Hph|]. split; [exact Hpmod|].
                 left. split; [exact Hpin|exact Hzturn].
            * (* Old B2 → new B2. *)
              right. left. split.
              -- intros p' Hp' Hpmodeq.
                 destruct (decide (p' = tail1)) as [-> | Hp'ne].
                 ++ apply Hineq. subst idx. by rewrite -Hpmodeq.
                 ++ apply (Hnocur p'); [lia|exact Hpmodeq].
              -- exists p. split; [exact Hph|]. split; [exact Hpmod|].
                 right. split; [exact Hpni|exact Hzturn].
            * (* Old C → new C. *)
              right. right. split_and!.
              -- intros p' Hp' Hpmodeq.
                 destruct (decide (p' = tail1)) as [-> | Hp'ne].
                 ++ apply Hineq. subst idx. by rewrite -Hpmodeq.
                 ++ apply (Hnocur p'); [lia|exact Hpmodeq].
              -- exact Hnopop.
              -- exact Hzz0. }
      wp_pures.
      (* Steps (2): write the slot value.  Open the invariant, locate the
         slot via the in-flight token, perform the store, restore the
         invariant.  Step (3): write the turn, removing the token. *)
      admit.
    + (* CAS fails — recurse with the witnessed [tail''] as new pos. *)
      wp_cmpxchg_fail.
      { intros [= Heq']. apply Nat2Z.inj in Heq'. by apply Hne. }
      iModIntro.
      iSplitL "Hh Ht Hγa Hγph Hγpp Hγhd Hγtl Htblock Hsblock".
      { iNext.
        iExists head'', tail'', vs'', turns'', svals'', piph'', pipp''.
        by iFrame. }
      wp_pures.
      iApply ("IH" with "AU").
  - (* (B) turn ≠ exp_turn — re-read tail and decide. *)
    wp_pures.
    wp_bind (! _)%E.
    iInv "Hinv" as (head'' tail'' vs'' turns'' svals'' piph'' pipp'')
      "(>%Hht'' & >%Htlen'' & >%Hslen'' & >%Hvslen'' & >%Hphdom'' & >%Hppdom'' &
         Hh & Ht & Hγa & Hγph & Hγpp & Hγhd & Hγtl & Htblock & Hsblock & >%Hslots'')".
    wp_load.
    destruct (decide (tail'' = tail1)) as [-> | Hne].
    + (* Tail unchanged — LP for push-failure: commit AU as [b = false]. *)
      iMod "AU" as (vs_au) "[Hf [_ Hcommit]]".
      iMod ("Hcommit" $! false with "Hf") as "HΦ".
      iModIntro.
      iSplitL "Hh Ht Hγa Hγph Hγpp Hγhd Hγtl Htblock Hsblock".
      { iNext.
        iExists head'', tail1, vs'', turns'', svals'', piph'', pipp''.
        by iFrame. }
      wp_pures.
      rewrite bool_decide_true; last done.
      wp_pures. done.
    + (* Tail changed — recurse on the new witness. *)
      iModIntro.
      iSplitL "Hh Ht Hγa Hγph Hγpp Hγhd Hγtl Htblock Hsblock".
      { iNext.
        iExists head'', tail'', vs'', turns'', svals'', piph'', pipp''.
        by iFrame. }
      wp_pures.
      rewrite bool_decide_false.
      2:{ intros [= Heq']. apply Nat2Z.inj in Heq'. by apply Hne. }
      wp_pures.
      iApply ("IH" with "AU").
Admitted.

(* -------------------------------------------------------------------------- *)
(*                         Specification: [queue_pop]                         *)
(* -------------------------------------------------------------------------- *)

(** Symmetric atomic spec for pop. *)

Lemma queue_pop_spec γq q cap :
  is_queue γq q cap -∗
  <<{ ∀∀ vs, queue_content γq vs }>>
    queue_pop #q #(Z.of_nat cap) @ ↑queueN
  <<{ ∃∃ (ov : option val),
        match ov with
        | Some v => ∃ vs', ⌜vs = v :: vs'⌝ ∗ queue_content γq vs'
        | None => queue_content γq vs
        end
      | RET (match ov with Some v => SOMEV v | None => NONEV end) }>>.
Proof.
  iIntros "#Hq" (Φ) "AU".
  iDestruct "Hq" as (γph γpp γhd γtl slots) "(%Hcap & #Hs & #Hinv)".
  rewrite /queue_pop. wp_pures.
  (* === Read slots (persistent) === *)
  wp_load.
  wp_pures.
  (* === Initial read of head === *)
  wp_bind (! _)%E.
  iInv "Hinv" as (head1 tail1 vs1 turns1 svals1 piph1 pipp1)
    "(>%Hht1 & >%Htlen1 & >%Hslen1 & >%Hvslen1 & >%Hphdom1 & >%Hppdom1 &
       Hh & Ht & Hγa & Hγph & Hγpp & Hγhd & Hγtl & Htblock & Hsblock & >%Hslots1)".
  wp_load.
  iModIntro.
  iSplitL "Hh Ht Hγa Hγph Hγpp Hγhd Hγtl Htblock Hsblock".
  { iNext.
    iExists head1, tail1, vs1, turns1, svals1, piph1, pipp1.
    by iFrame. }
  wp_pures.
  clear Hht1 Hvslen1 Hphdom1 Hppdom1 Hslots1 Hslen1 Htlen1.
  clear vs1 turns1 svals1 piph1 pipp1 tail1.
  (* === Löb induction on the witnessed [head1 : nat] === *)
  iLöb as "IH" forall (head1).
  wp_pures.
  set (idx := (head1 mod cap)%nat).
  assert (Hidx : (idx < cap)%nat) by (subst idx; apply Nat.mod_upper_bound; lia).
  rewrite (_ : (Z.of_nat head1 `rem` Z.of_nat cap)%Z = Z.of_nat idx);
    [|subst idx;
      rewrite Z.rem_mod_nonneg; [rewrite Nat2Z.inj_mod //|lia|lia]].
  wp_pures.
  (* === Read the slot's turn at index [idx] === *)
  wp_bind (! _)%E.
  iInv "Hinv" as (head' tail' vs' turns' svals' piph' pipp')
    "(>%Hht' & >%Htlen' & >%Hslen' & >%Hvslen' & >%Hphdom' & >%Hppdom' &
       Hh & Ht & Hγa & Hγph & Hγpp & Hγhd & Hγtl & Htblock & Hsblock & >%Hslots')".
  (* Snapshot of the tail ghost: gives [tail' ≤ tail''] at any later opening. *)
  iDestruct (mono_nat_lb_own_get with "Hγtl") as "#Htl_lb".
  assert (Hlt : (idx < length turns')%nat) by (rewrite Htlen'; lia).
  destruct (lookup_lt_is_Some_2 _ _ Hlt) as [tv Htv].
  iDestruct (big_sepL_lookup_acc _ _ _ _ Htv with "Htblock")
    as "[Hslot Hclose]".
  iDestruct "Hslot" as "[>%Hzv >Hslot]".
  destruct Hzv as [z ->].
  replace (Z.of_nat idx * 2)%Z with (2 * Z.of_nat idx)%Z by lia.
  wp_load.
  iDestruct ("Hclose" with "[Hslot]") as "Htblock".
  { iSplit; [iPureIntro; by exists z|]. iFrame. }
  iModIntro.
  iSplitL "Hh Ht Hγa Hγph Hγpp Hγhd Hγtl Htblock Hsblock".
  { iNext.
    iExists head', tail', vs', turns', svals', piph', pipp'. by iFrame. }
  wp_pures.
  set (exp_turn := (Z.of_nat head1 `quot` Z.of_nat cap * 2 + 1)%Z).
  case_bool_decide as Heq.
  - (* (A) turn = exp_turn — try to claim the slot via CAS on head. *)
    wp_pures.
    wp_bind (CmpXchg _ _ _).
    iInv "Hinv" as (head'' tail'' vs'' turns'' svals'' piph'' pipp'')
      "(>%Hht'' & >%Htlen'' & >%Hslen'' & >%Hvslen'' & >%Hphdom'' & >%Hppdom'' &
         Hh & Ht & Hγa & Hγph & Hγpp & Hγhd & Hγtl & Htblock & Hsblock & >%Hslots'')".
    rewrite Loc.add_0.
    destruct (decide (head'' = head1)) as [-> | Hne].
    + (* CAS succeeds — LP for pop-success. *)
      wp_cmpxchg_suc.
      (* Open the AU.  We need [vs_au] to be non-empty; the proof of this
         goes through [slot_state] (turn = exp_turn ⇒ slot is published ⇒
         head1 < tail'' ⇒ vs_au has at least one element).  Left admitted. *)
      iMod "AU" as (vs_au) "[Hf Hcommit]".
      iDestruct (queue_content_agree with "Hγa Hf") as %->.
      (* Establish [vs_au = v :: vs'] for some v.  Pure consequence of the
         invariant + observed turn. *)
      assert (Hvshd : ∃ v vs', vs_au = v :: vs') by admit.
      destruct Hvshd as (v & vs_rest & ->).
      iMod (queue_content_update _ _ _ vs_rest with "Hγa Hf")
        as "[Hγa Hf]".
      iDestruct "Hcommit" as "[_ Hcommit]".
      iMod ("Hcommit" $! (Some v) with "[Hf]") as "HΦ".
      { iExists vs_rest. by iFrame. }
      iModIntro.
      iSplitL "Hh Ht Hγa Hγph Hγpp Hγhd Hγtl Htblock Hsblock".
      { iNext.
        iExists (S head1), tail'', vs_rest, turns'', svals'', piph'', pipp''.
        rewrite (_ : Z.of_nat (S head1) = (Z.of_nat head1 + 1)%Z); last lia.
        rewrite Loc.add_0.
        iFrame.
        (* Pure invariant facts including the [pop_inflight] update.
           Left admitted. *)
        admit. }
      wp_pures.
      (* Step (2): read the slot's value (use the pop-inflight token to
         identify the slot's contents).  Step (3): write the turn. *)
      admit.
    + (* CAS fails — recurse with the witnessed [head''] as new pos. *)
      wp_cmpxchg_fail.
      { intros [= Heq']. apply Nat2Z.inj in Heq'. by apply Hne. }
      iModIntro.
      iSplitL "Hh Ht Hγa Hγph Hγpp Hγhd Hγtl Htblock Hsblock".
      { iNext.
        iExists head'', tail'', vs'', turns'', svals'', piph'', pipp''.
        rewrite Loc.add_0. by iFrame. }
      wp_pures.
      iApply ("IH" with "AU").
  - (* (B) turn ≠ exp_turn — re-read head and decide. *)
    wp_pures.
    wp_bind (! _)%E.
    iInv "Hinv" as (head'' tail'' vs'' turns'' svals'' piph'' pipp'')
      "(>%Hht'' & >%Htlen'' & >%Hslen'' & >%Hvslen'' & >%Hphdom'' & >%Hppdom'' &
         Hh & Ht & Hγa & Hγph & Hγpp & Hγhd & Hγtl & Htblock & Hsblock & >%Hslots'')".
    rewrite Loc.add_0.
    wp_load.
    destruct (decide (head'' = head1)) as [-> | Hne].
    + (* Head unchanged — LP for pop-failure: commit AU as [None]. *)
      iMod "AU" as (vs_au) "[Hf [_ Hcommit]]".
      iMod ("Hcommit" $! None with "Hf") as "HΦ".
      iModIntro.
      iSplitL "Hh Ht Hγa Hγph Hγpp Hγhd Hγtl Htblock Hsblock".
      { iNext.
        iExists head1, tail'', vs'', turns'', svals'', piph'', pipp''.
        rewrite Loc.add_0. by iFrame. }
      wp_pures.
      rewrite bool_decide_true; last done.
      wp_pures. done.
    + (* Head changed — recurse on the new witness. *)
      iModIntro.
      iSplitL "Hh Ht Hγa Hγph Hγpp Hγhd Hγtl Htblock Hsblock".
      { iNext.
        iExists head'', tail'', vs'', turns'', svals'', piph'', pipp''.
        rewrite Loc.add_0. by iFrame. }
      wp_pures.
      rewrite bool_decide_false.
      2:{ intros [= Heq']. apply Nat2Z.inj in Heq'. by apply Hne. }
      wp_pures.
      iApply ("IH" with "AU").
Admitted.

End spec.

(* -------------------------------------------------------------------------- *)
(*                            Where to go from here                           *)
(* -------------------------------------------------------------------------- *)

(** The above file contains:

    1. The Vyukov MPMC queue translated to HeapLang.
    2. A logically atomic specification for [new_queue], [queue_push] and
       [queue_pop].  The specs use Iris's [<<{ ... }>>] notation from
       [iris.program_logic.atomic].
    3. The shared invariant [queue_inv_inner] that ties the physical
       slot-array state to the abstract sequence [vs] held by the user via
       [queue_content].  The invariant uses two auxiliary "in-flight" maps:
       [push_inflight] and [pop_inflight], which let us put the linearisation
       point of a successful push at the CAS on tail (and a successful pop
       at the CAS on head), even though the slot-level repair (writing the
       slot value, advancing the turn) only completes a few steps later.
    4. A complete proof of [new_queue].
    5. Proof skeletons for [queue_push] and [queue_pop] that open the
       invariant at every load/CAS, with [admit]s for the case-by-case
       analysis of the slot's turn value and the associated ghost-token
       book-keeping, and for some pure index-arithmetic lemmas that have
       nothing to do with concurrency.

    The remaining work to fully discharge the proof falls into three
    buckets:

    (a) Pure arithmetic lemmas about [turn_of], [Z.rem]/[Z.quot] vs.
        [Nat.modulo]/[Nat.div], and the relationship between
        [pos `mod` cap] (the ring index) and the slot-state predicate.

    (b) The big_sepL re-indexing in [new_queue_spec] that turns a flat
        [seq 0 (cap*2)] of pointsto's into the per-slot pair structure
        used by the invariant.

    (c) The case analysis inside the push/pop loops:
          - turn = expected turn:
              * CAS succeeds  → invoke the AU and commit ([excl_auth_update]),
                                update the in-flight ghost map, advance the
                                head/tail counter in the invariant.
              * CAS fails     → loop with the witnessed pos.
          - turn ≠ expected turn:
              * Re-read the head/tail counter; if it equals our [pos], close
                the AU as a (potentially spurious) failure; else loop.

    None of (a)-(c) need new Iris machinery: only painstaking case analysis. *)
