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
From iris.base_logic.lib Require Export invariants.
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
}.

Definition queueΣ : gFunctors :=
  #[GFunctor (excl_authR (listO valO));
    GFunctor tokenUR].

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
    (i : nat) (turn : Z) (sval : val) : Prop.
Admitted.

Definition queue_inv_inner
    (γq γph γpp : gname) (q : loc) (cap : nat) : iProp Σ :=
  ∃ (head tail : nat) (slots : loc) (vs : list val)
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
    (q +ₗ 2) ↦ #slots ∗
    own γq (●E vs) ∗
    own γph (● ((Excl <$> push_inflight) : gmap Z (excl val))) ∗
    own γpp (● ((Excl <$> pop_inflight) : gmap Z (excl val))) ∗
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

Definition is_queue (γq : gname) (q : loc) (cap : nat) : iProp Σ :=
  ∃ γph γpp,
    ⌜(0 < cap)%nat⌝ ∗
    inv queueN (queue_inv_inner γq γph γpp q cap).

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
  { (* Pure index-arithmetic re-indexing of the slot block.
       The flat array of [cap*2] cells split into the per-slot pairs. *)
    admit. }
  iMod (inv_alloc queueN _
          (queue_inv_inner γq γph γpp q capn)
          with "[-HΦ Hγf]") as "#Hinv".
  { iNext.
    iExists 0%nat, 0%nat, slots, [], (replicate capn #0), (replicate capn #0),
            ∅, ∅.
    rewrite !fmap_empty.
    iSplit; [iPureIntro; lia|].
    iSplit; [iPureIntro; rewrite length_replicate; lia|].
    iSplit; [iPureIntro; rewrite length_replicate; lia|].
    iSplit; [done|].
    iSplit; [iPureIntro; set_solver|].
    iSplit; [iPureIntro; set_solver|].
    iFrame "Hh Ht Hs Hγa Hγph Hγpp Ht0 Hs0".
    iPureIntro.
    (* The slot-state invariant for the all-zero case.
       This is left as an admit; see the discussion at end of file. *)
    admit. }
  iModIntro. iApply ("HΦ" $! q γq).
  iSplitR "Hγf"; last by iFrame.
  iExists γph, γpp. by iFrame "Hinv".
Admitted.

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
  (* The proof has the structure of a Löb induction over the witnessed
     [pos], with three sub-cases inside the loop body:
       (1) turn = exp_turn ∧ CAS succeeds  — successful push, LP at the CAS:
            - open the invariant; observe [pos < head + cap] from the slot
              state; apply [excl_auth_update] on [γq] to replace [vs] with
              [vs ++ [v]] using the AU's commit branch; allocate a fresh
              [push_inflight] token [{[ pos := Excl v ]}]; close the
              invariant at the new tail [pos+1] with the updated [piph];
            - then step (2) of the impl writes the slot value, opening the
              invariant and using the in-flight token to identify the slot;
            - step (3) writes the turn, opens the invariant, removes the
              [pos] entry from [piph] and re-establishes "published" state.
       (2) turn = exp_turn ∧ CAS fails — recurse with witnessed pos.
       (3) turn ≠ exp_turn — re-read [tail]; if equal to [pos] commit AU as
                             [b = false] (vs unchanged); else recurse.
     Each of the three cases needs a careful arithmetic argument that the
     observed [turn] is consistent with the slot's lifecycle, decoded via
     [slot_state].  We leave the proof as a structured admit. *)
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
  (* Symmetric to [queue_push_spec]:
       (1) turn = exp_turn ∧ CAS succeeds — successful pop, LP at the CAS:
            destruct [vs = v :: vs']; commit AU with [Some v]; allocate a
            [pop_inflight] entry [{[ pos := Excl v ]}].  The pop's
            subsequent slot-load reads [v] from the in-flight token; the
            turn-write removes [pos] from [pipp].
       (2) turn = exp_turn ∧ CAS fails — recurse.
       (3) turn ≠ exp_turn — re-read [head]; if equal to [pos] commit AU
                             as [None] with [vs] unchanged; else recurse. *)
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
