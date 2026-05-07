(**
 * Lock-free MPMC ring-buffer queue translated to HeapLang (Vyukov, 2010).
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
 *)

From iris.heap_lang Require Import lang notation.
From iris.prelude Require Import options.

(** Allocate a new queue with the given capacity.
    All head/tail counters and slot turns are initialised to 0 via AllocN. *)
Definition new_queue : val :=
  λ: "cap",
    (* slots array: cap * 2 cells, all zero (turn=0, val=0 per slot) *)
    let: "slots" := AllocN ("cap" * #2) #0 in
    (* queue header: [head | tail | slots_ptr], then overwrite slots_ptr *)
    let: "q" := AllocN #3 #0 in
    "q" +ₗ #2 <- "slots";;
    "q".

(** Push [v] onto queue [q] with capacity [cap].
    Returns [#true] on success, [#false] if the queue is full. *)
Definition queue_push : val :=
  λ: "q" "cap" "v",
    let: "slots" := !("q" +ₗ #2) in
    (* Loop variable: the tail position we are trying to claim. *)
    (rec: "loop" "pos" :=
       let: "idx"       := "pos" `rem` "cap" in
       let: "turn_ptr"  := "slots" +ₗ ("idx" * #2) in
       let: "turn"      := !"turn_ptr" in
       (* Expected turn for a push at logical position pos:
          TURN(pos)*2  =  (pos `quot` cap) * 2                              *)
       let: "exp_turn"  := ("pos" `quot` "cap") * #2 in
       if: "exp_turn" = "turn"
       then
         (* Slot is free; try to claim the tail counter. *)
         let: "r" := CmpXchg ("q" +ₗ #1) "pos" ("pos" + #1) in
         if: Snd "r"
         then
           (* We own the slot — write the value, then publish by setting turn. *)
           ("slots" +ₗ ("idx" * #2 + #1)) <- "v";;
           "turn_ptr" <- "exp_turn" + #1;;
           #true
         else
           (* tail changed; Fst "r" is the witnessed current tail *)
           "loop" (Fst "r")
       else
         (* Slot is not in the expected state; check whether the queue is full. *)
         let: "new_pos" := !("q" +ₗ #1) in
         if: "new_pos" = "pos"
         then #false          (* tail did not advance since we last read it *)
         else "loop" "new_pos")
    !("q" +ₗ #1).

(** Pop from queue [q] with capacity [cap].
    Returns [SOME v] on success, [NONE] if the queue is empty. *)
Definition queue_pop : val :=
  λ: "q" "cap",
    let: "slots" := !("q" +ₗ #2) in
    (* Loop variable: the head position we are trying to claim. *)
    (rec: "loop" "pos" :=
       let: "idx"       := "pos" `rem` "cap" in
       let: "turn_ptr"  := "slots" +ₗ ("idx" * #2) in
       let: "turn"      := !"turn_ptr" in
       (* Expected turn for a pop at logical position pos:
          TURN(pos)*2 + 1  =  (pos `quot` cap) * 2 + 1                      *)
       let: "exp_turn"  := ("pos" `quot` "cap") * #2 + #1 in
       if: "exp_turn" = "turn"
       then
         (* Slot is full; try to claim the head counter. *)
         let: "r" := CmpXchg ("q" +ₗ #0) "pos" ("pos" + #1) in
         if: Snd "r"
         then
           (* We own the slot — read the value, then release by advancing turn. *)
           let: "v" := !("slots" +ₗ ("idx" * #2 + #1)) in
           "turn_ptr" <- ("pos" `quot` "cap") * #2 + #2;;
           SOME "v"
         else
           (* head changed; Fst "r" is the witnessed current head *)
           "loop" (Fst "r")
       else
         (* Slot is not ready; check whether the queue is empty. *)
         let: "new_pos" := !("q" +ₗ #0) in
         if: "new_pos" = "pos"
         then NONE            (* head did not advance since we last read it *)
         else "loop" "new_pos")
    !("q" +ₗ #0).
