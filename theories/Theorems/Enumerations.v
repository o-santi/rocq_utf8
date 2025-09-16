(*
From Coq Require Import Strings.Byte.
From Coq Require Import Lists.List. Import ListNotations.

Require Import Utf8.Parser.
Require Import Utf8.Spec.
Require Import Utf8.Theorems.Order.
*)

Require Import List.
From Coq Require Import Structures.Orders.
From Coq Require Import ZArith.BinInt.
From Coq Require Import Lia.
Import ListNotations.

Module FiniteEnumerations (Import O : OrderedTypeFull').

(* Get all the nice notations for free *)
Local Open Scope list_scope.

(* t is our generic ordered type *)

Definition interval (count n : Z) : Prop :=
  (0 <= n /\ n < count)%Z.

Definition ordered_enumeration (count : Z) (get_nth : Z -> option t) (get_index : t -> Z) : Prop :=
  (forall (n : Z) (element : t), get_nth n = Some element -> get_index element = n) (* get_index is a left-inverse for get_nth *)
  /\ (forall (element : t), get_nth (get_index element) = Some element) (* get_index is a right-inverse for get_nth *)
  /\ (forall (element : t), (interval count (get_index element))) (* get_index ranges on the interval *)
  /\ (forall (n : Z), get_nth n = None -> (not (interval count n))) (* get_nth is always defined in the interval *)
  /\ (forall (n m : Z) (element0 element1 : t), (* Strictly increasing: each element is strictly less than the next *)
       interval count n ->
       interval count m ->
       (n < m)%Z ->
       get_nth n = Some element0 ->
       get_nth m = Some element1 ->
       element0 < element1).

Theorem get_nth_unique : forall count f0 f1 g0 g1,
  ordered_enumeration count f0 g0 ->
  ordered_enumeration count f1 g1 ->
  ((forall n,
    interval count n ->
    f0 n = f1 n)
  /\ (forall element, g0 element = g1 element)).
Proof.
  intros.
  assert (count < 0 \/ 0 <= count)%Z by lia.
  destruct H1.
  - admit. (* in this case forall n, ~(interval count n)) *)
  - apply Z.right_induction with (z := 0%Z) (n := count); try apply H1.
    * (* wtf? *) admit.
    * admit.
    * admit.
Admitted.

End FiniteEnumerations.
