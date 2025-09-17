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

Definition partial_morphism {X Y}
  (domain : X -> Prop) (range : Y -> Prop) (f : X -> option Y) : Prop :=
  (forall (x : X) (y : Y), f x = Some y -> range y) (* f is contained in the range *)
  /\ (forall (x : X), f x = None -> (not (domain x))) (* f always returns a value in its domain *).

Definition and_then {X Y Z}
  (f : X -> option Y) (g : Y -> option Z) : X -> option Z :=
  fun x =>
    match (f x) with
    | Some y => (g y)
    | None => None
    end.

Definition pointwise_equal {X Y}
  (domain : X -> Prop) (f g : X -> option Y) : Prop :=
  forall x, domain x -> f x = g x.

Theorem partial_compose {X Y Z} : forall
  (first : X -> Prop) (second : Y -> Prop) (third : Z -> Prop)
  (f : X -> option Y) (g : Y -> option Z),
  partial_morphism first second f ->
  partial_morphism second third g ->
  partial_morphism first third (and_then f g).
Proof.
  unfold partial_morphism. intros.
  destruct H as [f_range f_domain]. destruct H0 as [g_range g_domain].
  split.
  - unfold and_then. intros x z. destruct (f x) as [y| ] eqn:current_case; try discriminate; intros.
    apply g_range with (x := y). assumption.
  - unfold and_then. intros x. destruct (f x) as [y| ] eqn:current_case; intros.
    + exfalso. apply ((g_domain y H) (f_range x y current_case)).
    + apply f_domain. apply current_case.
Qed.

Theorem strengthen_domain {X Y} : forall
  (strong_domain : X -> Prop) (weak_domain : X -> Prop) (range : Y -> Prop) (f : X -> option Y),
  (forall x, (strong_domain x) -> weak_domain x) ->
  partial_morphism weak_domain range f ->
  partial_morphism strong_domain range f.
Proof.
  unfold partial_morphism.
  intros strong_domain weak_domain range f domain_assertion [f_range f_domain].
  split.
  - apply f_range.
  - unfold not. intros x x_undefined x_in_strong_domain.
    apply ((f_domain x x_undefined) (domain_assertion x x_in_strong_domain)).
Qed.

Theorem weaken_range {X Y} : forall
  (domain : X -> Prop) (strong_range : Y -> Prop) (weak_range : Y -> Prop) (f : X -> option Y),
  (forall y, (strong_range y) -> weak_range y) ->
  partial_morphism domain strong_range f ->
  partial_morphism domain weak_range f.
Proof.
  unfold partial_morphism.
  intros domain strong_range weak_range f range_assertion [f_range f_domain].
  split.
  - intros x y f_x_is_some_y. apply range_assertion.
    apply f_range with (x := x).
    apply f_x_is_some_y.
  - apply f_domain.
Qed.

Definition ordered_enumeration (range : t -> Prop) (count : Z) (get_nth : Z -> option t) (get_index : t -> option Z) : Prop :=
  (partial_morphism (interval count) range get_nth)
  /\ (partial_morphism range (interval count) get_index)
  /\ (pointwise_equal (interval count) (and_then get_nth get_index) (fun x => Some x))
  /\ (pointwise_equal range (and_then get_index get_nth) (fun x => Some x))
  /\ (forall (n m : Z) (element0 element1 : t),
       (interval count n) ->
       (interval count m) ->
       (n < m)%Z ->
       (Some element0 = get_nth n) ->
       (Some element1 = get_nth m) ->
       element0 < element1) (* these redundant hypothesis feel a bit dumb but ok *).

Theorem get_nth_unique : forall range count f0 f1 g0 g1,
  ordered_enumeration range count f0 g0 ->
  ordered_enumeration range count f1 g1 ->
  (pointwise_equal (interval count) f0 f1)
  /\ (pointwise_equal range g0 g1).
Proof.
  intros range count.
  remember (count - 1)%Z as predecessor.
  assert (count = predecessor + 1)%Z by lia.
  subst count. clear Heqpredecessor.
  assert (predecessor < 0 \/ 0 <= predecessor)%Z as [nonnegative_count | positive_count] by lia.
  - admit. (* vacuously true *)
  - intros. generalize dependent range.
    apply Wf_Z.natlike_ind with (x := predecessor); try apply positive_count.
    + simpl. intros. unfold pointwise_equal. split.
      * admit.
      * intros x x_is_zero. unfold interval in x_is_zero.
        assert (partial_morphism range (interval 1) g0) by (
          unfold ordered_enumeration in H; destruct H as [a [b c]]; apply b).
        assert (partial_morphism range (interval 1) g1) by (
          unfold ordered_enumeration in H0; destruct H0 as [a [b c]]; apply b).
        unfold partial_morphism in H1, H2.
        destruct H1, H2.
        destruct (g0 x). (* oof so annoying *)
        -- admit.
        -- admit.
    + intros. admit.
Admitted.

End FiniteEnumerations.
