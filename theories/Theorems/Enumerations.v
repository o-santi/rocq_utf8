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

(* Get all the nice notations for free *)
Local Open Scope list_scope.
                        
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

Theorem partial_induction {X Y}
  (domain : X -> Prop) (range : Y -> Prop) (f : X -> option Y)
  (P : option Y -> Prop) :
  partial_morphism domain range f ->
  (forall y, (range y) -> (exists x, f x = Some y ) -> P (Some y)) ->
  forall x, (domain x) -> P (f x).
Proof.
  unfold partial_morphism.
  intros [f_range f_domain] induction_principle x x_in_domain.
  destruct (f x) eqn:current_case.
  - assert (range y) by (apply (f_range x y current_case)).
    apply (induction_principle y H).
    exists x. apply current_case.
  - assert (~ (domain x)).
    + apply f_domain. apply current_case.
    + exfalso. apply (H x_in_domain).
Qed.

Record Ordered {T} (compare: T -> T -> comparison) := {
    eq : forall t1 t2, compare t1 t2 = Eq <-> t1 = t2;
    antisym : forall t1 t2, compare t1 t2 = CompOpp (compare t2 t1);
    trans : forall t1 t2 t3 res, compare t1 t2 = res -> compare t2 t3 = res -> compare t1 t3 = res;
  }.

Definition increasing {T1 T2}
  (domain: T1 -> Prop)
  (compare1: T1 -> T1 -> comparison) (compare2: T2 -> T2 -> comparison)
  (to: T1 -> option T2) :=
  forall n m, (domain n) -> (domain m) ->
      match (to n, to m) with
      | (Some a, Some b) => (compare1 n m) = (compare2 a b)
      | _ => False
      end.

Record OrderedPartialIsomorphism {T1 T2} (domain: T1 -> Prop) (range: T2 -> Prop) (compare1: T1 -> T1 -> comparison) (compare2: T2 -> T2 -> comparison) (to: T1 -> option T2) (from: T2 -> option T1)
   := {
    ordered1 : @Ordered T1 compare1;
    ordered2 : @Ordered T2 compare2;
    from_morphism : partial_morphism domain range to;
    to_morphism: partial_morphism range domain from;
    from_to_id : pointwise_equal domain (and_then to from) (fun x => Some x);
    to_from_id : pointwise_equal range (and_then from to) (fun x => Some x);
    from_preserves_compare : increasing domain compare1 compare2 to;
  }.


(* Lemma interval_enumeration_unique : forall count f g,
  ordered_enumeration (interval count) count f g ->
   ((pointwise_equal (interval count) f (fun x => Some x))
   /\ (pointwise_equal (interval count) g (fun x => Some x))).
   Admitted. *)
(* TODO: parameterize other type in ordered_enumeration *)

(* TODO: if get_nth is increasing then so is get_index *)

(* TODO: the inverse function is unique in the sense of pointwise_equal *)

Theorem finite_partial_isomorphism_unique {T0 T1} (count: Z) (range0: T0 -> Prop) (range1: T1 -> Prop) compare0 compare1:
  forall from0 from1 from2 to0 to1 to2,
    OrderedPartialIsomorphism (interval count) range0 Z.compare compare0 to0 from0 ->
    OrderedPartialIsomorphism (interval count) range1 Z.compare compare1 to1 from1 ->
    partial_morphism range0 range1 to2 ->
    partial_morphism range1 range0 from2 ->
    increasing range0 compare0 compare1 to2 ->
    increasing range1 compare1 compare0 from2 ->
  (pointwise_equal range0 to2 (and_then from0 to1))
  /\ (pointwise_equal range1 from2 (and_then from1 to0)).
Proof.
  (* intros range count. *)
  (* remember (count - 1)%Z as predecessor. *)
  (* assert (count = predecessor + 1)%Z by lia. *)
  (* subst count. clear Heqpredecessor. *)
  (* assert (predecessor < 0 \/ 0 <= predecessor)%Z as [nonnegative_count | positive_count] by lia. *)
  (* - admit. (* vacuously true *) *)
  (* - intros. generalize dependent range. *)
  (*   apply Wf_Z.natlike_ind with (x := predecessor); try apply positive_count. *)
  (*   + simpl. intros. unfold pointwise_equal. split. *)
  (*     * admit. *)
  (*     * intros x x_is_zero. unfold interval in x_is_zero. *)
  (*       assert (partial_morphism range (interval 1) g0) by ( *)
  (*         unfold ordered_enumeration in H; destruct H as [a [b c]]; apply b). *)
  (*       assert (partial_morphism range (interval 1) g1) by ( *)
  (*         unfold ordered_enumeration in H0; destruct H0 as [a [b c]]; apply b). *)
  (*       apply partial_induction *)
  (*         with (f := g0) (x := x) (domain := range) (range := (interval 1)); *)
  (*         try assumption; intros. (* that's what I'm talking about! *) *)
  (*       apply partial_induction *)
  (*         with (f := g1) (x := x) (domain := range) (range := (interval 1)); *)
  (*         try assumption; intros. *)
  (*       unfold interval in H3, H4. assert (y = y0%Z) by lia. *)
  (*       rewrite H5. reflexivity. *)
  (*   + intros. admit. *)
Admitted.
