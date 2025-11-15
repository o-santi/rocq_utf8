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

Record PartialIsomorphism {T1 T2}
  (domain: T1 -> Prop) (range: T2 -> Prop)
  (to: T1 -> option T2) (from: T2 -> option T1) :=
  {
    from_morphism : partial_morphism domain range to;
    to_morphism: partial_morphism range domain from;
    from_to_id : pointwise_equal domain (and_then to from) (fun x => Some x);
    to_from_id : pointwise_equal range (and_then from to) (fun x => Some x);
  }.

(* TODO: bundle the data in a record *)
Record OrderedPartialIsomorphism {T1 T2}
  (domain: T1 -> Prop) (range: T2 -> Prop)
  (compare1: T1 -> T1 -> comparison) (compare2: T2 -> T2 -> comparison)
  (to: T1 -> option T2) (from: T2 -> option T1)
   := {
    opi_ordered1 : @Ordered T1 compare1;
    opi_ordered2 : @Ordered T2 compare2;
    opi_isomorphism : @PartialIsomorphism T1 T2 domain range to from;
    opi_to_preserves_compare : increasing domain compare1 compare2 to;
  }.

Definition partially_covers {X} (domain : X -> Prop) (compare : X -> X -> comparison) (x0 x1 : X) : Prop :=
  (compare x0 x1 = Lt)
  /\ (forall x2, not ((compare x0 x2 = Lt) /\ (compare x2 x1 = Lt) /\ (domain x2))).

Definition partially_minimum {X} (domain : X -> Prop) (compare : X -> X -> comparison) (x0 : X) : Prop :=
  forall x1, ~ (domain x1 /\ compare x0 x1 = Lt).

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

Theorem partial_morphism_induction {X Y}
  (domain : X -> Prop) (range : Y -> Prop) (f : X -> option Y)
  (P : X -> option Y -> Prop) :
  partial_morphism domain range f ->
  (forall x y, (domain x) -> (range y) -> (f x = Some y) -> P x (Some y)) ->
  forall (x: X), (domain x) -> P x (f x).
Proof.
  unfold partial_morphism.
  intros [f_range f_domain] induction_principle x x_in_domain.
  destruct (f x) eqn:current_case.
  - assert (range y) by (apply (f_range x y current_case)).
    apply (induction_principle x y x_in_domain H).
    apply current_case.
  - assert (~ (domain x)).
    + apply f_domain. apply current_case.
    + exfalso. apply (H x_in_domain).
Qed.

Lemma some_injective : forall {X} (x0 x1 : X),
  Some x0 = Some x1 ->
  x0 = x1.
Proof.
  intros.
  inversion H; reflexivity.
Qed.

Theorem partial_isomorphism_symmetry  {X Y}
  (domain : X -> Prop) (range : Y -> Prop)
  (to : X -> option Y) (from : Y -> option X)
  (iso : PartialIsomorphism domain range to from):
  PartialIsomorphism range domain from to.
Proof.
Admitted.

Theorem partial_isomorphism_elimination {X Y}
  (domain : X -> Prop) (range : Y -> Prop) (to : X -> option Y)
  (from : Y -> option X) (x : X) :
  PartialIsomorphism domain range to from ->
  domain x ->
  exists y,
    ((range y)
    /\ (from y = Some x)
    /\ (to x = Some y)).
Proof.
Admitted.

Lemma ordered_partial_isomorphism_increasing {T1 T2}
  (domain: T1 -> Prop) (range: T2 -> Prop)
  (compare1: T1 -> T1 -> comparison) (compare2: T2 -> T2 -> comparison)
  (to: T1 -> option T2) (from: T2 -> option T1)
  (x0 x1 : T1) (y0 y1 : T2)
  (iso : OrderedPartialIsomorphism domain range compare1 compare2 to from) :
  domain x0 -> domain x1 ->
  range y0 -> range y1 ->
  to x0 = Some y0 -> to x1 = Some y1 ->
  from y0 = Some x0 -> from y1 = Some x1 ->
  compare1 x0 x1 = compare2 y0 y1.
Proof.
Admitted.

Lemma ordered_partial_isomorphism_from_increasing {T1 T2}
  (domain: T1 -> Prop) (range: T2 -> Prop)
  (compare1: T1 -> T1 -> comparison) (compare2: T2 -> T2 -> comparison)
  (to: T1 -> option T2) (from: T2 -> option T1) :
  OrderedPartialIsomorphism domain range compare1 compare2 to from ->
  increasing range compare2 compare1 from.
Proof.
  intros iso. destruct iso as [_ _ iso to_preserves_compare].
  unfold increasing. intros x0 x1 range_x0 range_x1.
  apply partial_isomorphism_symmetry in iso.
  generalize (partial_isomorphism_elimination range domain from to x0 iso range_x0).
  intros [y0 [domain_y0 [x0_definition y0_definition]]].
  rewrite y0_definition.
  generalize (partial_isomorphism_elimination range domain from to x1 iso range_x1).
  intros [y1 [domain_y1 [x1_definition y1_definition]]].
  rewrite y1_definition.
  generalize (to_preserves_compare y0 y1 domain_y0 domain_y1).
  rewrite x0_definition, x1_definition.
  intros; symmetry; assumption.
Qed.

Lemma ordered_partial_isomorphism_symmetry  {T1 T2}
  (domain: T1 -> Prop) (range: T2 -> Prop)
  (compare1: T1 -> T1 -> comparison) (compare2: T2 -> T2 -> comparison)
  (to: T1 -> option T2) (from: T2 -> option T1) :
  OrderedPartialIsomorphism domain range compare1 compare2 to from ->
  OrderedPartialIsomorphism range domain compare2 compare1 from to.
Proof.
Admitted.

Lemma ordered_partial_isomorphism_composition {T1 T2 T3}
  {domain: T1 -> Prop} {intermediate: T2 -> Prop} {range: T3 -> Prop}
  {compare1: T1 -> T1 -> comparison} {compare2: T2 -> T2 -> comparison}
  {compare3: T3 -> T3 -> comparison}
  {to0: T1 -> option T2} {to1: T2 -> option T3}
  {from0: T2 -> option T1} {from1: T3 -> option T2}
  (iso0 : OrderedPartialIsomorphism domain intermediate compare1 compare2 to0 from0)
  (iso1 : OrderedPartialIsomorphism intermediate range compare2 compare3 to1 from1):
  OrderedPartialIsomorphism
    domain range
    compare1 compare3
    (and_then to0 to1) (and_then from1 from0).
Proof.
Admitted.

Theorem Z_covering_classification : forall n m,
  partially_covers (fun _ => True) Z.compare n m <-> m = (n + 1)%Z.
Proof.
  intros n m; split; intros.
  - destruct H as [n_m_compare covering_property].
    destruct (Z.compare m (n+1))%Z eqn:m_Sn_compare.
    + apply Z.compare_eq; try assumption.
    + exfalso. rewrite Z.compare_lt_iff in n_m_compare.
      rewrite Z.compare_lt_iff in m_Sn_compare. lia.
    + exfalso. apply covering_property with (x2 := (n+1)%Z).
      split.
      * rewrite -> Z.compare_lt_iff. lia.
      * rewrite -> Z.compare_lt_iff. rewrite Z.compare_gt_iff in m_Sn_compare.
        rewrite Z.compare_lt_iff in n_m_compare. lia.
  - unfold partially_covers. subst m. split.
    + rewrite Z.compare_lt_iff. lia.
    + intros x2 [H0 H1]. rewrite Z.compare_lt_iff in H0.
      rewrite Z.compare_lt_iff in H1. lia.
Qed.

Theorem Z_inteval_minimum_zero : forall n,
  partially_minimum (interval n) Z.compare 0%Z.
Proof.
Admitted.

Theorem partially_covers_unique {X} (domain : X -> Prop) (compare : X -> X -> comparison) (x0 x1 x2 : X) :
  Ordered compare ->
  domain x0 -> domain x1 -> domain x2 ->
  partially_covers domain compare x0 x1 ->
  partially_covers domain compare x0 x2 ->
  x1 = x2.
Proof.
  unfold partially_covers.
  intros [eq antisym trans]
    domain_x0 domain_x1 domain_x2
    [x0_x1_compare x0_x1_no_between]
    [x0_x2_compare x0_x2_no_between].
  destruct (compare x1 x2) eqn:x1_x2_compare.
  - rewrite <- eq. apply x1_x2_compare.
  - exfalso. apply (x0_x2_no_between x1). do 2 (try split; try assumption).
  - exfalso. generalize (antisym x2 x1). rewrite x1_x2_compare; simpl.
    clear x1_x2_compare. intros x1_x2_compare.
    apply (x0_x1_no_between x2). do 2 (try split; try assumption).
Qed.

Theorem partially_minimum_unique {X} (domain : X -> Prop) (compare : X -> X -> comparison) (x0 x1 : X) :
  domain x0 -> domain x1 ->
  partially_minimum domain compare x0 ->
  partially_minimum domain compare x1 ->
  x0 = x1.
Proof.
Admitted.

Theorem ordered_isomorphism_preserves_cover {T1 T2}
  (domain: T1 -> Prop) (range: T2 -> Prop)
  (compare1: T1 -> T1 -> comparison) (compare2: T2 -> T2 -> comparison)
  (to: T1 -> option T2) (from: T2 -> option T1)
  (x0 x1 : T1) (y0 y1 : T2) :
  OrderedPartialIsomorphism domain range compare1 compare2 to from ->
  domain x0 -> domain x1 ->
  range y0 -> range y1 ->
  to x0 = Some y0 -> to x1 = Some y1 ->
  from y0 = Some x0 -> from y1 = Some x1 ->
  partially_covers domain compare1 x0 x1 ->
  partially_covers range compare2 y0 y1.
Proof.
  intros iso domain_x0 domain_x1
    range_y0 range_y1 y0_definition y1_definition x0_definition x1_definition.
  unfold partially_covers. intros [x0_x1_comparison x0_x1_no_between]. split.
  - rewrite <- x0_x1_comparison. symmetry.
    apply
      (ordered_partial_isomorphism_increasing domain range compare1 compare2 to from x0 x1 y0 y1); assumption.
  - unfold not; intros y2 [y0_y2_comparison [y2_y1_comparison range_y2]].
    unfold not in x0_x1_no_between.
    apply ordered_partial_isomorphism_symmetry in iso.
    generalize
      (partial_isomorphism_elimination range domain from to y2
        (opi_isomorphism range domain compare2 compare1 from to iso)
        range_y2);
    intros [x2 [domain_x2 [y2_definition x2_definition]]].
    apply (x0_x1_no_between  x2).
    apply ordered_partial_isomorphism_symmetry in iso.
    split; try split.
    + rewrite (ordered_partial_isomorphism_increasing
        domain range compare1 compare2 to from x0 x2 y0 y2); assumption.
    + rewrite (ordered_partial_isomorphism_increasing
        domain range compare1 compare2 to from x2 x1 y2 y1); assumption.
    + assumption.
Qed.

Theorem ordered_isomorphism_preserves_minimum {T1 T2}
  (domain: T1 -> Prop) (range: T2 -> Prop)
  (compare1: T1 -> T1 -> comparison) (compare2: T2 -> T2 -> comparison)
  (to: T1 -> option T2) (from: T2 -> option T1)
  (x : T1) (y : T2) :
  OrderedPartialIsomorphism domain range compare1 compare2 to from ->
  domain x -> range y ->
  to x = Some y -> from y = Some x ->
  partially_minimum domain compare1 x ->
  partially_minimum range compare2 y.
Proof.
Admitted.

Theorem finite_partial_isomorphism_unique_aux {T0 T1} (count: Z) (range0: T0 -> Prop) (range1: T1 -> Prop) compare0 compare1:
  forall from0 from1 to0 to1 to2,
  OrderedPartialIsomorphism (interval count) range0 Z.compare compare0 to0 from0 ->
  OrderedPartialIsomorphism (interval count) range1 Z.compare compare1 to1 from1 ->
  partial_morphism range0 range1 to2 ->
  increasing range0 compare0 compare1 to2 ->
  (pointwise_equal range0 to2 (and_then from0 to1)).
Proof.
  intros from0 from1 to0 to1 to2 iso0 iso1 morphism increasing.
  apply ordered_partial_isomorphism_symmetry in iso0.
  generalize (ordered_partial_isomorphism_composition iso0 iso1); intros iso2.
  admit.
Admitted.

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
  intros from0 from1 from2 to0 to1 to2 iso0 iso1 morphism0 morphism1
  increasing0 increasing1. admit.
Admitted.
