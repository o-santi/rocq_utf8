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
  forall x1, ~ (domain x1 /\ compare x1 x0 = Lt).

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

Theorem partial_morphism_elimination {X Y}
  {domain : X -> Prop} {range : Y -> Prop} {f : X -> option Y} :
  partial_morphism domain range f ->
  forall (x : X),
    domain x ->
  exists y,
    ((range y) /\ (f x = Some y)).
Proof.
  intros [f_some f_none] x domain_x.
  destruct (f x) as [y|] eqn:f_x.
  - exists y. repeat split. apply f_some in f_x. apply f_x.
  - apply f_none in f_x. apply f_x in domain_x. exfalso. auto.
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
  destruct iso.
  split; assumption.
Qed.
  

Theorem partial_isomorphism_elimination {X Y}
  {domain : X -> Prop} {range : Y -> Prop} {to : X -> option Y}
  {from : Y -> option X} {x : X} :
  PartialIsomorphism domain range to from ->
  domain x ->
  exists y,
    ((range y)
    /\ (from y = Some x)
    /\ (to x = Some y)).
Proof.
  intros partial_iso x_domain.
  destruct partial_iso.
  destruct from_morphism0 as [to_some to_none].
  destruct to_morphism0 as [from_some from_none].
  destruct (to x) eqn:y_definition.
  - exists y. repeat split. apply to_some with (x:=x). assumption.
    apply to_some in y_definition as y_range.
    unfold pointwise_equal in to_from_id0, from_to_id0.
    apply from_to_id0 in x_domain.
    unfold and_then in y_range, x_domain.
    rewrite y_definition in x_domain.
    apply x_domain.
  - apply to_none in y_definition. apply y_definition in x_domain. exfalso. apply x_domain.
Qed.

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
  intros domain_x0 domain_x1 range_y0 range_y1 y0_definition y1_definition x0_definition x1_definition.
  destruct iso.
  specialize (opi_to_preserves_compare0 x0 x1 domain_x0 domain_x1).
  rewrite y0_definition, y1_definition in opi_to_preserves_compare0.
  assumption.
Qed.

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
  generalize (partial_isomorphism_elimination iso range_x0).
  intros [y0 [domain_y0 [x0_definition y0_definition]]].
  rewrite y0_definition.
  generalize (partial_isomorphism_elimination iso range_x1).
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
  intros iso.
  destruct iso.
  destruct opi_isomorphism0.
  split; try assumption.
  - split; assumption.
  - intros x0 y0 range_x0 range_y0.
    destruct to_morphism0 as [from_some from_none].
    destruct (from x0) as [x1|] eqn:from_x0;
      [| apply from_none in from_x0; apply from_x0 in range_x0; exfalso; auto].
    destruct (from y0) as [y1|] eqn:from_y0;
      [| apply from_none in from_y0; apply from_y0 in range_y0; exfalso; auto].
    apply from_some in from_x0 as x1_domain, from_y0 as y1_domain.
    specialize (to_from_id0 x0 range_x0) as to_x1.
    specialize (to_from_id0 y0 range_y0) as to_y1.
    unfold and_then in to_x1, to_y1. rewrite from_x0 in to_x1. rewrite from_y0 in to_y1.
    specialize (opi_to_preserves_compare0 x1 y1 x1_domain y1_domain).
    rewrite to_x1, to_y1 in opi_to_preserves_compare0.
    symmetry. apply opi_to_preserves_compare0.
Qed.

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

Theorem Z_interval_minimum_zero : forall n,
  partially_minimum (interval n) Z.compare 0%Z.
Proof.
  intros n zero [interval_zero zero_less_than_zero].
  unfold interval in interval_zero.
  destruct interval_zero.
  destruct (Z.compare_spec zero 0).
  - subst. discriminate.
  - lia.
  - discriminate.
Qed.

Theorem Z_interval_succ_partially_covers : forall count n,
    partially_covers (interval count) Z.compare n (Z.succ n).
Proof.
  intros count n.
  split.
  - apply Z.lt_succ_diag_r.
  - intros n_intra [n_less_n_intra [n_intra_less_succ n_intra_interval]].
    rewrite Z.compare_lt_iff in n_less_n_intra, n_intra_less_succ. lia.
Qed.

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

Definition partially_minimum_unique {X} (domain : X -> Prop) (compare : X -> X -> comparison)  (x0 x1 : X) :
  forall (ordered: Ordered compare),
  domain x0 -> domain x1 ->
  partially_minimum domain compare x0 ->
  partially_minimum domain compare x1 ->
  x0 = x1.
Proof.
  intros ordered domain_x0 domain_x1 minimum_x0 minimum_x1.
  unfold partially_minimum in minimum_x0, minimum_x1.
  destruct ordered.
  destruct (compare x0 x1) eqn:compare_x0_x1.
  - apply eq0. apply compare_x0_x1. 
  - specialize (minimum_x1 x0).
    assert (domain x0 /\ compare x0 x1 = Lt) as F.
    split; assumption. apply minimum_x1 in F. exfalso. apply F.
  - specialize (minimum_x0 x1).
    rewrite antisym0 in compare_x0_x1.
    apply (f_equal CompOpp) in compare_x0_x1.
    rewrite CompOpp_involutive in compare_x0_x1. simpl in compare_x0_x1.
    assert (domain x1 /\ compare x1 x0 = Lt) as F.
    split; assumption. apply minimum_x0 in F. exfalso. apply F.
Qed.

Theorem ordered_isomorphism_preserves_cover {T1 T2}
  {domain: T1 -> Prop} {range: T2 -> Prop}
  {compare1: T1 -> T1 -> comparison} {compare2: T2 -> T2 -> comparison}
  {to: T1 -> option T2} {from: T2 -> option T1}
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
      (partial_isomorphism_elimination
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
  intros iso domain_x range_y y_definition x_definition minimum_x.
  intros n [range_n n_less_than_y].
  destruct iso. unfold partially_minimum in minimum_x.
  destruct opi_isomorphism0.
  unfold partial_morphism.
  specialize (to_from_id0 n range_n) as n_definition.
  unfold and_then in n_definition.
  destruct (from n) as [m|] eqn:m_definition; [| discriminate].
  destruct to_morphism0 as [to_some to_none].
  specialize (to_some n m m_definition) as domain_m.
  specialize (opi_to_preserves_compare0 x m domain_x domain_m).
  rewrite y_definition, n_definition in opi_to_preserves_compare0.
  destruct opi_ordered4 as [_ comp1_antisym _].
  rewrite comp1_antisym in opi_to_preserves_compare0.
  rewrite n_less_than_y in opi_to_preserves_compare0.
  destruct opi_ordered3 as [_ comp2_antisym _].
  rewrite comp2_antisym in opi_to_preserves_compare0.
  apply (f_equal CompOpp) in opi_to_preserves_compare0.
  rewrite CompOpp_involutive in opi_to_preserves_compare0.
  simpl in opi_to_preserves_compare0.
  specialize (minimum_x m). apply minimum_x. split; assumption.
Qed.

Theorem ordered_morphism_preserves_minimum {T1 T2}
  (domain: T1 -> Prop) (range: T2 -> Prop)
  (compare0: T1 -> T1 -> comparison) (compare1: T2 -> T2 -> comparison)
  (to: T1 -> option T2)
  (x : T1) (y : T2) :
  partial_morphism domain range to ->
  increasing domain compare0 compare1 to ->
  domain x -> range y ->
  to x = Some y ->
  partially_minimum domain compare0 x ->
  partially_minimum range compare1 y.
Proof.
Admitted.

Theorem no_ordered_morphism_to_smaller_interval (n m: Z) (to : Z -> option Z):
  (0 <= n)%Z ->
  (m < n)%Z ->
  (partial_morphism (interval n) (interval m) to /\ increasing (interval n) Z.compare Z.compare to) ->
  False.
Proof.
Admitted.

Theorem interval_ordered_automorphism_is_id :
  forall (n: Z),
  (0 <= n)%Z ->
  forall (to : Z -> option Z),
  partial_morphism (interval n) (interval n) to ->
  increasing (interval n) Z.compare Z.compare to ->
  (pointwise_equal (interval n) to (fun x => Some x)).
Proof.
  apply (Wf_Z.natlike_ind (fun n =>
    forall to : Z -> option Z,
    partial_morphism (interval n) (interval n) to ->
    increasing (interval n) Z.compare Z.compare to ->
    pointwise_equal (interval n) to (fun x : Z => Some x))).
  - intros to morphism increasing. unfold pointwise_equal.
    unfold interval. intros x x_in_empty_interval.
    lia.
  - intros n n_nonnegative induction_hypothesis to morphism increasing.
    assert (to n = Some n) as n_works.
    * specialize
      (partial_morphism_elimination morphism n)
      as [n' [n'_in_interval n'_definition]]. unfold interval; lia.
      rewrite n'_definition; apply f_equal.
      assert (n' < n \/ n' = n)%Z as n'_cases by (unfold interval in *; lia). 
      destruct n'_cases as [n'_smaller | duh].
      + assert (partial_morphism (interval (Z.succ n)) (interval (Z.succ n')) to) as stricter_morphism. admit.
        exfalso. apply (no_ordered_morphism_to_smaller_interval (Z.succ n) (Z.succ n') to). unfold interval in *; lia.
        unfold interval in *; lia. split; assumption.
      + apply duh.
    * unfold pointwise_equal. intros x x_in_interval.
      assert (x = n \/ interval n x) as [x_is_n | x_smaller_than_n] by (unfold interval in *; lia).
      + subst x; assumption.
      + unfold pointwise_equal in induction_hypothesis. apply induction_hypothesis.
        -- admit.
        -- admit.
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
  (*apply ordered_partial_isomorphism_symmetry in iso0.
     generalize (ordered_partial_isomorphism_composition iso0 iso1); intros iso2. *)
  unfold pointwise_equal. intros x range0_x.
  apply ordered_partial_isomorphism_symmetry in iso0.
  specialize (partial_isomorphism_elimination (opi_isomorphism range0 (interval count) compare0 Z.compare from0 to0 iso0) range0_x)
  as [n [interval_n [x_definition n_definition]]].
  unfold interval in interval_n.
  destruct interval_n as [n_nonnegative n_bounded].
  generalize dependent x.
  generalize dependent n.
  apply (Wf_Z.natlike_ind (fun n =>
    (n < count)%Z ->
    forall x : T0, range0 x ->
    to0 n = Some x -> from0 x = Some n -> to2 x = and_then from0 to1 x)).
  - intros count_positive x range0_x x_definition zero_definition. unfold and_then.
    rewrite zero_definition.
    revert x_definition zero_definition.
    apply (partial_morphism_induction range0 range1 to2); try assumption.
    clear x range0_x.
    intros x y0 range0_x range1_y y0_definition x_definition zero_definition_from0.
    assert (interval count 0) as zero_interval by (unfold interval; lia).
    specialize (partial_isomorphism_elimination
      (opi_isomorphism (interval count) range1 Z.compare compare1 to1 from1 iso1)
      zero_interval)
    as [y1 [range1_y1 [zero_definition_from1 y1_definition]]].
    rewrite y1_definition. apply f_equal.
    Check partially_minimum_unique.
    apply partially_minimum_unique with  (domain:=range1) (compare:=compare1); try assumption.
    apply (opi_ordered2 (interval count) range1 Z.compare compare1 to1 from1 iso1).
    * apply ordered_morphism_preserves_minimum with (domain:=range0)
        (compare0:=compare0) (compare1:=compare1) (to:=to2) (x:=x); try assumption.
      apply ordered_partial_isomorphism_symmetry in iso0.
      apply ordered_isomorphism_preserves_minimum with (domain:=interval count)
      (compare1:=Z.compare) (to:=to0) (from:=from0) (x:=0%Z); try assumption.
      apply Z_interval_minimum_zero.
    * apply ordered_isomorphism_preserves_minimum with (domain:=interval count)
      (compare1:=Z.compare) (to:=to1) (from:=from1) (x:=0%Z); try assumption. apply Z_interval_minimum_zero.
  - intros n n_nonnegative IHn n_small x range0_x x_definition n_succ_definition.
    unfold and_then. rewrite n_succ_definition.
    assert (interval count n) as n_interval. unfold interval; lia.
    assert (interval count (Z.succ n)) as n_succ_interval. unfold interval; lia.
    specialize (partial_isomorphism_elimination
      (opi_isomorphism (interval count) range1 Z.compare compare1 to1 from1 iso1)
      n_succ_interval)
      as [y [range1_y [n_succ_definition_from1 y_definition]]].
    specialize (partial_isomorphism_elimination
      (opi_isomorphism (interval count) range1 Z.compare compare1 to1 from1 iso1)
      n_interval)
      as [y_pred [range1_y_pred [n_definition_from1 y_pred_definition]]].
    apply ordered_partial_isomorphism_symmetry in iso0.
    specialize (partial_isomorphism_elimination
      (opi_isomorphism (interval count) range0 Z.compare compare0 to0 from0 iso0)
      n_interval)
      as [x_pred [range1_x_pred [n_definition_from0 x_pred_definition]]].
      rewrite y_definition.
    specialize
      (partial_morphism_elimination morphism x_pred)
    as [y_pred' [range1_y_pred' y_pred'_definition]]; try assumption.
    assert (y_pred' = y_pred).
    * apply some_injective. rewrite <- y_pred'_definition.
      replace (Some y_pred) with (and_then from0 to1 x_pred).
      apply IHn; try assumption. lia.
      unfold and_then.
      rewrite n_definition_from0. apply y_pred_definition.
    * subst y_pred'. clear range1_y_pred'.
      rename y_pred'_definition into y_pred_definition_to2.
      specialize
        (partial_morphism_elimination morphism x)
      as [y' [range1_y' y'_definition]]; try assumption.
      rewrite y'_definition. apply f_equal.
      Check partially_covers_unique.
      apply partially_covers_unique with (domain:=range1) (compare:=compare1)
      (x0:=y_pred) (x1:=y') (x2:=y); try assumption.
      apply (opi_ordered2
        (interval count) range1
        Z.compare compare1
        to1 from1 iso1).
      + (* turns out this is not trivial lol *) admit.
      + apply (ordered_isomorphism_preserves_cover n (Z.succ n) y_pred y iso1);
        try assumption. apply Z_interval_succ_partially_covers.
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
  increasing0 increasing1.
  split.
  - apply finite_partial_isomorphism_unique_aux with
    (count:=count) (range1:=range1) (compare0:=compare0)
    (compare1:=compare1) (from1:=from1) (to0:=to0); assumption.
  - apply finite_partial_isomorphism_unique_aux with
    (count:=count) (range1:=range0) (compare0:=compare1)
    (compare1:=compare0) (from1:=from0) (to0:=to1); assumption.
Qed.
