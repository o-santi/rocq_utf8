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


Theorem strengthen_increasing {T1 T2}
  (strong_domain weak_domain: T1 -> Prop) (range: T2 -> Prop)
  (compare1: T1 -> T1 -> comparison) (compare2: T2 -> T2 -> comparison)
  (to: T1 -> option T2) :
  (forall x, strong_domain x -> weak_domain x) ->
  partial_morphism weak_domain range to ->
  increasing weak_domain compare1 compare2 to ->
  increasing strong_domain compare1 compare2 to.
Proof.
  intros strong_to_weak [to_some to_none] increasing_to x y x_domain y_domain.
  apply strong_to_weak in x_domain as x_weak.
  apply strong_to_weak in y_domain as y_weak.
  destruct (to x) as [x'|] eqn:x'_definition; [| apply to_none in x'_definition; tauto].
  destruct (to y) as [y'|] eqn:y'_definition; [| apply to_none in y'_definition; tauto].
  specialize (increasing_to x y x_weak y_weak).
  rewrite x'_definition, y'_definition in increasing_to.
  apply increasing_to.
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
  {domain: T1 -> Prop} {range: T2 -> Prop}
  {compare1: T1 -> T1 -> comparison} {compare2: T2 -> T2 -> comparison}
  {to: T1 -> option T2} {from: T2 -> option T1} :
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

Lemma ordered_morphism_restriction (n m n' m' : Z) (to : Z -> option Z) :
  partial_morphism (interval n) (interval m) to ->
  increasing (interval n) Z.compare Z.compare to ->
  interval n n' ->
  interval m m' ->
  to n' = Some m' ->
  partial_morphism (interval n') (interval m') to.
Proof.
Admitted.

Lemma tighten_ordered_morphism (n m m' : Z) (to : Z -> option Z) :
  partial_morphism (interval (Z.succ n)) (interval m) to ->
  increasing (interval (Z.succ n)) Z.compare Z.compare to ->
  interval m m' ->
  to n = Some m' ->
  partial_morphism (interval (Z.succ n)) (interval (Z.succ m')) to.
Proof.
Admitted.

Theorem no_ordered_morphism_to_smaller_interval : forall (n m : Z) (to : Z -> option Z),
  (0 <= m)%Z ->
  (m < n)%Z ->
  partial_morphism (interval n) (interval m) to ->
  increasing (interval n) Z.compare Z.compare to ->
  False.
Proof.
  assert
  (forall (bound : Z)
    (_ : (0 <= bound)%Z)
    (m : Z)
    (_ : (m <= bound)%Z)
    (n : Z) (to : Z -> option Z),
    (0 <= m)%Z ->
    (m < n)%Z ->
    partial_morphism (interval n) (interval m) to ->
    increasing (interval n) Z.compare Z.compare to ->
    False) as lemma.
  - apply (Wf_Z.natlike_ind
            (fun bound =>
              forall m : Z,
              (m <= bound)%Z ->
              forall (n : Z) (to : Z -> option Z),
              (0 <= m)%Z ->
              (m < n)%Z ->
              partial_morphism (interval n) (interval m) to ->
              increasing (interval n) Z.compare Z.compare to -> False)).
    + intros m m_zero n to m_nonnegative m_less_n [to_some to_none] increasing_to.
      destruct (to 0%Z) as [z'|] eqn:to_z.
      * apply to_some in to_z as [z_nonneg z_neg].
        lia.
      * apply to_none in to_z.
        apply to_z.
        split; lia.
    + intros bound bound_nonnegative induction_hypothesis m m_bound n to m_nonneg is_less morphism increasing_to.
      replace n with (Z.succ (Z.pred n)) in * by lia.
      remember (Z.pred n) as n_pred eqn:n_pred_definition.
      specialize
        (partial_morphism_elimination morphism n_pred)
        as [m' [m'_in_interval m'_definition]].
      unfold interval. lia.
      apply induction_hypothesis with (m:=m') (n:=n_pred) (to:=to); try (unfold interval in *; lia).
      * apply ordered_morphism_restriction with (n:=(Z.succ n_pred)) (m:=m); try assumption.
        unfold interval. lia.
      * apply strengthen_increasing with (weak_domain:=(interval (Z.succ n_pred))); try assumption.
        unfold interval; lia.
  - intros n m to m_nonnegative is_less morphism. apply (lemma m) with (m := m); try assumption. lia.
Qed.

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
    + assert (partial_morphism (interval (Z.succ n)) (interval (Z.succ n')) to) as stricter_morphism.
      apply tighten_ordered_morphism with (m:=(Z.succ n)); try assumption.
      exfalso.
      destruct n'_in_interval as [n'_nonneg n'_less_succ_n].
      apply (no_ordered_morphism_to_smaller_interval (Z.succ n) (Z.succ n') to); try lia; assumption.
    + apply duh.
    * unfold pointwise_equal. intros x x_in_interval.
      assert (x = n \/ interval n x) as [x_is_n | x_smaller_than_n] by (unfold interval in *; lia).
      + subst x; assumption.
      + unfold pointwise_equal in induction_hypothesis. apply induction_hypothesis.
        -- apply ordered_morphism_restriction with (n:=(Z.succ n)) (m:=(Z.succ n)); try assumption; unfold interval; lia.
        -- apply strengthen_increasing with (weak_domain:=(interval (Z.succ n))); try assumption. unfold interval. lia.
        -- assumption.
Qed.

Theorem finite_partial_isomorphism_unique_aux {T0 T1} (count: Z) (range0: T0 -> Prop) (range1: T1 -> Prop) compare0 compare1:
  (0 <= count)%Z ->
  forall from0 from1 to0 to1 to2,
  OrderedPartialIsomorphism (interval count) range0 Z.compare compare0 to0 from0 ->
  OrderedPartialIsomorphism (interval count) range1 Z.compare compare1 to1 from1 ->
  partial_morphism range0 range1 to2 ->
  increasing range0 compare0 compare1 to2 ->
  (pointwise_equal range0 to2 (and_then from0 to1)).
Proof.
  intros count_nonneg from0 from1 to0 to1 to2 iso0 iso1 [to2_some to2_none] increasing_to.
    assert (partial_morphism (interval count) (interval count) (and_then to0 (and_then to2 from1))) as morphism. {
    destruct iso0. destruct opi_isomorphism0 as [[to0_some to0_none] [from0_some from0_none] _ _].
    destruct iso1. destruct opi_isomorphism0 as [[to1_some to1_none] [from1_some from1_none] _ _].
    split.
    + intros x0 y0 composition.
      unfold and_then in composition.
      destruct (to0 x0) as [y1|] eqn:y1_definition; [| discriminate].
      destruct (to2 y1) as [y2|] eqn:y2_definition; [| discriminate].
      apply from1_some in composition. apply composition.
    + intros x0 composition x0_interval.
      unfold and_then in composition.
      destruct (to0 x0) as [y1|] eqn:y1_definition.
      * destruct (to2 y1) as [y2|] eqn:y2_definition.
        -- apply from1_none in composition. apply to2_some in y2_definition. apply composition. apply y2_definition.
        -- apply to2_none in y2_definition. apply to0_some in y1_definition. apply y2_definition. apply y1_definition.
      * apply to0_none in y1_definition. apply y1_definition. apply x0_interval.
    }
    assert (increasing (interval count) Z.compare Z.compare
              (and_then to0 (and_then to2 from1))) as increasing_composition. {
      destruct iso0. destruct opi_isomorphism0 as [[to0_some to0_none] [from0_some from0_none] to0_from0 from0_to0].
      assert (G:= iso1).
      destruct G. destruct opi_isomorphism0 as [[to1_some to1_none] [from1_some from1_none] to1_from1 from1_to1].
      intros x0 y0 x0_interval y0_interval. unfold and_then.
      destruct (to0 x0)   as [y1|] eqn:y1_definition;
        [apply to0_some in y1_definition as y1_interval | apply to0_none   in y1_definition; tauto].
      destruct (to2 y1)   as [y2|] eqn:y2_definition;
        [apply to2_some in y2_definition as y2_interval | apply to2_none   in y2_definition; tauto].
      destruct (from1 y2) as [x1|] eqn:x1_definition;
        [apply from1_some in x1_definition as x1_interval | apply from1_none in x1_definition; tauto].
      destruct (to0 y0) as [y3|] eqn:y3_definition;
        [apply to0_some in y3_definition as y3_interval | apply to0_none in y3_definition; tauto].
      destruct (to2 y3) as [y4|] eqn:y4_definition;
        [apply to2_some in y4_definition as y4_interval | apply to2_none in y4_definition; tauto].
      destruct (from1 y4) as [x2|] eqn:x2_definition;
        [apply from1_some in x2_definition as x2_interval | apply from1_none in x2_definition; tauto].
      specialize (opi_to_preserves_compare0 x0 y0 x0_interval y0_interval).
      rewrite y1_definition, y3_definition in opi_to_preserves_compare0. rewrite opi_to_preserves_compare0.
      specialize (increasing_to y1 y3 y1_interval y3_interval).
      rewrite y2_definition, y4_definition in increasing_to. rewrite increasing_to.
      specialize (ordered_partial_isomorphism_from_increasing iso1) as from1_increasing.
      specialize (from1_increasing y2 y4 y2_interval y4_interval).
      rewrite x1_definition, x2_definition in from1_increasing. apply from1_increasing.
    }
    specialize (interval_ordered_automorphism_is_id count count_nonneg (and_then to0 (and_then to2 from1)) morphism increasing_composition) as composition_equal.
    intros x0 x0_interval.
    destruct (to2 x0) as [y0|] eqn:y0_definition; [ | apply to2_none in y0_definition ; tauto].
    unfold and_then.
    destruct iso0 as [_ _ [[to0_some to0_none] [from0_some from0_none] to0_from0 from0_to0] _].
    destruct iso1 as [_ _ [[to1_some to1_none] [from1_some from1_none] to1_from1 from1_to1] _].
    destruct (from0 x0) as [y1|] eqn:y1_definition; [apply from0_some in y1_definition as y1_interval | apply from0_none in y1_definition; tauto].
    destruct (to1 y1) as [y2|] eqn:y2_definition; [apply to1_some in y2_definition as y2_interval | apply to1_none in y2_definition; tauto ].
    apply f_equal.
    specialize (composition_equal y1 y1_interval). simpl in composition_equal.
    unfold and_then in composition_equal.
    destruct (to0 y1) as [y3|] eqn:y3_definition; [apply to0_some in y3_definition as y3_interval | apply to0_none in y3_definition; tauto].
    destruct (to2 y3) as [y4|] eqn:y4_definition; [apply to2_some in y4_definition as y4_interval | apply to2_none in y4_definition; tauto].
    specialize (from1_to1 y4 y4_interval) as to1_y4. unfold and_then in to1_y4.
    rewrite composition_equal in to1_y4.
    rewrite to1_y4 in y2_definition. inversion y2_definition. subst. clear y2_definition.
    specialize (from0_to0 x0 x0_interval) as to0_x0. unfold and_then in to0_x0.
    rewrite y1_definition in to0_x0.
    rewrite to0_x0 in y3_definition. inversion y3_definition. subst. clear y3_definition.
    rewrite y4_definition in y0_definition. inversion y0_definition. 
    reflexivity.
Qed.

Theorem finite_partial_isomorphism_unique {T0 T1} (count: Z) (range0: T0 -> Prop) (range1: T1 -> Prop) compare0 compare1:
  forall from0 from1 from2 to0 to1 to2,
    (0 <= count)%Z ->
    OrderedPartialIsomorphism (interval count) range0 Z.compare compare0 to0 from0 ->
    OrderedPartialIsomorphism (interval count) range1 Z.compare compare1 to1 from1 ->
    partial_morphism range0 range1 to2 ->
    partial_morphism range1 range0 from2 ->
    increasing range0 compare0 compare1 to2 ->
    increasing range1 compare1 compare0 from2 ->
  (pointwise_equal range0 to2 (and_then from0 to1))
  /\ (pointwise_equal range1 from2 (and_then from1 to0)).
Proof.
  intros from0 from1 from2 to0 to1 to2 count_nonnegative iso0 iso1 morphism0 morphism1
    increasing0 increasing1.
  split.
  - apply finite_partial_isomorphism_unique_aux with
    (count:=count) (range1:=range1) (compare0:=compare0)
    (compare1:=compare1) (from1:=from1) (to0:=to0); assumption.
  - apply finite_partial_isomorphism_unique_aux with
    (count:=count) (range1:=range0) (compare0:=compare1)
    (compare1:=compare0) (from1:=from0) (to0:=to1); assumption.
Qed.
