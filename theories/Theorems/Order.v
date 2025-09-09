Require Import Utf8.Spec.

Ltac crush_bits :=
  let B := fresh "B" in
  repeat match goal with
    | |- context[if ?bit then _ else _] =>
        destruct bit eqn:B
    | _: context[if ?bit then _ else _ ] |- _ =>
        destruct bit eqn:B
    end.

Ltac to_bits byte :=
  let rec break_bit bits :=
    match type of bits with
    | (bool * bool)%type => let b1 := fresh "b" in let b2 := fresh "b" in destruct bits as [b1 b2]
    | (bool * ?rest)%type => let b := fresh "b" in destruct bits as [b _bits]; break_bit _bits
    | (?rest * bool)%type => let b := fresh "b" in destruct bits as [_bits b]; break_bit _bits
    | ?other => idtac other
    end
  in 
  match type of byte with
  | Spec.codepoint =>
      unfold Spec.codepoint, Spec.b4 in byte;
      let b := fresh "b" in
      destruct byte as [[[[[b b4_1] b4_2] b4_3] b4_4] b4_5];
      break_bit b4_1; break_bit b4_2; break_bit b4_3; break_bit b4_4; break_bit b4_5
  | Spec.b7 =>
      unfold Spec.b7 in byte; break_bit byte
  | Spec.b6 =>
      unfold Spec.b6 in byte; break_bit byte
  | Spec.b5 =>
      unfold Spec.b5 in byte; break_bit byte
  | Spec.b4 =>
      unfold Spec.b4 in byte; break_bit byte
  | Spec.b3 =>
      unfold Spec.b3 in byte; break_bit byte
  | Byte.byte =>
      let B := fresh "B" in
      let eqn_name := fresh "byte_bits" in
      remember (Byte.to_bits byte) as B eqn:eqn_name;
      break_bit B;
      symmetry in eqn_name;
      apply (f_equal Byte.of_bits) in eqn_name;
      rewrite Byte.of_bits_to_bits in eqn_name
  end.

Definition antisymmetric {T} (comp: T -> T -> comparison) :=
  forall t1 t2,
    match comp t1 t2 with
    | More => comp t2 t1 = Less
    | Less => comp t2 t1 = More
    | Equal => t1 = t2
    end.

Definition transitive {T} (comp: T -> T -> comparison) :=
  forall t1 t2 t3,
    comp t1 t2 = comp t2 t3 -> comp t1 t2 = comp t1 t3.

Definition antisymmetric_reflexive {T} (comp: T -> T -> comparison):
  antisymmetric comp ->
  forall t, comp t t = Equal.
Proof.
  intros comp_spec t.
  unfold antisymmetric in comp_spec.
  specialize (comp_spec t t).
  destruct (comp t t) eqn:comp_t; [discriminate | reflexivity | discriminate].
Qed.

Lemma if_equal_pair_antisymmetric {T} (comp: T -> T -> comparison) :
    antisymmetric comp -> 
    antisymmetric
      (fun (a b: T * T) =>
         let '(a1, a2) := a in
         let '(b1, b2) := b in
         if_equal (comp a1 b1) (comp a2 b2)).
Proof.
  intros comp_spec a b.
  destruct a as [a1 a2]; destruct b as [b1 b2].
  unfold if_equal. simpl.
  specialize (comp_spec a1 b1) as comp_spec1.
  destruct (comp a1 b1) eqn:comp1; rewrite comp_spec1; auto. subst. rewrite comp1.
  specialize (comp_spec a2 b2) as comp_spec2.
  destruct (comp a2 b2) eqn:comp2; subst; auto.
Qed.

Lemma if_equal_pair_transitive {T} (comp: T -> T -> comparison) :
  antisymmetric comp ->
  transitive comp -> 
  transitive 
      (fun (a b: T * T) =>
         let '(a1, a2) := a in
         let '(b1, b2) := b in
         if_equal (comp a1 b1) (comp a2 b2)).
Proof.
  intros comp_anti comp_trans a b c comp_eq.
  destruct a as [a1 a2]; destruct b as [b1 b2]. destruct c as [c1 c2].
  unfold if_equal. simpl.
  destruct (comp a1 b1) eqn:comp1.
  - simpl in comp_eq. destruct (comp b1 c1) eqn:comp2; try discriminate.
    + rewrite <- comp2 in comp1.
      specialize (comp_trans a1 b1 c1 comp1) as G. rewrite <- G. rewrite comp1. rewrite comp2. reflexivity.
    + simpl in comp_eq. specialize (comp_anti b1 c1) as G. rewrite comp2 in G. subst. rewrite comp1. reflexivity.
  - specialize (comp_anti a1 b1) as G. rewrite comp1 in G. subst. simpl in comp_eq.
    destruct (comp b1 c1) eqn:comp2; try assumption.
    simpl in comp_eq.
    specialize (comp_trans a2 b2 c2 comp_eq). apply comp_trans.
  - simpl in comp_eq. destruct (comp b1 c1) eqn:comp2; try discriminate.
    + simpl in comp_eq. specialize (comp_anti b1 c1) as G. rewrite comp2 in G. subst. rewrite comp1. reflexivity.
    + rewrite <- comp2 in comp1.
      specialize (comp_trans a1 b1 c1 comp1) as G. rewrite <- G. rewrite comp1. rewrite comp2. reflexivity.
Qed.
  
Lemma bool_compare_antisymmetric : antisymmetric bool_compare.
Proof.
  intros a b.
  destruct a; destruct b; reflexivity.
Qed.

Lemma bool_compare_transitive : transitive bool_compare.
Proof.
  intros a b c bool_compare_bc.
  unfold bool_compare in *.
  destruct a; destruct b; destruct c; try discriminate; reflexivity.
Qed.

Lemma b2_compare_antisymmetric : antisymmetric b2_compare.
Proof.
  apply if_equal_pair_antisymmetric. apply bool_compare_antisymmetric.
Qed.

Lemma b2_compare_transitive : transitive b2_compare.
Proof.
  apply if_equal_pair_transitive. apply bool_compare_antisymmetric. apply bool_compare_transitive.
Qed.

Lemma b4_compare_antisymmetric : antisymmetric b4_compare.
Proof.
  intros a b.
  to_bits a. to_bits b.
  unfold b4_compare, if_equal.
  specialize (b2_compare_antisymmetric (b2, b3) (b5, b6)) as b2_comp.
  destruct (b2_compare (b2, b3) (b5, b6)) eqn:comp1; rewrite b2_comp; auto.
  specialize (b2_compare_antisymmetric (b1, b0) (b, b4)) as b2_comp2. inversion b2_comp. subst.
  destruct (b2_compare (b1, b0) (b, b4)) eqn:comp2.
  - rewrite comp1. apply b2_comp2.
  - inversion b2_comp2. reflexivity.
  - rewrite comp1. apply b2_comp2.
Qed.

Lemma b4_compare_transitive : transitive b4_compare.
Proof.
  intros a b c comp.
  destruct a as [[[a1 a2] a3] a4]. destruct b as [[[b1 b2] b3] b4].
  destruct c as [[[c1 c2] c3] c4].
  unfold b4_compare in *.
  specialize (if_equal_pair_transitive b2_compare b2_compare_antisymmetric b2_compare_transitive) as G.
  unfold transitive in G.
  specialize (G ((a1,a2), (a3, a4)) ((b1, b2), (b3, b4)) ((c1, c2), (c3, c4))). simpl in G. apply G in comp. apply comp.
Qed.

Lemma byte_compare_antisymmetric : antisymmetric byte_compare.
Proof.
  intros byte1 byte2.
  unfold byte_compare, if_equal; to_bits byte1; to_bits byte2.
  specialize (b4_compare_antisymmetric (b6, b5, b4, b3) (b14, b13, b12, b11)) as G.
  destruct (b4_compare (b6, b5, b4, b3) (b14, b13, b12, b11)) eqn:comp1; rewrite G; auto.
  inversion G. subst.
  specialize (b4_compare_antisymmetric (b2, b1, b0, b) (b10, b9, b8, b7)) as G1.
  destruct (b4_compare (b2, b1, b0, b) (b10, b9, b8, b7)) eqn:comp2.
  - rewrite antisymmetric_reflexive. assumption. apply b4_compare_antisymmetric.
  - inversion G1. reflexivity.
  - rewrite antisymmetric_reflexive. assumption. apply b4_compare_antisymmetric.
Qed.

Lemma byte_compare_transitive : transitive byte_compare.
Proof.
  intros a b c compare_ab_bc.
  unfold byte_compare in *.
  destruct (Byte.to_bits a) as [a1 [a2 [a3 [a4 [a5 [a6 [a7 a8]]]]]]].
  destruct (Byte.to_bits b) as [b1 [b2 [b3 [b4 [b5 [b6 [b7 b8]]]]]]].
  destruct (Byte.to_bits c) as [c1 [c2 [c3 [c4 [c5 [c6 [c7 c8]]]]]]].
  specialize (if_equal_pair_transitive b4_compare b4_compare_antisymmetric b4_compare_transitive) as G.
  unfold transitive in G.
  specialize (G ((a8, a7, a6, a5), (a4,a3,a2,a1)) ((b8, b7, b6, b5), (b4,b3,b2,b1)) ((c8, c7, c6, c5), (c4,c3,c2,c1))). simpl in G. unfold b4_compare, b2_compare in compare_ab_bc. apply G in compare_ab_bc. apply compare_ab_bc.
Qed.

Lemma codepoint_compare_antisymmetric : antisymmetric codepoint_compare.
  intros a b.
  unfold codepoint_compare, if_equal. to_bits a. to_bits b.
  repeat
    let comp_eq := fresh "comp_eq" in
    let comp_spec := fresh "comp_eq" in
    match goal with
    | [|- context[match bool_compare ?a ?b with | _ => _ end]] =>
        specialize (bool_compare_antisymmetric a b) as comp_spec;
        destruct (bool_compare a b) eqn:comp_eq;
        try rewrite comp_spec; try rewrite comp_eq
    | [|- context[match b4_compare ?a ?b with | _ => _ end]] =>
        specialize (b4_compare_antisymmetric a b) as comp_spec;
        destruct (b4_compare a b) eqn:comp_eq;
        try rewrite comp_spec; try rewrite comp_eq
    end; try discriminate; auto.
Qed.

Lemma codepoint_compare_transitive : transitive codepoint_compare.
  intros a b c compare_ab_bc.
  to_bits a. to_bits b. to_bits c.
  unfold codepoint_compare in *.
  Admitted.

Lemma lexicographic_compare_antisymmetric {T} (comp: T -> T -> comparison):
  antisymmetric comp ->
  antisymmetric (lexicographic_compare comp).
Proof.
  intros comp_spec. intros a.
  induction a as [|a a_tail]; intros b; destruct b as [|b b_tail] ; simpl; auto.
  unfold if_equal.
  specialize (comp_spec a b) as comp_spec1.
  destruct (comp a b) eqn:comp1; rewrite comp_spec1; auto. subst. rewrite comp1.
  specialize (IHa_tail b_tail).
  destruct (lexicographic_compare comp a_tail b_tail) eqn: comp2; try assumption; subst; reflexivity.
Qed.


Lemma lexicographic_compare_transitive {T} (comp: T -> T -> comparison):
  antisymmetric comp ->
  transitive comp ->
  transitive (lexicographic_compare comp).
Proof.
  intros comp_anti comp_trans. intro a. induction a; intros b c compare_ab_bc.
  - destruct b; simpl in *.
    + destruct c; tauto.
    + destruct c; auto. discriminate.
  - destruct b; destruct c; simpl in *; try discriminate; try tauto.
    specialize (comp_trans a t t0).
    specialize (comp_anti a t) as anti1.
    specialize (comp_anti t t0) as anti2.
    destruct (comp a t) eqn:comp1; destruct (comp t t0) eqn:comp2; simpl in *; subst; try discriminate; try tauto.
    + specialize (comp_trans ltac:(reflexivity)). rewrite <- comp_trans. reflexivity.
    + rewrite comp1. reflexivity.
    + rewrite comp2. simpl. apply compare_ab_bc.
    + rewrite antisymmetric_reflexive. simpl. apply IHa. apply compare_ab_bc. assumption.
    + rewrite comp2. simpl. assumption.
    + rewrite comp1. simpl. reflexivity.
    + specialize (comp_trans ltac:(reflexivity)). rewrite <- comp_trans. reflexivity.
Qed.


Lemma codepoints_compare_antisymmetric : antisymmetric codepoints_compare.
Proof.
  apply lexicographic_compare_antisymmetric.
  apply codepoint_compare_antisymmetric.
Qed.

Lemma codepoints_compare_transitive : transitive codepoints_compare.
Proof.
  apply lexicographic_compare_transitive.
  apply codepoint_compare_antisymmetric.
  apply codepoint_compare_transitive.
Qed.

Lemma bytes_compare_antisymmetric : antisymmetric bytes_compare.
Proof.
  apply lexicographic_compare_antisymmetric.
  apply byte_compare_antisymmetric.
Qed.


Lemma bytes_compare_transitive : transitive bytes_compare.
Proof.
  apply lexicographic_compare_transitive.
  apply byte_compare_antisymmetric.
  apply byte_compare_transitive.
Qed.

Lemma lexicographic_compare_nil_smallest {T} (comp: T -> T -> comparison):
  forall ts,
    antisymmetric comp ->
    lexicographic_compare comp nil ts = More -> False.
Proof.
  intros ts comp_anti compare_nil.
  destruct ts; discriminate.
Qed.  
