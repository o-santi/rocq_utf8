Require Import Utf8.Spec.
From Coq Require Import Lists.List. Import ListNotations.

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
      unfold Spec.codepoint in byte;
      let b := fresh "b" in
      destruct byte as [[[[[b b4_1] b4_2] b4_3] b4_4] b4_5];
      break_bit b4_1; break_bit b4_2; break_bit b4_3; break_bit b4_4; break_bit b4_5
  | Byte.byte =>
      let B := fresh "B" in
      let eqn_name := fresh "byte_bits" in
      remember (Byte.to_bits byte) as B eqn:eqn_name;
      break_bit B;
      symmetry in eqn_name;
      apply (f_equal Byte.of_bits) in eqn_name;
      rewrite Byte.of_bits_to_bits in eqn_name
  end.

Lemma byte_compare_antisymmetric : forall byte1 byte2, byte_compare byte1 byte2 = CompOpp (byte_compare byte2 byte1).
Proof.
  intros byte1 byte2.
  unfold byte_compare.
  apply PeanoNat.Nat.compare_antisym.
Qed.

Lemma byte_compare_eq_iff : forall b1 b2, byte_compare b1 b2 = Eq <-> b1 = b2.
Proof.
  intros b1 b2.
  unfold byte_compare.
  specialize (PeanoNat.Nat.compare_eq_iff (Byte.to_nat b1) (Byte.to_nat b2)) as [G1 G2].
  split; intros.
  - apply G1 in H. apply (f_equal Byte.of_nat) in H. do 2 rewrite Byte.of_to_nat in H. inversion H. reflexivity.
  - subst. specialize (G2 ltac:(reflexivity)).
    apply G2.
Qed.

Lemma list_compare_refl_if {T} (cmp: T -> T -> comparison) : forall (t: list T), 
    (forall x y, cmp x y = Eq <-> x = y) ->
    list_compare cmp t t = Eq.
Proof.
  intros t cmp_eq.
  apply list_compare_refl; [| reflexivity].
  apply cmp_eq.
Qed.
