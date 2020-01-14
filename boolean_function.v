Require Import String.
Definition goal := "tesst assures of boolean xor function"%string.

Definition xor (b1 b2 : bool) : bool :=
  match (b1,b2) with
  | (true,  true) => false
  | (false, false) => false
  | _ => true
  end.

(*fasle, false should be false*)
Fact xor1: xor false false = false.
Proof. simpl. reflexivity. Qed.

(*false, true should be true*)
Fact xor2: xor false true = true.
Proof. simpl. reflexivity. Qed.

(*false, false should be false*)
Fact xor3: xor true false = true.
Proof. simpl. reflexivity. Qed.

(*true, true should be false*)
Fact xor4: xor true true = false.
Proof. simpl. reflexivity. Qed.

Require Import String.
Print goal. 