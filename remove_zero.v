(*Define a List of Numbers and it's Length *)
Require Import String.

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Fixpoint length (ns: natlist) : nat :=
  match ns with
  | nil => 0
  | cons n ns' => 1+length ns'
  end.

(*Counting the Zeros of a List of Numbers *)

Fixpoint count0 (ns: natlist) : nat :=
  match ns with
  | nil => 0
  | cons 0 ns' => 1 + count0 ns'
  | cons n ns' => count0 ns'
  end.

(*Removing the Zeros of a List of Numbers *)

Fixpoint remove0 (ns: natlist) : natlist :=
  match ns with
  | nil => ns
  | cons 0 ns' => (remove0 ns')
  | cons n ns' => cons n (remove0 ns')
  end.


(*Testing Remove Zero Funcation*)
Fact test1: remove0 nil = nil.
Proof. simpl. reflexivity. Qed.

Fact test2: remove0 (cons 1 nil) = cons 1 nil.
Proof. simpl. reflexivity. Qed.

Fact test3: remove0 (cons 0 (cons 1 nil)) = cons 1 nil.
Proof. simpl. reflexivity. Qed.

Fact test4: remove0 (cons 0 (cons 2 (cons 0 nil))) = cons 2 nil.
Proof. simpl. reflexivity. Qed.

Let list :=
  cons 0 (cons 1 (cons 0 (cons 2 (cons 0 (cons 3 (cons 0 nil)))))).
                                                         
Fact test5: remove0 list = cons 1 (cons 2 (cons 3 nil)).
Proof. simpl. reflexivity. Qed.

(* A Lemma   *)

Lemma remove0_length:
  forall ns, length ns = count0 ns + length(remove0 ns).
Proof.
  induction ns as [ | n ns' IH ].
  - simpl. reflexivity.
  - simpl. destruct n. simpl. rewrite <- IH. reflexivity. simpl. auto with arith. rewrite -> IH. auto with arith.
   Qed.