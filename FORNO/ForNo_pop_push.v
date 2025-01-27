Require Import List.

Definition pop (n : nat) (lc : list nat * nat) : (list nat * nat) :=
match lc with
| (l, c) =>
  match c with 
  | 0 => match l with
    | nil  => (nil, 1)
    | cons h t => match Nat.eqb n h with
       | false => (l,1)
       | true  => (t, 0)
       end
    end
  | S m => match l with 
    | nil  => (l, S (S m))
    | cons h t => match Nat.eqb n h with
       | false => (l, S (S m))
       | true => (l, S m)
       end
    end
  end
end .

Definition push (n : nat) (lc : list nat * nat) : list nat * nat :=
match lc with
| (l, c) =>
  match c with
  | 0 => (cons n l, 0)
  | S m => match l with
    | nil  => (l, m)
    | cons h t => match Nat.eqb n h with
      | false => (l, m)
      | true => (l, S m)
      end
    end
  end 
end .

Theorem pred_inv_succ: forall n l c, pop n (push n (l,c)) = (l,c).
Proof.
intros.
destruct c.
+ simpl.
  rewrite PeanoNat.Nat.eqb_refl.
  auto.
+ destruct l.
  - destruct c.
    * auto.
    * auto.
  - simpl.
    destruct (Nat.eqb n n0) eqn:eqb.
    * simpl. rewrite eqb. auto.
    * simpl. 
      destruct c.
      ** rewrite eqb. auto.
      ** rewrite eqb. auto.
Qed.

Theorem succ_inv_pred: forall n l c, push n (pop n (l,c)) = (l,c).
Proof.
intros.
destruct c.
+ destruct l.
  - simpl. auto.
  - simpl.
    destruct (Nat.eqb n n0) eqn:eqb.
    * simpl. 
      apply PeanoNat.Nat.eqb_eq in eqb.
      rewrite eqb.
      auto.
    * simpl.
      rewrite eqb.
      auto.
+ destruct l.
  - simpl. auto.
  - simpl.
    destruct (Nat.eqb n n0) eqn:eqb.
    * simpl.
      rewrite eqb.
      auto.
    * simpl.
      rewrite eqb.
      auto.
Qed.