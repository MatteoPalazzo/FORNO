Require Import BinNums.
Require Import Coq.NArith.BinNatDef.
Require Import List.

Definition pred0 (p : N * nat) : N * nat :=
match p with
| (          N0,   0) => (             N0,   0)
| (          N0, S c) => (             N0, S c)
| (   Npos (xH),   c) => (      Npos (xH), S c)
| (Npos (xO bs),   0) => (      Npos (bs),   0)
| (Npos (xO bs), S c) => (   Npos (xO bs), S c)
| (Npos (xI bs),   c) => (   Npos (xI bs), S c)
end.

Definition succ0 (p : N * nat) : N * nat :=
match p with
| (          N0,      0) => (          N0,   0)
| (          N0,    S c) => (          N0, S c)
| (   Npos (xH),    S c) => (   Npos (xH),   c)
| (      Npos (bs),   0) => (Npos (xO bs),   0)
| (   Npos (xO bs), S c) => (Npos (xO bs), S c)
| (   Npos (xI bs), S c) => (Npos (xI bs),   c)
end.

Lemma pred0_inverse_succ0 : forall x, pred0 (succ0 x) = x.
Proof.
intros.
destruct x as (b,n).
simpl;
destruct b;
destruct n;
try destruct p;
auto.
Qed.

Lemma succ0_inverse_pred0 : forall x, succ0 (pred0 x) = x.
Proof.
intros.
destruct x as (b,n).
simpl;
destruct b;
destruct n;
try destruct p;
auto.
destruct p; auto.
Qed.


Definition pred1 (p : N * nat) : N * nat :=
match p with
| (          N0,   c) => (          N0, S c)
| (   Npos (xH),   0) => (          N0,   0)
| (   Npos (xH), S c) => (   Npos (xH), S c)
| (Npos (xI bs),   0) => (   Npos (bs),   0)
| (Npos (xI bs), S c) => (Npos (xI bs), S c)
| (Npos (xO bs),   c) => (Npos (xO bs), S c)
end.

Definition succ1 (p : N * nat) : N * nat :=
match p with
| (          N0, S c) => (          N0,   c) 
| (          N0,   0) => (   Npos (xH),   0) 
| (   Npos (xH), S c) => (   Npos (xH), S c) 
| (   Npos (bs),   0) => (Npos (xI bs),   0) 
| (Npos (xI bs), S c) => (Npos (xI bs), S c) 
| (Npos (xO bs), S c) => (Npos (xO bs),   c)
end.

Lemma pred1_inverse_succ1 : forall x, pred1 (succ1 x) = x.
Proof.
intros.
destruct x as (b,n).
simpl;
destruct b;
destruct n;
try destruct p;
auto.
Qed.

Lemma succ1_inverse_pred1 : forall x, succ1 (pred1 x) = x.
Proof.
intros.
destruct x as (b,n).
simpl;
destruct b;
destruct n;
try destruct p;
auto.
destruct p; auto.
Qed.

  