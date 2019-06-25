Require Import Coq.Program.Program.
Require Import datatypes.
Require Import Coq.Lists.Streams.
Require Import eqchain.

Instance Nat_ia (C : Type) : F_initial_algebra (Sum one arg2) C nat :=
  {
    cata X f := fix cataf (n : nat) := match n with
                                       | O    => f (inl ())
                                       | S n' => f (inr (cataf n'))
                                       end;
                
    in_ := [ fun x => O , S ]
  }.
Proof.
  intros X f φ.
  split.
  - intros H; extensionality x; induction x.
    + specialize (equal_f H (inl tt)) as H0; cbv in H0.
      exact H0.
    + specialize (equal_f H (inr x)) as H1; cbv in H1.
      rewrite <- IHx. exact H1.
  - intros H; extensionality x; induction x.
    + rewrite H; induction a; easy.
    + rewrite H; easy.
Defined.

CoInductive mid_tree :=
| Nil  : nat -> mid_tree
| Cons : nat -> mid_tree -> mid_tree.

Definition mid_tree_ana (X : Type) (f : X -> nat * (unit + X)) : X -> mid_tree :=
  cofix anaf (x : X)
    := match (f x) with
       | (n, ux) => match ux with inl () => Nil n | inr x  => Cons n (anaf x) end
       end.

Definition mid_tree_out (t : mid_tree) : nat * (unit + mid_tree) :=
  match t with
  | Nil n     => (n, inl tt)
  | Cons n t' => (n, inr t')
  end.

Definition epsilon (t : mid_tree) : nat :=
  match t with
  | Nil n    => n
  | Cons n _ => n
  end.

Definition theta (t : mid_tree) : unit + mid_tree :=
  match t with
  | Nil _     => inl tt
  | Cons _ t' => inr t'
  end.

CoInductive EqMidtree (t1 t2 : mid_tree): Prop :=
| eqmid : epsilon t1 = epsilon t2
          -> ((theta t1 = inl tt /\ theta t2 = inl tt)
              \/ (forall a b, theta t1 = inr a -> theta t2 = inr b -> EqMidtree a b))
          -> EqMidtree t1 t2
.

Proposition EqMidtree_refl (t : mid_tree) :
  EqMidtree t t.
Proof.
  revert t; cofix CIH.
  intros t; apply eqmid.
  - easy.
  - destruct t.
    + left. cbv. easy.
    + right. intros.
      inversion H.
      inversion H0.
      rewrite <- H2; rewrite <- H3.
      apply CIH.
Qed.

Axiom eq_ext :
  forall (t1 t2 : mid_tree), EqMidtree t1 t2 -> t1 = t2.

Proposition mid_tree_ana_frob (X : Type) (φ : X -> nat * (unit + X)) (x : X) :
  mid_tree_ana X φ x
  = match (φ x) with
    | (n, tx) => match tx with
                 | inl _ => Nil n
                 | inr x => Cons n (mid_tree_ana X φ x)
                 end
    end.
Proof.
  apply eq_ext. cbv. remember (φ x) as p. induction p.
  constructor.
  - cbv. rewrite <- Heqp. induction b.
    + induction a0. easy.
    + easy.
  - cbv. rewrite <- Heqp. induction b.
    + induction a0. left. easy.
    + right. intros.
      rewrite H in H0. inversion H0. apply EqMidtree_refl.
Qed.

Instance Mid_tree_tc
  : F_terminal_coalgebra (Prod arg1 (Sum one arg2)) nat mid_tree :=
  {
    ana  := mid_tree_ana;
    out_ := mid_tree_out
  }.
Proof.
  intros; split.
  - intros H; extensionality x. apply eq_ext.
    revert x. cofix CIH. constructor.
    + specialize (equal_f H x) as H0; cbv in H0. revert H0.
      cbv; induction (φ x). destruct (f x).
      * intros H0; inversion H0. induction b.
        -- inversion H0; easy.
        -- easy.
      * intros H0; inversion H0. induction b.
        -- inversion H0.
        -- easy.
    + specialize (equal_f H x) as H0; cbv in H0; revert H0.
      case_eq (φ x). case_eq (f x).
      * intros. induction i0.
        -- inversion H1.
           left. cbv. rewrite H1. induction a. easy.
        -- inversion H2.
      * intros. induction i0. 
        -- inversion H2.
        -- inversion H2.
           right.
           intros.
           rewrite mid_tree_ana_frob in H6.
           rewrite H1 in H6.
           inversion H6.
           inversion H3.
           apply CIH.
  - intros H; extensionality x; rewrite H; cbv; destruct (φ x); cbv.
    induction i0.
    + induction a; easy.
    + easy.
Defined.

Definition onec {X : Type} := (fun _ : X => 1).
Definition add p := (fst p) + (snd p).
Definition distl {A B C : Type} : A * (B + C) -> (A * B) + (A * C) :=
  fun x => match x with
           | (a, bc) => match bc with
                        | inl b => inl (a, b)
                        | inr c => inr (a, c)
                        end
           end.

Definition fibo := {| [ onec , [ onec ∘ snd, add ∘ (id ⊗ (fst ∘ out_)) ] ∘ distl ∘ out_ ] |}.

Theorem fibo_SSn :
  forall (n : nat),
    fibo (S (S n)) = fibo (S n) + fibo n.
Proof.
  apply two_induction; try easy.
Qed.

Time Eval cbv in (fibo 0).
(* Finished transaction in 0. secs (0.u,0.s) (successful) *)
(* Finished transaction in 0. secs (0.u,0.s) (successful) *)
(* Finished transaction in 0.001 secs (0.u,0.s) *)

Time Eval cbv in (fibo 5).
(* Finished transaction in 0.006 secs (0.001u,0.001s) *)
(* Finished transaction in 0.002 secs (0.001u,0.s) *)
(* Finished transaction in 0.002 secs (0.001u,0.s) *)

Time Eval cbv in (fibo 10).
(* Finished transaction in 0.009 secs (0.004u,0.003s) *)
(* Finished transaction in 0.009 secs (0.004u,0.003s) *)
(* Finished transaction in 0.007 secs (0.004u,0.003s) *)
(* Finished transaction in 0.004 secs (0.004u,0.s) *)
(* Finished transaction in 0.002 secs (0.002u,0.s) *)

Time Eval cbv in (fibo 15).
(* Finished transaction in 0.068 secs (0.05u,0.013s) *)
(* Finished transaction in 0.008 secs (0.008u,0.s) *)
(* Finished transaction in 0.009 secs (0.007u,0.s) *)
(* Finished transaction in 0.008 secs (0.007u,0.s) *)
(* Finished transaction in 0.008 secs (0.007u,0.s) *)

Time Eval cbv in (fibo 20).
(* Finished transaction in 0.05 secs (0.04u,0.s) *)
(* Finished transaction in 0.041 secs (0.036u,0.001s) *)
(* Finished transaction in 0.034 secs (0.03u,0.s) *)
(* Finished transaction in 0.04 secs (0.034u,0.s) *)
(* Finished transaction in 0.039 secs (0.037u,0.s) *)