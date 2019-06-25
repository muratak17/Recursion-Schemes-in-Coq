Require Import Coq.Program.Program.
Require Import datatypes.
Require Import Coq.Lists.List.
Require Import eqchain.

Definition fmap {F : PolyF} {μF A B : Type}
           {ia1 : F_initial_algebra F A μF}
           {ia2 : F_initial_algebra F B μF}
           (f : A -> B)
  := ⦇ in_ ∘ F❲ f ❳[id] ⦈.

Section data_functor.

  Variable (F : PolyF) (μF : Type) (A B C : Type)
           (ia1 : F_initial_algebra F A μF)
           (ia2 : F_initial_algebra F B μF)
           (ia3 : F_initial_algebra F C μF)
           (ia : F_initial_algebra F A μF).

  Theorem map_map_fusion :
    forall (f : A -> B) (g : B -> C),
      (fmap g) ∘ (fmap f) = fmap (g ∘ f).
  Proof.
    intros; unfold fmap.
    assert ( (fmap g) ∘ in_ ∘ F❲f❳[id] = in_ ∘ F❲g ∘ f❳[id] ∘ F❲id❳[fmap g] ) as H0.
    {
      unfold fmap.
      Left
      = ( ⦇in_ ∘ F❲g❳[id]⦈ ∘ in_ ∘ F❲f❳[id] ).
      = ( in_ ∘ (F❲g❳[id] ∘ F❲id❳[⦇in_ ∘ F❲g❳[id]⦈]) ∘ F❲f❳[id] )  { by cata_cancel }.
      = ( in_ ∘ (F❲g❳[⦇in_ ∘ F❲g❳[id]⦈] ∘ F❲f❳[id]) )  { by fmap_functor_dist }.
      = ( in_ ∘ (F❲g ∘ f❳[⦇in_ ∘ F❲g❳[id]⦈]) )  { by fmap_functor_dist }.
      = ( in_ ∘ (F❲g ∘ f❳[id] ∘ F❲id❳[⦇in_ ∘ F❲g❳[id]⦈]) )  { by fmap_functor_dist }.
      = Right.
    }
    unfold fmap in H0.
    Left
    = ( ⦇ in_ ∘ F❲g❳[id] ⦈ ∘ ⦇ in_ ∘ F❲f❳[id] ⦈ ).
    = ( ⦇in_ ∘ F ❲g ∘ f❳[id] ⦈ )  { apply cata_fusion }.
    = Right.
  Qed.

End data_functor.

Definition list_cata (A X : Type) (f : unit + (A * X) -> X) : (list A) -> X :=
  fix cata (la : list A)
    := match la with
       | nil       => f (inl tt)
       | cons a xs => f (inr (a, (cata xs)))
       end.

Definition list_in (A : Type) (ual : unit + (A * (list A))) : list A :=
  match ual with
  | inl tt => nil
  | inr al => let (a,l) := al in cons a l
  end.

Instance list_ia (A : Type)
  : F_initial_algebra (Sum one (Prod arg1 arg2)) A (list A) :=
  {
    cata := list_cata A;
    in_  := list_in A
  }.
Proof.
  intros. split.
  - intros H; extensionality l; induction l.
    + specialize (equal_f H (inl tt)) as H0.
      cbv in H0; cbv; easy.
    + specialize (equal_f H (inr (a, l))) as H0.
      cbv in H0; cbv. rewrite H0. rewrite IHl. easy.
  - intros H; extensionality l. induction l.
    + rewrite H; induction a; specialize (equal_f H []) as H0. easy.
    + rewrite H. induction b; specialize (equal_f H (cons a b)) as H0.
      easy.
Defined.

Eval cbv in (fmap (plus 10) [1 ; 2 ; 3 ; 4 ; 5]).