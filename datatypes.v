Require Import Coq.Program.Program.
Require Import eqchain.

Inductive PolyF : Type :=
| zer : PolyF
| one : PolyF
| arg1 : PolyF
| arg2 : PolyF
| Sum : PolyF -> PolyF -> PolyF
| Prod : PolyF -> PolyF -> PolyF
.

Fixpoint inst (F : PolyF) (A X : Type) : Type :=
  match F with
  | zer      => Empty_set
  | one      => unit
  | arg1     => A
  | arg2     => X
  | Sum F G  => (inst F A X) + (inst G A X)
  | Prod F G => (inst F A X) * (inst G A X)
  end.

Notation "⟦ F ⟧" := (inst F) (at level 20).

Definition fprod {A B C : Type} (f : A -> B) (g : A -> C): A -> B * C :=
  fun (x : A) => (f x, g x).

Definition fsum {A B C : Type} (f : A -> C) (g : B -> C): A + B -> C :=
  fun (x : A + B) =>
    match x with
    | inl x => f x
    | inr x => g x
    end.

Notation "〈 f , g 〉" := (fprod f g) (at level 20).
Notation "[ f , g ]" := (fsum  f g) (at level 20).

Notation " f ⊗ g " := ( 〈 f ∘ fst , g ∘ snd 〉 )   (at level 20).
Notation " f ⊕ g " := ( [ inl ∘ f , inr ∘ g ] ) (at level 20).

Definition unique_mor_initial  {A : Type} : Empty_set -> A := fun x => match x with end. 
Definition unique_mor_terminal {A : Type} : A -> unit      := fun (x : A) => tt.

Notation " ¡ " := ( @unique_mor_initial _ ).
Notation " ! " := ( @unique_mor_terminal _ ).

Section Basic_Properties.

  Variable A B C D E X : Type.
  
  Lemma fst_fprod :
    forall (f : A -> B) (g : A -> C), fst ∘ 〈 f , g 〉 = f.
  Proof.
    easy.
  Qed.  

  Lemma snd_fprod :
    forall (f : A -> B) (g : A -> C), snd ∘ 〈 f , g 〉 = g.
  Proof.
    easy.
  Qed.

  Lemma fsum_inl :
    forall (f : A -> C) (g : B -> C), [ f , g ] ∘ inl = f.
  Proof.
    easy.
  Qed.

  Lemma fsum_irl :
    forall (f : A -> C) (g : B -> C), [ f , g ] ∘ inr = g.
  Proof.
    easy.
  Qed.
  
  Lemma pairing :
    forall (f : A -> B*C), 〈 fst ∘ f , snd ∘ f 〉 = f.
  Proof.
    intros f. extensionality x. cbv. induction (f x). easy.
  Qed.

  Lemma copairing :
    forall (f : A+B -> C), [ f ∘ inl , f ∘ inr ] = f.
  Proof.
    intros f. extensionality x. cbv. induction x.
    - easy.
    - easy.
  Qed.
  
  Lemma pairing2 :
    forall (f : X -> A) (g : X -> B) (i : A -> C) (j : B -> D),
      (i ⊗ j) ∘ 〈 f , g 〉 = 〈 i ∘ f , j ∘ g 〉.
  Proof.
    intros f g h i. extensionality x. cbv; easy.
  Qed.

  Lemma copairing2 :
    forall (f : A -> X) (g : B -> X) (i : X -> C),
      i ∘ [f, g] = [ i ∘ f , i ∘ g ].
  Proof.
    intros. extensionality x. induction x.
    - easy.
    - easy.
  Qed.
End Basic_Properties.
Hint Resolve pairing.
Hint Resolve copairing.
Hint Resolve pairing2.
Hint Resolve copairing2.

(* Functors *)

Fixpoint fmap (F : PolyF) {A0 A1 X0 X1 : Type}
  (f : A0 -> A1) (g : X0 -> X1) : ⟦F⟧ A0 X0 -> ⟦F⟧ A1 X1 :=
  match F with
  | zer      => id
  | one      => id
  | arg1     => f
  | arg2     => g
  | Sum F G  => fun x
                => match x with
                   | inl x => inl (fmap F f g x)
                   | inr x => inr (fmap G f g x)
                   end
  | Prod F G => fun x
                => (fmap F f g (fst x), fmap G f g (snd x))
  end.

Notation " F ❲ f ❳ [ g ]" := (@fmap F _ _ _ _ f g) (at level 10).
Notation " F [ f ]"       := (@fmap F _ _ _ _ id f) (at level 10).

Lemma fmap_functor_dist :
  forall (F : PolyF) {A0 A1 A2 X0 X1 X2 : Type}
         (f0 : A0 -> A1) (f1 : A1 -> A2) (g0 : X0 -> X1) (g1 : X1 -> X2),
    F ❲f1 ∘ f0❳ [g1 ∘ g0] = F ❲ f1 ❳ [ g1 ] ∘ F ❲ f0 ❳ [g0] .
Proof.
  intros F A0 A1 A2 X0 X1 X2 f0 f1 g0 g1.
  extensionality x. induction F.
  - easy.
  - easy.
  - easy.
  - easy.
  - cbn. induction x.
    + rewrite IHF1. easy.
    + rewrite IHF2. easy.
  - cbn. rewrite IHF1; rewrite IHF2. induction x. easy.
Qed.
Hint Resolve fmap_functor_dist.

Lemma fmap_functor_distr :
  forall (F : PolyF) {A X0 X1 X2 : Type} (g0 : X0 -> X1) (g1 : X1 -> X2),
    F ❲ @id A ❳ [g1 ∘ g0] = F [ g1 ] ∘ F [g0] .
Proof.
  intros F A X0 X1 X2 g0 g1.
  rewrite <- fmap_functor_dist.
  easy.
Qed.
Hint Resolve fmap_functor_distr. 

Lemma fmap_functor_id :
  forall (F : PolyF) {A X : Type},
    F ❲ @id A ❳ [ @id X ] = id.
Proof.
  intros F A X. extensionality x. induction F.
  - easy.
  - easy.
  - easy.
  - easy.
  - cbn. induction x.
    + rewrite IHF1; easy.
    + rewrite IHF2; easy. 
  - cbn. induction x. rewrite IHF1; rewrite IHF2. easy.
Qed.
Hint Resolve fmap_functor_id. 

(* Typeclass for F-initial algebra *)
Class F_initial_algebra (F : PolyF) (A : Type) (μF : Type) :=
  {
    cata : forall (X : Type), (⟦ F ⟧ A X -> X) -> (μF -> X) ;
    in_  : ⟦ F ⟧ A μF -> μF ;
    cata_charn : forall (X : Type) (f : μF -> X) (φ : ⟦ F ⟧ A X -> X),
        f ∘ in_ = φ ∘ F[f] <-> f = cata X φ
  }.

Notation "⦇ f ⦈" := (cata _ f) (at level 5).

(* Properties of catamorphisms *)
Section catamorphism.

  Variable (F : PolyF) (A : Type) (μF : Type)
           (ia : F_initial_algebra F A μF).
  
  Proposition cata_cancel :
    forall (X : Type) (φ : ⟦ F ⟧ A X -> X),
      ⦇ φ ⦈ ∘ in_ = φ ∘ F[⦇ φ ⦈].
  Proof.
    intros X φ.
    apply cata_charn; reflexivity.
  Qed.

  Proposition cata_refl : ⦇ in_ ⦈ = id.
  Proof.
    symmetry. apply cata_charn.
    rewrite fmap_functor_id. easy.
  Qed.
  Hint Resolve cata_refl.

  Proposition cata_fusion :
    forall (X Y : Type) (φ : ⟦ F ⟧ A X -> X) (ψ : ⟦ F ⟧ A Y -> Y) f,
      f ∘ φ = ψ ∘ F[f] -> f ∘ ⦇φ⦈ = ⦇ψ⦈.
  Proof.
    intros X Y φ ψ f H. 
    apply cata_charn.
    @ goal : ( f ∘ ⦇ φ ⦈ ∘ in_ = ψ ∘ F [f ∘ ⦇ φ ⦈] ).
    Left
    = ( f ∘ (⦇ φ ⦈ ∘ in_) ).
    = ( f ∘ φ ∘ F[⦇ φ ⦈] )       { by cata_cancel }.
    = ( ψ ∘ (F[f] ∘ F[⦇ φ ⦈]) )  { by H }.
    = ( ψ ∘ F[f ∘ ⦇ φ ⦈] )       { by fmap_functor_distr }.
    = Right.
  Qed.

  Proposition lambek1 : (in_) ∘ ⦇ F[in_] ⦈ = id.
  Proof.
    Left
    = ( ⦇ in_ ⦈ )     { apply cata_fusion; easy }.
    = ( @id (μF) )    { by cata_refl }.
    = Right.
  Qed.

  Proposition lambek2 : ⦇ F[in_] ⦈ ∘ in_  = id.
  Proof.
    Left
    = ( ⦇ F[in_] ⦈ ∘ in_ ).
    = ( F[in_] ∘ ( F❲@id A❳[⦇ F[in_] ⦈] ) )  { by cata_cancel }.
    = ( F❲@id A❳[in_ ∘ ⦇ F[in_] ⦈] ).
    = ( F❲@id A❳[@id μF] )                   { by lambek1 }.
    = ( @id (⟦F⟧ A μF) ).
    = Right.
  Qed.

  Proposition lemma1 : in_ ∘ ⦇ F[in_] ⦈ = id /\ ⦇ F[in_] ⦈ ∘ in_ = id.
  Proof.
    intros; split.
    - apply lambek1.
    - apply lambek2.
  Qed.
  
  Definition in_inv {F : PolyF} {A : Type} {μF : Type}
             {ia : F_initial_algebra F A μF}
    := ⦇ F❲@id A❳[in_] ⦈.

  Proposition in_inv_charn1 :
    in_ ∘ in_inv = id.
  Proof.
    apply lambek1.
  Qed.

  Proposition in_inv_charn2 : in_inv ∘ in_ = id.
  Proof.
    apply lambek2.
  Qed.

  Proposition in_inv_charn :
    in_ ∘ in_inv = id /\ in_inv ∘ in_ = id.
  Proof.
    split.
    - apply lambek1.
    - apply lambek2.
  Qed.
End catamorphism.
  
(* Terminal-coalgebra and anamorphism *)
Class F_terminal_coalgebra (F : PolyF) (A : Type) (νF : Type) :=
  {
    ana  : forall (X : Type), (X -> ⟦ F ⟧ A X) -> (X -> νF);
    out_ : νF -> ⟦ F ⟧ A νF;
    ana_charn : forall (X : Type) (f : X -> νF) (φ : X -> ⟦ F ⟧ A X),
        out_ ∘ f = F[f] ∘ φ <-> f = ana X φ
  }.

Notation "〖 f 〗" := (ana _  f) (at level 5).
 
Section anamorphism.
  Variable (F : PolyF) (A : Type) (νF : Type)
           (tc : F_terminal_coalgebra F A νF).

  Proposition ana_charn_right:
    forall (X : Type) (f : X -> νF) (φ : X -> ⟦ F ⟧ A X),
      out_ ∘ f = F[f] ∘ φ -> f =〖 φ 〗.
  Proof.
    intros; apply ana_charn. exact H.
  Qed.
  
  Proposition ana_cancel:
    forall (X : Type) (φ : X -> ⟦ F ⟧ A X),
      out_ ∘〖 φ 〗 = F[〖 φ 〗] ∘ φ.
  Proof.
    intros; apply ana_charn; reflexivity.
  Qed.

  Proposition ana_refl:〖 out_ 〗 = id.
  Proof.
    intros; symmetry.
    apply ana_charn. rewrite fmap_functor_id. easy.
  Qed.

  Proposition ana_fusion:
    forall (X Y : Type) (φ : X -> ⟦ F ⟧ A X) (ψ: Y -> ⟦ F ⟧ A Y) (f : X -> Y),
      ψ ∘ f = F[f] ∘ φ -> 〖 ψ 〗∘ f = 〖 φ 〗. 
  Proof.
    intros. apply ana_charn.
    Left
    = ( F[〖 ψ 〗] ∘ ψ ∘ f )      { by ana_cancel }.
    = ( F[〖 ψ 〗] ∘ (ψ ∘ f) ).
    = ( F[〖 ψ 〗] ∘ F[f] ∘ φ )   { by H }.
    = ( F[〖 ψ 〗∘ f] ∘ φ )       { by fmap_functor_distr }.
    = Right.
  Qed.

  Proposition out_inv_charn1_in: 〖 F[out_] 〗∘ out_ = id.
  Proof.
    intros.
    Left
    = (〖 out_ 〗 )              { apply ana_fusion }.
    = ( @id νF )                { by ana_refl }.
    = Right.
  Qed.

  Proposition out_inv_charn2_in: out_ ∘〖 F[out_] 〗= id.
  Proof.
    intros.
    Left
    = ( F[〖 F[out_] 〗] ∘ F❲@id A❳[out_] )   { by ana_cancel }.
    = ( F❲@id A❳[@id νF] )                   { by out_inv_charn1_in }.
    = Right.
  Qed.

  Definition out_inv {F : PolyF} {A : Type} {νF : Type}
             {tc : F_terminal_coalgebra F A νF}
    := 〖 F[out_] 〗.

  Proposition out_inv_charn1: out_inv ∘ out_ = id.
  Proof.
    apply out_inv_charn1_in.
  Qed.

  Proposition out_inv_charn2: out_ ∘ out_inv = id.
  Proof.
    apply out_inv_charn2_in.
  Qed.

  Proposition out_inv_charn: out_inv ∘ out_ = id /\ out_ ∘ out_inv = id.
  Proof.
    intros; split.
    - apply out_inv_charn1.
    - apply out_inv_charn2.
  Qed.
End anamorphism.

Proposition lemma2 :
  forall (F : PolyF) (A : Type) (μF : Type)
         (ia : F_initial_algebra F A μF)
         {C : Type} (f : μF -> C) (φ : ⟦ F ⟧ A (C * μF)%type -> C),
    f ∘ in_ = φ ∘ F [ 〈 f , id 〉 ] <-> f = fst ∘ ⦇ 〈 φ , in_ ∘ F[snd] 〉 ⦈.
Proof.
  intros; split.
  - intros H.
    assert ( 〈 f, id 〉 ∘ in_ = 〈 φ , in_ ∘ F[snd] 〉 ∘ F[〈 f , id 〉] ) as H1.
    {
      Left
      = ( 〈 f, id 〉 ∘ in_ ).
      = ( 〈 f ∘ in_ , in_ ∘ id 〉 ).
      = ( 〈 f ∘ in_ , in_ ∘ F[snd ∘ 〈 f, id 〉] 〉 )            { by fmap_functor_id }.
      = ( 〈 φ ∘ F[〈 f, id 〉] , in_ ∘ F[snd ∘ 〈 f, id 〉] 〉 )    { by H }.
      = ( 〈 φ ∘ F[〈 f, id 〉] , in_ ∘ F[snd] ∘ F[〈 f, id 〉] 〉 ) { by fmap_functor_distr }.
      = Right.
    }
    apply cata_charn in H1.
    @ H1 : ( 〈 f, id 〉 = ⦇ 〈 φ, in_ ∘ F [snd] 〉 ⦈ ).
    Left
    = ( fst ∘ ⦇ 〈 φ, in_ ∘ F[snd] 〉 ⦈ )   { by H1 }.
    = Right.
  - intros H.
    assert ( ⦇ 〈 φ, in_ ∘ F[snd] 〉 ⦈ ∘ in_ = 〈 φ, in_ ∘ F[snd] 〉 ∘ F[⦇ 〈 φ, in_ ∘ F[snd] 〉 ⦈])
      as H1 by (apply cata_charn; easy).
    assert ( snd ∘ 〈 φ, in_ ∘ F[snd] 〉 = in_ ∘ F[snd] ) as H2 by auto.
    assert ( snd ∘ ⦇ 〈 φ, in_ ∘ F[snd] 〉 ⦈ = ⦇ in_ ⦈ ) as H3.
    {
      apply cata_fusion; easy.
    }
    Left
    = ( f ∘ in_ ).
    = ( fst ∘ (⦇ 〈 φ, in_ ∘ F[snd] 〉 ⦈ ∘ in_) )                                   { by H }.
    = ( fst ∘ 〈 φ, in_ ∘ F[snd] 〉 ∘ F[⦇ 〈 φ, in_ ∘ F[snd] 〉 ⦈] )                   { by H1 }.
    = ( φ ∘ F[〈 fst ∘ ⦇ 〈 φ, in_ ∘ F[snd] 〉 ⦈ , snd ∘ ⦇ 〈 φ, in_ ∘ F[snd] 〉 ⦈ 〉] )  { by pairing }.
    = ( φ ∘ F[〈 f , snd ∘ ⦇ 〈 φ, in_ ∘ F[snd] 〉 ⦈ 〉] )                             { by H }.
    = ( φ ∘ F[〈 f , ⦇ in_ ⦈ 〉] )                                                  { by H3 }.
    = ( φ ∘ F[〈 f , id 〉] )                                                       { by cata_refl }.
    = Right.
Qed.

(* Definition of paramorphisms *)
Definition para (F : PolyF) (A : Type) (μF : Type)
           (ia : F_initial_algebra F A μF)
           {C : Type} (φ : ⟦ F ⟧ A (C * μF)%type -> C) 
  := fst ∘ ⦇ 〈 φ, in_ ∘ F[snd] 〉 ⦈.
Notation "◃ f ▹" := (para _ _ _ _ f) (at level 5).

(* Properties of paramorphisms *)
Section paramorphism.

  Variable (F : PolyF) (A : Type) (μF : Type)
           (ia : F_initial_algebra F A μF).
  
  Proposition para_charn:
    forall {C : Type} (f : μF -> C) (φ : ⟦ F ⟧ A (C * μF)%type -> C),
      f ∘ in_ = φ ∘ F[〈f, id〉] <-> f = ◃φ▹.
  Proof.
    intros; apply lemma2.
  Qed.

  Proposition para_cancel:
    forall {C : Type} (φ : ⟦ F ⟧ A (C * μF)%type -> C),
      ◃ φ ▹ ∘ in_ = φ ∘ F[〈◃φ▹, id〉].
  Proof.
    intros. apply para_charn; reflexivity.
  Qed.

  Proposition para_refl: id = ◃ in_ ∘ F[fst] ▹.
  Proof.
    intros. apply para_charn.
    Right
    = ( in_ ∘ F [fst] ∘ F [〈 id, id 〉] ).
    = ( in_ ∘ ( F [fst] ∘ F [〈 id, id 〉] ) ).
    = ( in_ ∘ ( F [fst ∘ 〈 id, id 〉] ) )          { by fmap_functor_distr }.
    = ( in_ ∘ F [id] ).
    = ( in_ ∘ id )                               { by fmap_functor_id } .
    = Left.
  Qed.

  Proposition para_fusion:
    forall {C D : Type} (f : C -> D) (φ : ⟦ F ⟧ A (C * μF)%type -> C)
           (ψ : ⟦ F ⟧ A (D * μF)%type -> D),
      f ∘ φ = ψ ∘ F[f ⊗ id] -> f ∘ ◃ φ ▹ = ◃ ψ ▹.
  Proof.
    intros. apply para_charn.
    Left
    = ( f ∘ ◃ φ ▹ ∘ in_ ).
    = ( f ∘ (◃ φ ▹ ∘ in_) ).
    = ( f ∘ (φ ∘ F[〈 ◃ φ ▹, id 〉]) )        { by para_cancel }.
    = ( (f ∘ φ) ∘ F[〈 ◃ φ ▹, id 〉] ).
    = ( ψ ∘ F[f ⊗ id] ∘ F[〈◃ φ ▹, id〉] )    { by H }.
    = ( ψ ∘ F[f ⊗ id ∘ 〈◃ φ ▹, id〉] )       { by fmap_functor_distr }.
    = ( ψ ∘ F[〈f ∘ ◃ φ ▹, id ∘ id〉] )       { by pairing2 }.
    = Right.
  Qed.

  Proposition para_cata:
    forall {C : Type} (φ : ⟦ F ⟧ A C -> C),
      ⦇ φ ⦈ = ◃ φ ∘ F[fst] ▹.
  Proof.
    intros C φ.
    apply para_charn.
    Left
    = ( ⦇ φ ⦈ ∘ in_ ).
    = ( φ ∘ F[⦇ φ ⦈] )                    { by cata_cancel }.
    = ( φ ∘ F[fst ∘ 〈 ⦇ φ ⦈ , id 〉] ).
    = ( φ ∘ F[fst] ∘ F[〈 ⦇ φ ⦈ , id 〉] )   { by fmap_functor_distr }.
    = Right.
  Qed.

  Proposition para_any:
    forall {C : Type} (f : μF -> C),
      f = ◃ f ∘ in_ ∘ F[snd] ▹.
  Proof.
    intros; apply para_charn.
    Right
    = ( f ∘ in_ ∘ F[snd] ∘ F[〈 f, id 〉] ).
    = ( f ∘ in_ ∘ (F[snd] ∘ F[〈 f, id 〉]) ).
    = ( f ∘ in_ ∘ (F[snd ∘ 〈 f, id 〉]) )      { by fmap_functor_distr }.
    = ( f ∘ in_ ∘ F[id] ).
    = ( f ∘ in_ ∘ id)                        { by fmap_functor_id }.
    = Left.
  Qed.

  Proposition para_in_inv:
    in_inv = ◃ F[snd] ▹.
  Proof.
    Left
    = ( ◃ in_inv ∘ in_ ∘ F[snd] ▹ )     { by para_any }.
    = ( ◃ F[snd] ▹ )                    { by in_inv_charn2 }.
    = Right.
  Qed.
  
End paramorphism.

(* Definition of apomorphisms *)
Definition apo (F : PolyF) (A : Type) (νF : Type)
           (tc : F_terminal_coalgebra F A νF)
           {C : Type} (φ : C -> ⟦ F ⟧ A (C + νF)%type) 
  := 〖[φ, F[inr] ∘ out_]〗∘ inl.

(*
  Unfortinently, we cannot find the parenthesis for apomorphism ("[\langle" and "\rangle]") in
  unicode characters, thus we use【 and 】instead of "[\langle" and "\rangle]".
 *)
Notation "【 f 】" := (apo _ _ _ _ f) (at level 5).

Section apomorphism.

  Variable (F : PolyF) (A : Type) (νF : Type)
           (tc : F_terminal_coalgebra F A νF).

  Proposition apo_charn:
    forall (C : Type) (φ : C -> ⟦ F ⟧ A (C + νF)%type) (f : C -> νF),
      out_ ∘ f = F[[f, id]] ∘ φ <-> f =【 φ 】.
  Proof.
    split.
    - intros H.
      assert ( out_ ∘ [f, @id νF] = F[[f, id]] ∘ [φ, F[inr] ∘ out_] ) as H0.
      {
        Left
        = ( out_ ∘ [f, @id νF] ).
        = ( [out_ ∘ f, id ∘ out_] )                         { by copairing2 }.
        = ( [out_ ∘ f, F[id] ∘ out_] )                      { by fmap_functor_id }.
        = ( [out_ ∘ f, F[[f, id]] ∘ F[inr] ∘ out_] )        { by fmap_functor_distr }.
        = ( [F[[f, id]] ∘ φ, F[[f, id]] ∘ F[inr] ∘ out_] )  { by H }.
        = ( F[[f, id]] ∘ [φ, F[inr] ∘ out_] )               { by copairing2 }.
        = Right.
      }
      specialize (ana_charn_right _ _ _ _ _ ([f, @id νF]) ([φ, F [inr] ∘ out_]) H0) as H1.
      @ H1 : ( [f, id] = 〖 [φ, F [inr] ∘ out_] 〗).
      Left
      = ( [f, @id νF] ∘ inl ).
      = (〖[φ, F[inr] ∘ out_]〗∘ inl)   { by H1 }.
      = Right.      
    - intros H.
      assert ( [φ, F[inr] ∘ out_] ∘ inr = F[inr] ∘ out_ ) as H0 by easy.
      specialize (ana_fusion _ _ _ _ _ _ out_ ([φ, F[inr] ∘ out_]) inr H0) as H1.
      Left
      = ( out_ ∘ f ).
      = ( out_ ∘〖[φ, F[inr] ∘ out_]〗∘ inl )                       { by H }.
      = ( F[〖 [φ, F[inr] ∘ out_] 〗] ∘ [φ, F[inr] ∘ out_] ∘ inl )  { by ana_cancel }.
      = ( F[ [〖 [φ, F[inr] ∘ out_] 〗∘ inl, 〖 [φ, F[inr] ∘ out_] 〗∘ inr] ] ∘ ([φ, F[inr] ∘ out_] ∘ inl) )
          { by copairing }.
      = ( F[ [〖 [φ, F[inr] ∘ out_] 〗∘ inl, 〖 [φ, F[inr] ∘ out_] 〗∘ inr] ] ∘ φ ).
      = ( F[ [f,〖 [φ, F[inr] ∘ out_] 〗∘ inr] ] ∘ φ )              { by H }.
      = ( F[ [f,〖 out_ 〗] ] ∘ φ )                                 { by H1 }.
      = ( F[ [f, id] ] ∘ φ )                                       { by ana_refl }.
      = Right.
  Qed.

  Proposition apo_charn_onlyif :
     forall (C : Type) (φ : C -> ⟦ F ⟧ A (C + νF)%type) (f : C -> νF),
       out_ ∘ f = F[[f, id]] ∘ φ -> f =【 φ 】.
  Proof.
    apply apo_charn.
  Qed.
  
  Proposition apo_cancel:
     forall (C : Type) (φ : C -> ⟦ F ⟧ A (C + νF)%type),
       out_ ∘【 φ 】 = F[[【 φ 】, id]] ∘ φ.
  Proof.
    intros; apply apo_charn; reflexivity.
  Qed.
  
  Proposition apo_refl:
    id =【 F[inl] ∘ out_ 】.
  Proof.
    apply apo_charn_onlyif.
    @ goal : ( out_ ∘ id = F [[id, id]] ∘ (F [inl] ∘ out_) ).
    Left
    = ( out_ ).
    = ( F[id] ∘ out_ )                    { by fmap_functor_id }.
    = ( F[ [id, id] ∘ inl] ∘ out_ ).
    = ( F[ [id, id] ] ∘ F[inl] ∘ out_ )   { by fmap_functor_distr }.
    = Right.
  Qed.

  Proposition apo_fusion:
    forall {C D : Type} (f : C -> D)
           (φ : C -> ⟦ F ⟧ A (C + νF)%type) (ψ : D -> ⟦ F ⟧ A (D + νF)%type),
      ψ ∘ f = F[(f ⊕ id)] ∘ φ -> 【 ψ 】 ∘ f =【 φ 】.
  Proof.
    intros C D f φ ψ H.
    apply apo_charn.
    Left
    = ( out_ ∘【 ψ 】∘ f ).
    = ( F[[【 ψ 】, id]] ∘ (ψ ∘ f) )           { by apo_cancel }.
    = ( F[[【 ψ 】, id]] ∘ F [f ⊕ id] ∘ φ )    { by H }.
    = ( F[ [【 ψ 】, id] ∘ (f ⊕ id) ] ∘ φ )    { by fmap_functor_distr }.
    = ( F[ [【 ψ 】∘ f , id] ] ∘ φ )           { by copairing2 }.
    = Right.
  Qed.

  Proposition apo_ana:
    forall {C : Type} (φ : C -> ⟦ F ⟧ A C),
      〖 φ 〗=【 F[inl] ∘ φ 】.
  Proof.
    intros.
    apply apo_charn.
    Left
    = ( out_ ∘ 〖 φ 〗).
    = ( F[〖 φ 〗] ∘ φ )                 { by ana_cancel }.
    = ( F[[〖 φ 〗, id] ∘ inl] ∘ φ ).
    = ( F[[〖 φ 〗, id]] ∘ F[inl] ∘ φ )  { by fmap_functor_distr }.
    = Right.
  Qed.

  Proposition apo_any:
    forall {C : Type} (f : C -> νF),
      f =【 F[inr] ∘ out_ ∘ f 】.
  Proof.
    intros. apply apo_charn.
    Right
    = ( F[[f, id]] ∘ F[inr] ∘ out_ ∘ f ).
    = ( F[[f, id] ∘ inr] ∘ out_ ∘ f  )     { by fmap_functor_distr }.
    = ( out_ ∘ f )                         { by fmap_functor_id }.
    = Left.
  Qed.

End apomorphism.

Lemma lemma3:
  forall (F : PolyF) (μF : Type) (C : Type) (νFC : Type)
         (ia : F_initial_algebra F _ μF)
         (tc : F_terminal_coalgebra (Prod arg1 F) _ νFC),
  forall (f : μF -> C) (φ : ⟦F⟧ C νFC -> C),
    f ∘ in_ = φ ∘ F[〖 〈 f, in_inv 〉 〗]
    <-> f = fst ∘ out_ ∘ ⦇ out_inv ∘ 〈 φ , id 〉 ⦈.
Proof.
  intros. split.
  - intros H.
    assert ( 〖 〈 f, in_inv 〉 〗∘ in_ = out_inv ∘ 〈 φ , id 〉 ∘ F[〖 〈 f, in_inv 〉 〗] ) as H1.
    {
      Left
      = (〖 〈 f, in_inv 〉 〗∘ in_ ).
      = ( id ∘〖 〈 f, in_inv 〉 〗∘ in_ ).
      = ( out_inv ∘ out_ ∘〖 〈 f, in_inv 〉 〗∘ in_ )   { by out_inv_charn1 }.
      = ( out_inv ∘ (out_ ∘〖 〈 f, in_inv 〉 〗) ∘ in_ ).
      = ( out_inv ∘ ((Prod arg1 F) [〖 〈 f, in_inv 〉 〗] ∘ 〈 f, in_inv 〉) ∘ in_ )  { by ana_cancel }.
      = ( out_inv ∘ 〈 f , F[〖 〈 f, in_inv 〉 〗] ∘ in_inv 〉 ∘ in_ ).
      = ( out_inv ∘ 〈 f ∘ in_  , F[〖 〈 f, in_inv 〉 〗] ∘ in_inv ∘ in_  〉 ).
      = ( out_inv ∘ 〈 φ ∘ F [〖 〈 f, in_inv 〉 〗], F [〖 〈 f, in_inv 〉 〗] ∘ (in_inv ∘ in_) 〉 )
          { by H }.
      = ( out_inv ∘ 〈 φ ∘ F [〖 〈 f, in_inv 〉 〗], F [〖 〈 f, in_inv 〉 〗] 〉 )
          { by in_inv_charn2 }.
      = Right.
    }
    apply cata_charn in H1.
    @ H1 : (〖 〈 f, in_inv 〉 〗 = ⦇ out_inv ∘ 〈 φ, id 〉 ⦈ ).
    Left
    = f.
    = ( fst ∘ 〈f, in_inv〉).
    = ( fst ∘ ( (Prod arg1 F)[〖 〈 f, in_inv 〉 〗] ∘ 〈f, in_inv〉) ).
    = ( fst ∘ (out_ ∘ 〖 〈 f, in_inv 〉 〗) )   { by ana_cancel }.
    = ( fst ∘ out_ ∘ ⦇ out_inv ∘ 〈 φ, id 〉 ⦈ ) { by H1 }.
    = Right.
  - intros.
    assert ( out_ ∘ ⦇ out_inv ∘ 〈 φ, id 〉 ⦈ = (Prod arg1 F) [ ⦇ out_inv ∘ 〈 φ, id 〉 ⦈ ] ∘ 〈 f, in_inv 〉 ) as H1.
    {
      Left
      = ( out_ ∘ ⦇ out_inv ∘ 〈 φ, id 〉 ⦈ ).
      = ( 〈 fst ∘ out_ ∘ ⦇ out_inv ∘ 〈 φ, id 〉 ⦈ , snd ∘ out_ ∘ ⦇ out_inv ∘ 〈 φ, id 〉 ⦈ 〉 )
          { symmetry; apply pairing }.
      = ( 〈 f , snd ∘ out_ ∘ ⦇ out_inv ∘ 〈 φ, id 〉 ⦈〉 )
          { by H }.
      = ( 〈 f , snd ∘ out_ ∘ ⦇ out_inv ∘ 〈 φ, id 〉 ⦈ ∘ (in_ ∘ in_inv) 〉 )
          { by in_inv_charn1 }.
      = ( 〈 f , snd ∘ out_ ∘ (⦇ out_inv ∘ 〈 φ, id 〉 ⦈ ∘ in_) ∘ in_inv 〉 ).
      = ( 〈 f, snd ∘ (out_ ∘ out_inv) ∘ 〈 φ, id 〉 ∘ F [⦇ out_inv ∘ 〈 φ, id 〉 ⦈] ∘ in_inv 〉 )
          { by cata_cancel }.
      = ( 〈 f, snd ∘ 〈 φ, id 〉 ∘ F [⦇ out_inv ∘ 〈 φ, id 〉 ⦈] ∘ in_inv 〉 )
          { by out_inv_charn2 }.
      = ( 〈 f, F [⦇ out_inv ∘ 〈 φ, id 〉 ⦈] ∘ in_inv 〉 ).
      = Right.
    }
    apply ana_charn in H1.
    @ H1 : ( ⦇ out_inv ∘ 〈 φ, id 〉 ⦈ = 〖 〈 f, in_inv 〉 〗 ).
    Left
    = ( f ∘ in_ ).
    = ( fst ∘ out_ ∘ ( ⦇ out_inv ∘ 〈 φ, id 〉 ⦈ ∘ in_) )  { by H }.
    = ( fst ∘ (out_ ∘ out_inv) ∘ 〈 φ, id 〉 ∘ F [⦇ out_inv ∘ 〈 φ, id 〉 ⦈] )
        { by cata_cancel }.
    = ( fst ∘ 〈 φ, id 〉 ∘ F [⦇ out_inv ∘ 〈 φ, id 〉 ⦈] )
        { by out_inv_charn2 }.
    = ( φ ∘ F [⦇ out_inv ∘ 〈 φ, id 〉 ⦈] ).
    = (  φ ∘ F [〖 〈 f, in_inv 〉 〗] )                 { by H1 }.
    = Right.
Qed.

Definition histo (F : PolyF) (μF : Type) (C : Type) (νFC : Type)
         (ia : F_initial_algebra F C μF)
         (tc : F_terminal_coalgebra (Prod arg1 F) C νFC)
         (φ : ⟦F⟧ C νFC -> C)
  := fst ∘ out_ ∘ ⦇ out_inv ∘ 〈 φ , id 〉 ⦈.

Notation " {| φ |} " := (histo _ _ _ _ _ _ φ).

Section histomorphism.
  
  Variable (F : PolyF) (μF : Type) (C : Type) (νFC : Type)
           (ia : F_initial_algebra F C μF)
           (tc : F_terminal_coalgebra (Prod arg1 F) C νFC).

  Proposition histo_charn :
    forall (f : μF -> C) (φ : ⟦F⟧ C νFC -> C),
      f ∘ in_ = φ ∘ F[〖 〈 f, in_inv 〉 〗] <-> f = {| φ |}.
  Proof.
    apply lemma3.
  Qed.

  Proposition histo_cancel :
    forall (φ : ⟦F⟧ C νFC -> C),
      {| φ |} ∘ in_ = φ ∘ F[〖 〈 {| φ |}, in_inv 〉 〗].
  Proof.
    intros.
    apply histo_charn.
    reflexivity.
  Qed.

End histomorphism.

Proposition histo_refl (F : PolyF) (μF : Type) (νFC : Type)
            (ia : F_initial_algebra F μF μF)
            (tc : F_terminal_coalgebra (Prod arg1 F) μF νFC)
  : id = {| in_ ∘ F[ fst ∘ out_ ] |}.
Proof.
  apply histo_charn.
  Left
  = ( in_ ).
  = ( in_ ∘ F[id] )   { by fmap_functor_id }.
  = ( in_ ∘ F[ fst ∘ 〈 id, in_inv 〉 ] ).
  = ( in_ ∘ F[ fst ∘ (( id ⊗ F[〖 〈 id, in_inv 〉 〗] ) ∘ 〈 id, in_inv 〉 ) ] ).
  = ( in_ ∘ F[ fst ∘ ( out_ ∘〖 〈 id, in_inv 〉 〗) ] )
      { by ana_cancel }.
  = ( in_ ∘ F[ fst ∘ out_ ∘〖 〈 id, in_inv 〉 〗] ).
  = ( in_ ∘ F[ fst ∘ out_ ] ∘ F[〖 〈 id, in_inv 〉 〗] )
      { by fmap_functor_distr }.
  = Right.
Qed.

(* It is not in principla type contest *)
Proposition histo_fusion :
  forall (F : PolyF) (μF C νFC : Type)
         (ia : F_initial_algebra F C μF)
         (tc : F_terminal_coalgebra (Prod arg1 F) C νFC)
         (φ : ⟦F⟧ C νFC -> C) (ψ : ⟦F⟧ C νFC -> C) (f : C -> C),
    f ∘ φ = ψ ∘ F[ @ana _ C νFC _ νFC ((f ⊗ id) ∘ out_)] -> f ∘ {| φ |} = {| ψ |}.
Proof.
  intros.
  assert ( (f ⊗ id) ∘ out_ ∘〖 〈 {| φ |} , in_inv 〉 〗
           = id ⊗ F[〖 〈 {| φ |} , in_inv 〉 〗] ∘ 〈 f ∘ {| φ |} , in_inv 〉 ).
  {
    Left
    = ( (f ⊗ id) ∘ (out_ ∘〖 〈 {| φ |} , in_inv 〉 〗) ).
    = ( f ⊗ id ∘ ((Prod arg1 F)[〖 〈 {|φ|}, in_inv 〉 〗] ∘ 〈 {|φ|}, in_inv 〉) )
        { by ana_cancel }.
    = ( f ⊗ id ∘ (id ⊗ F[〖 〈 {|φ|}, in_inv 〉 〗] ∘ 〈 {|φ|}, in_inv 〉) ).
    = ( 〈 f ∘ {|φ|}, F[〖 〈 {|φ|}, in_inv 〉 〗] ∘ in_inv 〉 ).
    = Right.
  }
  assert ( 〖 f ⊗ id ∘ out_ 〗 ∘ 〖 〈 {|φ|}, in_inv 〉 〗 = 〖 〈 f ∘ {|φ|}, in_inv 〉 〗 ) as H1 by (apply ana_fusion; easy).
  apply histo_charn.
  Left
  = ( f ∘ ({|φ|} ∘ in_) ).
  = ( f ∘ φ ∘ F [〖 〈 {|φ|}, in_inv 〉 〗] )                         { by histo_cancel }.
  = ( ψ ∘ F[〖 (f ⊗ id) ∘ out_ 〗] ∘ F[〖 〈 {|φ|}, in_inv 〉 〗] )    { by H }.
  = ( ψ ∘ F[〖 (f ⊗ id) ∘ out_ 〗∘〖 〈 {|φ|}, in_inv 〉 〗] )         { by fmap_functor_distr }.
  = ( ψ ∘ F[〖 〈 f ∘ {|φ|}, in_inv 〉 〗] )                          { by H1 }.
  = Right.
Qed.

Proposition histo_cata :
  forall (F : PolyF) (μF C νFC : Type)
         (ia : F_initial_algebra F C μF)
         (tc : F_terminal_coalgebra (Prod arg1 F) C νFC)
         (φ : ⟦F⟧ C C -> C),
    ⦇ φ ⦈ = {| φ ∘ F[fst ∘ out_] |}.
Proof.
  intros.
  apply histo_charn.
  Left
  = ( ⦇ φ ⦈ ∘ in_ ).
  = ( φ ∘ F [⦇ φ ⦈] )                                           { by cata_cancel }.
  = ( φ ∘ F[ fst ∘ 〈 ⦇ φ ⦈, in_inv 〉 ] ).
  = ( φ ∘ F[ fst ∘ ((Prod arg1 F)[〖 〈 ⦇ φ ⦈ , in_inv 〉 〗] ∘ 〈 ⦇ φ ⦈, in_inv 〉 ) ] ).
  = ( φ ∘ F[ fst ∘ out_ ∘〖 〈 ⦇ φ ⦈ , in_inv 〉 〗] )              { by ana_cancel }.
  = ( φ ∘ F [fst ∘ out_] ∘ F [〖 〈 ⦇ φ ⦈, in_inv 〉 〗] )          { by fmap_functor_distr }.
  = Right.
Qed.

Definition futu (F : PolyF) (νF : Type) (C : Type) (μFC : Type)
         (tc : F_terminal_coalgebra F C νF)
         (ia : F_initial_algebra (Sum arg1 F) C μFC)
         (φ : C -> ⟦F⟧ C μFC)
  := 〖 [ φ , id ] ∘ in_inv 〗 ∘ in_ ∘ inl .

Notation "[{ φ }] " := (futu _ _ _ _ _ _ φ).

Section futumorphism.

  Variable (F : PolyF) (νF : Type) (C : Type) (μFC : Type)
           (tc : F_terminal_coalgebra F C νF)
           (ia : F_initial_algebra (Sum arg1 F) C μFC)
           (φ : C -> ⟦F⟧ C μFC).
  
  Proposition futu_charn :
    forall (f : C -> νF),
      out_ ∘ f = F[ ⦇ [ f, out_inv ] ⦈ ] ∘ φ <-> f = [{ φ }] .
  Proof.
    intros; split.
    - intros H.
      assert ( out_ ∘  ⦇ [ f, out_inv ] ⦈ = F[ ⦇ [ f, out_inv ] ⦈ ] ∘ [ φ, id ] ∘ in_inv ) as H1.
      {
        Left
        = ( out_ ∘ ⦇ [ f, out_inv ] ⦈ ∘ (in_ ∘ in_inv) )               { by in_inv_charn1 }.
        = ( out_ ∘ (⦇ [ f, out_inv ] ⦈ ∘ in_) ∘ in_inv ).
        = ( out_ ∘ ( [f, out_inv] ∘ (Sum arg1 F)[⦇ [f, out_inv] ⦈] ) ∘ in_inv )
            { by cata_cancel }.
        = ( out_ ∘ ( [f, out_inv] ∘ (id ⊕ F[⦇ [f, out_inv] ⦈]) ) ∘ in_inv ).
        = ( out_ ∘ [ f, out_inv ∘ F[⦇ [f, out_inv] ⦈] ] ∘ in_inv )     { by copairing2 }.
        = ( [ out_ ∘ f, out_ ∘ out_inv ∘ F[⦇ [f, out_inv] ⦈] ] ∘ in_inv )
            { by copairing2 }.
        = ( [ out_ ∘ f,  F[⦇ [f, out_inv] ⦈] ] ∘ in_inv )
            { by out_inv_charn2 }.
        = ( [ F[⦇ [f, out_inv] ⦈] ∘ φ ,  F[⦇ [f, out_inv] ⦈] ] ∘ in_inv )
            { by H }.
        = ( F [⦇ [f, out_inv] ⦈] ∘ [φ, id] ∘ in_inv )
            { by copairing2 }.
        = Right.
      }
      apply ana_charn in H1.
      Left
      = f.
      = ( [f, out_inv] ∘ inl ).
      = ( [f, out_inv] ∘ (Sum arg1 F)[ ⦇ [f, out_inv] ⦈ ] ∘ inl ).
      = ( ⦇ [f, out_inv] ⦈ ∘ in_ ∘ inl )                              { by cata_cancel }.
      = (〖 [φ, id] ∘ in_inv 〗∘ in_ ∘ inl )                          { by H1 }.
      = Right.
    - intros H.
      assert (〖 [φ, id] ∘ in_inv 〗∘ in_ = [f, out_inv] ∘ (Sum arg1 F)[〖 [φ, id] ∘ in_inv 〗] ) as H1.
      {
        Left
        = (〖 [φ, id] ∘ in_inv 〗∘ in_ ).
        = ( [〖 [φ, id] ∘ in_inv 〗∘ in_ ∘ inl ,〖 [φ, id] ∘ in_inv 〗∘ in_ ∘ inr ] )
            { by copairing }.
        = ( [ f ,〖 [φ, id] ∘ in_inv 〗∘ in_ ∘ inr ] )
            { by H }.
        = ( [ f , out_inv ∘ out_ ∘〖 [φ, id] ∘ in_inv 〗∘ in_ ∘ inr ] )
            { by out_inv_charn1 }.
        = ( [ f , out_inv ∘ (out_ ∘〖 [φ, id] ∘ in_inv 〗) ∘ in_ ∘ inr ] ).
        = ( [ f, out_inv ∘ ( F[〖 [φ, id] ∘ in_inv 〗] ∘ ( [φ, id] ∘ in_inv ) ) ∘ in_ ∘ inr ] )
            { by ana_cancel }.
        = ( [ f, out_inv ∘ F[〖 [φ, id] ∘ in_inv 〗] ∘ [φ, id] ∘ (in_inv ∘ in_) ∘ inr ] ).
        = ( [ f, out_inv ∘ F[〖 [φ, id] ∘ in_inv 〗] ∘ ([φ, id] ∘ inr) ] )
            { by in_inv_charn2 }.
        = ( [ f, out_inv ∘ F[〖 [φ, id] ∘ in_inv 〗] ] ).
        = ( [ f, out_inv ] ∘ (Sum arg1 F)[〖 [φ, id] ∘ in_inv 〗] )
            { by copairing }.
        = Right.
      }
      apply cata_charn in H1.
      Left
      = ( out_ ∘ f ).
      = ( out_ ∘〖 [ φ , id ] ∘ in_inv 〗 ∘ in_ ∘ inl )                  { by H }.
      = ( F[〖 [φ, id] ∘ in_inv 〗] ∘ [φ, id] ∘ (in_inv ∘ in_) ∘ inl )   { by ana_cancel }.
      = ( F[〖 [φ, id] ∘ in_inv 〗] ∘ ( [φ, id] ∘ inl ) )                { by in_inv_charn2 }.
      = ( F[ ⦇ [f, out_inv] ⦈ ] ∘ φ )                                    { by H1 }.
      = Right.
  Qed.

  Proposition futu_charn_onlyif :
    forall (f : C -> νF),
      out_ ∘ f = F[ ⦇ [ f, out_inv ] ⦈ ] ∘ φ -> f = [{ φ }] .
  Proof.
    apply futu_charn.
  Qed.
  

  Proposition futu_cancel :
    out_ ∘ [{ φ }] = F[ ⦇ [ [{ φ }] , out_inv ] ⦈ ] ∘ φ.
  Proof.
    apply futu_charn; reflexivity.
  Qed.

End futumorphism.

Proposition futu_refl :
  forall (F : PolyF) (νF : Type) (μFC : Type)
         (tc : F_terminal_coalgebra F νF νF)
         (ia : F_initial_algebra (Sum arg1 F) νF μFC),
    id = [{ F[ in_ ∘ inl ] ∘ out_ }].
Proof.
  intros. apply futu_charn. 
  Right
  = ( F[ ⦇ [id, out_inv] ⦈ ] ∘ F[in_ ∘ inl] ∘ out_ ).
  = ( F[ ⦇ [id, out_inv] ⦈ ∘ in_ ∘ inl] ∘ out_ )
      { by fmap_functor_distr }.
  = ( F[ [id, out_inv] ∘ (Sum arg1 F)[ ⦇ [id, out_inv] ⦈ ] ∘ inl ] ∘ out_)
      { by cata_cancel }.
  = ( F[ [id, out_inv ∘ F[⦇ [id, out_inv] ⦈] ] ∘ inl ] ∘ out_ ).
  = ( F[ id ] ∘ out_  ).
  = ( out_ )
      { by fmap_functor_id }.
  = Left.
Qed.

Proposition futu_fusion :
  forall (F : PolyF) (νF C μFC : Type)
         (tc : F_terminal_coalgebra F C νF)
         (ia : F_initial_algebra (Sum arg1 F) C μFC)
         (φ : C -> ⟦F⟧ C μFC) (ψ : C -> ⟦F⟧ C μFC) (f : C -> C),
    ψ ∘ f = F[ ⦇ in_ ∘ (f ⊕ id) ⦈ ] ∘ φ -> [{ ψ }] ∘ f = [{ φ }].
Proof.
  intros.
  assert ( ⦇ [ [{ ψ }] , out_inv ] ⦈ ∘ in_ ∘ (f ⊕ id)
           = [ [{ ψ }] ∘ f , out_inv ] ∘ id ⊕ F[ ⦇ [ [{ ψ }] , out_inv ] ⦈ ] ).
  {
    Left
    = ( ⦇ [ [{ ψ }] , out_inv ] ⦈ ∘ in_ ∘ (f ⊕ id) ).
    = ( [ [{ψ}] , out_inv ] ∘ id ⊕ F[⦇ [[{ψ}], out_inv] ⦈] ∘ f ⊕ id )
        { by cata_cancel }.
    = ( [ [{ψ}] ∘ f , out_inv ∘ F[⦇ [[{ψ}], out_inv] ⦈] ] )
        { by copairing2 }.
    = ( [[{ψ}] ∘ f, out_inv] ∘ id ⊕ F [⦇ [[{ψ}], out_inv] ⦈] )
        { by copairing2 }.
    = Right.
  }
  assert ( ⦇ [ [{ ψ }] , out_inv] ⦈ ∘ ⦇ in_ ∘ f ⊕ id ⦈ = ⦇ [ [{ ψ }] ∘ f, out_inv] ⦈ ) as H2
      by ( apply cata_fusion; easy ).
  apply futu_charn.
  Left
  = ( out_ ∘ [{ψ}] ∘ f ).
  = ( F[⦇ [[{ ψ }], out_inv] ⦈] ∘ (ψ ∘ f) )                        { by futu_cancel }.  
  = ( F[ ⦇ [ [{ ψ }] , out_inv] ⦈] ∘ F[ ⦇ in_ ∘ f ⊕ id ⦈ ] ∘ φ )   { by H }.
  = ( F[ ⦇ [ [{ ψ }] , out_inv] ⦈ ∘ ⦇ in_ ∘ f ⊕ id ⦈ ] ∘ φ )       { by fmap_functor_distr }.
  = ( F[ ⦇ [ [{ ψ }] ∘ f, out_inv] ⦈ ] ∘ φ )                       { by H2 }.
  = Right.
Qed.

Proposition futu_ana :
  forall (F : PolyF) (νF C μFC : Type)
         (tc : F_terminal_coalgebra F C νF)
         (ia : F_initial_algebra (Sum arg1 F) C μFC)
         (φ : C -> ⟦F⟧ C C),
    〖 φ 〗 = [{ F[in_ ∘ inl] ∘ φ }].
Proof.
  intros; apply futu_charn.
  Right
  = ( F[ ⦇ [〖 φ 〗, out_inv] ⦈ ] ∘ F[ in_ ∘ inl ] ∘ φ ).
  = ( F[ ⦇ [〖 φ 〗, out_inv] ⦈ ∘ in_ ∘ inl ] ∘ φ )
      { by fmap_functor_distr }.
  = ( F[ [〖 φ 〗, out_inv ] ∘ (Sum arg1 F)[ ⦇ [〖 φ 〗, out_inv] ⦈ ] ∘ inl ] ∘ φ )
      { by cata_cancel }.
  = ( F[〖 φ 〗] ∘ φ ).
  = ( out_ ∘ 〖 φ 〗)  { by ana_cancel }.
  = Left.
Qed.
