Require Import Coq.Program.Basics.
Require Import Setoid.

(* state for memorizing direction of equational reasoning *)

Inductive equational_reasoning_direction : Type :=
  Rightwards : equational_reasoning_direction
| Leftwards  : equational_reasoning_direction.

Inductive direction (cs : equational_reasoning_direction) : Prop :=
  state : direction cs.

Tactic Notation "add_state" constr(cs) :=
  let statename := fresh "d" in (
    pose ( statename := direction cs )
  ).

Tactic Notation "set_state" constr(cs) :=
  match goal with
  | [d := direction cs : Prop |- _] => idtac
  | [d := direction _  : Prop |- _] => fail 1 "illegal direction"
  | _ => add_state cs
  end.

Tactic Notation "pop_state" :=
  match goal with
  | [d := direction _ : Prop |- _] => clear d
  end.

(* tactic for obvious rewriting *)

Ltac obvious := (simpl;reflexivity) + easy + auto.

(* rewriting *)

Ltac eq_rewrite_l c t :=
  let Hre := fresh "H" in(
    match goal with
    | [ |- _ ?l _ ] =>
      ( assert (l = c) as Hre );
      [ t;obvious | idtac ];
      (rewrite Hre at 1) +
      (match goal with
       | [ H : _ c c |- _] => idtac
       end);
      clear Hre
    end
  ).

Lemma flipgoal1 :
  forall {A B : Type} (R : A -> B -> Prop) (x : A) (y : B),
    flip R y x -> R x y. 
Proof.
  easy.
Qed.

Lemma flipgoal2 :
  forall {A B : Type} (R : A -> B -> Prop) (x : A) (y : B),
    R x y -> flip R y x. 
Proof.
  easy.
Qed.

Ltac flipgoal :=
  match goal with
  | [ |- flip _ _ _ ] => apply flipgoal2
  | [ |- _ _ _ ] => apply flipgoal1
  end.

Ltac eq_rewrite_r c t :=
  match goal with
  | [ |- ?R _ _ ] =>
    flipgoal;
    eq_rewrite_l c t;
    flipgoal
  end.

(* base tactic notations *)

Tactic Notation (at level 2) "Left" "=" constr(c) "{" tactic(t) "}" :=
  eq_rewrite_l c t ; set_state Rightwards.

Tactic Notation (at level 2) "Right" "=" constr(c) "{" tactic(t) "}" :=
  eq_rewrite_r c t ; set_state Leftwards.

Tactic Notation (at level 2) "=" constr(c) "{" tactic(t) "}" :=
  match goal with
  | [_ := direction Rightwards : Prop |- _] => eq_rewrite_l c t
  | [_ := direction Leftwards  : Prop |- _] => eq_rewrite_r c t
  end.

Tactic Notation (at level 2) "=" "Right" "{" tactic(t) "}" :=
  match goal with
  | [_ := direction Rightwards : Prop |- _ _ ?r] => eq_rewrite_l r t; reflexivity
  end.

Tactic Notation (at level 2) "=" "Left" "{" tactic(t) "}" :=
  match goal with
  | [_ := direction Leftwards : Prop |- _ ?l _] => eq_rewrite_r l t; reflexivity
  end.
  
Tactic Notation (at level 2) "=" "Temp" "(" ident(name) ")" :=
  match goal with
  | [ H : name = _ |- _ ] => rewrite H; try reflexivity; clear H
  | [_ := direction Rightwards : Prop |- ?l = _]
    => remember l as name; pop_state
  | [_ := direction Leftwards : Prop  |- _ = ?r]
    => remember r as name; pop_state
  end.

(* variants *)
Tactic Notation (at level 2)
       "Left" "=" constr(c) := Left = c { obvious }.
Tactic Notation (at level 2)
       "Left" "=" constr(c) "{" "by" uconstr(u) "}"
  := Left = c { rewrite u + rewrite <- u }.
Tactic Notation (at level 2)
       "Left" "=" constr(c) "{" "because" uconstr(u) "by" constr(t) "}"
  := Left = c { let H := fresh "H" in (assert u as H by t ; rewrite H + rewrite <- H ; clear H) }.

Tactic Notation (at level 2)
       "Left" "=" "{" tactic(t) "}" constr(c) := Left = c { t }.
Tactic Notation (at level 2)
       "Left" "=" "{" "by" uconstr(u) "}" constr(c) := (Left = c { by u }).
Tactic Notation (at level 2)
       "Left" "=" "{" "because" uconstr(u) "by" uconstr(t) "}" constr(c)
  := (Left = c { because u by t }).

Tactic Notation (at level 2)
       "Right" "=" constr(c) := Right = c { obvious }.
Tactic Notation (at level 2)
       "Right" "=" constr(c) "{" "by" uconstr(u) "}"
  := Right = c { rewrite u + rewrite <- u }.
Tactic Notation (at level 2)
       "Right" "=" constr(c) "{" "because" constr(t) "by" uconstr(u) "}"
  := Right = c { let H := fresh "H" in (assert t as H ; rewrite H + rewrite <- H ; clear H) }.

Tactic Notation (at level 2)
       "Right" "=" "{" tactic(t) "}" constr(c) := Right = c { t }.
Tactic Notation (at level 2)
       "Right" "=" "{" "by" uconstr(u) "}" constr(c) := (Right = c { by u }).
Tactic Notation (at level 2)
       "Right" "=" "{" "because" uconstr(u) "by" constr(t) "}" constr(c)
  := (Right = c { because u by t }).

Tactic Notation (at level 2)
       "=" constr(c) :=  = c { obvious }.
Tactic Notation (at level 2)
       "=" constr(c) "{" "by" uconstr(u) "}"
  :=  = c { rewrite u + rewrite <- u }.
Tactic Notation (at level 2)
       "=" constr(c) "{" "because" constr(t) "by" uconstr(u) "}"
  :=  = c { let H := fresh "H" in (assert t as H ; rewrite H + rewrite <- H ; clear H) }.

Tactic Notation (at level 2)
       "=" "{" tactic(t) "}" constr(c) := = c { t }.
Tactic Notation (at level 2)
       "=" "{" "by" uconstr(u) "}" constr(c) := = c { by u }.
Tactic Notation (at level 2)
       "=" "{" "because" uconstr(u) "by" uconstr(t) "}" constr(c)
  := = c { because u by t }.

Tactic Notation (at level 2)
       "=" "Left" := = Left { obvious }.
Tactic Notation (at level 2)
       "=" "Right" := = Right { obvious }.
Tactic Notation (at level 2)
       "Left" "=" "{" tactic(t) "}" "Right" := t.
Tactic Notation (at level 2)
       "Left" "{" tactic(t) "}" "=" "Right" := t.
Tactic Notation (at level 2)
       "Right" "=" "{" tactic(t) "}" "Left" := t.
Tactic Notation (at level 2)
       "Right" "{" tactic(t) "}" "=" "Left" := t.
Tactic Notation (at level 2)
       "Left" "=" "Right" := obvious.
Tactic Notation (at level 2)
       "Right" "=" "Left" := obvious.

(* tactics for annotation *)
Tactic Notation (at level 2)
       "@" ident(H1) ":" constr(t) :=
  match goal with
  | [ H : t |- _ ] =>
    match H with
    | H1 => idtac
    | _  => fail 2 "No such identifier"H1"that is typed"t
    end
  | _ => fail 2 "No such identifiers that is typed"t
  end.

Tactic Notation (at level 2)
       "@" "goal" ":" constr(t) :=
  match goal with
  | [ |- t ]   => idtac "OK, current goal is"t
  | [ |- ?t1 ] => fail 2 "Current goal is not"t", but"t1
  end.
