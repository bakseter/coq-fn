From Coq Require Import Nat.
From Coq Require Import Arith. Import Nat.
From Coq Require Import Program.Basics.
From Coq Require Import Lia.
From Coq Require Import Bool.
From Coq Require Import Strings.String.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Extraction.
From Coq Require Import ExtrHaskellBasic.
From Coq Require Import ExtrHaskellNatNum.
From Coq Require Import ExtrHaskellString.

Module Syntax.

  Inductive AExpr : Type :=
    | A_Const : nat -> AExpr
    | A_Id : string -> AExpr
    | A_Add : AExpr -> AExpr -> AExpr.

  Inductive LExpr {A : Type} : Type :=
    | L_Id : string -> LExpr
    | L_Nil : LExpr
    | L_Cons : A -> LExpr -> LExpr.

  Inductive BExpr : Type :=
    | B_True : BExpr
    | B_False : BExpr
    | B_Eq : AExpr -> AExpr -> BExpr
    | B_Lt : AExpr -> AExpr -> BExpr
    | B_Not : BExpr -> BExpr
    | B_And : BExpr -> BExpr -> BExpr.

  Inductive CExpr : Type :=
    | C_Skip : CExpr
    | C_Assign : string -> AExpr -> CExpr
    | C_Seq : CExpr -> CExpr -> CExpr
    | C_If : BExpr -> CExpr -> CExpr -> CExpr
    | C_While : BExpr -> CExpr -> CExpr.

  Coercion A_Id : string >-> AExpr.
  Coercion A_Const : nat >-> AExpr.

  Declare Custom Entry CExpr.
  Declare Scope com_scope.

  Notation "<{ e }>" := e (at level 0, e custom CExpr at level 99) : com_scope.
  Notation "( x )" := x (in custom CExpr, x at level 99) : com_scope.
  Notation "x" := x (in custom CExpr at level 0, x constr at level 0) : com_scope.
  Notation "f x .. y" := (.. (f x) .. y)
                    (in custom CExpr at level 0, only parsing,
                    f constr at level 0, x constr at level 9,
                    y constr at level 9) : com_scope.
  Notation "x + y" := (A_Add x y) (in custom CExpr at level 50, left associativity) : com_scope.
  Notation "'true'" := true (at level 1) : com_scope.
  Notation "'true'" := B_True (in custom CExpr at level 0) : com_scope.
  Notation "'false'" := false (at level 1) : com_scope.
  Notation "'false'" := B_False (in custom CExpr at level 0) : com_scope.
  Notation "x < y" := (B_Lt x y) (in custom CExpr at level 70, no associativity) : com_scope.
  Notation "x = y" := (B_Eq x y) (in custom CExpr at level 70, no associativity) : com_scope.
  Notation "x && y" := (B_And x y) (in custom CExpr at level 80, left associativity) : com_scope.
  Notation "'~' b" := (B_Not b) (in custom CExpr at level 75, right associativity) : com_scope.
  Notation "'skip'" :=
      C_Skip (in custom CExpr at level 0) : com_scope.
  Notation "x := y" :=
    (C_Assign x y)
      (in custom CExpr at level 0, x constr at level 0, y at level 85, no associativity) : com_scope.
  Notation "x ; y" :=
    (C_Seq x y)
      (in custom CExpr at level 90, right associativity) : com_scope.
  Notation "'if' x 'then' y 'else' z 'end'" :=
    (C_If x y z)
       (in custom CExpr at level 89, x at level 99,
        y at level 99, z at level 99) : com_scope.
  Notation "'while' x 'do' y 'end'" :=
     (C_While x y)
        (in custom CExpr at level 89, x at level 99, y at level 99) : com_scope.

  Open Scope com_scope.

End Syntax.

Module Semantics.
  Import Syntax.

  Notation "f <$> m" := (option_map f m) (at level 50, left associativity).

  Fixpoint ap {A B : Type} (f : @Maybe (A -> B)) (m : @Maybe A) : @Maybe B :=
    match f with
    | Nothing => Nothing
    | Just f' => f' <$> m
    end.

  Notation "f <*> m" := (ap f m) (at level 50, left associativity).

  Definition State := string -> @Maybe (nat + list nat).
  Definition empty_state : State := fun _ => Nothing.
  Definition update_state (s : State) (x : string) (n : nat + list nat) : State :=
    fun y => if String.eqb x y then Just n else s y.

  Fixpoint Aeval (e : AExpr) (s : State) : @Maybe (nat + list nat) :=
    match e with
    | A_Const n => Just (inl n)
    | A_Id n => s n
    | A_Add e1 e2 => (compose inl plus) <$> (Aeval e1 s) <*> (Aeval e2 s)
    end.

  Fixpoint Leval (e : LExpr) (s : State) : @Maybe (list nat) :=
    match e with
    | L_Id n => s n
    | L_Nil => Just nil
    | L_Cons e1 e2 => cons <$> (Aeval e1 s) <*> (Leval e2 s)
    end.

  Fixpoint Beval (e : BExpr) (s : State) : @Maybe bool :=
    match e with
    | B_True => Just true
    | B_False => Just false
    | B_Eq e1 e2 => Nat.eqb <$> (Aeval e1 s) <*> (Aeval e2 s)
    | B_Lt e1 e2 => Nat.ltb <$> (Aeval e1 s) <*> (Aeval e2 s)
    | B_Not e => negb <$> Beval e s
    | B_And e1 e2 => andb <$> (Beval e1 s) <*> (Beval e2 s)
    end.

  Inductive Ceval : CExpr -> State -> State -> Prop :=
    | CE_Skip : forall s,
        Ceval C_Skip s s
    | CE_Assign : forall s x e n,
        Aeval e s = Just n ->
        Ceval (C_Assign x e) s (update_state s x n)
    | CE_Seq : forall c1 c2 s1 s2 s3,
        Ceval c1 s1 s2 ->
        Ceval c2 s2 s3 ->
        Ceval (C_Seq c1 c2) s1 s3
    | CE_IfTrue : forall b c1 c2 s1 s2,
        Beval b s1 = Just true ->
        Ceval c1 s1 s2 ->
        Ceval (C_If b c1 c2) s1 s2
    | CE_IfFalse : forall b c1 c2 s1 s2,
        Beval b s1 = Just false ->
        Ceval c2 s1 s2 ->
        Ceval (C_If b c1 c2) s1 s2
    | CE_WhileFalse : forall b c s,
        Beval b s = Just false ->
        Ceval (C_While b c) s s
    | CE_WhileTrue : forall b c s1 s2 s3,
        Beval b s1 = Just true ->
        Ceval c s1 s2 ->
        Ceval (C_While b c) s2 s3 ->
        Ceval (C_While b c) s1 s3.

  Fixpoint Ceval_step (e : CExpr) (s : State) (max : nat) : State :=
    match max with
    | O => s
    | S max' =>
      match e with
      | C_Skip => s
      | C_Assign c a =>
          match Aeval a s with
          | Just n => update_state s c n
          | Nothing => s
          end
      | C_Seq c1 c2 => Ceval_step c2 (Ceval_step c1 s (max' - 1)) (max' - 1)
      | C_If b c1 c2 =>
          match Beval b s with
          | Just b' => if b' then Ceval_step c1 s (max' - 1) else Ceval_step c2 s (max' - 1)
          | Nohting => s
          end
      | C_While b c =>
          match Beval b s with
          | Just b' => if b' then Ceval_step (C_Seq c (C_While b c)) s (max' - 1) else s
          | Nothing => s
          end
      end
    end.

  Open Scope string_scope.
  Open Scope com_scope.
  Open Scope nat_scope.

  Example ex1 : CExpr :=
    <{
      while "x" < 5 do
        "x" := "x" + 1
      end
    }>.

End Semantics.

Import Syntax.
Import Semantics.

Extraction Language Haskell.

Extract Inductive Maybe => "Prelude.Maybe" ["Prelude.Nothing" "Prelude.Just"].
Extract Inductive nat => "Prelude.Integer" ["0" "Prelude.succ"]
  "(\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))".
Extract Inlined Constant fmap => "(Prelude.<$>)".
Extract Inlined Constant ap => "(Prelude.<*>)".

Extraction "asd.hs" test_prog_eval.
