From Coq Require Import Nat.
From Coq Require Import Arith. Import Nat.
From Coq Require Import Lists.List.
From Coq Require Import Program.Basics.
From Coq Require Import Lia.
From Coq Require Import Bool.
From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Extraction.
From Coq Require Import ExtrHaskellBasic.
From Coq Require Import ExtrHaskellNatNum.
From Coq Require Import ExtrHaskellString.


Module Syntax.

  Inductive FExpr : Type :=
  | F_Var : string -> FExpr
  | F_Lambda : string -> FExpr -> FExpr
  | F_Apply : FExpr -> Expr -> FExpr
  | F_Cond : BExpr -> FExpr -> FExpr -> FExpr
  | F_Let : string -> FExpr -> FExpr -> FExpr
  | F_Return : Expr -> FExpr

  with Expr : Type :=
    | E_Bool : BExpr -> Expr
    | E_Arith : AExpr -> Expr

  with BExpr : Type :=
    | B_True : BExpr
    | B_False : BExpr
    | B_Not : BExpr -> BExpr
    | B_And : BExpr -> BExpr -> BExpr
    | B_Le : AExpr -> AExpr -> BExpr

  with AExpr : Type :=
    | A_Const : nat -> AExpr
    | A_Var : string -> AExpr
    | A_Add : AExpr -> AExpr -> AExpr
    | A_Sub : AExpr -> AExpr -> AExpr
    | A_Mult : AExpr -> AExpr -> AExpr
    | A_Func : FExpr -> AExpr.

End Syntax.

Module Semantics.
  Import Syntax.

  Notation "f <$> m" := (option_map f m) (at level 50, left associativity).

  Fixpoint ap {A B : Type} (f : option (A -> B)) (m : option A) : option B :=
    match f with
    | Some f' => f' <$> m
    | None => None
    end.

  Notation "f <*> m" := (ap f m) (at level 50, left associativity).

  Inductive Env : Type :=
  | EmptyEnv : Env
  | ExtendEnv : string -> Value -> Env -> Env
    with Value : Type :=
    | V_Nat : nat -> Value
    | V_Bool : bool -> Value
    | V_Closure : FExpr -> Env -> Value
    | V_ReturnValue : Value -> Value.


  Example gpt : FExpr :=
    F_Let "factorial" (F_Lambda "n"
                    (F_Cond ((B_Le (A_Var "n") (A_Const 1)))
                      (F_Return (E_Arith (A_Const 1)))
                      (F_Return (E_Arith (A_Mult (A_Var "n") (A_Func (F_Apply (F_Var "factorial") (E_Arith (A_Sub (A_Var "n") (A_Const 1))))))))))
      (F_Return (E_Arith (A_Func (F_Apply (F_Var "factorial") (E_Arith (A_Const 5)))))).


  Fixpoint option_apply {A B : Type} (f : A -> option B) (x : option A) : option B :=
    match x with
    | Some x' => f x'
    | None => None
    end.

  Inductive Either {A B : Type} : Type :=
    | Right : B -> Either
    | Left : A -> Either.

  Definition either_map {A B C : Type} (f : A -> C) (either : Either) :=
    match either with
    | Right a => f a
    | Left b => b
    end.

  Open Scope string_scope.

  Fixpoint lookupEnv (env : Env) (varName : string) {struct env} : option Value :=
    match env with
    | EmptyEnv => None
    | ExtendEnv name value restEnv =>
        if String.eqb varName name
        then Some value
        else lookupEnv restEnv varName
    end.

  Fixpoint Feval (env : Env) (expr : FExpr) (max : nat) : @Either (list (string * option FExpr)) Value :=
    match max with
    | 0 =>
        Left (("Error: Maximum recursion depth exceeded", None) :: nil)
    | S max' =>
      match expr with
      | F_Var varName =>
          match lookupEnv env varName with
          | Some value => Right value
          | None =>
              Left (("Error: Unbound variable", Some (F_Var varName)) :: nil)
          end
      | F_Lambda paramName bodyExpr =>
          Right (V_Closure (F_Lambda paramName bodyExpr) env)
      | F_Apply funcExpr argExpr =>
          match Feval env funcExpr max' with
          | Right (V_Closure (F_Lambda paramName bodyExpr) closureEnv) =>
              let argValueEither := Feval env (F_Return argExpr) max' in
              match argValueEither with
              | Right argValue =>
                let extendedEnv := ExtendEnv paramName argValue closureEnv in
                Feval extendedEnv bodyExpr max'
              | Left err =>
                  Left 
                    (("Error: Function argument did not evaluate to a value"
                     , Some (F_Apply funcExpr argExpr)) :: nil)
              end
          | _ =>
              Left
                (("Error: Attempted to apply a non-function"
                 , Some (F_Apply funcExpr argExpr)) :: nil)
          end
      | F_Cond condExpr trueExpr falseExpr =>
          match Beval condExpr env max' with
          | Some true =>
              Feval env trueExpr max'
          | Some false =>
              Feval env falseExpr max'
          | _ =>
              Left
                (("Error: Condition did not evaluate to a boolean"
                 , Some (F_Cond condExpr trueExpr falseExpr)) :: nil)
          end
      | F_Let varName bindExpr bodyExpr =>
          let bindValueEither := Feval env bindExpr max' in
          match bindValueEither with
          | Right bindValue =>
            let extendedEnv := ExtendEnv varName bindValue env in
            Feval extendedEnv bodyExpr max'
          | Left err =>
              Left
                (("Error: Let binding did not evaluate to a value"
                 , Some (F_Let varName bindExpr bodyExpr)) :: nil)
          end
      | F_Return retExpr =>
          match retExpr with
          | E_Bool b => 
              match V_Bool <$> (Beval b env max') with
              | Some v =>
                  Right v
              | None =>
                  Left
                    (("Error: Boolean expression did not evaluate to a boolean"
                     , Some (F_Return retExpr)) :: nil)
              end
          | E_Arith a =>
              match V_Nat <$> (Aeval a env max') with
              | Some v =>
                  Right v
              | None =>
                  Left
                    (("Error: Arithmetic expression did not evaluate to a number"
                     , Some (F_Return retExpr)) :: nil)
              end
          end
      end
    end

  with Aeval (a : AExpr) (env : Env) (max : nat) : option nat :=
    match max with
    | 0 =>
        None
    | S max' =>
      match a with
      | A_Var n => 
          match lookupEnv env n with
          | Some (V_Nat n') =>
              Some n'
          | _ =>
              None
          end
      | A_Const n =>
          Some n
      | A_Add a1 a2 =>
          plus <$> (Aeval a1 env max') <*> (Aeval a2 env max')
      | A_Sub a1 a2 =>
          minus <$> (Aeval a1 env max') <*> (Aeval a2 env max')
      | A_Mult a1 a2 =>
          mult <$> (Aeval a1 env max') <*> (Aeval a2 env max')
      | A_Func f => 
          match Feval env f max' with
          | Right (V_Nat n) =>
              Some n
          | _ =>
              None
          end
      end
    end

  with Beval (b : BExpr) (e : Env) (max : nat) : option bool :=
    match max with
    | 0 =>
        None
    | S max' =>
      match b with
      | B_True =>
          Some true
      | B_False =>
          Some false
      | B_Not b' =>
          negb <$> Beval b' e max'
      | B_And b1 b2 =>
          andb <$> (Beval b1 e max') <*> (Beval b2 e max')
      | B_Le b1 b2 =>
          Nat.leb <$> (Aeval b1 e max') <*> (Aeval b2 e max')
      end
    end.


  Example bruh := F_Let "factorial" (F_Lambda "n"
  (F_Cond
    (B_Le (A_Var "n") (A_Const 1))
    (F_Return (E_Arith (A_Const 1)))
    (F_Return (E_Arith (A_Mult
                (A_Var "n")
                (A_Func (F_Apply (F_Var "factorial") (E_Arith (A_Sub (A_Var "n") (A_Const 1))))))))))
  (F_Apply (F_Var "factorial") (E_Arith (A_Const 5))).

  Example bruh2 :=
    F_Return (E_Arith (A_Func (F_Return (E_Arith (A_Mult (A_Const 2) (A_Const 3)))))).

  Compute Feval EmptyEnv bruh 100.
  Compute Feval EmptyEnv bruh2 100.

  Definition initialEnv : Env :=
  ExtendEnv "n" (V_Nat 10)
    (ExtendEnv "y" (V_Nat 5)
      EmptyEnv).
 
  Definition initialEnv' : Env :=
  ExtendEnv "factorial" (V_Closure
                          (F_Lambda "n"
                            (F_Cond
                              (B_Le (A_Var "n") (A_Const 1))
                              (F_Return (E_Arith (A_Const 1)))
                              (F_Return
                                (E_Arith 
                                (A_Mult
                                  (A_Var "n")
                                  (A_Func 
                                    (F_Apply
                                      (F_Var "factorial")
                                        (E_Arith
                                          (A_Sub
                                            (A_Var "n")
                                            (A_Const 1)
                                          )
                                        )
                                      )
                                    )
                                  ) 
                                )
                              )
                            )
                          )
                        initialEnv)
                        EmptyEnv.

  Eval simpl in 
    evalExpr
    EmptyEnv
    (F_Cond
      (B_False)
      (F_Return (E_Arith (A_Const 1)))
      (F_Return (E_Arith (A_Const 2))))
    1000.

  Eval simpl in evalExpr initialEnv' bruh 1000.
  Eval simpl in Feval bruh initialEnv' 1000.


  Eval simpl in evalExpr initialEnv bruh 1000.

  Inductive Ceval : CExpr -> State -> State -> Prop :=
    | CE_Skip : forall s,
        Ceval C_Skip s s
    | CE_AssignA : forall s x e n,
        Aeval e s = Some n ->
        Ceval (C_AssignA x e) s (update_state_A s x (Some n))
    | CE_AssignL : forall s x e n,
        Leval e s = Some n ->
        Ceval (C_AssignL x e) s (update_state_L s x (Some n))
    | CE_Seq : forall c1 c2 s1 s2 s3,
        Ceval c1 s1 s2 ->
        Ceval c2 s2 s3 ->
        Ceval (C_Seq c1 c2) s1 s3
    | CE_IfTrue : forall b c1 c2 s1 s2,
        Beval b s1 = Some true ->
        Ceval c1 s1 s2 ->
        Ceval (C_If b c1 c2) s1 s2
    | CE_IfFalse : forall b c1 c2 s1 s2,
        Beval b s1 = Some false ->
        Ceval c2 s1 s2 ->
        Ceval (C_If b c1 c2) s1 s2
    | CE_WhileFalse : forall b c s,
        Beval b s = Some false ->
        Ceval (C_While b c) s s
    | CE_WhileTrue : forall b c s1 s2 s3,
        Beval b s1 = Some true ->
        Ceval c s1 s2 ->
        Ceval (C_While b c) s2 s3 ->
        Ceval (C_While b c) s1 s3.


  Fixpoint list_update_at_index (l : list nat) (n : nat) (v : nat) : list nat :=
    match l with
    | nil => nil
    | cons x xs => match n with
                   | O => cons v xs
                   | S n' => cons x (list_update_at_index xs n' v)
                   end
    end.

  Fixpoint Ceval_step (e : CExpr) (s : State) (max : nat) : State :=
    match max with
    | O => s
    | S max' =>
      match e with
      | C_Skip => s
      | C_AssignA x e =>
          match Aeval e s with
          | Some n => update_state_A s x (Some n)
          | None => s
          end
      | C_AssignL x e =>
          match Leval e s with
          | Some n => update_state_L s x (Some n)
          | None => s
          end
      | C_Seq c1 c2 => Ceval_step c2 (Ceval_step c1 s max') max'
      | C_If b c1 c2 =>
          match Beval b s with
          | Some b' => if b' then Ceval_step c1 s max' else Ceval_step c2 s max'
          | Nohting => s
          end
      | C_While b c =>
          match Beval b s with
          | Some b' => if b' then Ceval_step (C_Seq c (C_While b c)) s max' else s
          | None => s
          end
      | C_Foreach x l c =>
          match Leval l s with
          | Some l' => 
              fold_left (fun s' a => Ceval_step (C_Seq (C_AssignA x (A_Const a)) c) s' max') l' s
          | None => s
          end
      | C_Print a => 
          match Aeval a s with
          | Some n => update_state_P s n
          | None => s
          end
      | C_ListUpdate n i v =>
          match Aeval i s, Aeval v s with
          | Some i', Some v' => 
              match L_State s n with
              | Some l => update_state_L s n (Some (list_update_at_index l i' v'))
              | None => s
              end
          | _, _ => s
          end
      end
    end.

  Open Scope string_scope.
  Open Scope com_scope.

  Definition swap :=
    Ceval_step <{
      "xs" @:= [1, 2, 3, 4, 5];
      "ys" @:= [6, 7, 8, 9, 10];
      "i" := 0;
      "j" := 0;
      foreach "x" in "xs" do
        foreach "y" in "ys" do
          if "x" < "y" then
            "tmp" := "x";
            (update "xs"["i"] to "y");
            (update "ys"[A_Id "j"] to "tmp")
          else
            skip
          end;
          "j" := "j" + 1
        done;
        "i" := "i" + 1
      done
    }> empty_state 10000.

  Compute A_State swap "i".
  Compute A_State swap "j".
  Compute L_State swap "xs".
  Compute L_State swap "ys".

End Semantics.

Import Syntax.
Import Semantics.

Extraction Language Haskell.

Extract Inductive option => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].
Extract Inductive nat => "Prelude.Integer" ["0" "Prelude.succ"]
  "(\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))".
Extract Inlined Constant option_map => "(Prelude.<$>)".
Extract Inlined Constant ap => "(Prelude.<*>)".

Extraction "Haskell.hs" Ceval_step swap.
