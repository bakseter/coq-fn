From Coq Require Import Nat.
From Coq Require Import Arith. Import Nat.
From Coq Require Import Datatypes.
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
From Hask Require Import Data.Maybe.
From Hask Require Import Data.Either.
From Hask Require Import Data.Functor.
From Hask Require Import Control.Applicative.

Module Syntax.

  Fixpoint digs (n : nat) (max : nat) {struct max} : list nat :=
    match max with
    | 0 =>
        nil
    | S max' =>
        match n with
        | 0 =>
            nil
        | n' =>
            (modulo n' 10) :: digs (div n' 10) max'
        end
    end.

  Fixpoint digs_to_string (ds : list nat) : string :=
    match ds with
    | nil =>
        ""
    | d :: ds' =>
        (digs_to_string ds') ++
        (String (ascii_of_nat (d + 48)) EmptyString)
    end.

  Definition nat_to_str (n : nat) : string :=
    match n with
    | 0 =>
        "0"
    | _ =>
        digs_to_string (digs n 100)
    end.

  Definition bool_to_str (b : bool) : string :=
    match b with
    | true =>
        "true"
    | false =>
        "false"
    end.

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
    | B_Const : bool -> BExpr
    | B_Not : BExpr -> BExpr
    | B_And : BExpr -> BExpr -> BExpr
    | B_Le : AExpr -> AExpr -> BExpr
    | B_Func : FExpr -> BExpr

  with AExpr : Type :=
    | A_Const : nat -> AExpr
    | A_Add : AExpr -> AExpr -> AExpr
    | A_Sub : AExpr -> AExpr -> AExpr
    | A_Mult : AExpr -> AExpr -> AExpr
    | A_Func : FExpr -> AExpr.

End Syntax.

Module Semantics.
  Import Syntax.

  Open Scope string_scope.

  Inductive Env : Type :=
  | EmptyEnv : Env
  | ExtendEnv : string -> Value -> Env -> Env
    with Value : Type :=
    | V_Nat : nat -> Value
    | V_Bool : bool -> Value
    | V_Closure : FExpr -> Env -> Value
    | V_ReturnValue : Value -> Value.

  Fixpoint lookupEnv (varName : string) (env : Env) {struct env} : Maybe Value :=
    match env with
    | EmptyEnv => Nothing
    | ExtendEnv name value restEnv =>
        if String.eqb varName name
        then Just value
        else lookupEnv varName restEnv
    end.

  Fixpoint env_to_string (env : Env) : string :=
    match env with
    | EmptyEnv => ""
    | ExtendEnv name value restEnv =>
        name ++ " = " ++ (value_to_string value) ++ ", " ++ (env_to_string restEnv)
    end

    with value_to_string (val : Value) : string :=
      match val with
      | V_Nat n => nat_to_str n
      | V_Bool b => bool_to_str b
      | V_Closure (F_Lambda paramName bodyExpr) closureEnv =>
          "λ" ++ paramName ++ " -> " ++ ("[fexpr]") ++ ", " ++ (env_to_string closureEnv)
      | V_ReturnValue v => "return " ++ (value_to_string v)
      |   _ => "not impl"
      end.

  Fixpoint Feval (expr : FExpr) (env : Env) (max : nat) : Either (list (string * Maybe FExpr)) Value :=
    match max with
    | 0 =>
        Left (("Error: Maximum recursion depth exceeded", Nothing) :: nil)
    | S max' =>
      match expr with
      | F_Var varName =>
          match lookupEnv varName env with
          | Just value =>
              Right value
          | Nothing =>
              Left
                (("(Feval) Error: Unbound variable"
                 , Just (F_Var varName)) :: nil)
          end
      | F_Lambda paramName bodyExpr =>
          Right (V_Closure (F_Lambda paramName bodyExpr) env)
      | F_Apply funcExpr argExpr =>
          match Feval funcExpr env max' with
          | Right (V_Closure (F_Lambda paramName bodyExpr) _) =>
              let argValueEither := Feval (F_Return argExpr) env max' in
              match argValueEither with
              | Right argValue =>
                let extendedEnv := ExtendEnv paramName argValue env in
                Feval bodyExpr extendedEnv max'
              | Left err =>
                  Left
                    (("(Feval) Error: Function argument did not evaluate to a value"
                     , Just (F_Apply funcExpr argExpr)) :: err)
              end
          | _ =>
              Left
                (("(Feval) Error: Attempted to apply a non-function"
                 , Just (F_Apply funcExpr argExpr)) :: nil)
          end
      | F_Cond condExpr trueExpr falseExpr =>
          match Beval condExpr env max' with
          | Right b =>
              if b
              then Feval trueExpr env max'
              else Feval falseExpr env max'
          | Left err =>
              let newErr :=
                ("(Feval) Error: Condition did not evaluate to a boolean"
                 , Just (F_Cond condExpr trueExpr falseExpr))
              in Left (newErr :: ((err , Nothing) :: nil))
          end
      | F_Let varName bindExpr bodyExpr =>
          let bindValueEither := Feval bindExpr env max' in
          match bindValueEither with
          | Right bindValue =>
            let extendedEnv := ExtendEnv varName bindValue env in
            Feval bodyExpr extendedEnv max'
          | Left err =>
              Left
                (("(Feval) Error: Let binding did not evaluate to a value"
                 , Just (F_Let varName bindExpr bodyExpr)) :: err)
          end
      | F_Return retExpr =>
          match retExpr with
          | E_Bool b =>
              match V_Bool <$> (Beval b env max') with
              | Right v =>
                  Right v
              | Left err =>
                  Left
                    (("(Feval) Error: Boolean expression did not evaluate to a boolean"
                     , Just (F_Return retExpr)) :: (err, Nothing) :: nil)
              end
          | E_Arith a =>
              match V_Nat <$> (Aeval a env max') with
              | Right v =>
                  Right v
              | Left err =>
                  Left
                    (("(Feval) Error: Arithmetic expression did not evaluate to a number with env: "
                        ++ env_to_string env
                     , Just (F_Return retExpr)) :: (err, Nothing) :: nil)
              end
          end
      end
    end

  with Aeval (a : AExpr) (env : Env) (max : nat) : Either string nat :=
    match max with
    | 0 =>
        Left "(Aeval) Error: Maximum recursion depth exceeded"
    | S max' =>
      match a with
      | A_Const n =>
          Right n
      | A_Add a1 a2 =>
          add <$> (Aeval a1 env max') <*> (Aeval a2 env max')
      | A_Sub a1 a2 =>
          minus <$> (Aeval a1 env max') <*> (Aeval a2 env max')
      | A_Mult a1 a2 =>
          mult <$> (Aeval a1 env max') <*> (Aeval a2 env max')
      | A_Func f =>
          match Feval f env max' with
          | Right (V_Nat n) =>
              Right n
          | _ =>
              Left
                ("(Aeval) Error: Function did not evaluate to a number with env: "
                 ++ env_to_string env)
          end
      end
    end

  with Beval (b : BExpr) (env : Env) (max : nat) : Either string bool :=
    match max with
    | 0 =>
        Left "(Beval) Error: Maximum recursion depth exceeded"
    | S max' =>
      match b with
      | B_Const b =>
          Right b
      | B_Not b' =>
          negb <$> Beval b' env max'
      | B_And b1 b2 =>
          andb <$> (Beval b1 env max') <*> (Beval b2 env max')
      | B_Le b1 b2 =>
          Nat.leb <$> (Aeval b1 env max') <*> (Aeval b2 env max')
      | B_Func f =>
          match Feval f env max' with
          | Right (V_Bool b) =>
              Right b
          | _ =>
              Left
               ("(Beval) Error: Function did not evaluate to a boolean with env: "
                 ++ env_to_string env)
          end
      end
    end.

End Semantics.

Module Examples.

  Import Syntax.
  Import Semantics.

  Example factorial :=
    F_Let "factorial"
      (F_Lambda "n"
        (F_Cond
          (B_Le (A_Func (F_Var "n")) (A_Const 1))
          (F_Return (E_Arith (A_Const 1)))
          (F_Return (E_Arith (A_Mult
                      (A_Func (F_Var "n"))
                      (A_Func (F_Apply (F_Var "factorial") (E_Arith (A_Sub (A_Func (F_Var "n")) (A_Const 1))))))))))
      (F_Apply (F_Var "factorial") (E_Arith (A_Const 5))).

  Example factorial_eval (n : nat) := Feval factorial EmptyEnv n.

End Examples.

Import Syntax.
Import Semantics.
Import Examples.

Extraction Language Haskell.

Extract Inductive nat => "Prelude.Integer" ["0" "Prelude.succ"]
  "(\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))".

Extraction
  "Main.hs"
  factorial_eval.
