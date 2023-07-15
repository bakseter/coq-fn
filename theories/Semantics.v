From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
From Coq Require Import Init.Nat.

Require Import Syntax. Import Syntax.

Module Semantics.

  Open Scope string_scope.

  Inductive Env : Type :=
  | EmptyEnv : Env
  | ExtendEnv : string -> Value -> Env -> Env
    with Value : Type :=
    | V_Nat : nat -> Value
    | V_Bool : bool -> Value
    | V_Closure : FExpr -> Env -> Value
    | V_ReturnValue : Value -> Value.

  Fixpoint lookup_env (varName : string) (env : Env) {struct env} : sum string Value :=
    match env with
    | EmptyEnv => inl "(lookup_env) Error: Unbound variable"
    | ExtendEnv name value restEnv =>
        if String.eqb varName name
        then inr value
        else lookup_env varName restEnv
    end.

  Definition sum_map {A B C : Type} (f : B -> C) (s : sum A B) : sum A C :=
    match s with
    | inl a => inl a
    | inr b => inr (f b)
    end.

  Notation "f <$> s" := (sum_map f s) (at level 50, left associativity).

  Definition sum_ap {A B C : Type} (f : sum A (B -> C)) (s : sum A B) : sum A C :=
    match f with
    | inl a => inl a
    | inr f' => f' <$> s
    end.

  Notation "f <*> s" := (sum_ap f s) (at level 50, left associativity).

  Fixpoint Feval (expr : FExpr) (env : Env) (max : nat) : sum (list string) Value :=
    match max with
    | 0 =>
        inl ("Error: Maximum recursion depth exceeded" :: nil)
    | S max' =>
      match expr with
      | F_Var varName =>
          match lookup_env varName env with
          | inr value =>
              inr value
          | inl err =>
              inl
                ("(Feval) Error: Unbound variable" :: err :: nil)
          end
      | F_Lambda paramName bodyExpr =>
          inr (V_Closure (F_Lambda paramName bodyExpr) env)
      | F_Apply funcExpr argExpr =>
          match Feval funcExpr env max' with
          | inr (V_Closure (F_Lambda paramName bodyExpr) _) =>
              let argValueSum := Feval (F_Return argExpr) env max' in
              match argValueSum with
              | inr argValue =>
                let extendedEnv := ExtendEnv paramName argValue env in
                Feval bodyExpr extendedEnv max'
              | inl err =>
                  inl
                    ("(Feval) Error: Function argument did not evaluate to a value"
                      :: err)
              end
          | _ =>
              inl
                ("(Feval) Error: Attempted to apply a non-function" :: nil)
          end
      | F_Cond condExpr trueExpr falseExpr =>
          match Beval condExpr env max' with
          | inr b =>
              if b
              then Feval trueExpr env max'
              else Feval falseExpr env max'
          | inl err =>
              inl ("(Feval) Error: Condition did not evaluate to a boolean" :: err :: nil)
          end
      | F_Let varName bindExpr bodyExpr =>
          let bindValueSum := Feval bindExpr env max' in
          match bindValueSum with
          | inr bindValue =>
            let extendedEnv := ExtendEnv varName bindValue env in
            Feval bodyExpr extendedEnv max'
          | inl err =>
              inl
                ("(Feval) Error: Let binding did not evaluate to a value" :: err)
          end
      | F_Return retExpr =>
          match retExpr with
          | E_Bool b =>
              match V_Bool <$> (Beval b env max') with
              | inr v =>
                  inr v
              | inl err =>
                  inl
                    ("(Feval) Error: Boolean expression did not evaluate to a boolean" :: err :: nil)
              end
          | E_Arith a =>
              match V_Nat <$> (Aeval a env max') with
              | inr v =>
                  inr v
              | inl err =>
                  inl
                    (("(Feval) Error: Arithmetic expression did not evaluate to a number" :: err :: nil))
              end
          end
      end
    end

  with Aeval (a : AExpr) (env : Env) (max : nat) : sum string nat :=
    match max with
    | 0 =>
        inl "(Aeval) Error: Maximum recursion depth exceeded"
    | S max' =>
      match a with
      | A_Const n =>
          inr n
      | A_Add a1 a2 =>
          add <$> (Aeval a1 env max') <*> (Aeval a2 env max')
      | A_Sub a1 a2 =>
          minus <$> (Aeval a1 env max') <*> (Aeval a2 env max')
      | A_Mult a1 a2 =>
          mult <$> (Aeval a1 env max') <*> (Aeval a2 env max')
      | A_Func f =>
          match Feval f env max' with
          | inr (V_Nat n) =>
              inr n
          | _ =>
              inl
                "(Aeval) Error: Function did not evaluate to a number"
          end
      end
    end

  with Beval (b : BExpr) (env : Env) (max : nat) : sum string bool :=
    match max with
    | 0 =>
        inl "(Beval) Error: Maximum recursion depth exceeded"
    | S max' =>
      match b with
      | B_Const b =>
          inr b
      | B_Not b' =>
          negb <$> Beval b' env max'
      | B_And b1 b2 =>
          andb <$> (Beval b1 env max') <*> (Beval b2 env max')
      | B_Eq e1 e2 =>
          match e1, e2 with
          | E_Bool b1, E_Bool b2 =>
              Bool.eqb <$> (Beval b1 env max') <*> (Beval b2 env max')
          | E_Arith a1, E_Arith a2 =>
              Nat.eqb <$> (Aeval a1 env max') <*> (Aeval a2 env max')
          | _, _ =>
              inl
                ("(Beval) Error: Attempted to compare a boolean to a number")
          end
      | B_Le b1 b2 =>
          Nat.leb <$> (Aeval b1 env max') <*> (Aeval b2 env max')
      | B_Func f =>
          match Feval f env max' with
          | inr (V_Bool b) =>
              inr b
          | _ =>
              inl
               ("(Beval) Error: Function did not evaluate to a boolean")
          end
      end
    end.

End Semantics.
