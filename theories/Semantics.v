From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
From Coq Require Import Init.Nat.
From Coq Require Import Program.Wf.
From Coq Require Import Program.Basics.

Require Import Syntax. Import Syntax.

Module Semantics.

  Open Scope string_scope.

  Definition bool_to_string (b : bool) : string :=
    match b with
    | true => "true"
    | false => "false"
    end.

  Fixpoint concat_string_list (l : list string) : string :=
    match l with
    | nil => ""
    | h :: t => h ++ concat_string_list t
    end.

  Inductive Env : Type :=
  | EmptyEnv : Env
  | ExtendEnv : string -> Value -> Env -> Env
    with Value : Type :=
    | V_Nat : nat -> Value
    | V_Bool : bool -> Value
    | V_Closure : string -> Expr -> Env -> Value.

  Fixpoint lookup_env (varName : string) (env : Env) {struct env} : sum string Value :=
    match env with
    | EmptyEnv =>
        inl ("(lookup_env) Error: Unbound variable '" ++ varName ++ "'")
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

  Definition value_to_string (val : Value) : string :=
    match val with
    | V_Nat n => "V_Nat"
    | V_Bool b => match b with true => "V_Bool true" | false => "V_Bool false" end
    | V_Closure paramName bodyExpr closureEnv =>
        "(λ" ++ paramName ++ ")"
    end.

  Definition dep_types_check (n : nat) : forall returnNat : bool, if returnNat then nat else bool.
  Proof.
    intros.
    destruct returnNat; try assumption.
    apply (fun n : nat => if Nat.eqb n 1 then true else false).
    assumption.
  Qed.

  Fixpoint eval (expr : Expr) (env : Env) (max : nat) : sum ((Expr * Env) * list string) Value :=
    match max with
    | 0 =>
        inl ((expr, env), ("(eval) Error: Maximum recursion depth exceeded" :: nil))
    | S max' =>
      match expr with
      | Var varName =>
          match lookup_env varName env with
          | inr value =>
              inr value
          | inl err =>
              inl
                ((expr, env), (("(eval) Error: Unbound variable '" ++ varName ++ "'") :: err :: nil))
          end
      | Lambda paramName bodyExpr =>
          inr (V_Closure paramName (Lambda paramName bodyExpr) env)
      | Apply expr1 expr2 =>
          match eval expr1 env max', eval expr2 env max' with
          | inr (V_Closure _ (Lambda paramName bodyExpr) closureEnv), inr argValue =>
              eval bodyExpr (ExtendEnv paramName argValue env) max'
          | inr argValue, inr (V_Closure _ (Lambda paramName bodyExpr) closureEnv) =>
              eval bodyExpr (ExtendEnv paramName argValue env) max'
          | inr (V_Closure _ (Lambda paramName bodyExpr) closureEnv), inl err =>
              inl err
          | inl err, _ =>
              inl err
          | _, inl err =>
              inl err
          | _, _ =>
              inl ((expr, env), "Error: Application did not evaluate to a closure" :: nil)
          end
      | Cond condExpr trueExpr falseExpr =>
          match eval condExpr env max' with
          | inr val =>
              match val with
              | V_Bool b =>
                if b
                then eval trueExpr env max'
                else eval falseExpr env max'
              | _ =>
                  inl ((expr, env), ("(eval) Error: Condition did not evaluate to a boolean" :: nil))
              end
          | inl (_, err) =>
              inl ((expr, env), ("(eval) Error: Condition did not evaluate to a boolean" :: err))
          end
      | Let varName bindExpr bodyExpr =>
          match eval bindExpr env max' with
          | inr val =>
              eval bodyExpr (ExtendEnv varName val env) max'
          | inl err =>
              inl err
          end
      | Nat n =>
          inr (V_Nat n)
      | Bool b =>
          inr (V_Bool b)
      | Add e1 e2 =>
          match eval e1 env max', eval e2 env max' with
          | inr (V_Nat n1), inr (V_Nat n2) =>
              inr (V_Nat (n1 + n2))
          | _, _ => inl ((expr, env), "Error: Addition did not evaluate to a number" :: nil)
          end
      | Sub e1 e2 =>
          match eval e1 env max', eval e2 env max' with
          | inr (V_Nat n1), inr (V_Nat n2) =>
              inr (V_Nat (n1 - n2))
          | _, _ => inl ((expr, env), "Error: Subtraction did not evaluate to a number" :: nil)
          end
      | Mul e1 e2 =>
          match eval e1 env max', eval e2 env max' with
          | inr (V_Nat n1), inr (V_Nat n2) =>
              inr (V_Nat (n1 * n2))

          | inr (V_Nat n1), inr (V_Closure paramName bodyExpr closureEnv) =>
              inr (V_Closure paramName (Mul (Nat n1) bodyExpr) closureEnv)

          | inr (V_Closure paramName bodyExpr closureEnv), inr (V_Nat n2) =>
              inr (V_Closure paramName (Mul bodyExpr (Nat n2)) closureEnv)

          | inr (V_Closure paramName1 bodyExpr1 closureEnv1), inr (V_Closure paramName2 bodyExpr2 closureEnv2) =>
              inr (V_Closure paramName1 (Mul bodyExpr1 (Apply bodyExpr2 (Var paramName1))) closureEnv1)

          | inr val, inr val' =>
              inl ((expr, env), ("1Error: Multiplication did not evaluate to a number: " ++ value_to_string val ++ value_to_string val') :: nil)

          | inr val, inl (_, err) =>
              inl ((expr, env), ("2Error: Multiplication did not evaluate to a number: " ++ value_to_string val) :: err)

          | inl (_, err), inr val =>
              inl ((expr, env), ("3Error: Multiplication did not evaluate to a number: " ++ value_to_string val) :: err)

          | _, _ =>
              inl ((expr, env), "E4rror: Multiplication did not evaluate to a number" :: nil)
          end
      | And e1 e2 =>
          match eval e1 env max', eval e2 env max' with
          | inr (V_Bool b1), inr (V_Bool b2) =>
              inr (V_Bool (andb b1 b2))
          | _, _ => inl ((expr, env), "Error: And did not evaluate to a boolean" :: nil)
          end
      | Eq e1 e2 =>
          match eval e1 env max', eval e2 env max' with
          | inr (V_Nat n1), inr (V_Nat n2) =>
              inr (V_Bool (Nat.eqb n1 n2))
          | inr (V_Bool b1), inr (V_Bool b2) =>
              inr (V_Bool (Bool.eqb b1 b2))
          | _, _ => inl ((expr, env), "Error: Cannot compare values of non-equal types" :: nil)
          end
      end
    end.


    Compute eval (Let "factorial" (Lambda "n" (Cond (Eq (Var "n") (Nat 1)) (Nat 1) (Mul (Var "n") (Apply (Var "factorial") (Sub (Var "n") (Nat 1)))))) (Apply (Var "factorial") (Nat 5))) EmptyEnv 100.

    Compute eval
      (Let "mult"
        (Lambda "n"
          (Lambda "m"
            (Mul (Var "m") (Var "n"))
          )
        )
        (Apply
          (Apply
            (Var "mult") (Var "ione")
          )
          (Var "itwo")
        )
      ) (ExtendEnv "ione" (V_Nat 2) (ExtendEnv "itwo" (V_Nat 3) EmptyEnv)) 100.

End Semantics.
