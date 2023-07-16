From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
From Coq Require Import Init.Nat.
From Coq Require Import Program.Wf.

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
  | V_Closure : string -> FExpr_Sub -> Env -> Value
  | V_Fix : string -> FExpr_Sub -> Env -> Value.

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

  Fixpoint value_to_string (val : Value) : string :=
    match val with
    | V_Nat n => "V_Nat"
    | V_Bool b => match b with true => "V_Bool true" | false => "V_Bool false" end
    | V_Closure paramName bodyExpr closureEnv =>
        "(λ" ++ paramName ++ ")"
    | V_Fix fixName (F_Lambda paramName bodyExpr) fixEnv =>
        "(fix " ++ fixName ++ " (λ" ++ paramName ++ "))"
    | V_Fix fixName _ _ =>
        "(fix " ++ fixName ++ " <non-function>)"
    end.

  Fixpoint Feval_Sub (expr : FExpr_Sub) (env : Env) (max : nat) : sum (Env * list string) Value :=
    match max with
    | 0 =>
        inl (env, ("(Feval_Sub) Error: Maximum recursion depth exceeded" :: nil))
    | S max' =>
      match expr with
      | F_Var varName =>
          match lookup_env varName env with
          | inr value =>
              inr value
          | inl err =>
              inl
                (env, (("(Feval_Sub) Error: Unbound variable '" ++ varName ++ "'") :: err :: nil))
          end
      | F_Lambda paramName bodyExpr =>
          inr (V_Closure paramName (F_Lambda paramName bodyExpr) env)
      | F_Fix fixName (F_Lambda paramName bodyExpr) => 
          let fixClosure := V_Fix fixName (F_Lambda paramName bodyExpr) env in
          let env' := ExtendEnv paramName fixClosure env in
          inr fixClosure (* Wrap the result in a closure *)
      | F_Fix fixName _ =>
          inl
            (env, (("(Feval_Sub) Error: Fix expression does not resolve to a function '" ++ fixName ++ "'") :: nil))
      | F_Apply funcExpr argExpr =>
          match Feval_Sub funcExpr env max' with
          | inr (V_Closure _ (F_Lambda paramName bodyExpr) closureEnv) =>
              match Feval_Sub argExpr env max' with
              | inr argValue =>
                Feval_Sub bodyExpr (ExtendEnv paramName argValue closureEnv) max'
              | inl err =>
                  inl 
                    (env, ("Error: Function argument did not evaluate to a value" :: (snd err)))
              end
          | inr (V_Fix fixName (F_Lambda paramName bodyExpr) fixEnv) =>
              let fixClosure := V_Fix paramName (F_Lambda paramName bodyExpr) fixEnv in
              let env' := ExtendEnv fixName fixClosure env in
              Feval_Sub bodyExpr env' max'
          | _ =>
              inl
                (env, ("(Feval_Sub) Error: Function expression did not evaluate to a function" :: nil))
          end
      | F_Cond condExpr trueExpr falseExpr =>
          match Beval condExpr env max' with
          | inr b =>
              if b
              then Feval_Sub trueExpr env max'
              else Feval_Sub falseExpr env max'
          | inl err =>
              inl (env, ("(Feval_Sub) Error: Condition did not evaluate to a boolean" :: err :: nil))
          end
      | F_Return retExpr =>
          match retExpr with
          | E_Bool b =>
              match V_Bool <$> (Beval b env max') with
              | inr v =>
                  inr v
              | inl err =>
                  inl
                    (env, ("(Feval_Sub) Error: Boolean expression did not evaluate to a boolean" :: err :: nil))
              end
          | E_Arith a =>
              match V_Nat <$> (Aeval a env max') with
              | inr v =>
                  inr v
              | inl err =>
                  inl
                    (env, (("(Feval_Sub) Error: Arithmetic expression did not evaluate to a number" :: err :: nil)))
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
      | A_Mul a1 a2 =>
          mult <$> (Aeval a1 env max') <*> (Aeval a2 env max')
      | A_Func f =>
          match Feval_Sub f env max' with
          | inr (V_Nat n) =>
              inr n
          | inr (V_Bool b) =>
              match b with
              | true => inl "(Aeval) Error: Function did not evaluate to a number: 'true'"
              | false => inl "(Aeval) Error: Function did not evaluate to a number: 'false'"
              end
          | inr (V_Closure _ _ _) =>
              inl "(Aeval) Error: Function did not evaluate to a number: V_Closure"
          | inr (V_Fix _ _ _) =>
              inl "(Aeval) Error: Function did not evaluate to a number: V_Fix"
          | inl err =>
              inl
              ((concat_string_list (snd err)) ++
                "(Aeval) Error: Function did not evaluate to a number")
          end
      | A_Var varName =>
          match lookup_env varName env with
          | inr (V_Nat n) =>
              inr n
          | _ =>
              inl
                ("(Aeval) Error: Variable did not evaluate to a number: '" ++ varName ++ "'")
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
      | B_And b1 b2 =>
          andb <$> (Beval b1 env max') <*> (Beval b2 env max')
      | B_Func f =>
          match Feval_Sub f env max' with
          | inr (V_Bool b) =>
              inr b
          | _ =>
              inl
               ("(Beval) Error: Function did not evaluate to a boolean")
          end
      | B_Var varName =>
          match lookup_env varName env with
          | inr (V_Bool b) =>
              inr b
          | _ =>
              inl
                ("(Beval) Error: Variable did not evaluate to a boolean: '" ++ varName ++ "'")
          end
      end
    end.

  Fixpoint Feval (expr : FExpr) (env : Env) (max : nat) : sum (Env * list string) Value :=
    match max with
    | 0 =>
        inl
          (env, ("(Feval) Error: Maximum recursion depth exceeded" :: nil))
    | S max' =>
      match expr with
      | F_Let varName bindExpr bodyExpr =>
          match Feval_Sub bindExpr env max' with
          | inr val =>
              Feval_Sub bodyExpr (ExtendEnv varName val env) max'
          | inl err =>
              inl err
          end
      | F_LetRec varname bindExpr bodyExpr =>
          Feval (F_Let varname (F_Fix varname bindExpr) bodyExpr) env max'
      end
    end.


  Compute
    Feval
      (F_Let "isFive"
        (F_Lambda "x"
          (F_Cond (B_Eq (E_Arith (A_Func (F_Var "x"))) (E_Arith (A_Const 5)))
            (F_Return (E_Bool (B_Const true)))
            (F_Return (E_Bool (B_Const false)))
          )
        )
        (F_Apply
          (F_Var "isFive")
          (F_Return (E_Arith (A_Const 0)))
        )
      )
      EmptyEnv 6.

  Compute
    Feval
      (F_LetRec "infinite"
        (F_Lambda "x"
          (F_Cond (B_Eq (E_Arith (A_Func (F_Var "x"))) (E_Arith (A_Const 5)))
            (F_Return (E_Arith (A_Const 0)))
            (F_Var "x")
          )
        )
        (F_Apply
          (F_Var "infinite")
          (F_Return (E_Arith (A_Const 0)))
        )
      )
      EmptyEnv
      5000.

  Example inf_env_1 :=
    ExtendEnv "infinite"
             (V_Fix "infinite"
            (F_Lambda "x"
               (F_Cond (B_Eq (E_Arith (A_Var "x")) (E_Arith (A_Const 5)))
                  (F_Return (E_Arith (A_Const 0)))
                  (F_Apply (F_Var "infinite")
                     (F_Return (E_Arith (A_Add (A_Var "x") (A_Const 1))))))) EmptyEnv)
              EmptyEnv.

  Compute
    Feval_Sub
          (F_Cond (B_Eq (E_Arith (A_Var "x")) (E_Arith (A_Const 5)))
            (F_Return (E_Arith (A_Const 0)))
            (F_Apply
              (F_Var "infinite")
              (F_Return (E_Arith (A_Add (A_Var "x") (A_Const 1))))
            )) inf_env_1 1000.



  Compute
    Feval
      (F_LetRec "factorial"
        (F_Lambda "n"
          (F_Cond (B_Eq (E_Arith (A_Var "n")) (E_Arith (A_Const 1)))
            (F_Return (E_Arith (A_Const 1)))
            (F_Apply
              (F_Var "factorial")
              (F_Return (E_Arith (A_Var "n")))
            )
          )
        )
          (F_Apply
            (F_Var "factorial")
            (F_Return (E_Arith (A_Const 5)))
          )
      )
      (ExtendEnv "input" (V_Nat 5) EmptyEnv)
      1000.

  Compute
    Feval_Sub
    (F_Apply
    (F_Fix "factorial"
      (F_Lambda "n"
        (F_Cond
          (B_Eq (E_Arith (A_Func (F_Var "n"))) (E_Arith (A_Const 1)))
          (F_Return ((E_Arith (A_Const 1))))
          (F_Return (E_Arith
            (A_Mul
              (A_Func (F_Var "n"))
              (A_Func (F_Apply
                (F_Var "factorial")
                (F_Return (E_Arith (A_Sub (A_Func (F_Var "n")) (A_Const 1))))
              ))))))))
              (F_Return (E_Arith (A_Const 5)))
              ) EmptyEnv 1000.



  Compute Feval_Sub ((F_Return (E_Arith (A_Add (A_Const 1) (A_Const 2))))) EmptyEnv 100.
  Compute Feval (F_Let "x" ((F_Return (E_Arith (A_Add (A_Const 1) (A_Const 2))))) ((F_Return (E_Arith (A_Add (A_Const 3) (A_Func (F_Var "x"))))))) EmptyEnv 100.
  Compute Feval
    (F_Let "double"
      (F_Lambda "n"
        (F_Return
          (E_Arith
            (A_Mul (A_Func (F_Var "n")) (A_Const 2))
          )
        )
      )
      (F_Apply
        (F_Var "double")
        (F_Return
          (E_Arith
            (A_Add (A_Const 8) (A_Const 9))
          )
        )
      )
    )
    EmptyEnv
    100.

End Semantics.
