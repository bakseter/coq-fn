From Coq Require Import Strings.String.
Require Import Syntax.
Require Import Semantics.
Require Import Parser.

Module Examples.

  Import Syntax.
  Import Semantics.

  Open Scope string_scope.

  Example factorial :=
    F_Let "factorial"
      (F_Lambda "n"
        (F_Cond
          (B_Le (A_Func (F_Var "n")) (A_Const 1))
          (F_Return (E_Arith (A_Const 1)))
          (F_Return (E_Arith (A_Mult
                      (A_Func (F_Var "n"))
                      (A_Func (F_Apply (F_Var "factorial") (E_Arith (A_Sub (A_Func (F_Var "n")) (A_Const 1))))))))))
      (F_Apply (F_Var "factorial") (E_Arith (A_Func (F_Var "input")))).

  Example factorial_eval (n : nat) :=
    Feval factorial (ExtendEnv "input" (V_Nat n) EmptyEnv) 1000.

End Examples.

Import Semantics.
Import Examples.
Import Parser.

Extraction Language Haskell.

Extract Inlined Constant sum_map => "(Prelude.<$>)".
Extract Inlined Constant sum_ap => "(Prelude.<*>)".

Extract Inductive sum => "Prelude.Either" ["Prelude.Left" "Prelude.Right"].
Extract Inductive nat => "Prelude.Integer" ["0" "Prelude.succ"]
  "(\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))".

Extraction
  "Examples.hs"
  factorial_eval
  test_ex_hask_parse.
