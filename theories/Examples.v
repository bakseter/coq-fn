From Coq Require Import Strings.String.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Extraction.
From Coq Require Import ExtrHaskellBasic.
From Coq Require Import ExtrHaskellString.
From Coq Require Import ExtrHaskellNatNum.
Require Import Syntax.
Require Import Semantics.
Require Import Parser.

Module Examples.

  Import Syntax.
  Import Semantics.
  Import Parser.

  Open Scope string_scope.

  Example mult_str :=
    "Let mult := \n -> \m -> n * m In (mult . ione) . itwo".
  Example parse_mult := parse (parse_Expr 10) mult_str.
  Compute parse (parse_Expr 10) mult_str.

  Example double_str :=
    "Let double := \n -> n * 2 In double . input".
  Example parse_double := parse (parse_Expr 10) double_str.
  Compute parse_double.
  Example parse_double_exec := execute double_str (input_vars [("input", 10)]) 50.

  Example factorial_str :=
    "Let factorial :=
      \n ->
        If {n == 1}
        Then 1
        Else n * (factorial . (n - 1))
     In
     factorial . input".
  Example parse_factorial := parse (parse_Expr 10) factorial_str.
  Compute parse_factorial.
  Example parse_factorial_exec := execute factorial_str (input_vars [("input", 5)]) 50.
  Compute parse_factorial_exec.

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
  "extr/Examples.hs"
  parse_mult
  parse_double
  parse_double_exec
  parse_factorial
  parse_factorial_exec
  execute.
