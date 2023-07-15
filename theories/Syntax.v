From Coq Require Import Strings.String.

Module Syntax.

  Inductive FExpr : Type :=
  | F_Var : string -> FExpr
  | F_Lambda : string -> FExpr -> FExpr
  | F_Apply : FExpr -> Expr -> FExpr
  | F_Cond : BExpr -> FExpr -> FExpr -> FExpr
  | F_Return : Expr -> FExpr

  with Expr : Type :=
    | E_Bool : BExpr -> Expr
    | E_Arith : AExpr -> Expr

  with BExpr : Type :=
    | B_Const : bool -> BExpr
    | B_Eq : Expr -> Expr -> BExpr
    | B_Func : FExpr -> BExpr

  with AExpr : Type :=
    | A_Const : nat -> AExpr
    | A_Add : AExpr -> AExpr -> AExpr
    | A_Sub : AExpr -> AExpr -> AExpr
    | A_Func : FExpr -> AExpr.

End Syntax.
