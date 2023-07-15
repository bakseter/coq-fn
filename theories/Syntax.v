From Coq Require Import Strings.String.

Module Syntax.

  Inductive FExpr : Type :=
    | F_Let : string -> FExpr_Sub -> FExpr_Sub -> FExpr

  with FExpr_Sub : Type :=
    | F_Var : string -> FExpr_Sub
    | F_Lambda : string -> FExpr_Sub -> FExpr_Sub
    | F_Apply : FExpr_Sub -> FExpr_Sub -> FExpr_Sub
    | F_Cond : BExpr -> FExpr_Sub -> FExpr_Sub -> FExpr_Sub
    | F_Return : Expr -> FExpr_Sub

  with Expr : Type :=
    | E_Bool : BExpr -> Expr
    | E_Arith : AExpr -> Expr

  with BExpr : Type :=
    | B_Const : bool -> BExpr
    | B_Eq : Expr -> Expr -> BExpr
    | B_And : BExpr -> BExpr -> BExpr
    | B_Func : FExpr_Sub -> BExpr
    | B_Var : string -> BExpr

  with AExpr : Type :=
    | A_Const : nat -> AExpr
    | A_Add : AExpr -> AExpr -> AExpr
    | A_Sub : AExpr -> AExpr -> AExpr
    | A_Mul : AExpr -> AExpr -> AExpr
    | A_Func : FExpr_Sub -> AExpr
    | A_Var : string -> AExpr.

End Syntax.
