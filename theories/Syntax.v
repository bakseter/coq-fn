From Coq Require Import Strings.String.

Module Syntax.

  Inductive Expr : Type :=
    | Let : string -> Expr -> Expr -> Expr
    | Var : string -> Expr
    | Lambda : string -> Expr -> Expr
    | Apply : Expr -> Expr -> Expr
    | Cond : Expr -> Expr -> Expr -> Expr
    | Nat : nat -> Expr
    | Add : Expr -> Expr -> Expr
    | Sub : Expr -> Expr -> Expr
    | Mul : Expr -> Expr -> Expr
    | Bool : bool -> Expr
    | And : Expr -> Expr -> Expr
    | Eq : Expr -> Expr -> Expr.

End Syntax.
