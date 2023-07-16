From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import List. Import ListNotations.
From Coq Require Import Program.Tactics.
From Coq Require Import Program.Wf.
From Coq Require Import FunInd.
Require Import Syntax. Import Syntax.
Require Import Semantics. Import Semantics.

Module Parser.

  Close Scope string_scope.

   Definition isWhite (c : ascii) : bool :=
    let n := nat_of_ascii c in
    orb (orb (n =? 32) (* space *)
             (n =? 9)) (* tab *)
        (orb (n =? 10) (* linefeed *)
             (n =? 13)). (* Carriage return. *)

  Notation "x '<=?' y" := (x <=? y)
    (at level 70, no associativity) : nat_scope.

  Definition isLowerAlpha (c : ascii) : bool :=
    let n := nat_of_ascii c in
      andb (97 <=? n) (n <=? 122).

  Definition isAlpha (c : ascii) : bool :=
    let n := nat_of_ascii c in
      orb (andb (65 <=? n) (n <=? 90))
          (andb (97 <=? n) (n <=? 122)).

  Definition isDigit (c : ascii) : bool :=
    let n := nat_of_ascii c in
       andb (48 <=? n) (n <=? 57).

  Inductive chartype := white | alpha | digit | other.

  Definition classifyChar (c : ascii) : chartype :=
    if isWhite c then
      white
    else if isAlpha c then
      alpha
    else if isDigit c then
      digit
    else
      other.

  Fixpoint list_of_string (s : string) : list ascii :=
    match s with
    | EmptyString => []
    | String c s => c :: (list_of_string s)
    end.

  Definition string_of_list (xs : list ascii) : string :=
    fold_right String EmptyString xs.

  Fixpoint string_to_nat' (cs : list ascii) (len : nat) {struct cs} : option nat :=
    match cs with
    | h :: t =>
        match classifyChar h with
        | digit =>
          match string_to_nat' t (len - 1) with
          | Some n =>
              Some (pow 10 (len - 1) * (nat_of_ascii h - 48) + n)
          | None =>
              None
          end
        | _ =>
            None
        end
    | [] => Some 0
    end.

  Definition string_to_nat (s : string) : option nat :=
    let char_list := (list_of_string s) in
    let len := Datatypes.length char_list in
    string_to_nat' char_list len.

  Fixpoint tokenize_helper (cls : chartype) (acc xs : list ascii)
                         : list (list ascii) :=
    let tk := match acc with [] => [] | _::_ => [rev acc] end in
    match xs with
    | [] => tk
    | x :: xs' =>
      match cls, classifyChar x, x with
      | _, _, "(" =>
        tk ++ ["("] :: (tokenize_helper other [] xs')
      | _, _, ")" =>
        tk ++ [")"] :: (tokenize_helper other [] xs')
      | _, white, _ =>
        tk ++ (tokenize_helper white [] xs')
      | alpha, alpha, x =>
        tokenize_helper alpha (x :: acc) xs'
      | digit, digit, x =>
        tokenize_helper digit (x :: acc) xs'
      | other, other, x =>
        tokenize_helper other (x :: acc) xs'
      | _, tp, x =>
        tk ++ (tokenize_helper tp [x] xs')
      end
    end %char.

  Definition tokenize (s : string) : list string :=
    map string_of_list (tokenize_helper white [] (list_of_string s)).


  (* Define the Parser Monad *)
  Inductive parser (A : Type) : Type :=
    | Parser : (list string -> sum (list string) (A * list string)) -> parser A.

  Arguments Parser {A}.

  (* Implement basic parser combinators *)
  Definition pure {A : Type} (x : A) : parser A :=
    Parser (fun input : list string => inr (x, input)).

  Definition bind {A B : Type} (p : parser A) (f : A -> parser B) : parser B :=
    Parser (fun input =>
              match p with
              | Parser parse =>
                match parse input with
                | inr (result, rest) =>
                    match f result with
                    | Parser parse' => parse' rest
                    end
                | inl err =>
                    inl err
                end
              end).

  Notation "x <- e1 ; e2" :=
    (bind e1 (fun x => e2))
      (at level 60, right associativity).


  Definition bind_discard_L {A B : Type} (p : parser A) (p' : parser B) : parser B :=
    Parser (fun input =>
              match p with
              | Parser parse =>
                match parse input with
                | inr (result, rest) =>
                    match p' with
                    | Parser parse' => parse' rest
                    end
                | inl err =>
                    inl err
                end
              end).

  Notation "'_' <- e1 ; e2" :=
    (bind_discard_L e1 e2)
      (at level 60, right associativity).

  Definition alternative {A : Type} (p1 p2 : parser A) : parser A :=
    Parser (fun input =>
              match p1 with
              | Parser parse =>
                match parse input with
                | inr (result, rest) => inr (result, rest)
                | inl err1 =>
                    match p2 with
                    | Parser parse' =>
                        match parse' input with
                        | inr (result', rest') => inr (result', rest')
                        | inl err2 => inl (err1 ++ err2)
                        end
                    end
                end
              end).

  Notation "e1 <|> e2" :=
    (alternative e1 e2)
      (at level 61, left associativity).

  Definition fail_parser (A : Type) : parser A :=
    Parser (fun _ => inl ["Failed to parse."%string]).

  Fixpoint chainl1 {A : Type} (max : nat) (p : parser A) (op : parser (A -> A -> A)) : parser A :=
    match max with
    | 0 => fail_parser A
    | S max' =>
      x <- p;
      f <- op;
      y <- chainl1 max' p op;
      (pure (f x y)
      <|> p)
    end.

  Fixpoint chainr1 {A : Type} (max : nat) (p : parser A) (op : parser (A -> A -> A)) : parser A :=
    match max with
    | 0 => fail_parser A
    | S max' =>
      x <- p;
      f <- op;
      y <- chainr1 max' p op;
      (pure (f x y)
      <|> p)
    end.

  Notation "p '`chainl1`' op" :=
    ((chainl1 100) p op)
      (at level 69, left associativity).

  Notation "p '`chainr1`' op" :=
    ((chainr1 100) p op)
      (at level 69, left associativity).

  Fixpoint words' (l : list ascii) (str : string) (acc : list string) : list string :=
    match l with
    | [] => acc ++ [str]
    | h :: t =>
        match classifyChar h with
        | white =>
            words' t EmptyString (acc ++ [str])
        | _ =>
            words' t (str ++ (String h EmptyString)) acc
        end
    end.

  Definition words (s : string) : list string :=
    words' (list_of_string s) EmptyString [].

  Definition parse_map {A B : Type} (f : A -> B) (p : parser A) : parser B :=
    Parser (fun input =>
              match p with
              | Parser parse =>
                match parse input with
                | inr (result, rest) => inr (f result, rest)
                | inl err => inl err
                end
              end).


  (* Parsing functions *)
  Definition parse {A : Type} (p : parser A) (input : string) : sum (list string) (A * list string) :=
    match p with
    | Parser parseFunc => parseFunc (tokenize input)
    end.

  Open Scope string_scope.

  (* Define parsers for language constructs *)
  Definition parse_nat : parser nat :=
    Parser (fun input =>
      match input with
      | [] => inl ["Nothing to parse."]
      | h :: t =>
          match string_to_nat h with
            | Some n =>
                inr (n, t)
            | None =>
                inl
                  ["Not a valid number: "
                  ++ "'" ++ h
                  ++ "', expected a number at '"
                  ++ concat_string_list (h :: " " :: t)
                  ++ "'."]
        end
      end).

  Definition parse_var_name : parser string :=
    Parser (fun input =>
      match input with
      | [] => inl ["Nothing to parse."]
      | h :: t =>
          if forallb isLowerAlpha (list_of_string h) then
            inr (h, t)
          else
            inl
              ["Not a valid variable string: "
              ++ "'" ++ h
              ++ "', expected a string at '"
              ++ concat_string_list (h :: " " :: t)
              ++ "'."]
      end).

  Definition parse_keyword (keyword : string) : parser string :=
    Parser (fun input =>
      match input with
      | [] => inl ["Nothing to parse."]
      | h :: t =>
          match String.eqb keyword h with
          | true => inr (keyword, t)
          | false => inl ["Not a valid keyword: "
                          ++ "'" ++ h
                          ++ "', expected '"
                          ++ keyword
                          ++ "' at '"
                          ++ concat_string_list (h :: " " :: t)
                          ++ "'."]
          end
      end).

  Compute parse (parse_keyword "\") "\ x -> x".

  Definition parse_A_Const : parser AExpr :=
    n <- parse_nat;
    pure (A_Const n).

  Definition parse_A_Var : parser AExpr :=
    x <- parse_var_name;
    pure (A_Var x).

  Definition parse_A_Func (p : parser FExpr_Sub) : parser AExpr :=
    f <- p;
    pure (A_Func f).

  Definition parse_A_Add : parser (AExpr -> AExpr -> AExpr) :=
    _ <- parse_keyword "+";
    pure A_Add.

  Definition parse_A_Sub : parser (AExpr -> AExpr -> AExpr) :=
    _ <- parse_keyword "-";
    pure A_Sub.

  Definition parse_A_Mul : parser (AExpr -> AExpr -> AExpr) :=
    _ <- parse_keyword "*";
    pure A_Mul.

  Definition parse_F_Var : parser FExpr_Sub :=
    x <- parse_var_name;
    pure (F_Var x).

  Definition parse_F_Lambda (p : parser FExpr_Sub) : parser FExpr_Sub :=
    _ <- parse_keyword "\";
    x <- parse_var_name;
    _ <- parse_keyword "->";
    f <- p;
    pure (F_Lambda x f).

  Definition parse_F_Apply (pf : parser FExpr_Sub) : parser FExpr_Sub :=
    _ <- parse_keyword "(";
    f1 <- pf;
    _ <- parse_keyword ")";
    _ <- parse_keyword "(";
    f2 <- pf;
    _ <- parse_keyword ")";
    pure (F_Apply f1 f2).

  Definition parse_F_Cond (pb : parser BExpr) (pf : parser FExpr_Sub) : parser FExpr_Sub :=
    _ <- parse_keyword "If";
    b <- pb;
    _ <- parse_keyword "Then";
    f1 <- pf;
    _ <- parse_keyword "Else";
    f2 <- pf;
    pure (F_Cond b f1 f2).


  Definition parse_F_Return (pe : parser Expr) : parser FExpr_Sub :=
    _ <- parse_keyword "Return";
    a <- pe;
    pure (F_Return a).

  (* BBBBBBEEEEEEXXXXXXPPPPPPPRRRRRREEEEESSS *)

  Definition parse_B_Const : parser BExpr :=
    p <- parse_keyword "True" <|> parse_keyword "False";
    match p with
    | "True" => pure (B_Const true)
    | "False" => pure (B_Const false)
    | _ => fail_parser BExpr
    end.


  Definition parse_B_Eq (p : parser Expr) : parser BExpr :=
    _ <- parse_keyword "{";
    a1 <- p;
    _ <- parse_keyword "==";
    a2 <- p;
    _ <- parse_keyword "}";
    pure (B_Eq a1 a2).

  Definition parse_B_Func (p : parser FExpr_Sub) : parser BExpr :=
    f <- p;
    pure (B_Func f).

  Definition parse_B_Var : parser BExpr :=
    x <- parse_var_name;
    pure (B_Var x).

  Definition parse_B_And : parser (BExpr -> BExpr -> BExpr) :=
    _ <- parse_keyword "&&";
    pure B_And.

  Fixpoint parse_FExpr_Sub (n : nat) : parser FExpr_Sub :=
    match n with
    | 0 => parse_F_Var
    | S n' =>
          parse_F_Lambda (parse_FExpr_Sub n')
      <|> parse_F_Return (parse_Expr n')
      <|> parse_F_Var
      <|> parse_F_Cond (parse_BExpr n') (parse_FExpr_Sub n')
      <|> parse_F_Apply (parse_FExpr_Sub n')
    end

  with parse_BExpr (n : nat) : parser BExpr :=
    match n with
    | 0 => parse_B_Const
    | S n' =>
        let parse_Sub_BExpr :=
          _ <- parse_keyword "(";
          x <- parse_BExpr n';
          _ <- parse_keyword ")";
          pure x
        in
        let parse_B_Prims := parse_Sub_BExpr <|> parse_B_Const <|> parse_B_Var <|> parse_B_Func (parse_FExpr_Sub n')
        in
        (x <- parse_B_Prims;
        op <- (parse_B_And);
        y <- parse_B_Prims;
        pure (op x y)) <|> parse_B_Prims <|> parse_B_Eq (parse_Expr n')
    end

  with parse_AExpr (max : nat) : parser AExpr :=
    match max with
    | 0 => fail_parser AExpr
    | S max' =>
        let parse_Sub_AExpr :=
          _ <- parse_keyword "(";
          x <- parse_AExpr max';
          _ <- parse_keyword ")";
          pure x
        in
        let parse_A_Prims := parse_Sub_AExpr <|> parse_A_Const <|> parse_A_Var <|> parse_A_Func (parse_FExpr_Sub max')
        in
        (x <- parse_A_Prims;
        op <- (parse_A_Add <|> parse_A_Sub <|> parse_A_Mul);
        y <- parse_A_Prims;
        pure (op x y)) <|> parse_A_Prims
    end

  with parse_Expr (n : nat) : parser Expr :=
    match n with
    | 0 => fail_parser Expr
    | S n' =>
            (parse_map E_Arith (parse_AExpr n'))
        <|> (parse_map E_Bool (parse_BExpr n'))
    end.

  Definition parse_F_Let (n : nat) : parser FExpr :=
    _ <- parse_keyword "Let";
    x <- parse_var_name;
    _ <- parse_keyword ":=";
    f <- parse_FExpr_Sub n;
    _ <- parse_keyword "In";
    f' <- parse_FExpr_Sub n;
    pure (F_Let x f f').

  Definition parse_FExpr (n : nat) : parser FExpr :=
    parse_F_Let n.

  Example parse_Expr_test1 :
    parse (parse_Expr 1000) "2 + 3" =
    inr ((E_Arith (A_Add (A_Const 2) (A_Const 3)), [])).
  Proof. simpl. reflexivity. Qed.

  Example parse_Expr_test2 :
    parse (parse_Expr 3) "(2 + 3) + 1" =
    inr ((E_Arith (A_Add (A_Add (A_Const 2) (A_Const 3)) (A_Const 1)), [])).
  Proof. simpl. reflexivity. Qed.

  Example parse_F_Lambda_test :
    parse (parse_F_Lambda (parse_FExpr_Sub 5)) "\x -> x" =
    inr ((F_Lambda "x" (F_Var "x")), []).
  Proof. simpl. reflexivity. Qed.

  Example parse_F_Return_test :
    parse (parse_F_Return (parse_Expr 5)) "Return 2 + 3" =
    inr ((F_Return (E_Arith (A_Add (A_Const 2) (A_Const 3)))), []).
  Proof. simpl. reflexivity. Qed.

  Example parse_FExpr_test1 :
    parse (parse_FExpr_Sub 5) "\x -> Return 2 + 1" =
    inr ((F_Lambda "x" (F_Return (E_Arith (A_Add (A_Const 2) (A_Const 1)))), [])).
  Proof. simpl. reflexivity. Qed.

  Example parse_FExpr_test2 :
    parse (parse_FExpr_Sub 5) "\x -> Return x + 1" =
    inr ((F_Lambda "x" (F_Return (E_Arith (A_Add (A_Var "x") (A_Const 1))))), []).
  Proof. simpl. reflexivity. Qed.

  Definition execute (s : string) (e : Env) :=
    match parse (parse_FExpr 10) s with
    | inr (f, _) =>
        match Feval f e 10 with
        | inr v => inr v
        | inl err => inl err
        end
    | inl err => inl err
    end.

  Example program_AST :=
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
        (F_Return (E_Arith (A_Func (F_Var "input"))))
      )
    ).

  Compute Feval program_AST (ExtendEnv "input" (V_Nat 3) EmptyEnv) 5.

  Definition input_vars (assignments : list (string * nat)) : Env :=
    fold_right (fun (assignment : string * nat) (env : Env) =>
      match assignment with
      | (x, n) => ExtendEnv x (V_Nat n) env
      end
    ) EmptyEnv assignments.

  Example double_str :=
    "Let double := \n -> Return n * 2 In (double) (Return input)".
  Compute parse (parse_FExpr 10) double_str.
  Compute execute double_str (input_vars [("input", 10)]).

  Example mult_str :=
    "Let mult :=
      \n -> \m ->
          Return n * m
     In
      (
        (mult)
        (Return ione)
      )
      (Return itwo)".
  Compute parse (parse_FExpr 10) mult_str.
  Compute execute mult_str (input_vars [("ione", 10); ("itwo", 20)]).

  Compute Feval_Sub (F_Apply (F_Var "m") (F_Return (E_Arith (A_Const 2))))
(ExtendEnv "m"
         (V_Closure (F_Return (E_Arith (A_Mul (A_Var "n") (A_Var "m"))))
            (ExtendEnv "n" (V_Nat 10)
               (ExtendEnv "mult"
                  (V_Closure
                     (F_Lambda "n"
                        (F_Lambda "m"
                           (F_Return
                              (E_Arith (A_Mul (A_Var "n") (A_Var "m"))))))
                     (ExtendEnv "ione" (V_Nat 10)
                        (ExtendEnv "itwo" (V_Nat 20) EmptyEnv)))
                  (ExtendEnv "ione" (V_Nat 10)
                     (ExtendEnv "itwo" (V_Nat 20) EmptyEnv))))) EmptyEnv) 10.

  Example parse_F_Cond_test :
    parse
      (parse_F_Cond (parse_BExpr 5) (parse_FExpr_Sub 5))
      "If {1 == 0} Then Return 1 Else Return 2" =
    inr ((F_Cond (B_Eq (E_Arith (A_Const 1)) (E_Arith (A_Const 0))) (F_Return (E_Arith (A_Const 1))) (F_Return (E_Arith (A_Const 2)))), []).
  Proof. simpl. reflexivity. Qed.

  Compute
    Feval
      (F_Let "halla"
        (F_Fixpoint "rec" 
          (F_Lambda "n"
            (F_Cond
              (B_Eq (E_Arith (A_Var "n")) (E_Arith (A_Const 1)))
                (F_Return (E_Arith (A_Const 1)))
                (F_Apply
                  (F_Var "rec")
                  (F_Return (E_Arith (A_Sub (A_Func (F_Var "n")) (A_Const 1))))
                )
             )
          )
        )
        (F_Apply (F_Var "halla") (F_Return (E_Arith (A_Const 5))))
      )
    EmptyEnv 100.

  Compute
    Feval_Sub
        (F_Fixpoint "rec" 
          (F_Lambda "n"
            (F_Cond
              (B_Eq (E_Arith (A_Var "n")) (E_Arith (A_Const 1)))
                (F_Return (E_Arith (A_Const 1)))
                (F_Apply
                  (F_Var "rec")
                  (F_Return (E_Arith (A_Sub (A_Func (F_Var "n")) (A_Const 1))))
                )
            )
          )
        )
      EmptyEnv
      100.

  Example factorial_str :=
    "Let factorial :=
      \n ->
        If {n == 1}
        Then Return 1
        Else (factorial) (Return n - 1)
     In
     (factorial)
     (Return input)".

  Compute parse (parse_FExpr 10) factorial_str.

  Example Y_combinator :=
      "Let ycomb :=
          \f ->
            (\x -> (f) ((x) (x)))
            (\x -> (f) ((x) (x)))
        In
        (ycomb)
        (ycomb)
        ".

  Compute parse (parse_FExpr 10) Y_combinator.

  Example factorial_with_Y_Combinator :=
    "Let factorial :=
      \rec ->
        \n ->
          If {n == 1}
          Then Return 1
          Else (f) (Return n - 1)
     In
     (
        (factorial)
         (\f -> (\x -> (f) ((x) (x))) (\x -> (f) ((x) (x))))
     )
    (input)
     ".

    Compute parse (parse_FExpr 10) factorial_with_Y_Combinator.
    Compute execute factorial_with_Y_Combinator (input_vars [("input", 5)]).

  

  Compute parse (parse_FExpr 10) factorial_str.
  Compute execute factorial_str (input_vars [("input", 5)]).

  Example mult_AST : FExpr :=
    (F_Let "mult"
      (F_Lambda "n"
        (F_Lambda "m"
          (F_Return
            (E_Arith
              (A_Mul (A_Func (F_Var "n")) (A_Func (F_Var "m")))
            )
          )
        )
      )
      (F_Apply
        (F_Apply
          (F_Var "mult")
          (F_Return (E_Arith (A_Const 2)))
        )
        (F_Return (E_Arith (A_Const 8)))
      )
    ).

  Compute Feval mult_AST EmptyEnv 10.

End Parser.
