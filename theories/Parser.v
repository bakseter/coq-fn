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

   Definition is_white (c : ascii) : bool :=
    let n := nat_of_ascii c in
    orb (orb (n =? 32) (* space *)
             (n =? 9)) (* tab *)
        (orb (n =? 10) (* linefeed *)
             (n =? 13)). (* Carriage return. *)

  Notation "x '<=?' y" := (x <=? y)
    (at level 70, no associativity) : nat_scope.

  Definition is_lower_alpha (c : ascii) : bool :=
    let n := nat_of_ascii c in
      andb (97 <=? n) (n <=? 122).

  Definition is_alpha (c : ascii) : bool :=
    let n := nat_of_ascii c in
      orb (andb (65 <=? n) (n <=? 90))
          (andb (97 <=? n) (n <=? 122)).

  Definition is_digit (c : ascii) : bool :=
    let n := nat_of_ascii c in
       andb (48 <=? n) (n <=? 57).

  Inductive chartype := white | alpha | digit | other.

  Definition classify_char (c : ascii) : chartype :=
    if is_white c then
      white
    else if is_alpha c then
      alpha
    else if is_digit c then
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
        match classify_char h with
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
      match cls, classify_char x, x with
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
          if forallb is_lower_alpha (list_of_string h) then
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

  Definition parse_Var : parser Expr :=
    x <- parse_var_name;
    pure (Var x).

  Definition parse_Add : parser (Expr -> Expr -> Expr) :=
    _ <- parse_keyword "+";
    pure Add.

  Definition parse_Sub : parser (Expr -> Expr -> Expr) :=
    _ <- parse_keyword "-";
    pure Sub.

  Definition parse_Mul : parser (Expr -> Expr -> Expr) :=
    _ <- parse_keyword "*";
    pure Mul.

  Definition parse_Lambda (p : parser Expr) : parser Expr :=
    _ <- parse_keyword "\";
    x <- parse_var_name;
    _ <- parse_keyword "->";
    f <- p;
    pure (Lambda x f).

  Definition parse_Apply : parser (Expr -> Expr -> Expr) :=
    _ <- parse_keyword ".";
    pure Apply.

  Definition parse_Cond (p : parser Expr) : parser Expr :=
    _ <- parse_keyword "If";
    e1 <- p;
    _ <- parse_keyword "Then";
    e2 <- p;
    _ <- parse_keyword "Else";
    e3 <- p;
    pure (Cond e1 e2 e3).

  Definition parse_Bool : parser Expr :=
    p <- parse_keyword "True" <|> parse_keyword "False";
    match p with
    | "True" => pure (Bool true)
    | "False" => pure (Bool false)
    | _ => fail_parser Expr
    end.

  Definition parse_Nat : parser Expr :=
    parse_map Nat parse_nat.

  Definition parse_Eq (p : parser Expr) : parser Expr :=
    _ <- parse_keyword "{";
    a1 <- p;
    _ <- parse_keyword "==";
    a2 <- p;
    _ <- parse_keyword "}";
    pure (Eq a1 a2).

  Definition parse_And : parser (Expr -> Expr -> Expr) :=
    _ <- parse_keyword "&&";
    pure And.

  Definition parse_Let (p : parser Expr) : parser Expr :=
    _ <- parse_keyword "Let";
    x <- parse_var_name;
    _ <- parse_keyword ":=";
    f <- p;
    _ <- parse_keyword "In";
    f' <- p;
    pure (Let x f f').

  Fixpoint parse_Expr (n : nat) : parser Expr :=
    match n with
    | 0 => fail_parser Expr
    | S n' =>
        let parse_Sub_Expr :=
          _ <- parse_keyword "(";
          x <- parse_Expr n';
          _ <- parse_keyword ")";
          pure x
        in
        let parse_Simple :=
            parse_Sub_Expr
        <|> parse_Var
        <|> parse_Lambda (parse_Expr n')
        <|> parse_Bool
        <|> parse_Nat
        <|> parse_Cond (parse_Expr n')
        <|> parse_Let (parse_Expr n')
        <|> parse_Eq (parse_Expr n')
        in
        let parse_Complex :=
            parse_Add
        <|> parse_Sub
        <|> parse_Mul
        <|> parse_And
        <|> parse_Apply
        in
        (x <- parse_Simple;
        op <- parse_Complex;
        y <- parse_Simple;
        pure (op x y)) <|> parse_Simple
    end.

  Example parse_Expr_test1 :
    parse (parse_Expr 1000) "2 + 3" =
    inr ((Add (Nat 2) (Nat 3)), []).
  Proof. simpl. reflexivity. Qed.

  Example parse_Expr_test2 :
    parse (parse_Expr 3) "(2 + 3) + 1" =
    inr ((Add (Add (Nat 2) (Nat 3)) (Nat 1)), []).
  Proof. simpl. reflexivity. Qed.

  Example parse_F_Lambda_test :
    parse (parse_Lambda (parse_Expr 5)) "\x -> x" =
    inr ((Lambda "x" (Var "x")), []).
  Proof. simpl. reflexivity. Qed.

  Example parse_Expr_test3 :
    parse (parse_Expr 5) "\x -> 2 + 1" =
    inr ((Lambda "x" (Add (Nat 2) (Nat 1))), []).
  Proof. simpl. reflexivity. Qed.

  Example parse_Expr_test4 :
    parse (parse_Expr 5) "\x -> x + 1" =
    inr ((Lambda "x" (Add (Var "x") (Nat 1))), []).
  Proof. simpl. reflexivity. Qed.

  Example parse_Cond_test :
    parse (parse_Cond (parse_Expr 10)) "If {1 == 0} Then 1 Else 2" =
    inr ((Cond (Eq (Nat 1) (Nat 0)) (Nat 1) (Nat 2)), []).
  Proof. simpl. reflexivity. Qed.

  Definition execute (s : string) (e : Env) (max : nat) : sum (list string) Value :=
    match parse (parse_Expr 10) s with
    | inr (f, _) =>
        match eval f e max with
        | inr v => inr v
        | inl err => inl (snd err)
        end
    | inl err => inl err
    end.

  Definition input_vars (assignments : list (string * nat)) : Env :=
    fold_right (fun (assignment : string * nat) (env : Env) =>
      match assignment with
      | (x, n) => ExtendEnv x (V_Nat n) env
      end
    ) EmptyEnv assignments.

End Parser.
