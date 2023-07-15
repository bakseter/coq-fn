module Parser where

import qualified Prelude

length :: (([]) a1) -> Prelude.Integer
length l =
  case l of {
   ([]) -> 0;
   (:) _ l' -> Prelude.succ (length l')}

app :: (([]) a1) -> (([]) a1) -> ([]) a1
app l m =
  case l of {
   ([]) -> m;
   (:) a l1 -> (:) a (app l1 m)}

sub :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
sub = (\n m -> Prelude.max 0 (n Prelude.- m))

eqb :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
eqb n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Prelude.True)
      (\_ -> Prelude.False)
      m)
    (\n' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Prelude.False)
      (\m' -> eqb n' m')
      m)
    n

leb :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
leb n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Prelude.True)
    (\n' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Prelude.False)
      (\m' -> leb n' m')
      m)
    n

pow :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
pow n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Prelude.succ 0)
    (\m0 -> (Prelude.*) n (pow n m0))
    m

data Positive =
   XI Positive
 | XO Positive
 | XH

data N =
   N0
 | Npos Positive

succ :: Positive -> Positive
succ x =
  case x of {
   XI p -> XO (succ p);
   XO p -> XI p;
   XH -> XO XH}

add :: Positive -> Positive -> Positive
add x y =
  case x of {
   XI p ->
    case y of {
     XI q -> XO (add_carry p q);
     XO q -> XI (add p q);
     XH -> XO (succ p)};
   XO p ->
    case y of {
     XI q -> XI (add p q);
     XO q -> XO (add p q);
     XH -> XI p};
   XH -> case y of {
          XI q -> XO (succ q);
          XO q -> XI q;
          XH -> XO XH}}

add_carry :: Positive -> Positive -> Positive
add_carry x y =
  case x of {
   XI p ->
    case y of {
     XI q -> XI (add_carry p q);
     XO q -> XO (add_carry p q);
     XH -> XI (succ p)};
   XO p ->
    case y of {
     XI q -> XO (add_carry p q);
     XO q -> XI (add p q);
     XH -> XO (succ p)};
   XH -> case y of {
          XI q -> XI (succ q);
          XO q -> XO (succ q);
          XH -> XI XH}}

mul :: Positive -> Positive -> Positive
mul x y =
  case x of {
   XI p -> add y (XO (mul p y));
   XO p -> XO (mul p y);
   XH -> y}

iter_op :: (a1 -> a1 -> a1) -> Positive -> a1 -> a1
iter_op op p a =
  case p of {
   XI p0 -> op a (iter_op op p0 (op a a));
   XO p0 -> iter_op op p0 (op a a);
   XH -> a}

to_nat :: Positive -> Prelude.Integer
to_nat x =
  iter_op (Prelude.+) x (Prelude.succ 0)

add0 :: N -> N -> N
add0 n m =
  case n of {
   N0 -> m;
   Npos p -> case m of {
              N0 -> n;
              Npos q -> Npos (add p q)}}

mul0 :: N -> N -> N
mul0 n m =
  case n of {
   N0 -> N0;
   Npos p -> case m of {
              N0 -> N0;
              Npos q -> Npos (mul p q)}}

to_nat0 :: N -> Prelude.Integer
to_nat0 a =
  case a of {
   N0 -> 0;
   Npos p -> to_nat p}

forallb :: (a1 -> Prelude.Bool) -> (([]) a1) -> Prelude.Bool
forallb f l =
  case l of {
   ([]) -> Prelude.True;
   (:) a l0 -> (Prelude.&&) (f a) (forallb f l0)}

n_of_digits :: (([]) Prelude.Bool) -> N
n_of_digits l =
  case l of {
   ([]) -> N0;
   (:) b l' ->
    add0 (case b of {
           Prelude.True -> Npos XH;
           Prelude.False -> N0}) (mul0 (Npos (XO XH)) (n_of_digits l'))}

n_of_ascii :: Prelude.Char -> N
n_of_ascii a =
  (\f a -> f (Data.Bits.testBit (Data.Char.ord a) 0)
              (Data.Bits.testBit (Data.Char.ord a) 1)
              (Data.Bits.testBit (Data.Char.ord a) 2)
              (Data.Bits.testBit (Data.Char.ord a) 3)
              (Data.Bits.testBit (Data.Char.ord a) 4)
              (Data.Bits.testBit (Data.Char.ord a) 5)
              (Data.Bits.testBit (Data.Char.ord a) 6)
              (Data.Bits.testBit (Data.Char.ord a) 7))
    (\a0 a1 a2 a3 a4 a5 a6 a7 ->
    n_of_digits ((:) a0 ((:) a1 ((:) a2 ((:) a3 ((:) a4 ((:) a5 ((:) a6 ((:)
      a7 ([]))))))))))
    a

nat_of_ascii :: Prelude.Char -> Prelude.Integer
nat_of_ascii a =
  to_nat0 (n_of_ascii a)

append :: Prelude.String -> Prelude.String -> Prelude.String
append s1 s2 =
  case s1 of {
   ([]) -> s2;
   (:) c s1' -> (:) c (append s1' s2)}

data FExpr =
   F_Var Prelude.String
 | F_Lambda Prelude.String FExpr
 | F_Apply FExpr Expr
 | F_Cond BExpr FExpr FExpr
 | F_Let Prelude.String FExpr FExpr
 | F_Return Expr
data Expr =
   E_Bool BExpr
 | E_Arith AExpr
data BExpr =
   B_Const Prelude.Bool
 | B_Not BExpr
 | B_And BExpr BExpr
 | B_Eq Expr Expr
 | B_Le AExpr AExpr
 | B_Func FExpr
data AExpr =
   A_Const Prelude.Integer
 | A_Add AExpr AExpr
 | A_Sub AExpr AExpr
 | A_Mult AExpr AExpr
 | A_Func FExpr

isWhite :: Prelude.Char -> Prelude.Bool
isWhite c =
  let {n = nat_of_ascii c} in
  (Prelude.||)
    ((Prelude.||)
      (eqb n (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ
        0)))))))))))))))))))))))))))))))))
      (eqb n (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        0)))))))))))
    ((Prelude.||)
      (eqb n (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ 0)))))))))))
      (eqb n (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        0)))))))))))))))

isLowerAlpha :: Prelude.Char -> Prelude.Bool
isLowerAlpha c =
  let {n = nat_of_ascii c} in
  (Prelude.&&)
    (leb (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ
      0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      n)
    (leb n (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ
      0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

isAlpha :: Prelude.Char -> Prelude.Bool
isAlpha c =
  let {n = nat_of_ascii c} in
  (Prelude.||)
    ((Prelude.&&)
      (leb (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ
        0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) n)
      (leb n (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ
        0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    ((Prelude.&&)
      (leb (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ
        0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        n)
      (leb n (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ
        0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

isDigit :: Prelude.Char -> Prelude.Bool
isDigit c =
  let {n = nat_of_ascii c} in
  (Prelude.&&)
    (leb (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      0)))))))))))))))))))))))))))))))))))))))))))))))) n)
    (leb n (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ
      0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

data Chartype =
   White
 | Alpha
 | Digit
 | Other

classifyChar :: Prelude.Char -> Chartype
classifyChar c =
  case isWhite c of {
   Prelude.True -> White;
   Prelude.False ->
    case isAlpha c of {
     Prelude.True -> Alpha;
     Prelude.False ->
      case isDigit c of {
       Prelude.True -> Digit;
       Prelude.False -> Other}}}

list_of_string :: Prelude.String -> ([]) Prelude.Char
list_of_string s =
  case s of {
   ([]) -> ([]);
   (:) c s0 -> (:) c (list_of_string s0)}

string_to_nat' :: (([]) Prelude.Char) -> Prelude.Integer -> Prelude.Maybe
                  Prelude.Integer
string_to_nat' cs len =
  case cs of {
   ([]) -> Prelude.Just 0;
   (:) h t ->
    case classifyChar h of {
     Digit ->
      case string_to_nat' t (sub len (Prelude.succ 0)) of {
       Prelude.Just n -> Prelude.Just
        ((Prelude.+)
          ((Prelude.*)
            (pow (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
              (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
              (Prelude.succ (Prelude.succ 0))))))))))
              (sub len (Prelude.succ 0)))
            (sub (nat_of_ascii h) (Prelude.succ (Prelude.succ (Prelude.succ
              (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
              (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
              (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
              (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
              (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
              (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
              (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
              (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
              (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
              (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
              (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
              (Prelude.succ
              0)))))))))))))))))))))))))))))))))))))))))))))))))) n);
       Prelude.Nothing -> Prelude.Nothing};
     _ -> Prelude.Nothing}}

string_to_nat :: Prelude.String -> Prelude.Maybe Prelude.Integer
string_to_nat s =
  let {char_list = list_of_string s} in
  let {len = length char_list} in string_to_nat' char_list len

type Parser a =
  (([]) Prelude.String) -> Prelude.Either (([]) Prelude.String)
  ((,) a (([]) Prelude.String))
  -- singleton inductive, whose constructor was Parser
  
pure :: a1 -> Parser a1
pure x input =
  Prelude.Right ((,) x input)

bind :: (Parser a1) -> (a1 -> Parser a2) -> Parser a2
bind p f input =
  case p input of {
   Prelude.Left err -> Prelude.Left err;
   Prelude.Right p0 -> case p0 of {
                        (,) result rest -> f result rest}}

alternative :: (Parser a1) -> (Parser a1) -> Parser a1
alternative p1 p2 input =
  case p1 input of {
   Prelude.Left err1 ->
    case p2 input of {
     Prelude.Left err2 -> Prelude.Left (app err1 err2);
     Prelude.Right p -> Prelude.Right p};
   Prelude.Right p -> Prelude.Right p}

words' :: (([]) Prelude.Char) -> Prelude.String -> (([]) Prelude.String) ->
          ([]) Prelude.String
words' l str acc =
  case l of {
   ([]) -> app acc ((:) str ([]));
   (:) h t ->
    case classifyChar h of {
     White -> words' t "" (app acc ((:) str ([])));
     _ -> words' t (append str ((:) h "")) acc}}

words :: Prelude.String -> ([]) Prelude.String
words s =
  words' (list_of_string s) "" ([])

parse :: (Parser a1) -> Prelude.String -> Prelude.Either
         (([]) Prelude.String) ((,) a1 (([]) Prelude.String))
parse p input =
  p (words input)

concat_string_list :: (([]) Prelude.String) -> Prelude.String
concat_string_list l =
  case l of {
   ([]) -> "";
   (:) h t -> append h (concat_string_list t)}

parse_nat :: Parser Prelude.Integer
parse_nat input =
  case input of {
   ([]) -> Prelude.Left ((:) "Nothing to parse." ([]));
   (:) h t ->
    case string_to_nat h of {
     Prelude.Just n -> Prelude.Right ((,) n t);
     Prelude.Nothing -> Prelude.Left ((:)
      (append "Not a valid number: "
        (append "'"
          (append h
            (append "', expected a number at '"
              (append (concat_string_list ((:) h ((:) " " t))) "'.")))))
      ([]))}}

parse_string :: Parser Prelude.String
parse_string input =
  case input of {
   ([]) -> Prelude.Left ((:) "Nothing to parse." ([]));
   (:) h t ->
    case forallb isLowerAlpha (list_of_string h) of {
     Prelude.True -> Prelude.Right ((,) h t);
     Prelude.False -> Prelude.Left ((:)
      (append "Not a valid variable string: "
        (append "'"
          (append h
            (append "', expected a string at '"
              (append (concat_string_list ((:) h ((:) " " t))) "'.")))))
      ([]))}}

parse_keyword :: Prelude.String -> Parser Prelude.String
parse_keyword keyword input =
  case input of {
   ([]) -> Prelude.Left ((:) "Nothing to parse." ([]));
   (:) h t ->
    case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
           keyword h of {
     Prelude.True -> Prelude.Right ((,) keyword t);
     Prelude.False -> Prelude.Left ((:)
      (append "Not a valid keyword: "
        (append "'"
          (append h
            (append "', expected '"
              (append keyword
                (append "' at '"
                  (append (concat_string_list ((:) h ((:) " " t))) "'.")))))))
      ([]))}}

parse_A_Const :: Parser AExpr
parse_A_Const =
  bind parse_nat (\n -> pure (A_Const n))

parse_A_Operators :: Parser (AExpr -> AExpr -> AExpr)
parse_A_Operators input =
  case input of {
   ([]) -> Prelude.Left ((:) "Nothing to parse." ([]));
   (:) h t ->
    case h of {
     ([]) -> Prelude.Left ((:)
      (append "Not a valid operator: "
        (append "'"
          (append h
            (append "', expected '+' at '"
              (append (concat_string_list ((:) h ((:) " " t))) "'.")))))
      ([]));
     (:) a s ->
      (\f a -> f (Data.Bits.testBit (Data.Char.ord a) 0)
              (Data.Bits.testBit (Data.Char.ord a) 1)
              (Data.Bits.testBit (Data.Char.ord a) 2)
              (Data.Bits.testBit (Data.Char.ord a) 3)
              (Data.Bits.testBit (Data.Char.ord a) 4)
              (Data.Bits.testBit (Data.Char.ord a) 5)
              (Data.Bits.testBit (Data.Char.ord a) 6)
              (Data.Bits.testBit (Data.Char.ord a) 7))
        (\b b0 b1 b2 b3 b4 b5 b6 ->
        case b of {
         Prelude.True ->
          case b0 of {
           Prelude.True ->
            case b1 of {
             Prelude.True -> Prelude.Left ((:)
              (append "Not a valid operator: "
                (append "'"
                  (append h
                    (append "', expected '+' at '"
                      (append (concat_string_list ((:) h ((:) " " t))) "'.")))))
              ([]));
             Prelude.False ->
              case b2 of {
               Prelude.True ->
                case b3 of {
                 Prelude.True -> Prelude.Left ((:)
                  (append "Not a valid operator: "
                    (append "'"
                      (append h
                        (append "', expected '+' at '"
                          (append (concat_string_list ((:) h ((:) " " t)))
                            "'."))))) ([]));
                 Prelude.False ->
                  case b4 of {
                   Prelude.True ->
                    case b5 of {
                     Prelude.True -> Prelude.Left ((:)
                      (append "Not a valid operator: "
                        (append "'"
                          (append h
                            (append "', expected '+' at '"
                              (append
                                (concat_string_list ((:) h ((:) " " t)))
                                "'."))))) ([]));
                     Prelude.False ->
                      case b6 of {
                       Prelude.True -> Prelude.Left ((:)
                        (append "Not a valid operator: "
                          (append "'"
                            (append h
                              (append "', expected '+' at '"
                                (append
                                  (concat_string_list ((:) h ((:) " " t)))
                                  "'."))))) ([]));
                       Prelude.False ->
                        case s of {
                         ([]) -> Prelude.Right ((,) (\x x0 -> A_Add x x0) t);
                         (:) _ _ -> Prelude.Left ((:)
                          (append "Not a valid operator: "
                            (append "'"
                              (append h
                                (append "', expected '+' at '"
                                  (append
                                    (concat_string_list ((:) h ((:) " " t)))
                                    "'."))))) ([]))}}};
                   Prelude.False -> Prelude.Left ((:)
                    (append "Not a valid operator: "
                      (append "'"
                        (append h
                          (append "', expected '+' at '"
                            (append (concat_string_list ((:) h ((:) " " t)))
                              "'."))))) ([]))}};
               Prelude.False -> Prelude.Left ((:)
                (append "Not a valid operator: "
                  (append "'"
                    (append h
                      (append "', expected '+' at '"
                        (append (concat_string_list ((:) h ((:) " " t)))
                          "'."))))) ([]))}};
           Prelude.False ->
            case b1 of {
             Prelude.True ->
              case b2 of {
               Prelude.True ->
                case b3 of {
                 Prelude.True -> Prelude.Left ((:)
                  (append "Not a valid operator: "
                    (append "'"
                      (append h
                        (append "', expected '+' at '"
                          (append (concat_string_list ((:) h ((:) " " t)))
                            "'."))))) ([]));
                 Prelude.False ->
                  case b4 of {
                   Prelude.True ->
                    case b5 of {
                     Prelude.True -> Prelude.Left ((:)
                      (append "Not a valid operator: "
                        (append "'"
                          (append h
                            (append "', expected '+' at '"
                              (append
                                (concat_string_list ((:) h ((:) " " t)))
                                "'."))))) ([]));
                     Prelude.False ->
                      case b6 of {
                       Prelude.True -> Prelude.Left ((:)
                        (append "Not a valid operator: "
                          (append "'"
                            (append h
                              (append "', expected '+' at '"
                                (append
                                  (concat_string_list ((:) h ((:) " " t)))
                                  "'."))))) ([]));
                       Prelude.False ->
                        case s of {
                         ([]) -> Prelude.Right ((,) (\x x0 -> A_Sub x x0) t);
                         (:) _ _ -> Prelude.Left ((:)
                          (append "Not a valid operator: "
                            (append "'"
                              (append h
                                (append "', expected '+' at '"
                                  (append
                                    (concat_string_list ((:) h ((:) " " t)))
                                    "'."))))) ([]))}}};
                   Prelude.False -> Prelude.Left ((:)
                    (append "Not a valid operator: "
                      (append "'"
                        (append h
                          (append "', expected '+' at '"
                            (append (concat_string_list ((:) h ((:) " " t)))
                              "'."))))) ([]))}};
               Prelude.False -> Prelude.Left ((:)
                (append "Not a valid operator: "
                  (append "'"
                    (append h
                      (append "', expected '+' at '"
                        (append (concat_string_list ((:) h ((:) " " t)))
                          "'."))))) ([]))};
             Prelude.False -> Prelude.Left ((:)
              (append "Not a valid operator: "
                (append "'"
                  (append h
                    (append "', expected '+' at '"
                      (append (concat_string_list ((:) h ((:) " " t))) "'.")))))
              ([]))}};
         Prelude.False ->
          case b0 of {
           Prelude.True ->
            case b1 of {
             Prelude.True -> Prelude.Left ((:)
              (append "Not a valid operator: "
                (append "'"
                  (append h
                    (append "', expected '+' at '"
                      (append (concat_string_list ((:) h ((:) " " t))) "'.")))))
              ([]));
             Prelude.False ->
              case b2 of {
               Prelude.True ->
                case b3 of {
                 Prelude.True -> Prelude.Left ((:)
                  (append "Not a valid operator: "
                    (append "'"
                      (append h
                        (append "', expected '+' at '"
                          (append (concat_string_list ((:) h ((:) " " t)))
                            "'."))))) ([]));
                 Prelude.False ->
                  case b4 of {
                   Prelude.True ->
                    case b5 of {
                     Prelude.True -> Prelude.Left ((:)
                      (append "Not a valid operator: "
                        (append "'"
                          (append h
                            (append "', expected '+' at '"
                              (append
                                (concat_string_list ((:) h ((:) " " t)))
                                "'."))))) ([]));
                     Prelude.False ->
                      case b6 of {
                       Prelude.True -> Prelude.Left ((:)
                        (append "Not a valid operator: "
                          (append "'"
                            (append h
                              (append "', expected '+' at '"
                                (append
                                  (concat_string_list ((:) h ((:) " " t)))
                                  "'."))))) ([]));
                       Prelude.False ->
                        case s of {
                         ([]) -> Prelude.Right ((,) (\x x0 -> A_Mult x x0) t);
                         (:) _ _ -> Prelude.Left ((:)
                          (append "Not a valid operator: "
                            (append "'"
                              (append h
                                (append "', expected '+' at '"
                                  (append
                                    (concat_string_list ((:) h ((:) " " t)))
                                    "'."))))) ([]))}}};
                   Prelude.False -> Prelude.Left ((:)
                    (append "Not a valid operator: "
                      (append "'"
                        (append h
                          (append "', expected '+' at '"
                            (append (concat_string_list ((:) h ((:) " " t)))
                              "'."))))) ([]))}};
               Prelude.False -> Prelude.Left ((:)
                (append "Not a valid operator: "
                  (append "'"
                    (append h
                      (append "', expected '+' at '"
                        (append (concat_string_list ((:) h ((:) " " t)))
                          "'."))))) ([]))}};
           Prelude.False -> Prelude.Left ((:)
            (append "Not a valid operator: "
              (append "'"
                (append h
                  (append "', expected '+' at '"
                    (append (concat_string_list ((:) h ((:) " " t))) "'.")))))
            ([]))}})
        a}}

parse_A_Op_Expr :: Parser AExpr
parse_A_Op_Expr =
  bind parse_A_Const (\n1 ->
    bind parse_A_Operators (\p -> bind parse_A_Const (\n2 -> pure (p n1 n2))))

parse_F_Var :: Parser FExpr
parse_F_Var =
  bind parse_string (\x -> pure (F_Var x))

parse_F_Lambda :: (Parser FExpr) -> Parser FExpr
parse_F_Lambda p =
  bind (parse_keyword "\\") (\_ ->
    bind parse_string (\x ->
      bind (parse_keyword "->") (\_ -> bind p (\f -> pure (F_Lambda x f)))))

parse_F_Apply :: (Parser FExpr) -> (Parser Expr) -> Parser FExpr
parse_F_Apply p1 p2 =
  bind p1 (\f -> bind p2 (\e -> pure (F_Apply f e)))

parse_F_Cond :: (Parser BExpr) -> (Parser FExpr) -> (Parser FExpr) -> Parser
                FExpr
parse_F_Cond p1 p2 p3 =
  bind (parse_keyword "if") (\_ ->
    bind p1 (\b ->
      bind (parse_keyword "then") (\_ ->
        bind p2 (\f1 ->
          bind (parse_keyword "else") (\_ ->
            bind p3 (\f2 -> pure (F_Cond b f1 f2)))))))

parse_F_Let :: (Parser FExpr) -> Parser FExpr
parse_F_Let p =
  bind (parse_keyword "let") (\_ ->
    bind parse_string (\x ->
      bind (parse_keyword ":=") (\_ ->
        bind p (\f1 ->
          bind (parse_keyword "in") (\_ ->
            bind p (\f2 -> pure (F_Let x f1 f2)))))))

parse_Return :: (Parser Expr) -> Parser FExpr
parse_Return p =
  bind (parse_keyword "return") (\_ -> bind p (\a -> pure (F_Return a)))

parse_B_Const :: Parser BExpr
parse_B_Const input =
  case input of {
   ([]) -> Prelude.Left ((:) "Nothing to parse." ([]));
   (:) h t ->
    case h of {
     ([]) -> Prelude.Left ((:)
      (append "Not a valid boolean: "
        (append "'"
          (append h
            (append "', expected 'true' or 'false' at '"
              (append (concat_string_list ((:) h ((:) " " t))) "'.")))))
      ([]));
     (:) a s ->
      (\f a -> f (Data.Bits.testBit (Data.Char.ord a) 0)
              (Data.Bits.testBit (Data.Char.ord a) 1)
              (Data.Bits.testBit (Data.Char.ord a) 2)
              (Data.Bits.testBit (Data.Char.ord a) 3)
              (Data.Bits.testBit (Data.Char.ord a) 4)
              (Data.Bits.testBit (Data.Char.ord a) 5)
              (Data.Bits.testBit (Data.Char.ord a) 6)
              (Data.Bits.testBit (Data.Char.ord a) 7))
        (\b b0 b1 b2 b3 b4 b5 b6 ->
        case b of {
         Prelude.True -> Prelude.Left ((:)
          (append "Not a valid boolean: "
            (append "'"
              (append h
                (append "', expected 'true' or 'false' at '"
                  (append (concat_string_list ((:) h ((:) " " t))) "'.")))))
          ([]));
         Prelude.False ->
          case b0 of {
           Prelude.True ->
            case b1 of {
             Prelude.True ->
              case b2 of {
               Prelude.True -> Prelude.Left ((:)
                (append "Not a valid boolean: "
                  (append "'"
                    (append h
                      (append "', expected 'true' or 'false' at '"
                        (append (concat_string_list ((:) h ((:) " " t)))
                          "'."))))) ([]));
               Prelude.False ->
                case b3 of {
                 Prelude.True -> Prelude.Left ((:)
                  (append "Not a valid boolean: "
                    (append "'"
                      (append h
                        (append "', expected 'true' or 'false' at '"
                          (append (concat_string_list ((:) h ((:) " " t)))
                            "'."))))) ([]));
                 Prelude.False ->
                  case b4 of {
                   Prelude.True ->
                    case b5 of {
                     Prelude.True ->
                      case b6 of {
                       Prelude.True -> Prelude.Left ((:)
                        (append "Not a valid boolean: "
                          (append "'"
                            (append h
                              (append "', expected 'true' or 'false' at '"
                                (append
                                  (concat_string_list ((:) h ((:) " " t)))
                                  "'."))))) ([]));
                       Prelude.False ->
                        case s of {
                         ([]) -> Prelude.Left ((:)
                          (append "Not a valid boolean: "
                            (append "'"
                              (append h
                                (append "', expected 'true' or 'false' at '"
                                  (append
                                    (concat_string_list ((:) h ((:) " " t)))
                                    "'."))))) ([]));
                         (:) a0 s0 ->
                          (\f a -> f (Data.Bits.testBit (Data.Char.ord a) 0)
              (Data.Bits.testBit (Data.Char.ord a) 1)
              (Data.Bits.testBit (Data.Char.ord a) 2)
              (Data.Bits.testBit (Data.Char.ord a) 3)
              (Data.Bits.testBit (Data.Char.ord a) 4)
              (Data.Bits.testBit (Data.Char.ord a) 5)
              (Data.Bits.testBit (Data.Char.ord a) 6)
              (Data.Bits.testBit (Data.Char.ord a) 7))
                            (\b7 b8 b9 b10 b11 b12 b13 b14 ->
                            case b7 of {
                             Prelude.True ->
                              case b8 of {
                               Prelude.True -> Prelude.Left ((:)
                                (append "Not a valid boolean: "
                                  (append "'"
                                    (append h
                                      (append
                                        "', expected 'true' or 'false' at '"
                                        (append
                                          (concat_string_list ((:) h ((:) " "
                                            t))) "'."))))) ([]));
                               Prelude.False ->
                                case b9 of {
                                 Prelude.True -> Prelude.Left ((:)
                                  (append "Not a valid boolean: "
                                    (append "'"
                                      (append h
                                        (append
                                          "', expected 'true' or 'false' at '"
                                          (append
                                            (concat_string_list ((:) h ((:)
                                              " " t))) "'."))))) ([]));
                                 Prelude.False ->
                                  case b10 of {
                                   Prelude.True -> Prelude.Left ((:)
                                    (append "Not a valid boolean: "
                                      (append "'"
                                        (append h
                                          (append
                                            "', expected 'true' or 'false' at '"
                                            (append
                                              (concat_string_list ((:) h ((:)
                                                " " t))) "'."))))) ([]));
                                   Prelude.False ->
                                    case b11 of {
                                     Prelude.True -> Prelude.Left ((:)
                                      (append "Not a valid boolean: "
                                        (append "'"
                                          (append h
                                            (append
                                              "', expected 'true' or 'false' at '"
                                              (append
                                                (concat_string_list ((:) h
                                                  ((:) " " t))) "'.")))))
                                      ([]));
                                     Prelude.False ->
                                      case b12 of {
                                       Prelude.True ->
                                        case b13 of {
                                         Prelude.True ->
                                          case b14 of {
                                           Prelude.True -> Prelude.Left ((:)
                                            (append "Not a valid boolean: "
                                              (append "'"
                                                (append h
                                                  (append
                                                    "', expected 'true' or 'false' at '"
                                                    (append
                                                      (concat_string_list
                                                        ((:) h ((:) " " t)))
                                                      "'."))))) ([]));
                                           Prelude.False ->
                                            case s0 of {
                                             ([]) -> Prelude.Left ((:)
                                              (append "Not a valid boolean: "
                                                (append "'"
                                                  (append h
                                                    (append
                                                      "', expected 'true' or 'false' at '"
                                                      (append
                                                        (concat_string_list
                                                          ((:) h ((:) " "
                                                          t))) "'.")))))
                                              ([]));
                                             (:) a1 s1 ->
                                              (\f a -> f (Data.Bits.testBit (Data.Char.ord a) 0)
              (Data.Bits.testBit (Data.Char.ord a) 1)
              (Data.Bits.testBit (Data.Char.ord a) 2)
              (Data.Bits.testBit (Data.Char.ord a) 3)
              (Data.Bits.testBit (Data.Char.ord a) 4)
              (Data.Bits.testBit (Data.Char.ord a) 5)
              (Data.Bits.testBit (Data.Char.ord a) 6)
              (Data.Bits.testBit (Data.Char.ord a) 7))
                                                (\b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                case b15 of {
                                                 Prelude.True -> Prelude.Left
                                                  ((:)
                                                  (append
                                                    "Not a valid boolean: "
                                                    (append "'"
                                                      (append h
                                                        (append
                                                          "', expected 'true' or 'false' at '"
                                                          (append
                                                            (concat_string_list
                                                              ((:) h ((:) " "
                                                              t))) "'.")))))
                                                  ([]));
                                                 Prelude.False ->
                                                  case b16 of {
                                                   Prelude.True ->
                                                    Prelude.Left ((:)
                                                    (append
                                                      "Not a valid boolean: "
                                                      (append "'"
                                                        (append h
                                                          (append
                                                            "', expected 'true' or 'false' at '"
                                                            (append
                                                              (concat_string_list
                                                                ((:) h ((:)
                                                                " " t)))
                                                              "'."))))) ([]));
                                                   Prelude.False ->
                                                    case b17 of {
                                                     Prelude.True ->
                                                      case b18 of {
                                                       Prelude.True ->
                                                        case b19 of {
                                                         Prelude.True ->
                                                          Prelude.Left ((:)
                                                          (append
                                                            "Not a valid boolean: "
                                                            (append "'"
                                                              (append h
                                                                (append
                                                                  "', expected 'true' or 'false' at '"
                                                                  (append
                                                                    (concat_string_list
                                                                    ((:) h
                                                                    ((:) " "
                                                                    t)))
                                                                    "'.")))))
                                                          ([]));
                                                         Prelude.False ->
                                                          case b20 of {
                                                           Prelude.True ->
                                                            case b21 of {
                                                             Prelude.True ->
                                                              case b22 of {
                                                               Prelude.True ->
                                                                Prelude.Left
                                                                ((:)
                                                                (append
                                                                  "Not a valid boolean: "
                                                                  (append "'"
                                                                    (append h
                                                                    (append
                                                                    "', expected 'true' or 'false' at '"
                                                                    (append
                                                                    (concat_string_list
                                                                    ((:) h
                                                                    ((:) " "
                                                                    t)))
                                                                    "'.")))))
                                                                ([]));
                                                               Prelude.False ->
                                                                case s1 of {
                                                                 ([]) ->
                                                                  Prelude.Left
                                                                  ((:)
                                                                  (append
                                                                    "Not a valid boolean: "
                                                                    (append
                                                                    "'"
                                                                    (append h
                                                                    (append
                                                                    "', expected 'true' or 'false' at '"
                                                                    (append
                                                                    (concat_string_list
                                                                    ((:) h
                                                                    ((:) " "
                                                                    t)))
                                                                    "'.")))))
                                                                  ([]));
                                                                 (:) a2 s2 ->
                                                                  (\f a -> f (Data.Bits.testBit (Data.Char.ord a) 0)
              (Data.Bits.testBit (Data.Char.ord a) 1)
              (Data.Bits.testBit (Data.Char.ord a) 2)
              (Data.Bits.testBit (Data.Char.ord a) 3)
              (Data.Bits.testBit (Data.Char.ord a) 4)
              (Data.Bits.testBit (Data.Char.ord a) 5)
              (Data.Bits.testBit (Data.Char.ord a) 6)
              (Data.Bits.testBit (Data.Char.ord a) 7))
                                                                    (\b23 b24 b25 b26 b27 b28 b29 b30 ->
                                                                    case b23 of {
                                                                     Prelude.True ->
                                                                    case b24 of {
                                                                     Prelude.True ->
                                                                    case b25 of {
                                                                     Prelude.True ->
                                                                    Prelude.Left
                                                                    ((:)
                                                                    (append
                                                                    "Not a valid boolean: "
                                                                    (append
                                                                    "'"
                                                                    (append h
                                                                    (append
                                                                    "', expected 'true' or 'false' at '"
                                                                    (append
                                                                    (concat_string_list
                                                                    ((:) h
                                                                    ((:) " "
                                                                    t)))
                                                                    "'.")))))
                                                                    ([]));
                                                                     Prelude.False ->
                                                                    case b26 of {
                                                                     Prelude.True ->
                                                                    Prelude.Left
                                                                    ((:)
                                                                    (append
                                                                    "Not a valid boolean: "
                                                                    (append
                                                                    "'"
                                                                    (append h
                                                                    (append
                                                                    "', expected 'true' or 'false' at '"
                                                                    (append
                                                                    (concat_string_list
                                                                    ((:) h
                                                                    ((:) " "
                                                                    t)))
                                                                    "'.")))))
                                                                    ([]));
                                                                     Prelude.False ->
                                                                    case b27 of {
                                                                     Prelude.True ->
                                                                    case b28 of {
                                                                     Prelude.True ->
                                                                    case b29 of {
                                                                     Prelude.True ->
                                                                    case b30 of {
                                                                     Prelude.True ->
                                                                    Prelude.Left
                                                                    ((:)
                                                                    (append
                                                                    "Not a valid boolean: "
                                                                    (append
                                                                    "'"
                                                                    (append h
                                                                    (append
                                                                    "', expected 'true' or 'false' at '"
                                                                    (append
                                                                    (concat_string_list
                                                                    ((:) h
                                                                    ((:) " "
                                                                    t)))
                                                                    "'.")))))
                                                                    ([]));
                                                                     Prelude.False ->
                                                                    case s2 of {
                                                                     ([]) ->
                                                                    Prelude.Left
                                                                    ((:)
                                                                    (append
                                                                    "Not a valid boolean: "
                                                                    (append
                                                                    "'"
                                                                    (append h
                                                                    (append
                                                                    "', expected 'true' or 'false' at '"
                                                                    (append
                                                                    (concat_string_list
                                                                    ((:) h
                                                                    ((:) " "
                                                                    t)))
                                                                    "'.")))))
                                                                    ([]));
                                                                     (:) a3
                                                                    s3 ->
                                                                    (\f a -> f (Data.Bits.testBit (Data.Char.ord a) 0)
              (Data.Bits.testBit (Data.Char.ord a) 1)
              (Data.Bits.testBit (Data.Char.ord a) 2)
              (Data.Bits.testBit (Data.Char.ord a) 3)
              (Data.Bits.testBit (Data.Char.ord a) 4)
              (Data.Bits.testBit (Data.Char.ord a) 5)
              (Data.Bits.testBit (Data.Char.ord a) 6)
              (Data.Bits.testBit (Data.Char.ord a) 7))
                                                                    (\b31 b32 b33 b34 b35 b36 b37 b38 ->
                                                                    case b31 of {
                                                                     Prelude.True ->
                                                                    case b32 of {
                                                                     Prelude.True ->
                                                                    Prelude.Left
                                                                    ((:)
                                                                    (append
                                                                    "Not a valid boolean: "
                                                                    (append
                                                                    "'"
                                                                    (append h
                                                                    (append
                                                                    "', expected 'true' or 'false' at '"
                                                                    (append
                                                                    (concat_string_list
                                                                    ((:) h
                                                                    ((:) " "
                                                                    t)))
                                                                    "'.")))))
                                                                    ([]));
                                                                     Prelude.False ->
                                                                    case b33 of {
                                                                     Prelude.True ->
                                                                    case b34 of {
                                                                     Prelude.True ->
                                                                    Prelude.Left
                                                                    ((:)
                                                                    (append
                                                                    "Not a valid boolean: "
                                                                    (append
                                                                    "'"
                                                                    (append h
                                                                    (append
                                                                    "', expected 'true' or 'false' at '"
                                                                    (append
                                                                    (concat_string_list
                                                                    ((:) h
                                                                    ((:) " "
                                                                    t)))
                                                                    "'.")))))
                                                                    ([]));
                                                                     Prelude.False ->
                                                                    case b35 of {
                                                                     Prelude.True ->
                                                                    Prelude.Left
                                                                    ((:)
                                                                    (append
                                                                    "Not a valid boolean: "
                                                                    (append
                                                                    "'"
                                                                    (append h
                                                                    (append
                                                                    "', expected 'true' or 'false' at '"
                                                                    (append
                                                                    (concat_string_list
                                                                    ((:) h
                                                                    ((:) " "
                                                                    t)))
                                                                    "'.")))))
                                                                    ([]));
                                                                     Prelude.False ->
                                                                    case b36 of {
                                                                     Prelude.True ->
                                                                    case b37 of {
                                                                     Prelude.True ->
                                                                    case b38 of {
                                                                     Prelude.True ->
                                                                    Prelude.Left
                                                                    ((:)
                                                                    (append
                                                                    "Not a valid boolean: "
                                                                    (append
                                                                    "'"
                                                                    (append h
                                                                    (append
                                                                    "', expected 'true' or 'false' at '"
                                                                    (append
                                                                    (concat_string_list
                                                                    ((:) h
                                                                    ((:) " "
                                                                    t)))
                                                                    "'.")))))
                                                                    ([]));
                                                                     Prelude.False ->
                                                                    case s3 of {
                                                                     ([]) ->
                                                                    Prelude.Right
                                                                    ((,)
                                                                    (B_Const
                                                                    Prelude.False)
                                                                    t);
                                                                     (:) _
                                                                    _ ->
                                                                    Prelude.Left
                                                                    ((:)
                                                                    (append
                                                                    "Not a valid boolean: "
                                                                    (append
                                                                    "'"
                                                                    (append h
                                                                    (append
                                                                    "', expected 'true' or 'false' at '"
                                                                    (append
                                                                    (concat_string_list
                                                                    ((:) h
                                                                    ((:) " "
                                                                    t)))
                                                                    "'.")))))
                                                                    ([]))}};
                                                                     Prelude.False ->
                                                                    Prelude.Left
                                                                    ((:)
                                                                    (append
                                                                    "Not a valid boolean: "
                                                                    (append
                                                                    "'"
                                                                    (append h
                                                                    (append
                                                                    "', expected 'true' or 'false' at '"
                                                                    (append
                                                                    (concat_string_list
                                                                    ((:) h
                                                                    ((:) " "
                                                                    t)))
                                                                    "'.")))))
                                                                    ([]))};
                                                                     Prelude.False ->
                                                                    Prelude.Left
                                                                    ((:)
                                                                    (append
                                                                    "Not a valid boolean: "
                                                                    (append
                                                                    "'"
                                                                    (append h
                                                                    (append
                                                                    "', expected 'true' or 'false' at '"
                                                                    (append
                                                                    (concat_string_list
                                                                    ((:) h
                                                                    ((:) " "
                                                                    t)))
                                                                    "'.")))))
                                                                    ([]))}}};
                                                                     Prelude.False ->
                                                                    Prelude.Left
                                                                    ((:)
                                                                    (append
                                                                    "Not a valid boolean: "
                                                                    (append
                                                                    "'"
                                                                    (append h
                                                                    (append
                                                                    "', expected 'true' or 'false' at '"
                                                                    (append
                                                                    (concat_string_list
                                                                    ((:) h
                                                                    ((:) " "
                                                                    t)))
                                                                    "'.")))))
                                                                    ([]))}};
                                                                     Prelude.False ->
                                                                    Prelude.Left
                                                                    ((:)
                                                                    (append
                                                                    "Not a valid boolean: "
                                                                    (append
                                                                    "'"
                                                                    (append h
                                                                    (append
                                                                    "', expected 'true' or 'false' at '"
                                                                    (append
                                                                    (concat_string_list
                                                                    ((:) h
                                                                    ((:) " "
                                                                    t)))
                                                                    "'.")))))
                                                                    ([]))})
                                                                    a3}};
                                                                     Prelude.False ->
                                                                    Prelude.Left
                                                                    ((:)
                                                                    (append
                                                                    "Not a valid boolean: "
                                                                    (append
                                                                    "'"
                                                                    (append h
                                                                    (append
                                                                    "', expected 'true' or 'false' at '"
                                                                    (append
                                                                    (concat_string_list
                                                                    ((:) h
                                                                    ((:) " "
                                                                    t)))
                                                                    "'.")))))
                                                                    ([]))};
                                                                     Prelude.False ->
                                                                    Prelude.Left
                                                                    ((:)
                                                                    (append
                                                                    "Not a valid boolean: "
                                                                    (append
                                                                    "'"
                                                                    (append h
                                                                    (append
                                                                    "', expected 'true' or 'false' at '"
                                                                    (append
                                                                    (concat_string_list
                                                                    ((:) h
                                                                    ((:) " "
                                                                    t)))
                                                                    "'.")))))
                                                                    ([]))};
                                                                     Prelude.False ->
                                                                    Prelude.Left
                                                                    ((:)
                                                                    (append
                                                                    "Not a valid boolean: "
                                                                    (append
                                                                    "'"
                                                                    (append h
                                                                    (append
                                                                    "', expected 'true' or 'false' at '"
                                                                    (append
                                                                    (concat_string_list
                                                                    ((:) h
                                                                    ((:) " "
                                                                    t)))
                                                                    "'.")))))
                                                                    ([]))}}};
                                                                     Prelude.False ->
                                                                    Prelude.Left
                                                                    ((:)
                                                                    (append
                                                                    "Not a valid boolean: "
                                                                    (append
                                                                    "'"
                                                                    (append h
                                                                    (append
                                                                    "', expected 'true' or 'false' at '"
                                                                    (append
                                                                    (concat_string_list
                                                                    ((:) h
                                                                    ((:) " "
                                                                    t)))
                                                                    "'.")))))
                                                                    ([]))};
                                                                     Prelude.False ->
                                                                    Prelude.Left
                                                                    ((:)
                                                                    (append
                                                                    "Not a valid boolean: "
                                                                    (append
                                                                    "'"
                                                                    (append h
                                                                    (append
                                                                    "', expected 'true' or 'false' at '"
                                                                    (append
                                                                    (concat_string_list
                                                                    ((:) h
                                                                    ((:) " "
                                                                    t)))
                                                                    "'.")))))
                                                                    ([]))})
                                                                    a2}};
                                                             Prelude.False ->
                                                              Prelude.Left
                                                              ((:)
                                                              (append
                                                                "Not a valid boolean: "
                                                                (append "'"
                                                                  (append h
                                                                    (append
                                                                    "', expected 'true' or 'false' at '"
                                                                    (append
                                                                    (concat_string_list
                                                                    ((:) h
                                                                    ((:) " "
                                                                    t)))
                                                                    "'.")))))
                                                              ([]))};
                                                           Prelude.False ->
                                                            Prelude.Left ((:)
                                                            (append
                                                              "Not a valid boolean: "
                                                              (append "'"
                                                                (append h
                                                                  (append
                                                                    "', expected 'true' or 'false' at '"
                                                                    (append
                                                                    (concat_string_list
                                                                    ((:) h
                                                                    ((:) " "
                                                                    t)))
                                                                    "'.")))))
                                                            ([]))}};
                                                       Prelude.False ->
                                                        Prelude.Left ((:)
                                                        (append
                                                          "Not a valid boolean: "
                                                          (append "'"
                                                            (append h
                                                              (append
                                                                "', expected 'true' or 'false' at '"
                                                                (append
                                                                  (concat_string_list
                                                                    ((:) h
                                                                    ((:) " "
                                                                    t)))
                                                                  "'.")))))
                                                        ([]))};
                                                     Prelude.False ->
                                                      Prelude.Left ((:)
                                                      (append
                                                        "Not a valid boolean: "
                                                        (append "'"
                                                          (append h
                                                            (append
                                                              "', expected 'true' or 'false' at '"
                                                              (append
                                                                (concat_string_list
                                                                  ((:) h ((:)
                                                                  " " t)))
                                                                "'.")))))
                                                      ([]))}}})
                                                a1}};
                                         Prelude.False -> Prelude.Left ((:)
                                          (append "Not a valid boolean: "
                                            (append "'"
                                              (append h
                                                (append
                                                  "', expected 'true' or 'false' at '"
                                                  (append
                                                    (concat_string_list ((:)
                                                      h ((:) " " t))) "'.")))))
                                          ([]))};
                                       Prelude.False -> Prelude.Left ((:)
                                        (append "Not a valid boolean: "
                                          (append "'"
                                            (append h
                                              (append
                                                "', expected 'true' or 'false' at '"
                                                (append
                                                  (concat_string_list ((:) h
                                                    ((:) " " t))) "'.")))))
                                        ([]))}}}}};
                             Prelude.False -> Prelude.Left ((:)
                              (append "Not a valid boolean: "
                                (append "'"
                                  (append h
                                    (append
                                      "', expected 'true' or 'false' at '"
                                      (append
                                        (concat_string_list ((:) h ((:) " "
                                          t))) "'."))))) ([]))})
                            a0}};
                     Prelude.False -> Prelude.Left ((:)
                      (append "Not a valid boolean: "
                        (append "'"
                          (append h
                            (append "', expected 'true' or 'false' at '"
                              (append
                                (concat_string_list ((:) h ((:) " " t)))
                                "'."))))) ([]))};
                   Prelude.False -> Prelude.Left ((:)
                    (append "Not a valid boolean: "
                      (append "'"
                        (append h
                          (append "', expected 'true' or 'false' at '"
                            (append (concat_string_list ((:) h ((:) " " t)))
                              "'."))))) ([]))}}};
             Prelude.False -> Prelude.Left ((:)
              (append "Not a valid boolean: "
                (append "'"
                  (append h
                    (append "', expected 'true' or 'false' at '"
                      (append (concat_string_list ((:) h ((:) " " t))) "'.")))))
              ([]))};
           Prelude.False ->
            case b1 of {
             Prelude.True ->
              case b2 of {
               Prelude.True -> Prelude.Left ((:)
                (append "Not a valid boolean: "
                  (append "'"
                    (append h
                      (append "', expected 'true' or 'false' at '"
                        (append (concat_string_list ((:) h ((:) " " t)))
                          "'."))))) ([]));
               Prelude.False ->
                case b3 of {
                 Prelude.True ->
                  case b4 of {
                   Prelude.True ->
                    case b5 of {
                     Prelude.True ->
                      case b6 of {
                       Prelude.True -> Prelude.Left ((:)
                        (append "Not a valid boolean: "
                          (append "'"
                            (append h
                              (append "', expected 'true' or 'false' at '"
                                (append
                                  (concat_string_list ((:) h ((:) " " t)))
                                  "'."))))) ([]));
                       Prelude.False ->
                        case s of {
                         ([]) -> Prelude.Left ((:)
                          (append "Not a valid boolean: "
                            (append "'"
                              (append h
                                (append "', expected 'true' or 'false' at '"
                                  (append
                                    (concat_string_list ((:) h ((:) " " t)))
                                    "'."))))) ([]));
                         (:) a0 s0 ->
                          (\f a -> f (Data.Bits.testBit (Data.Char.ord a) 0)
              (Data.Bits.testBit (Data.Char.ord a) 1)
              (Data.Bits.testBit (Data.Char.ord a) 2)
              (Data.Bits.testBit (Data.Char.ord a) 3)
              (Data.Bits.testBit (Data.Char.ord a) 4)
              (Data.Bits.testBit (Data.Char.ord a) 5)
              (Data.Bits.testBit (Data.Char.ord a) 6)
              (Data.Bits.testBit (Data.Char.ord a) 7))
                            (\b7 b8 b9 b10 b11 b12 b13 b14 ->
                            case b7 of {
                             Prelude.True -> Prelude.Left ((:)
                              (append "Not a valid boolean: "
                                (append "'"
                                  (append h
                                    (append
                                      "', expected 'true' or 'false' at '"
                                      (append
                                        (concat_string_list ((:) h ((:) " "
                                          t))) "'."))))) ([]));
                             Prelude.False ->
                              case b8 of {
                               Prelude.True ->
                                case b9 of {
                                 Prelude.True -> Prelude.Left ((:)
                                  (append "Not a valid boolean: "
                                    (append "'"
                                      (append h
                                        (append
                                          "', expected 'true' or 'false' at '"
                                          (append
                                            (concat_string_list ((:) h ((:)
                                              " " t))) "'."))))) ([]));
                                 Prelude.False ->
                                  case b10 of {
                                   Prelude.True -> Prelude.Left ((:)
                                    (append "Not a valid boolean: "
                                      (append "'"
                                        (append h
                                          (append
                                            "', expected 'true' or 'false' at '"
                                            (append
                                              (concat_string_list ((:) h ((:)
                                                " " t))) "'."))))) ([]));
                                   Prelude.False ->
                                    case b11 of {
                                     Prelude.True ->
                                      case b12 of {
                                       Prelude.True ->
                                        case b13 of {
                                         Prelude.True ->
                                          case b14 of {
                                           Prelude.True -> Prelude.Left ((:)
                                            (append "Not a valid boolean: "
                                              (append "'"
                                                (append h
                                                  (append
                                                    "', expected 'true' or 'false' at '"
                                                    (append
                                                      (concat_string_list
                                                        ((:) h ((:) " " t)))
                                                      "'."))))) ([]));
                                           Prelude.False ->
                                            case s0 of {
                                             ([]) -> Prelude.Left ((:)
                                              (append "Not a valid boolean: "
                                                (append "'"
                                                  (append h
                                                    (append
                                                      "', expected 'true' or 'false' at '"
                                                      (append
                                                        (concat_string_list
                                                          ((:) h ((:) " "
                                                          t))) "'.")))))
                                              ([]));
                                             (:) a1 s1 ->
                                              (\f a -> f (Data.Bits.testBit (Data.Char.ord a) 0)
              (Data.Bits.testBit (Data.Char.ord a) 1)
              (Data.Bits.testBit (Data.Char.ord a) 2)
              (Data.Bits.testBit (Data.Char.ord a) 3)
              (Data.Bits.testBit (Data.Char.ord a) 4)
              (Data.Bits.testBit (Data.Char.ord a) 5)
              (Data.Bits.testBit (Data.Char.ord a) 6)
              (Data.Bits.testBit (Data.Char.ord a) 7))
                                                (\b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                case b15 of {
                                                 Prelude.True ->
                                                  case b16 of {
                                                   Prelude.True ->
                                                    Prelude.Left ((:)
                                                    (append
                                                      "Not a valid boolean: "
                                                      (append "'"
                                                        (append h
                                                          (append
                                                            "', expected 'true' or 'false' at '"
                                                            (append
                                                              (concat_string_list
                                                                ((:) h ((:)
                                                                " " t)))
                                                              "'."))))) ([]));
                                                   Prelude.False ->
                                                    case b17 of {
                                                     Prelude.True ->
                                                      case b18 of {
                                                       Prelude.True ->
                                                        Prelude.Left ((:)
                                                        (append
                                                          "Not a valid boolean: "
                                                          (append "'"
                                                            (append h
                                                              (append
                                                                "', expected 'true' or 'false' at '"
                                                                (append
                                                                  (concat_string_list
                                                                    ((:) h
                                                                    ((:) " "
                                                                    t)))
                                                                  "'.")))))
                                                        ([]));
                                                       Prelude.False ->
                                                        case b19 of {
                                                         Prelude.True ->
                                                          case b20 of {
                                                           Prelude.True ->
                                                            case b21 of {
                                                             Prelude.True ->
                                                              case b22 of {
                                                               Prelude.True ->
                                                                Prelude.Left
                                                                ((:)
                                                                (append
                                                                  "Not a valid boolean: "
                                                                  (append "'"
                                                                    (append h
                                                                    (append
                                                                    "', expected 'true' or 'false' at '"
                                                                    (append
                                                                    (concat_string_list
                                                                    ((:) h
                                                                    ((:) " "
                                                                    t)))
                                                                    "'.")))))
                                                                ([]));
                                                               Prelude.False ->
                                                                case s1 of {
                                                                 ([]) ->
                                                                  Prelude.Left
                                                                  ((:)
                                                                  (append
                                                                    "Not a valid boolean: "
                                                                    (append
                                                                    "'"
                                                                    (append h
                                                                    (append
                                                                    "', expected 'true' or 'false' at '"
                                                                    (append
                                                                    (concat_string_list
                                                                    ((:) h
                                                                    ((:) " "
                                                                    t)))
                                                                    "'.")))))
                                                                  ([]));
                                                                 (:) a2 s2 ->
                                                                  (\f a -> f (Data.Bits.testBit (Data.Char.ord a) 0)
              (Data.Bits.testBit (Data.Char.ord a) 1)
              (Data.Bits.testBit (Data.Char.ord a) 2)
              (Data.Bits.testBit (Data.Char.ord a) 3)
              (Data.Bits.testBit (Data.Char.ord a) 4)
              (Data.Bits.testBit (Data.Char.ord a) 5)
              (Data.Bits.testBit (Data.Char.ord a) 6)
              (Data.Bits.testBit (Data.Char.ord a) 7))
                                                                    (\b23 b24 b25 b26 b27 b28 b29 b30 ->
                                                                    case b23 of {
                                                                     Prelude.True ->
                                                                    case b24 of {
                                                                     Prelude.True ->
                                                                    Prelude.Left
                                                                    ((:)
                                                                    (append
                                                                    "Not a valid boolean: "
                                                                    (append
                                                                    "'"
                                                                    (append h
                                                                    (append
                                                                    "', expected 'true' or 'false' at '"
                                                                    (append
                                                                    (concat_string_list
                                                                    ((:) h
                                                                    ((:) " "
                                                                    t)))
                                                                    "'.")))))
                                                                    ([]));
                                                                     Prelude.False ->
                                                                    case b25 of {
                                                                     Prelude.True ->
                                                                    case b26 of {
                                                                     Prelude.True ->
                                                                    Prelude.Left
                                                                    ((:)
                                                                    (append
                                                                    "Not a valid boolean: "
                                                                    (append
                                                                    "'"
                                                                    (append h
                                                                    (append
                                                                    "', expected 'true' or 'false' at '"
                                                                    (append
                                                                    (concat_string_list
                                                                    ((:) h
                                                                    ((:) " "
                                                                    t)))
                                                                    "'.")))))
                                                                    ([]));
                                                                     Prelude.False ->
                                                                    case b27 of {
                                                                     Prelude.True ->
                                                                    Prelude.Left
                                                                    ((:)
                                                                    (append
                                                                    "Not a valid boolean: "
                                                                    (append
                                                                    "'"
                                                                    (append h
                                                                    (append
                                                                    "', expected 'true' or 'false' at '"
                                                                    (append
                                                                    (concat_string_list
                                                                    ((:) h
                                                                    ((:) " "
                                                                    t)))
                                                                    "'.")))))
                                                                    ([]));
                                                                     Prelude.False ->
                                                                    case b28 of {
                                                                     Prelude.True ->
                                                                    case b29 of {
                                                                     Prelude.True ->
                                                                    case b30 of {
                                                                     Prelude.True ->
                                                                    Prelude.Left
                                                                    ((:)
                                                                    (append
                                                                    "Not a valid boolean: "
                                                                    (append
                                                                    "'"
                                                                    (append h
                                                                    (append
                                                                    "', expected 'true' or 'false' at '"
                                                                    (append
                                                                    (concat_string_list
                                                                    ((:) h
                                                                    ((:) " "
                                                                    t)))
                                                                    "'.")))))
                                                                    ([]));
                                                                     Prelude.False ->
                                                                    case s2 of {
                                                                     ([]) ->
                                                                    Prelude.Right
                                                                    ((,)
                                                                    (B_Const
                                                                    Prelude.True)
                                                                    t);
                                                                     (:) _
                                                                    _ ->
                                                                    Prelude.Left
                                                                    ((:)
                                                                    (append
                                                                    "Not a valid boolean: "
                                                                    (append
                                                                    "'"
                                                                    (append h
                                                                    (append
                                                                    "', expected 'true' or 'false' at '"
                                                                    (append
                                                                    (concat_string_list
                                                                    ((:) h
                                                                    ((:) " "
                                                                    t)))
                                                                    "'.")))))
                                                                    ([]))}};
                                                                     Prelude.False ->
                                                                    Prelude.Left
                                                                    ((:)
                                                                    (append
                                                                    "Not a valid boolean: "
                                                                    (append
                                                                    "'"
                                                                    (append h
                                                                    (append
                                                                    "', expected 'true' or 'false' at '"
                                                                    (append
                                                                    (concat_string_list
                                                                    ((:) h
                                                                    ((:) " "
                                                                    t)))
                                                                    "'.")))))
                                                                    ([]))};
                                                                     Prelude.False ->
                                                                    Prelude.Left
                                                                    ((:)
                                                                    (append
                                                                    "Not a valid boolean: "
                                                                    (append
                                                                    "'"
                                                                    (append h
                                                                    (append
                                                                    "', expected 'true' or 'false' at '"
                                                                    (append
                                                                    (concat_string_list
                                                                    ((:) h
                                                                    ((:) " "
                                                                    t)))
                                                                    "'.")))))
                                                                    ([]))}}};
                                                                     Prelude.False ->
                                                                    Prelude.Left
                                                                    ((:)
                                                                    (append
                                                                    "Not a valid boolean: "
                                                                    (append
                                                                    "'"
                                                                    (append h
                                                                    (append
                                                                    "', expected 'true' or 'false' at '"
                                                                    (append
                                                                    (concat_string_list
                                                                    ((:) h
                                                                    ((:) " "
                                                                    t)))
                                                                    "'.")))))
                                                                    ([]))}};
                                                                     Prelude.False ->
                                                                    Prelude.Left
                                                                    ((:)
                                                                    (append
                                                                    "Not a valid boolean: "
                                                                    (append
                                                                    "'"
                                                                    (append h
                                                                    (append
                                                                    "', expected 'true' or 'false' at '"
                                                                    (append
                                                                    (concat_string_list
                                                                    ((:) h
                                                                    ((:) " "
                                                                    t)))
                                                                    "'.")))))
                                                                    ([]))})
                                                                    a2}};
                                                             Prelude.False ->
                                                              Prelude.Left
                                                              ((:)
                                                              (append
                                                                "Not a valid boolean: "
                                                                (append "'"
                                                                  (append h
                                                                    (append
                                                                    "', expected 'true' or 'false' at '"
                                                                    (append
                                                                    (concat_string_list
                                                                    ((:) h
                                                                    ((:) " "
                                                                    t)))
                                                                    "'.")))))
                                                              ([]))};
                                                           Prelude.False ->
                                                            Prelude.Left ((:)
                                                            (append
                                                              "Not a valid boolean: "
                                                              (append "'"
                                                                (append h
                                                                  (append
                                                                    "', expected 'true' or 'false' at '"
                                                                    (append
                                                                    (concat_string_list
                                                                    ((:) h
                                                                    ((:) " "
                                                                    t)))
                                                                    "'.")))))
                                                            ([]))};
                                                         Prelude.False ->
                                                          Prelude.Left ((:)
                                                          (append
                                                            "Not a valid boolean: "
                                                            (append "'"
                                                              (append h
                                                                (append
                                                                  "', expected 'true' or 'false' at '"
                                                                  (append
                                                                    (concat_string_list
                                                                    ((:) h
                                                                    ((:) " "
                                                                    t)))
                                                                    "'.")))))
                                                          ([]))}};
                                                     Prelude.False ->
                                                      Prelude.Left ((:)
                                                      (append
                                                        "Not a valid boolean: "
                                                        (append "'"
                                                          (append h
                                                            (append
                                                              "', expected 'true' or 'false' at '"
                                                              (append
                                                                (concat_string_list
                                                                  ((:) h ((:)
                                                                  " " t)))
                                                                "'.")))))
                                                      ([]))}};
                                                 Prelude.False ->
                                                  Prelude.Left ((:)
                                                  (append
                                                    "Not a valid boolean: "
                                                    (append "'"
                                                      (append h
                                                        (append
                                                          "', expected 'true' or 'false' at '"
                                                          (append
                                                            (concat_string_list
                                                              ((:) h ((:) " "
                                                              t))) "'.")))))
                                                  ([]))})
                                                a1}};
                                         Prelude.False -> Prelude.Left ((:)
                                          (append "Not a valid boolean: "
                                            (append "'"
                                              (append h
                                                (append
                                                  "', expected 'true' or 'false' at '"
                                                  (append
                                                    (concat_string_list ((:)
                                                      h ((:) " " t))) "'.")))))
                                          ([]))};
                                       Prelude.False -> Prelude.Left ((:)
                                        (append "Not a valid boolean: "
                                          (append "'"
                                            (append h
                                              (append
                                                "', expected 'true' or 'false' at '"
                                                (append
                                                  (concat_string_list ((:) h
                                                    ((:) " " t))) "'.")))))
                                        ([]))};
                                     Prelude.False -> Prelude.Left ((:)
                                      (append "Not a valid boolean: "
                                        (append "'"
                                          (append h
                                            (append
                                              "', expected 'true' or 'false' at '"
                                              (append
                                                (concat_string_list ((:) h
                                                  ((:) " " t))) "'.")))))
                                      ([]))}}};
                               Prelude.False -> Prelude.Left ((:)
                                (append "Not a valid boolean: "
                                  (append "'"
                                    (append h
                                      (append
                                        "', expected 'true' or 'false' at '"
                                        (append
                                          (concat_string_list ((:) h ((:) " "
                                            t))) "'."))))) ([]))}})
                            a0}};
                     Prelude.False -> Prelude.Left ((:)
                      (append "Not a valid boolean: "
                        (append "'"
                          (append h
                            (append "', expected 'true' or 'false' at '"
                              (append
                                (concat_string_list ((:) h ((:) " " t)))
                                "'."))))) ([]))};
                   Prelude.False -> Prelude.Left ((:)
                    (append "Not a valid boolean: "
                      (append "'"
                        (append h
                          (append "', expected 'true' or 'false' at '"
                            (append (concat_string_list ((:) h ((:) " " t)))
                              "'."))))) ([]))};
                 Prelude.False -> Prelude.Left ((:)
                  (append "Not a valid boolean: "
                    (append "'"
                      (append h
                        (append "', expected 'true' or 'false' at '"
                          (append (concat_string_list ((:) h ((:) " " t)))
                            "'."))))) ([]))}};
             Prelude.False -> Prelude.Left ((:)
              (append "Not a valid boolean: "
                (append "'"
                  (append h
                    (append "', expected 'true' or 'false' at '"
                      (append (concat_string_list ((:) h ((:) " " t))) "'.")))))
              ([]))}}})
        a}}

parse_B_Not :: (Parser BExpr) -> Parser BExpr
parse_B_Not p =
  bind (parse_keyword "not") (\_ -> bind p (\b -> pure (B_Not b)))

parse_B_And :: (Parser BExpr) -> Parser BExpr
parse_B_And p =
  bind p (\b1 ->
    bind (parse_keyword "and") (\_ -> bind p (\b2 -> pure (B_And b1 b2))))

parse_B_Eq :: (Parser Expr) -> Parser BExpr
parse_B_Eq p =
  bind p (\a1 ->
    bind (parse_keyword "==") (\_ -> bind p (\a2 -> pure (B_Eq a1 a2))))

parse_B_Le :: (Parser AExpr) -> Parser BExpr
parse_B_Le p =
  bind p (\a1 ->
    bind (parse_keyword "<=") (\_ -> bind p (\a2 -> pure (B_Le a1 a2))))

parse_B_Func :: (Parser FExpr) -> Parser BExpr
parse_B_Func p =
  bind p (\f -> pure (B_Func f))

fail_parser :: Parser a1
fail_parser _ =
  Prelude.Left ((:) "Failed to parse." ([]))

parse_FExpr :: Prelude.Integer -> Parser FExpr
parse_FExpr n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> parse_F_Var)
    (\n' ->
    alternative
      (alternative
        (alternative
          (alternative
            (alternative (parse_F_Lambda (parse_FExpr n'))
              (parse_F_Apply (parse_FExpr n') (parse_Expr n')))
            (parse_F_Cond (parse_BExpr n') (parse_FExpr n') (parse_FExpr n')))
          (parse_F_Let (parse_FExpr n'))) (parse_Return (parse_Expr n')))
      parse_F_Var)
    n

parse_BExpr :: Prelude.Integer -> Parser BExpr
parse_BExpr n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> parse_B_Const)
    (\n' ->
    alternative
      (alternative
        (alternative
          (alternative
            (alternative parse_B_Const (parse_B_Not (parse_BExpr n')))
            (parse_B_And (parse_BExpr n'))) (parse_B_Eq (parse_Expr n')))
        (parse_B_Le (parse_AExpr n'))) (parse_B_Func (parse_FExpr n')))
    n

parse_AExpr :: Prelude.Integer -> Parser AExpr
parse_AExpr n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> fail_parser)
    (\_ -> alternative parse_A_Const parse_A_Op_Expr)
    n

parse_Expr :: Prelude.Integer -> Parser Expr
parse_Expr n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> fail_parser)
    (\n' input ->
    case input of {
     ([]) -> Prelude.Left ((:) "Nothing to parse." ([]));
     (:) h t ->
      let {filtered_var = parse (parse_AExpr n') (concat_string_list input)}
      in
      case filtered_var of {
       Prelude.Left _ ->
        let {
         filtered_var0 = parse (parse_BExpr n') (concat_string_list input)}
        in
        case filtered_var0 of {
         Prelude.Left _ -> Prelude.Left ((:)
          (append "Not a valid expression: "
            (append "'"
              (append h
                (append
                  "', expected an arithmetic or boolean expression at '"
                  (append (concat_string_list ((:) h ((:) " " t))) "'.")))))
          ([]));
         Prelude.Right p ->
          case p of {
           (,) b t' -> Prelude.Right ((,) (E_Bool b) t')}};
       Prelude.Right p ->
        case p of {
         (,) a t' -> Prelude.Right ((,) (E_Arith a) t')}}})
    n

test_ex_hask_parse :: Prelude.Either (([]) Prelude.String)
                      ((,) FExpr (([]) Prelude.String))
test_ex_hask_parse =
  parse
    (parse_FExpr (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ
      0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    "let lol := \\x -> if 2 < 3 then return x else return x + 1 in lol 2"

