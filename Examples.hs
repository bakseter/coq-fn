module Examples where

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

eqb0 :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
eqb0 b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False ->
    case b2 of {
     Prelude.True -> Prelude.False;
     Prelude.False -> Prelude.True}}

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

data Env =
   EmptyEnv
 | ExtendEnv Prelude.String Value Env
data Value =
   V_Nat Prelude.Integer
 | V_Bool Prelude.Bool
 | V_Closure FExpr Env
 | V_ReturnValue Value

lookup_env :: Prelude.String -> Env -> Prelude.Either Prelude.String Value
lookup_env varName env =
  case env of {
   EmptyEnv -> Prelude.Left "(lookup_env) Error: Unbound variable";
   ExtendEnv name value restEnv ->
    case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
           varName name of {
     Prelude.True -> Prelude.Right value;
     Prelude.False -> lookup_env varName restEnv}}

feval :: FExpr -> Env -> Prelude.Integer -> Prelude.Either
         (([]) Prelude.String) Value
feval expr env max =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Prelude.Left ((:) "Error: Maximum recursion depth exceeded"
    ([])))
    (\max' ->
    case expr of {
     F_Var varName ->
      case lookup_env varName env of {
       Prelude.Left err -> Prelude.Left ((:)
        "(Feval) Error: Unbound variable" ((:) err ([])));
       Prelude.Right value -> Prelude.Right value};
     F_Lambda paramName bodyExpr -> Prelude.Right (V_Closure (F_Lambda
      paramName bodyExpr) env);
     F_Apply funcExpr argExpr ->
      case feval funcExpr env max' of {
       Prelude.Left _ -> Prelude.Left ((:)
        "(Feval) Error: Attempted to apply a non-function" ([]));
       Prelude.Right v ->
        case v of {
         V_Closure f _ ->
          case f of {
           F_Lambda paramName bodyExpr ->
            let {argValueSum = feval (F_Return argExpr) env max'} in
            case argValueSum of {
             Prelude.Left err -> Prelude.Left ((:)
              "(Feval) Error: Function argument did not evaluate to a value"
              err);
             Prelude.Right argValue ->
              let {extendedEnv = ExtendEnv paramName argValue env} in
              feval bodyExpr extendedEnv max'};
           _ -> Prelude.Left ((:)
            "(Feval) Error: Attempted to apply a non-function" ([]))};
         _ -> Prelude.Left ((:)
          "(Feval) Error: Attempted to apply a non-function" ([]))}};
     F_Cond condExpr trueExpr falseExpr ->
      case beval condExpr env max' of {
       Prelude.Left err -> Prelude.Left ((:)
        "(Feval) Error: Condition did not evaluate to a boolean" ((:) err
        ([])));
       Prelude.Right b ->
        case b of {
         Prelude.True -> feval trueExpr env max';
         Prelude.False -> feval falseExpr env max'}};
     F_Let varName bindExpr bodyExpr ->
      let {bindValueSum = feval bindExpr env max'} in
      case bindValueSum of {
       Prelude.Left err -> Prelude.Left ((:)
        "(Feval) Error: Let binding did not evaluate to a value" err);
       Prelude.Right bindValue ->
        let {extendedEnv = ExtendEnv varName bindValue env} in
        feval bodyExpr extendedEnv max'};
     F_Return retExpr ->
      case retExpr of {
       E_Bool b ->
        case (Prelude.<$>) (\x -> V_Bool x) (beval b env max') of {
         Prelude.Left err -> Prelude.Left ((:)
          "(Feval) Error: Boolean expression did not evaluate to a boolean"
          ((:) err ([])));
         Prelude.Right v -> Prelude.Right v};
       E_Arith a ->
        case (Prelude.<$>) (\x -> V_Nat x) (aeval a env max') of {
         Prelude.Left err -> Prelude.Left ((:)
          "(Feval) Error: Arithmetic expression did not evaluate to a number"
          ((:) err ([])));
         Prelude.Right v -> Prelude.Right v}}})
    max

aeval :: AExpr -> Env -> Prelude.Integer -> Prelude.Either Prelude.String
         Prelude.Integer
aeval a env max =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Prelude.Left
    "(Aeval) Error: Maximum recursion depth exceeded")
    (\max' ->
    case a of {
     A_Const n -> Prelude.Right n;
     A_Add a1 a2 ->
      (Prelude.<*>) ((Prelude.<$>) (Prelude.+) (aeval a1 env max'))
        (aeval a2 env max');
     A_Sub a1 a2 ->
      (Prelude.<*>) ((Prelude.<$>) sub (aeval a1 env max'))
        (aeval a2 env max');
     A_Mult a1 a2 ->
      (Prelude.<*>) ((Prelude.<$>) (Prelude.*) (aeval a1 env max'))
        (aeval a2 env max');
     A_Func f ->
      case feval f env max' of {
       Prelude.Left _ -> Prelude.Left
        "(Aeval) Error: Function did not evaluate to a number";
       Prelude.Right v ->
        case v of {
         V_Nat n -> Prelude.Right n;
         _ -> Prelude.Left
          "(Aeval) Error: Function did not evaluate to a number"}}})
    max

beval :: BExpr -> Env -> Prelude.Integer -> Prelude.Either Prelude.String
         Prelude.Bool
beval b env max =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Prelude.Left
    "(Beval) Error: Maximum recursion depth exceeded")
    (\max' ->
    case b of {
     B_Const b0 -> Prelude.Right b0;
     B_Not b' -> (Prelude.<$>) Prelude.not (beval b' env max');
     B_And b1 b2 ->
      (Prelude.<*>) ((Prelude.<$>) (Prelude.&&) (beval b1 env max'))
        (beval b2 env max');
     B_Eq e1 e2 ->
      case e1 of {
       E_Bool b1 ->
        case e2 of {
         E_Bool b2 ->
          (Prelude.<*>) ((Prelude.<$>) eqb0 (beval b1 env max'))
            (beval b2 env max');
         E_Arith _ -> Prelude.Left
          "(Beval) Error: Attempted to compare a boolean to a number"};
       E_Arith a1 ->
        case e2 of {
         E_Bool _ -> Prelude.Left
          "(Beval) Error: Attempted to compare a boolean to a number";
         E_Arith a2 ->
          (Prelude.<*>) ((Prelude.<$>) eqb (aeval a1 env max'))
            (aeval a2 env max')}};
     B_Le b1 b2 ->
      (Prelude.<*>) ((Prelude.<$>) leb (aeval b1 env max'))
        (aeval b2 env max');
     B_Func f ->
      case feval f env max' of {
       Prelude.Left _ -> Prelude.Left
        "(Beval) Error: Function did not evaluate to a boolean";
       Prelude.Right v ->
        case v of {
         V_Bool b0 -> Prelude.Right b0;
         _ -> Prelude.Left
          "(Beval) Error: Function did not evaluate to a boolean"}}})
    max

data FExpr0 =
   F_Var0 Prelude.String
 | F_Lambda0 Prelude.String FExpr0
 | F_Apply0 FExpr0 Expr0
 | F_Cond0 BExpr0 FExpr0 FExpr0
 | F_Let0 Prelude.String FExpr0 FExpr0
 | F_Return0 Expr0
data Expr0 =
   E_Bool0 BExpr0
 | E_Arith0 AExpr0
data BExpr0 =
   B_Const0 Prelude.Bool
 | B_Not0 BExpr0
 | B_And0 BExpr0 BExpr0
 | B_Eq0 Expr0 Expr0
 | B_Le0 AExpr0 AExpr0
 | B_Func0 FExpr0
data AExpr0 =
   A_Const0 Prelude.Integer
 | A_Add0 AExpr0 AExpr0
 | A_Sub0 AExpr0 AExpr0
 | A_Mult0 AExpr0 AExpr0
 | A_Func0 FExpr0

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

parse_A_Const :: Parser AExpr0
parse_A_Const =
  bind parse_nat (\n -> pure (A_Const0 n))

parse_A_Operators :: Parser (AExpr0 -> AExpr0 -> AExpr0)
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
                         ([]) -> Prelude.Right ((,) (\x x0 -> A_Add0 x x0) t);
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
                         ([]) -> Prelude.Right ((,) (\x x0 -> A_Sub0 x x0) t);
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
                         ([]) -> Prelude.Right ((,) (\x x0 -> A_Mult0 x x0)
                          t);
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

parse_A_Op_Expr :: Parser AExpr0
parse_A_Op_Expr =
  bind parse_A_Const (\n1 ->
    bind parse_A_Operators (\p -> bind parse_A_Const (\n2 -> pure (p n1 n2))))

parse_F_Var :: Parser FExpr0
parse_F_Var =
  bind parse_string (\x -> pure (F_Var0 x))

parse_F_Lambda :: (Parser FExpr0) -> Parser FExpr0
parse_F_Lambda p =
  bind (parse_keyword "\\") (\_ ->
    bind parse_string (\x ->
      bind (parse_keyword "->") (\_ -> bind p (\f -> pure (F_Lambda0 x f)))))

parse_F_Apply :: (Parser FExpr0) -> (Parser Expr0) -> Parser FExpr0
parse_F_Apply p1 p2 =
  bind p1 (\f -> bind p2 (\e -> pure (F_Apply0 f e)))

parse_F_Cond :: (Parser BExpr0) -> (Parser FExpr0) -> (Parser FExpr0) ->
                Parser FExpr0
parse_F_Cond p1 p2 p3 =
  bind (parse_keyword "if") (\_ ->
    bind p1 (\b ->
      bind (parse_keyword "then") (\_ ->
        bind p2 (\f1 ->
          bind (parse_keyword "else") (\_ ->
            bind p3 (\f2 -> pure (F_Cond0 b f1 f2)))))))

parse_F_Let :: (Parser FExpr0) -> Parser FExpr0
parse_F_Let p =
  bind (parse_keyword "let") (\_ ->
    bind parse_string (\x ->
      bind (parse_keyword ":=") (\_ ->
        bind p (\f1 ->
          bind (parse_keyword "in") (\_ ->
            bind p (\f2 -> pure (F_Let0 x f1 f2)))))))

parse_Return :: (Parser Expr0) -> Parser FExpr0
parse_Return p =
  bind (parse_keyword "return") (\_ -> bind p (\a -> pure (F_Return0 a)))

parse_B_Const :: Parser BExpr0
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
                                                                    (B_Const0
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
                                                                    (B_Const0
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

parse_B_Not :: (Parser BExpr0) -> Parser BExpr0
parse_B_Not p =
  bind (parse_keyword "not") (\_ -> bind p (\b -> pure (B_Not0 b)))

parse_B_And :: (Parser BExpr0) -> Parser BExpr0
parse_B_And p =
  bind p (\b1 ->
    bind (parse_keyword "and") (\_ -> bind p (\b2 -> pure (B_And0 b1 b2))))

parse_B_Eq :: (Parser Expr0) -> Parser BExpr0
parse_B_Eq p =
  bind p (\a1 ->
    bind (parse_keyword "==") (\_ -> bind p (\a2 -> pure (B_Eq0 a1 a2))))

parse_B_Le :: (Parser AExpr0) -> Parser BExpr0
parse_B_Le p =
  bind p (\a1 ->
    bind (parse_keyword "<=") (\_ -> bind p (\a2 -> pure (B_Le0 a1 a2))))

parse_B_Func :: (Parser FExpr0) -> Parser BExpr0
parse_B_Func p =
  bind p (\f -> pure (B_Func0 f))

fail_parser :: Parser a1
fail_parser _ =
  Prelude.Left ((:) "Failed to parse." ([]))

parse_FExpr :: Prelude.Integer -> Parser FExpr0
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

parse_BExpr :: Prelude.Integer -> Parser BExpr0
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

parse_AExpr :: Prelude.Integer -> Parser AExpr0
parse_AExpr n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> fail_parser)
    (\_ -> alternative parse_A_Const parse_A_Op_Expr)
    n

parse_Expr :: Prelude.Integer -> Parser Expr0
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
           (,) b t' -> Prelude.Right ((,) (E_Bool0 b) t')}};
       Prelude.Right p ->
        case p of {
         (,) a t' -> Prelude.Right ((,) (E_Arith0 a) t')}}})
    n

test_ex_hask_parse :: Prelude.Either (([]) Prelude.String)
                      ((,) FExpr0 (([]) Prelude.String))
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

factorial :: FExpr
factorial =
  F_Let "factorial" (F_Lambda "n" (F_Cond (B_Le (A_Func (F_Var "n")) (A_Const
    (Prelude.succ 0))) (F_Return (E_Arith (A_Const (Prelude.succ 0))))
    (F_Return (E_Arith (A_Mult (A_Func (F_Var "n")) (A_Func (F_Apply (F_Var
    "factorial") (E_Arith (A_Sub (A_Func (F_Var "n")) (A_Const (Prelude.succ
    0))))))))))) (F_Apply (F_Var "factorial") (E_Arith (A_Func (F_Var
    "input"))))

factorial_eval :: Prelude.Integer -> Prelude.Either (([]) Prelude.String)
                  Value
factorial_eval n =
  feval factorial (ExtendEnv "input" (V_Nat n) EmptyEnv) (Prelude.succ
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
    (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

