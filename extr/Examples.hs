module Examples where

import qualified Prelude

snd :: ((,) a1 a2) -> a2
snd p =
  case p of {
   (,) _ y -> y}

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

rev :: (([]) a1) -> ([]) a1
rev l =
  case l of {
   ([]) -> ([]);
   (:) x l' -> app (rev l') ((:) x ([]))}

map :: (a1 -> a2) -> (([]) a1) -> ([]) a2
map f l =
  case l of {
   ([]) -> ([]);
   (:) a t -> (:) (f a) (map f t)}

fold_right :: (a2 -> a1 -> a1) -> a1 -> (([]) a2) -> a1
fold_right f a0 l =
  case l of {
   ([]) -> a0;
   (:) b t -> f b (fold_right f a0 t)}

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

data Expr =
   Let Prelude.String Expr Expr
 | Var Prelude.String
 | Lambda Prelude.String Expr
 | Apply Expr Expr
 | Cond Expr Expr Expr
 | Nat Prelude.Integer
 | Add Expr Expr
 | Sub Expr Expr
 | Mul Expr Expr
 | Bool Prelude.Bool
 | And Expr Expr
 | Eq Expr Expr

concat_string_list :: (([]) Prelude.String) -> Prelude.String
concat_string_list l =
  case l of {
   ([]) -> "";
   (:) h t -> append h (concat_string_list t)}

data Env =
   EmptyEnv
 | ExtendEnv Prelude.String Value Env
data Value =
   V_Nat Prelude.Integer
 | V_Bool Prelude.Bool
 | V_Closure Prelude.String Expr Env

lookup_env :: Prelude.String -> Env -> Prelude.Either Prelude.String Value
lookup_env varName env =
  case env of {
   EmptyEnv -> Prelude.Left
    (append "(lookup_env) Error: Unbound variable '" (append varName "'"));
   ExtendEnv name value restEnv ->
    case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
           varName name of {
     Prelude.True -> Prelude.Right value;
     Prelude.False -> lookup_env varName restEnv}}

value_to_string :: Value -> Prelude.String
value_to_string val =
  case val of {
   V_Nat _ -> "V_Nat";
   V_Bool b ->
    case b of {
     Prelude.True -> "V_Bool true";
     Prelude.False -> "V_Bool false"};
   V_Closure paramName _ _ -> append "(\206\187" (append paramName ")")}

eval :: Expr -> Env -> Prelude.Integer -> Prelude.Either
        ((,) ((,) Expr Env) (([]) Prelude.String)) Value
eval expr env max =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Prelude.Left ((,) ((,) expr env) ((:)
    "(eval) Error: Maximum recursion depth exceeded" ([]))))
    (\max' ->
    case expr of {
     Let varName bindExpr bodyExpr ->
      case eval bindExpr env max' of {
       Prelude.Left err -> Prelude.Left err;
       Prelude.Right val -> eval bodyExpr (ExtendEnv varName val env) max'};
     Var varName ->
      case lookup_env varName env of {
       Prelude.Left err -> Prelude.Left ((,) ((,) expr env) ((:)
        (append "(eval) Error: Unbound variable '" (append varName "'")) ((:)
        err ([]))));
       Prelude.Right value -> Prelude.Right value};
     Lambda paramName bodyExpr -> Prelude.Right (V_Closure paramName (Lambda
      paramName bodyExpr) env);
     Apply expr1 expr2 ->
      case eval expr1 env max' of {
       Prelude.Left err -> Prelude.Left err;
       Prelude.Right argValue ->
        case argValue of {
         V_Closure _ e _ ->
          case e of {
           Let _ _ _ ->
            case eval expr2 env max' of {
             Prelude.Left err -> Prelude.Left err;
             Prelude.Right v ->
              case v of {
               V_Closure _ e2 _ ->
                case e2 of {
                 Lambda paramName bodyExpr ->
                  eval bodyExpr (ExtendEnv paramName argValue env) max';
                 _ -> Prelude.Left ((,) ((,) expr env) ((:)
                  "Error: Application did not evaluate to a closure" ([])))};
               _ -> Prelude.Left ((,) ((,) expr env) ((:)
                "Error: Application did not evaluate to a closure" ([])))}};
           Var _ ->
            case eval expr2 env max' of {
             Prelude.Left err -> Prelude.Left err;
             Prelude.Right v ->
              case v of {
               V_Closure _ e0 _ ->
                case e0 of {
                 Lambda paramName bodyExpr ->
                  eval bodyExpr (ExtendEnv paramName argValue env) max';
                 _ -> Prelude.Left ((,) ((,) expr env) ((:)
                  "Error: Application did not evaluate to a closure" ([])))};
               _ -> Prelude.Left ((,) ((,) expr env) ((:)
                "Error: Application did not evaluate to a closure" ([])))}};
           Lambda paramName bodyExpr ->
            case eval expr2 env max' of {
             Prelude.Left err -> Prelude.Left err;
             Prelude.Right argValue0 ->
              eval bodyExpr (ExtendEnv paramName argValue0 env) max'};
           Cond _ _ _ ->
            case eval expr2 env max' of {
             Prelude.Left err -> Prelude.Left err;
             Prelude.Right v ->
              case v of {
               V_Closure _ e3 _ ->
                case e3 of {
                 Lambda paramName bodyExpr ->
                  eval bodyExpr (ExtendEnv paramName argValue env) max';
                 _ -> Prelude.Left ((,) ((,) expr env) ((:)
                  "Error: Application did not evaluate to a closure" ([])))};
               _ -> Prelude.Left ((,) ((,) expr env) ((:)
                "Error: Application did not evaluate to a closure" ([])))}};
           Nat _ ->
            case eval expr2 env max' of {
             Prelude.Left err -> Prelude.Left err;
             Prelude.Right v ->
              case v of {
               V_Closure _ e0 _ ->
                case e0 of {
                 Lambda paramName bodyExpr ->
                  eval bodyExpr (ExtendEnv paramName argValue env) max';
                 _ -> Prelude.Left ((,) ((,) expr env) ((:)
                  "Error: Application did not evaluate to a closure" ([])))};
               _ -> Prelude.Left ((,) ((,) expr env) ((:)
                "Error: Application did not evaluate to a closure" ([])))}};
           Bool _ ->
            case eval expr2 env max' of {
             Prelude.Left err -> Prelude.Left err;
             Prelude.Right v ->
              case v of {
               V_Closure _ e0 _ ->
                case e0 of {
                 Lambda paramName bodyExpr ->
                  eval bodyExpr (ExtendEnv paramName argValue env) max';
                 _ -> Prelude.Left ((,) ((,) expr env) ((:)
                  "Error: Application did not evaluate to a closure" ([])))};
               _ -> Prelude.Left ((,) ((,) expr env) ((:)
                "Error: Application did not evaluate to a closure" ([])))}};
           _ ->
            case eval expr2 env max' of {
             Prelude.Left err -> Prelude.Left err;
             Prelude.Right v ->
              case v of {
               V_Closure _ e2 _ ->
                case e2 of {
                 Lambda paramName bodyExpr ->
                  eval bodyExpr (ExtendEnv paramName argValue env) max';
                 _ -> Prelude.Left ((,) ((,) expr env) ((:)
                  "Error: Application did not evaluate to a closure" ([])))};
               _ -> Prelude.Left ((,) ((,) expr env) ((:)
                "Error: Application did not evaluate to a closure" ([])))}}};
         _ ->
          case eval expr2 env max' of {
           Prelude.Left err -> Prelude.Left err;
           Prelude.Right v ->
            case v of {
             V_Closure _ e _ ->
              case e of {
               Lambda paramName bodyExpr ->
                eval bodyExpr (ExtendEnv paramName argValue env) max';
               _ -> Prelude.Left ((,) ((,) expr env) ((:)
                "Error: Application did not evaluate to a closure" ([])))};
             _ -> Prelude.Left ((,) ((,) expr env) ((:)
              "Error: Application did not evaluate to a closure" ([])))}}}};
     Cond condExpr trueExpr falseExpr ->
      case eval condExpr env max' of {
       Prelude.Left p ->
        case p of {
         (,) _ err -> Prelude.Left ((,) ((,) expr env) ((:)
          "(eval) Error: Condition did not evaluate to a boolean" err))};
       Prelude.Right val ->
        case val of {
         V_Bool b ->
          case b of {
           Prelude.True -> eval trueExpr env max';
           Prelude.False -> eval falseExpr env max'};
         _ -> Prelude.Left ((,) ((,) expr env) ((:)
          "(eval) Error: Condition did not evaluate to a boolean" ([])))}};
     Nat n -> Prelude.Right (V_Nat n);
     Add e1 e2 ->
      case eval e1 env max' of {
       Prelude.Left _ -> Prelude.Left ((,) ((,) expr env) ((:)
        "Error: Addition did not evaluate to a number" ([])));
       Prelude.Right v ->
        case v of {
         V_Nat n1 ->
          case eval e2 env max' of {
           Prelude.Left _ -> Prelude.Left ((,) ((,) expr env) ((:)
            "Error: Addition did not evaluate to a number" ([])));
           Prelude.Right v0 ->
            case v0 of {
             V_Nat n2 -> Prelude.Right (V_Nat ((Prelude.+) n1 n2));
             _ -> Prelude.Left ((,) ((,) expr env) ((:)
              "Error: Addition did not evaluate to a number" ([])))}};
         _ -> Prelude.Left ((,) ((,) expr env) ((:)
          "Error: Addition did not evaluate to a number" ([])))}};
     Sub e1 e2 ->
      case eval e1 env max' of {
       Prelude.Left _ -> Prelude.Left ((,) ((,) expr env) ((:)
        "Error: Subtraction did not evaluate to a number" ([])));
       Prelude.Right v ->
        case v of {
         V_Nat n1 ->
          case eval e2 env max' of {
           Prelude.Left _ -> Prelude.Left ((,) ((,) expr env) ((:)
            "Error: Subtraction did not evaluate to a number" ([])));
           Prelude.Right v0 ->
            case v0 of {
             V_Nat n2 -> Prelude.Right (V_Nat (sub n1 n2));
             _ -> Prelude.Left ((,) ((,) expr env) ((:)
              "Error: Subtraction did not evaluate to a number" ([])))}};
         _ -> Prelude.Left ((,) ((,) expr env) ((:)
          "Error: Subtraction did not evaluate to a number" ([])))}};
     Mul e1 e2 ->
      case eval e1 env max' of {
       Prelude.Left p ->
        case p of {
         (,) _ err ->
          case eval e2 env max' of {
           Prelude.Left _ -> Prelude.Left ((,) ((,) expr env) ((:)
            "E4rror: Multiplication did not evaluate to a number" ([])));
           Prelude.Right val -> Prelude.Left ((,) ((,) expr env) ((:)
            (append "3Error: Multiplication did not evaluate to a number: "
              (value_to_string val)) err))}};
       Prelude.Right val ->
        case val of {
         V_Nat n1 ->
          case eval e2 env max' of {
           Prelude.Left p ->
            case p of {
             (,) _ err -> Prelude.Left ((,) ((,) expr env) ((:)
              (append "2Error: Multiplication did not evaluate to a number: "
                (value_to_string val)) err))};
           Prelude.Right val' ->
            case val' of {
             V_Nat n2 -> Prelude.Right (V_Nat ((Prelude.*) n1 n2));
             V_Bool _ -> Prelude.Left ((,) ((,) expr env) ((:)
              (append "1Error: Multiplication did not evaluate to a number: "
                (append (value_to_string val) (value_to_string val'))) ([])));
             V_Closure paramName bodyExpr closureEnv -> Prelude.Right
              (V_Closure paramName (Mul (Nat n1) bodyExpr) closureEnv)}};
         V_Bool _ ->
          case eval e2 env max' of {
           Prelude.Left p ->
            case p of {
             (,) _ err -> Prelude.Left ((,) ((,) expr env) ((:)
              (append "2Error: Multiplication did not evaluate to a number: "
                (value_to_string val)) err))};
           Prelude.Right val' -> Prelude.Left ((,) ((,) expr env) ((:)
            (append "1Error: Multiplication did not evaluate to a number: "
              (append (value_to_string val) (value_to_string val'))) ([])))};
         V_Closure paramName1 bodyExpr1 closureEnv1 ->
          case eval e2 env max' of {
           Prelude.Left p ->
            case p of {
             (,) _ err -> Prelude.Left ((,) ((,) expr env) ((:)
              (append "2Error: Multiplication did not evaluate to a number: "
                (value_to_string val)) err))};
           Prelude.Right val' ->
            case val' of {
             V_Nat n2 -> Prelude.Right (V_Closure paramName1 (Mul bodyExpr1
              (Nat n2)) closureEnv1);
             V_Bool _ -> Prelude.Left ((,) ((,) expr env) ((:)
              (append "1Error: Multiplication did not evaluate to a number: "
                (append (value_to_string val) (value_to_string val'))) ([])));
             V_Closure _ bodyExpr2 _ -> Prelude.Right (V_Closure paramName1
              (Mul bodyExpr1 (Apply bodyExpr2 (Var paramName1))) closureEnv1)}}}};
     Bool b -> Prelude.Right (V_Bool b);
     And e1 e2 ->
      case eval e1 env max' of {
       Prelude.Left _ -> Prelude.Left ((,) ((,) expr env) ((:)
        "Error: And did not evaluate to a boolean" ([])));
       Prelude.Right v ->
        case v of {
         V_Bool b1 ->
          case eval e2 env max' of {
           Prelude.Left _ -> Prelude.Left ((,) ((,) expr env) ((:)
            "Error: And did not evaluate to a boolean" ([])));
           Prelude.Right v0 ->
            case v0 of {
             V_Bool b2 -> Prelude.Right (V_Bool ((Prelude.&&) b1 b2));
             _ -> Prelude.Left ((,) ((,) expr env) ((:)
              "Error: And did not evaluate to a boolean" ([])))}};
         _ -> Prelude.Left ((,) ((,) expr env) ((:)
          "Error: And did not evaluate to a boolean" ([])))}};
     Eq e1 e2 ->
      case eval e1 env max' of {
       Prelude.Left _ -> Prelude.Left ((,) ((,) expr env) ((:)
        "Error: Cannot compare values of non-equal types" ([])));
       Prelude.Right v ->
        case v of {
         V_Nat n1 ->
          case eval e2 env max' of {
           Prelude.Left _ -> Prelude.Left ((,) ((,) expr env) ((:)
            "Error: Cannot compare values of non-equal types" ([])));
           Prelude.Right v0 ->
            case v0 of {
             V_Nat n2 -> Prelude.Right (V_Bool (eqb n1 n2));
             _ -> Prelude.Left ((,) ((,) expr env) ((:)
              "Error: Cannot compare values of non-equal types" ([])))}};
         V_Bool b1 ->
          case eval e2 env max' of {
           Prelude.Left _ -> Prelude.Left ((,) ((,) expr env) ((:)
            "Error: Cannot compare values of non-equal types" ([])));
           Prelude.Right v0 ->
            case v0 of {
             V_Bool b2 -> Prelude.Right (V_Bool (eqb0 b1 b2));
             _ -> Prelude.Left ((,) ((,) expr env) ((:)
              "Error: Cannot compare values of non-equal types" ([])))}};
         V_Closure _ _ _ -> Prelude.Left ((,) ((,) expr env) ((:)
          "Error: Cannot compare values of non-equal types" ([])))}}})
    max

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

string_of_list :: (([]) Prelude.Char) -> Prelude.String
string_of_list xs =
  fold_right (\x x0 -> (:) x x0) "" xs

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

tokenize_helper :: Chartype -> (([]) Prelude.Char) -> (([]) Prelude.Char) ->
                   ([]) (([]) Prelude.Char)
tokenize_helper cls acc xs =
  let {tk = case acc of {
             ([]) -> ([]);
             (:) _ _ -> (:) (rev acc) ([])}} in
  case xs of {
   ([]) -> tk;
   (:) x xs' ->
    case cls of {
     White ->
      case classifyChar x of {
       White ->
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
             Prelude.True -> app tk (tokenize_helper White ([]) xs');
             Prelude.False ->
              case b1 of {
               Prelude.True -> app tk (tokenize_helper White ([]) xs');
               Prelude.False ->
                case b2 of {
                 Prelude.True ->
                  case b3 of {
                   Prelude.True -> app tk (tokenize_helper White ([]) xs');
                   Prelude.False ->
                    case b4 of {
                     Prelude.True ->
                      case b5 of {
                       Prelude.True ->
                        app tk (tokenize_helper White ([]) xs');
                       Prelude.False ->
                        case b6 of {
                         Prelude.True ->
                          app tk (tokenize_helper White ([]) xs');
                         Prelude.False ->
                          app tk ((:) ((:) ')' ([]))
                            (tokenize_helper Other ([]) xs'))}};
                     Prelude.False -> app tk (tokenize_helper White ([]) xs')}};
                 Prelude.False -> app tk (tokenize_helper White ([]) xs')}}};
           Prelude.False ->
            case b0 of {
             Prelude.True -> app tk (tokenize_helper White ([]) xs');
             Prelude.False ->
              case b1 of {
               Prelude.True -> app tk (tokenize_helper White ([]) xs');
               Prelude.False ->
                case b2 of {
                 Prelude.True ->
                  case b3 of {
                   Prelude.True -> app tk (tokenize_helper White ([]) xs');
                   Prelude.False ->
                    case b4 of {
                     Prelude.True ->
                      case b5 of {
                       Prelude.True ->
                        app tk (tokenize_helper White ([]) xs');
                       Prelude.False ->
                        case b6 of {
                         Prelude.True ->
                          app tk (tokenize_helper White ([]) xs');
                         Prelude.False ->
                          app tk ((:) ((:) '(' ([]))
                            (tokenize_helper Other ([]) xs'))}};
                     Prelude.False -> app tk (tokenize_helper White ([]) xs')}};
                 Prelude.False -> app tk (tokenize_helper White ([]) xs')}}}})
          x;
       Other ->
        let {tp = Other} in
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
             Prelude.True -> app tk (tokenize_helper tp ((:) x ([])) xs');
             Prelude.False ->
              case b1 of {
               Prelude.True -> app tk (tokenize_helper tp ((:) x ([])) xs');
               Prelude.False ->
                case b2 of {
                 Prelude.True ->
                  case b3 of {
                   Prelude.True ->
                    app tk (tokenize_helper tp ((:) x ([])) xs');
                   Prelude.False ->
                    case b4 of {
                     Prelude.True ->
                      case b5 of {
                       Prelude.True ->
                        app tk (tokenize_helper tp ((:) x ([])) xs');
                       Prelude.False ->
                        case b6 of {
                         Prelude.True ->
                          app tk (tokenize_helper tp ((:) x ([])) xs');
                         Prelude.False ->
                          app tk ((:) ((:) ')' ([]))
                            (tokenize_helper Other ([]) xs'))}};
                     Prelude.False ->
                      app tk (tokenize_helper tp ((:) x ([])) xs')}};
                 Prelude.False ->
                  app tk (tokenize_helper tp ((:) x ([])) xs')}}};
           Prelude.False ->
            case b0 of {
             Prelude.True -> app tk (tokenize_helper tp ((:) x ([])) xs');
             Prelude.False ->
              case b1 of {
               Prelude.True -> app tk (tokenize_helper tp ((:) x ([])) xs');
               Prelude.False ->
                case b2 of {
                 Prelude.True ->
                  case b3 of {
                   Prelude.True ->
                    app tk (tokenize_helper tp ((:) x ([])) xs');
                   Prelude.False ->
                    case b4 of {
                     Prelude.True ->
                      case b5 of {
                       Prelude.True ->
                        app tk (tokenize_helper tp ((:) x ([])) xs');
                       Prelude.False ->
                        case b6 of {
                         Prelude.True ->
                          app tk (tokenize_helper tp ((:) x ([])) xs');
                         Prelude.False ->
                          app tk ((:) ((:) '(' ([]))
                            (tokenize_helper Other ([]) xs'))}};
                     Prelude.False ->
                      app tk (tokenize_helper tp ((:) x ([])) xs')}};
                 Prelude.False ->
                  app tk (tokenize_helper tp ((:) x ([])) xs')}}}})
          x;
       x0 ->
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
             Prelude.True -> app tk (tokenize_helper x0 ((:) x ([])) xs');
             Prelude.False ->
              case b1 of {
               Prelude.True -> app tk (tokenize_helper x0 ((:) x ([])) xs');
               Prelude.False ->
                case b2 of {
                 Prelude.True ->
                  case b3 of {
                   Prelude.True ->
                    app tk (tokenize_helper x0 ((:) x ([])) xs');
                   Prelude.False ->
                    case b4 of {
                     Prelude.True ->
                      case b5 of {
                       Prelude.True ->
                        app tk (tokenize_helper x0 ((:) x ([])) xs');
                       Prelude.False ->
                        case b6 of {
                         Prelude.True ->
                          app tk (tokenize_helper x0 ((:) x ([])) xs');
                         Prelude.False ->
                          app tk ((:) ((:) ')' ([]))
                            (tokenize_helper Other ([]) xs'))}};
                     Prelude.False ->
                      app tk (tokenize_helper x0 ((:) x ([])) xs')}};
                 Prelude.False ->
                  app tk (tokenize_helper x0 ((:) x ([])) xs')}}};
           Prelude.False ->
            case b0 of {
             Prelude.True -> app tk (tokenize_helper x0 ((:) x ([])) xs');
             Prelude.False ->
              case b1 of {
               Prelude.True -> app tk (tokenize_helper x0 ((:) x ([])) xs');
               Prelude.False ->
                case b2 of {
                 Prelude.True ->
                  case b3 of {
                   Prelude.True ->
                    app tk (tokenize_helper x0 ((:) x ([])) xs');
                   Prelude.False ->
                    case b4 of {
                     Prelude.True ->
                      case b5 of {
                       Prelude.True ->
                        app tk (tokenize_helper x0 ((:) x ([])) xs');
                       Prelude.False ->
                        case b6 of {
                         Prelude.True ->
                          app tk (tokenize_helper x0 ((:) x ([])) xs');
                         Prelude.False ->
                          app tk ((:) ((:) '(' ([]))
                            (tokenize_helper Other ([]) xs'))}};
                     Prelude.False ->
                      app tk (tokenize_helper x0 ((:) x ([])) xs')}};
                 Prelude.False ->
                  app tk (tokenize_helper x0 ((:) x ([])) xs')}}}})
          x};
     Alpha ->
      case classifyChar x of {
       White ->
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
             Prelude.True -> app tk (tokenize_helper White ([]) xs');
             Prelude.False ->
              case b1 of {
               Prelude.True -> app tk (tokenize_helper White ([]) xs');
               Prelude.False ->
                case b2 of {
                 Prelude.True ->
                  case b3 of {
                   Prelude.True -> app tk (tokenize_helper White ([]) xs');
                   Prelude.False ->
                    case b4 of {
                     Prelude.True ->
                      case b5 of {
                       Prelude.True ->
                        app tk (tokenize_helper White ([]) xs');
                       Prelude.False ->
                        case b6 of {
                         Prelude.True ->
                          app tk (tokenize_helper White ([]) xs');
                         Prelude.False ->
                          app tk ((:) ((:) ')' ([]))
                            (tokenize_helper Other ([]) xs'))}};
                     Prelude.False -> app tk (tokenize_helper White ([]) xs')}};
                 Prelude.False -> app tk (tokenize_helper White ([]) xs')}}};
           Prelude.False ->
            case b0 of {
             Prelude.True -> app tk (tokenize_helper White ([]) xs');
             Prelude.False ->
              case b1 of {
               Prelude.True -> app tk (tokenize_helper White ([]) xs');
               Prelude.False ->
                case b2 of {
                 Prelude.True ->
                  case b3 of {
                   Prelude.True -> app tk (tokenize_helper White ([]) xs');
                   Prelude.False ->
                    case b4 of {
                     Prelude.True ->
                      case b5 of {
                       Prelude.True ->
                        app tk (tokenize_helper White ([]) xs');
                       Prelude.False ->
                        case b6 of {
                         Prelude.True ->
                          app tk (tokenize_helper White ([]) xs');
                         Prelude.False ->
                          app tk ((:) ((:) '(' ([]))
                            (tokenize_helper Other ([]) xs'))}};
                     Prelude.False -> app tk (tokenize_helper White ([]) xs')}};
                 Prelude.False -> app tk (tokenize_helper White ([]) xs')}}}})
          x;
       Alpha ->
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
             Prelude.True -> tokenize_helper Alpha ((:) x acc) xs';
             Prelude.False ->
              case b1 of {
               Prelude.True -> tokenize_helper Alpha ((:) x acc) xs';
               Prelude.False ->
                case b2 of {
                 Prelude.True ->
                  case b3 of {
                   Prelude.True -> tokenize_helper Alpha ((:) x acc) xs';
                   Prelude.False ->
                    case b4 of {
                     Prelude.True ->
                      case b5 of {
                       Prelude.True -> tokenize_helper Alpha ((:) x acc) xs';
                       Prelude.False ->
                        case b6 of {
                         Prelude.True ->
                          tokenize_helper Alpha ((:) x acc) xs';
                         Prelude.False ->
                          app tk ((:) ((:) ')' ([]))
                            (tokenize_helper Other ([]) xs'))}};
                     Prelude.False -> tokenize_helper Alpha ((:) x acc) xs'}};
                 Prelude.False -> tokenize_helper Alpha ((:) x acc) xs'}}};
           Prelude.False ->
            case b0 of {
             Prelude.True -> tokenize_helper Alpha ((:) x acc) xs';
             Prelude.False ->
              case b1 of {
               Prelude.True -> tokenize_helper Alpha ((:) x acc) xs';
               Prelude.False ->
                case b2 of {
                 Prelude.True ->
                  case b3 of {
                   Prelude.True -> tokenize_helper Alpha ((:) x acc) xs';
                   Prelude.False ->
                    case b4 of {
                     Prelude.True ->
                      case b5 of {
                       Prelude.True -> tokenize_helper Alpha ((:) x acc) xs';
                       Prelude.False ->
                        case b6 of {
                         Prelude.True ->
                          tokenize_helper Alpha ((:) x acc) xs';
                         Prelude.False ->
                          app tk ((:) ((:) '(' ([]))
                            (tokenize_helper Other ([]) xs'))}};
                     Prelude.False -> tokenize_helper Alpha ((:) x acc) xs'}};
                 Prelude.False -> tokenize_helper Alpha ((:) x acc) xs'}}}})
          x;
       Digit ->
        let {tp = Digit} in
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
             Prelude.True -> app tk (tokenize_helper tp ((:) x ([])) xs');
             Prelude.False ->
              case b1 of {
               Prelude.True -> app tk (tokenize_helper tp ((:) x ([])) xs');
               Prelude.False ->
                case b2 of {
                 Prelude.True ->
                  case b3 of {
                   Prelude.True ->
                    app tk (tokenize_helper tp ((:) x ([])) xs');
                   Prelude.False ->
                    case b4 of {
                     Prelude.True ->
                      case b5 of {
                       Prelude.True ->
                        app tk (tokenize_helper tp ((:) x ([])) xs');
                       Prelude.False ->
                        case b6 of {
                         Prelude.True ->
                          app tk (tokenize_helper tp ((:) x ([])) xs');
                         Prelude.False ->
                          app tk ((:) ((:) ')' ([]))
                            (tokenize_helper Other ([]) xs'))}};
                     Prelude.False ->
                      app tk (tokenize_helper tp ((:) x ([])) xs')}};
                 Prelude.False ->
                  app tk (tokenize_helper tp ((:) x ([])) xs')}}};
           Prelude.False ->
            case b0 of {
             Prelude.True -> app tk (tokenize_helper tp ((:) x ([])) xs');
             Prelude.False ->
              case b1 of {
               Prelude.True -> app tk (tokenize_helper tp ((:) x ([])) xs');
               Prelude.False ->
                case b2 of {
                 Prelude.True ->
                  case b3 of {
                   Prelude.True ->
                    app tk (tokenize_helper tp ((:) x ([])) xs');
                   Prelude.False ->
                    case b4 of {
                     Prelude.True ->
                      case b5 of {
                       Prelude.True ->
                        app tk (tokenize_helper tp ((:) x ([])) xs');
                       Prelude.False ->
                        case b6 of {
                         Prelude.True ->
                          app tk (tokenize_helper tp ((:) x ([])) xs');
                         Prelude.False ->
                          app tk ((:) ((:) '(' ([]))
                            (tokenize_helper Other ([]) xs'))}};
                     Prelude.False ->
                      app tk (tokenize_helper tp ((:) x ([])) xs')}};
                 Prelude.False ->
                  app tk (tokenize_helper tp ((:) x ([])) xs')}}}})
          x;
       Other ->
        let {tp = Other} in
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
             Prelude.True -> app tk (tokenize_helper tp ((:) x ([])) xs');
             Prelude.False ->
              case b1 of {
               Prelude.True -> app tk (tokenize_helper tp ((:) x ([])) xs');
               Prelude.False ->
                case b2 of {
                 Prelude.True ->
                  case b3 of {
                   Prelude.True ->
                    app tk (tokenize_helper tp ((:) x ([])) xs');
                   Prelude.False ->
                    case b4 of {
                     Prelude.True ->
                      case b5 of {
                       Prelude.True ->
                        app tk (tokenize_helper tp ((:) x ([])) xs');
                       Prelude.False ->
                        case b6 of {
                         Prelude.True ->
                          app tk (tokenize_helper tp ((:) x ([])) xs');
                         Prelude.False ->
                          app tk ((:) ((:) ')' ([]))
                            (tokenize_helper Other ([]) xs'))}};
                     Prelude.False ->
                      app tk (tokenize_helper tp ((:) x ([])) xs')}};
                 Prelude.False ->
                  app tk (tokenize_helper tp ((:) x ([])) xs')}}};
           Prelude.False ->
            case b0 of {
             Prelude.True -> app tk (tokenize_helper tp ((:) x ([])) xs');
             Prelude.False ->
              case b1 of {
               Prelude.True -> app tk (tokenize_helper tp ((:) x ([])) xs');
               Prelude.False ->
                case b2 of {
                 Prelude.True ->
                  case b3 of {
                   Prelude.True ->
                    app tk (tokenize_helper tp ((:) x ([])) xs');
                   Prelude.False ->
                    case b4 of {
                     Prelude.True ->
                      case b5 of {
                       Prelude.True ->
                        app tk (tokenize_helper tp ((:) x ([])) xs');
                       Prelude.False ->
                        case b6 of {
                         Prelude.True ->
                          app tk (tokenize_helper tp ((:) x ([])) xs');
                         Prelude.False ->
                          app tk ((:) ((:) '(' ([]))
                            (tokenize_helper Other ([]) xs'))}};
                     Prelude.False ->
                      app tk (tokenize_helper tp ((:) x ([])) xs')}};
                 Prelude.False ->
                  app tk (tokenize_helper tp ((:) x ([])) xs')}}}})
          x};
     Digit ->
      case classifyChar x of {
       White ->
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
             Prelude.True -> app tk (tokenize_helper White ([]) xs');
             Prelude.False ->
              case b1 of {
               Prelude.True -> app tk (tokenize_helper White ([]) xs');
               Prelude.False ->
                case b2 of {
                 Prelude.True ->
                  case b3 of {
                   Prelude.True -> app tk (tokenize_helper White ([]) xs');
                   Prelude.False ->
                    case b4 of {
                     Prelude.True ->
                      case b5 of {
                       Prelude.True ->
                        app tk (tokenize_helper White ([]) xs');
                       Prelude.False ->
                        case b6 of {
                         Prelude.True ->
                          app tk (tokenize_helper White ([]) xs');
                         Prelude.False ->
                          app tk ((:) ((:) ')' ([]))
                            (tokenize_helper Other ([]) xs'))}};
                     Prelude.False -> app tk (tokenize_helper White ([]) xs')}};
                 Prelude.False -> app tk (tokenize_helper White ([]) xs')}}};
           Prelude.False ->
            case b0 of {
             Prelude.True -> app tk (tokenize_helper White ([]) xs');
             Prelude.False ->
              case b1 of {
               Prelude.True -> app tk (tokenize_helper White ([]) xs');
               Prelude.False ->
                case b2 of {
                 Prelude.True ->
                  case b3 of {
                   Prelude.True -> app tk (tokenize_helper White ([]) xs');
                   Prelude.False ->
                    case b4 of {
                     Prelude.True ->
                      case b5 of {
                       Prelude.True ->
                        app tk (tokenize_helper White ([]) xs');
                       Prelude.False ->
                        case b6 of {
                         Prelude.True ->
                          app tk (tokenize_helper White ([]) xs');
                         Prelude.False ->
                          app tk ((:) ((:) '(' ([]))
                            (tokenize_helper Other ([]) xs'))}};
                     Prelude.False -> app tk (tokenize_helper White ([]) xs')}};
                 Prelude.False -> app tk (tokenize_helper White ([]) xs')}}}})
          x;
       Alpha ->
        let {tp = Alpha} in
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
             Prelude.True -> app tk (tokenize_helper tp ((:) x ([])) xs');
             Prelude.False ->
              case b1 of {
               Prelude.True -> app tk (tokenize_helper tp ((:) x ([])) xs');
               Prelude.False ->
                case b2 of {
                 Prelude.True ->
                  case b3 of {
                   Prelude.True ->
                    app tk (tokenize_helper tp ((:) x ([])) xs');
                   Prelude.False ->
                    case b4 of {
                     Prelude.True ->
                      case b5 of {
                       Prelude.True ->
                        app tk (tokenize_helper tp ((:) x ([])) xs');
                       Prelude.False ->
                        case b6 of {
                         Prelude.True ->
                          app tk (tokenize_helper tp ((:) x ([])) xs');
                         Prelude.False ->
                          app tk ((:) ((:) ')' ([]))
                            (tokenize_helper Other ([]) xs'))}};
                     Prelude.False ->
                      app tk (tokenize_helper tp ((:) x ([])) xs')}};
                 Prelude.False ->
                  app tk (tokenize_helper tp ((:) x ([])) xs')}}};
           Prelude.False ->
            case b0 of {
             Prelude.True -> app tk (tokenize_helper tp ((:) x ([])) xs');
             Prelude.False ->
              case b1 of {
               Prelude.True -> app tk (tokenize_helper tp ((:) x ([])) xs');
               Prelude.False ->
                case b2 of {
                 Prelude.True ->
                  case b3 of {
                   Prelude.True ->
                    app tk (tokenize_helper tp ((:) x ([])) xs');
                   Prelude.False ->
                    case b4 of {
                     Prelude.True ->
                      case b5 of {
                       Prelude.True ->
                        app tk (tokenize_helper tp ((:) x ([])) xs');
                       Prelude.False ->
                        case b6 of {
                         Prelude.True ->
                          app tk (tokenize_helper tp ((:) x ([])) xs');
                         Prelude.False ->
                          app tk ((:) ((:) '(' ([]))
                            (tokenize_helper Other ([]) xs'))}};
                     Prelude.False ->
                      app tk (tokenize_helper tp ((:) x ([])) xs')}};
                 Prelude.False ->
                  app tk (tokenize_helper tp ((:) x ([])) xs')}}}})
          x;
       Digit ->
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
             Prelude.True -> tokenize_helper Digit ((:) x acc) xs';
             Prelude.False ->
              case b1 of {
               Prelude.True -> tokenize_helper Digit ((:) x acc) xs';
               Prelude.False ->
                case b2 of {
                 Prelude.True ->
                  case b3 of {
                   Prelude.True -> tokenize_helper Digit ((:) x acc) xs';
                   Prelude.False ->
                    case b4 of {
                     Prelude.True ->
                      case b5 of {
                       Prelude.True -> tokenize_helper Digit ((:) x acc) xs';
                       Prelude.False ->
                        case b6 of {
                         Prelude.True ->
                          tokenize_helper Digit ((:) x acc) xs';
                         Prelude.False ->
                          app tk ((:) ((:) ')' ([]))
                            (tokenize_helper Other ([]) xs'))}};
                     Prelude.False -> tokenize_helper Digit ((:) x acc) xs'}};
                 Prelude.False -> tokenize_helper Digit ((:) x acc) xs'}}};
           Prelude.False ->
            case b0 of {
             Prelude.True -> tokenize_helper Digit ((:) x acc) xs';
             Prelude.False ->
              case b1 of {
               Prelude.True -> tokenize_helper Digit ((:) x acc) xs';
               Prelude.False ->
                case b2 of {
                 Prelude.True ->
                  case b3 of {
                   Prelude.True -> tokenize_helper Digit ((:) x acc) xs';
                   Prelude.False ->
                    case b4 of {
                     Prelude.True ->
                      case b5 of {
                       Prelude.True -> tokenize_helper Digit ((:) x acc) xs';
                       Prelude.False ->
                        case b6 of {
                         Prelude.True ->
                          tokenize_helper Digit ((:) x acc) xs';
                         Prelude.False ->
                          app tk ((:) ((:) '(' ([]))
                            (tokenize_helper Other ([]) xs'))}};
                     Prelude.False -> tokenize_helper Digit ((:) x acc) xs'}};
                 Prelude.False -> tokenize_helper Digit ((:) x acc) xs'}}}})
          x;
       Other ->
        let {tp = Other} in
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
             Prelude.True -> app tk (tokenize_helper tp ((:) x ([])) xs');
             Prelude.False ->
              case b1 of {
               Prelude.True -> app tk (tokenize_helper tp ((:) x ([])) xs');
               Prelude.False ->
                case b2 of {
                 Prelude.True ->
                  case b3 of {
                   Prelude.True ->
                    app tk (tokenize_helper tp ((:) x ([])) xs');
                   Prelude.False ->
                    case b4 of {
                     Prelude.True ->
                      case b5 of {
                       Prelude.True ->
                        app tk (tokenize_helper tp ((:) x ([])) xs');
                       Prelude.False ->
                        case b6 of {
                         Prelude.True ->
                          app tk (tokenize_helper tp ((:) x ([])) xs');
                         Prelude.False ->
                          app tk ((:) ((:) ')' ([]))
                            (tokenize_helper Other ([]) xs'))}};
                     Prelude.False ->
                      app tk (tokenize_helper tp ((:) x ([])) xs')}};
                 Prelude.False ->
                  app tk (tokenize_helper tp ((:) x ([])) xs')}}};
           Prelude.False ->
            case b0 of {
             Prelude.True -> app tk (tokenize_helper tp ((:) x ([])) xs');
             Prelude.False ->
              case b1 of {
               Prelude.True -> app tk (tokenize_helper tp ((:) x ([])) xs');
               Prelude.False ->
                case b2 of {
                 Prelude.True ->
                  case b3 of {
                   Prelude.True ->
                    app tk (tokenize_helper tp ((:) x ([])) xs');
                   Prelude.False ->
                    case b4 of {
                     Prelude.True ->
                      case b5 of {
                       Prelude.True ->
                        app tk (tokenize_helper tp ((:) x ([])) xs');
                       Prelude.False ->
                        case b6 of {
                         Prelude.True ->
                          app tk (tokenize_helper tp ((:) x ([])) xs');
                         Prelude.False ->
                          app tk ((:) ((:) '(' ([]))
                            (tokenize_helper Other ([]) xs'))}};
                     Prelude.False ->
                      app tk (tokenize_helper tp ((:) x ([])) xs')}};
                 Prelude.False ->
                  app tk (tokenize_helper tp ((:) x ([])) xs')}}}})
          x};
     Other ->
      case classifyChar x of {
       White ->
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
             Prelude.True -> app tk (tokenize_helper White ([]) xs');
             Prelude.False ->
              case b1 of {
               Prelude.True -> app tk (tokenize_helper White ([]) xs');
               Prelude.False ->
                case b2 of {
                 Prelude.True ->
                  case b3 of {
                   Prelude.True -> app tk (tokenize_helper White ([]) xs');
                   Prelude.False ->
                    case b4 of {
                     Prelude.True ->
                      case b5 of {
                       Prelude.True ->
                        app tk (tokenize_helper White ([]) xs');
                       Prelude.False ->
                        case b6 of {
                         Prelude.True ->
                          app tk (tokenize_helper White ([]) xs');
                         Prelude.False ->
                          app tk ((:) ((:) ')' ([]))
                            (tokenize_helper Other ([]) xs'))}};
                     Prelude.False -> app tk (tokenize_helper White ([]) xs')}};
                 Prelude.False -> app tk (tokenize_helper White ([]) xs')}}};
           Prelude.False ->
            case b0 of {
             Prelude.True -> app tk (tokenize_helper White ([]) xs');
             Prelude.False ->
              case b1 of {
               Prelude.True -> app tk (tokenize_helper White ([]) xs');
               Prelude.False ->
                case b2 of {
                 Prelude.True ->
                  case b3 of {
                   Prelude.True -> app tk (tokenize_helper White ([]) xs');
                   Prelude.False ->
                    case b4 of {
                     Prelude.True ->
                      case b5 of {
                       Prelude.True ->
                        app tk (tokenize_helper White ([]) xs');
                       Prelude.False ->
                        case b6 of {
                         Prelude.True ->
                          app tk (tokenize_helper White ([]) xs');
                         Prelude.False ->
                          app tk ((:) ((:) '(' ([]))
                            (tokenize_helper Other ([]) xs'))}};
                     Prelude.False -> app tk (tokenize_helper White ([]) xs')}};
                 Prelude.False -> app tk (tokenize_helper White ([]) xs')}}}})
          x;
       Other ->
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
             Prelude.True -> tokenize_helper Other ((:) x acc) xs';
             Prelude.False ->
              case b1 of {
               Prelude.True -> tokenize_helper Other ((:) x acc) xs';
               Prelude.False ->
                case b2 of {
                 Prelude.True ->
                  case b3 of {
                   Prelude.True -> tokenize_helper Other ((:) x acc) xs';
                   Prelude.False ->
                    case b4 of {
                     Prelude.True ->
                      case b5 of {
                       Prelude.True -> tokenize_helper Other ((:) x acc) xs';
                       Prelude.False ->
                        case b6 of {
                         Prelude.True ->
                          tokenize_helper Other ((:) x acc) xs';
                         Prelude.False ->
                          app tk ((:) ((:) ')' ([]))
                            (tokenize_helper Other ([]) xs'))}};
                     Prelude.False -> tokenize_helper Other ((:) x acc) xs'}};
                 Prelude.False -> tokenize_helper Other ((:) x acc) xs'}}};
           Prelude.False ->
            case b0 of {
             Prelude.True -> tokenize_helper Other ((:) x acc) xs';
             Prelude.False ->
              case b1 of {
               Prelude.True -> tokenize_helper Other ((:) x acc) xs';
               Prelude.False ->
                case b2 of {
                 Prelude.True ->
                  case b3 of {
                   Prelude.True -> tokenize_helper Other ((:) x acc) xs';
                   Prelude.False ->
                    case b4 of {
                     Prelude.True ->
                      case b5 of {
                       Prelude.True -> tokenize_helper Other ((:) x acc) xs';
                       Prelude.False ->
                        case b6 of {
                         Prelude.True ->
                          tokenize_helper Other ((:) x acc) xs';
                         Prelude.False ->
                          app tk ((:) ((:) '(' ([]))
                            (tokenize_helper Other ([]) xs'))}};
                     Prelude.False -> tokenize_helper Other ((:) x acc) xs'}};
                 Prelude.False -> tokenize_helper Other ((:) x acc) xs'}}}})
          x;
       x0 ->
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
             Prelude.True -> app tk (tokenize_helper x0 ((:) x ([])) xs');
             Prelude.False ->
              case b1 of {
               Prelude.True -> app tk (tokenize_helper x0 ((:) x ([])) xs');
               Prelude.False ->
                case b2 of {
                 Prelude.True ->
                  case b3 of {
                   Prelude.True ->
                    app tk (tokenize_helper x0 ((:) x ([])) xs');
                   Prelude.False ->
                    case b4 of {
                     Prelude.True ->
                      case b5 of {
                       Prelude.True ->
                        app tk (tokenize_helper x0 ((:) x ([])) xs');
                       Prelude.False ->
                        case b6 of {
                         Prelude.True ->
                          app tk (tokenize_helper x0 ((:) x ([])) xs');
                         Prelude.False ->
                          app tk ((:) ((:) ')' ([]))
                            (tokenize_helper Other ([]) xs'))}};
                     Prelude.False ->
                      app tk (tokenize_helper x0 ((:) x ([])) xs')}};
                 Prelude.False ->
                  app tk (tokenize_helper x0 ((:) x ([])) xs')}}};
           Prelude.False ->
            case b0 of {
             Prelude.True -> app tk (tokenize_helper x0 ((:) x ([])) xs');
             Prelude.False ->
              case b1 of {
               Prelude.True -> app tk (tokenize_helper x0 ((:) x ([])) xs');
               Prelude.False ->
                case b2 of {
                 Prelude.True ->
                  case b3 of {
                   Prelude.True ->
                    app tk (tokenize_helper x0 ((:) x ([])) xs');
                   Prelude.False ->
                    case b4 of {
                     Prelude.True ->
                      case b5 of {
                       Prelude.True ->
                        app tk (tokenize_helper x0 ((:) x ([])) xs');
                       Prelude.False ->
                        case b6 of {
                         Prelude.True ->
                          app tk (tokenize_helper x0 ((:) x ([])) xs');
                         Prelude.False ->
                          app tk ((:) ((:) '(' ([]))
                            (tokenize_helper Other ([]) xs'))}};
                     Prelude.False ->
                      app tk (tokenize_helper x0 ((:) x ([])) xs')}};
                 Prelude.False ->
                  app tk (tokenize_helper x0 ((:) x ([])) xs')}}}})
          x}}}

tokenize :: Prelude.String -> ([]) Prelude.String
tokenize s =
  map string_of_list (tokenize_helper White ([]) (list_of_string s))

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

bind_discard_L :: (Parser a1) -> (Parser a2) -> Parser a2
bind_discard_L p p' input =
  case p input of {
   Prelude.Left err -> Prelude.Left err;
   Prelude.Right p0 -> case p0 of {
                        (,) _ rest -> p' rest}}

alternative :: (Parser a1) -> (Parser a1) -> Parser a1
alternative p1 p2 input =
  case p1 input of {
   Prelude.Left err1 ->
    case p2 input of {
     Prelude.Left err2 -> Prelude.Left (app err1 err2);
     Prelude.Right p -> Prelude.Right p};
   Prelude.Right p -> Prelude.Right p}

fail_parser :: Parser a1
fail_parser _ =
  Prelude.Left ((:) "Failed to parse." ([]))

parse_map :: (a1 -> a2) -> (Parser a1) -> Parser a2
parse_map f p input =
  case p input of {
   Prelude.Left err -> Prelude.Left err;
   Prelude.Right p0 ->
    case p0 of {
     (,) result rest -> Prelude.Right ((,) (f result) rest)}}

parse :: (Parser a1) -> Prelude.String -> Prelude.Either
         (([]) Prelude.String) ((,) a1 (([]) Prelude.String))
parse p input =
  p (tokenize input)

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

parse_var_name :: Parser Prelude.String
parse_var_name input =
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

parse_Var :: Parser Expr
parse_Var =
  bind parse_var_name (\x -> pure (Var x))

parse_Add :: Parser (Expr -> Expr -> Expr)
parse_Add =
  bind_discard_L (parse_keyword "+") (pure (\x x0 -> Add x x0))

parse_Sub :: Parser (Expr -> Expr -> Expr)
parse_Sub =
  bind_discard_L (parse_keyword "-") (pure (\x x0 -> Sub x x0))

parse_Mul :: Parser (Expr -> Expr -> Expr)
parse_Mul =
  bind_discard_L (parse_keyword "*") (pure (\x x0 -> Mul x x0))

parse_Lambda :: (Parser Expr) -> Parser Expr
parse_Lambda p =
  bind_discard_L (parse_keyword "\\")
    (bind parse_var_name (\x ->
      bind_discard_L (parse_keyword "->") (bind p (\f -> pure (Lambda x f)))))

parse_Apply :: Parser (Expr -> Expr -> Expr)
parse_Apply =
  bind_discard_L (parse_keyword ".") (pure (\x x0 -> Apply x x0))

parse_Cond :: (Parser Expr) -> Parser Expr
parse_Cond p =
  bind_discard_L (parse_keyword "If")
    (bind p (\e1 ->
      bind_discard_L (parse_keyword "Then")
        (bind p (\e2 ->
          bind_discard_L (parse_keyword "Else")
            (bind p (\e3 -> pure (Cond e1 e2 e3)))))))

parse_Bool :: Parser Expr
parse_Bool =
  bind (alternative (parse_keyword "True") (parse_keyword "False")) (\p ->
    case p of {
     ([]) -> fail_parser;
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
         Prelude.True -> fail_parser;
         Prelude.False ->
          case b0 of {
           Prelude.True ->
            case b1 of {
             Prelude.True ->
              case b2 of {
               Prelude.True -> fail_parser;
               Prelude.False ->
                case b3 of {
                 Prelude.True -> fail_parser;
                 Prelude.False ->
                  case b4 of {
                   Prelude.True -> fail_parser;
                   Prelude.False ->
                    case b5 of {
                     Prelude.True ->
                      case b6 of {
                       Prelude.True -> fail_parser;
                       Prelude.False ->
                        case s of {
                         ([]) -> fail_parser;
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
                               Prelude.True -> fail_parser;
                               Prelude.False ->
                                case b9 of {
                                 Prelude.True -> fail_parser;
                                 Prelude.False ->
                                  case b10 of {
                                   Prelude.True -> fail_parser;
                                   Prelude.False ->
                                    case b11 of {
                                     Prelude.True -> fail_parser;
                                     Prelude.False ->
                                      case b12 of {
                                       Prelude.True ->
                                        case b13 of {
                                         Prelude.True ->
                                          case b14 of {
                                           Prelude.True -> fail_parser;
                                           Prelude.False ->
                                            case s0 of {
                                             ([]) -> fail_parser;
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
                                                 Prelude.True -> fail_parser;
                                                 Prelude.False ->
                                                  case b16 of {
                                                   Prelude.True ->
                                                    fail_parser;
                                                   Prelude.False ->
                                                    case b17 of {
                                                     Prelude.True ->
                                                      case b18 of {
                                                       Prelude.True ->
                                                        case b19 of {
                                                         Prelude.True ->
                                                          fail_parser;
                                                         Prelude.False ->
                                                          case b20 of {
                                                           Prelude.True ->
                                                            case b21 of {
                                                             Prelude.True ->
                                                              case b22 of {
                                                               Prelude.True ->
                                                                fail_parser;
                                                               Prelude.False ->
                                                                case s1 of {
                                                                 ([]) ->
                                                                  fail_parser;
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
                                                                    fail_parser;
                                                                     Prelude.False ->
                                                                    case b26 of {
                                                                     Prelude.True ->
                                                                    fail_parser;
                                                                     Prelude.False ->
                                                                    case b27 of {
                                                                     Prelude.True ->
                                                                    case b28 of {
                                                                     Prelude.True ->
                                                                    case b29 of {
                                                                     Prelude.True ->
                                                                    case b30 of {
                                                                     Prelude.True ->
                                                                    fail_parser;
                                                                     Prelude.False ->
                                                                    case s2 of {
                                                                     ([]) ->
                                                                    fail_parser;
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
                                                                    fail_parser;
                                                                     Prelude.False ->
                                                                    case b33 of {
                                                                     Prelude.True ->
                                                                    case b34 of {
                                                                     Prelude.True ->
                                                                    fail_parser;
                                                                     Prelude.False ->
                                                                    case b35 of {
                                                                     Prelude.True ->
                                                                    fail_parser;
                                                                     Prelude.False ->
                                                                    case b36 of {
                                                                     Prelude.True ->
                                                                    case b37 of {
                                                                     Prelude.True ->
                                                                    case b38 of {
                                                                     Prelude.True ->
                                                                    fail_parser;
                                                                     Prelude.False ->
                                                                    case s3 of {
                                                                     ([]) ->
                                                                    pure
                                                                    (Bool
                                                                    Prelude.False);
                                                                     (:) _
                                                                    _ ->
                                                                    fail_parser}};
                                                                     Prelude.False ->
                                                                    fail_parser};
                                                                     Prelude.False ->
                                                                    fail_parser}}};
                                                                     Prelude.False ->
                                                                    fail_parser}};
                                                                     Prelude.False ->
                                                                    fail_parser})
                                                                    a3}};
                                                                     Prelude.False ->
                                                                    fail_parser};
                                                                     Prelude.False ->
                                                                    fail_parser};
                                                                     Prelude.False ->
                                                                    fail_parser}}};
                                                                     Prelude.False ->
                                                                    fail_parser};
                                                                     Prelude.False ->
                                                                    fail_parser})
                                                                    a2}};
                                                             Prelude.False ->
                                                              fail_parser};
                                                           Prelude.False ->
                                                            fail_parser}};
                                                       Prelude.False ->
                                                        fail_parser};
                                                     Prelude.False ->
                                                      fail_parser}}})
                                                a1}};
                                         Prelude.False -> fail_parser};
                                       Prelude.False -> fail_parser}}}}};
                             Prelude.False -> fail_parser})
                            a0}};
                     Prelude.False -> fail_parser}}}};
             Prelude.False -> fail_parser};
           Prelude.False ->
            case b1 of {
             Prelude.True ->
              case b2 of {
               Prelude.True -> fail_parser;
               Prelude.False ->
                case b3 of {
                 Prelude.True ->
                  case b4 of {
                   Prelude.True -> fail_parser;
                   Prelude.False ->
                    case b5 of {
                     Prelude.True ->
                      case b6 of {
                       Prelude.True -> fail_parser;
                       Prelude.False ->
                        case s of {
                         ([]) -> fail_parser;
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
                             Prelude.True -> fail_parser;
                             Prelude.False ->
                              case b8 of {
                               Prelude.True ->
                                case b9 of {
                                 Prelude.True -> fail_parser;
                                 Prelude.False ->
                                  case b10 of {
                                   Prelude.True -> fail_parser;
                                   Prelude.False ->
                                    case b11 of {
                                     Prelude.True ->
                                      case b12 of {
                                       Prelude.True ->
                                        case b13 of {
                                         Prelude.True ->
                                          case b14 of {
                                           Prelude.True -> fail_parser;
                                           Prelude.False ->
                                            case s0 of {
                                             ([]) -> fail_parser;
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
                                                    fail_parser;
                                                   Prelude.False ->
                                                    case b17 of {
                                                     Prelude.True ->
                                                      case b18 of {
                                                       Prelude.True ->
                                                        fail_parser;
                                                       Prelude.False ->
                                                        case b19 of {
                                                         Prelude.True ->
                                                          case b20 of {
                                                           Prelude.True ->
                                                            case b21 of {
                                                             Prelude.True ->
                                                              case b22 of {
                                                               Prelude.True ->
                                                                fail_parser;
                                                               Prelude.False ->
                                                                case s1 of {
                                                                 ([]) ->
                                                                  fail_parser;
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
                                                                    fail_parser;
                                                                     Prelude.False ->
                                                                    case b25 of {
                                                                     Prelude.True ->
                                                                    case b26 of {
                                                                     Prelude.True ->
                                                                    fail_parser;
                                                                     Prelude.False ->
                                                                    case b27 of {
                                                                     Prelude.True ->
                                                                    fail_parser;
                                                                     Prelude.False ->
                                                                    case b28 of {
                                                                     Prelude.True ->
                                                                    case b29 of {
                                                                     Prelude.True ->
                                                                    case b30 of {
                                                                     Prelude.True ->
                                                                    fail_parser;
                                                                     Prelude.False ->
                                                                    case s2 of {
                                                                     ([]) ->
                                                                    pure
                                                                    (Bool
                                                                    Prelude.True);
                                                                     (:) _
                                                                    _ ->
                                                                    fail_parser}};
                                                                     Prelude.False ->
                                                                    fail_parser};
                                                                     Prelude.False ->
                                                                    fail_parser}}};
                                                                     Prelude.False ->
                                                                    fail_parser}};
                                                                     Prelude.False ->
                                                                    fail_parser})
                                                                    a2}};
                                                             Prelude.False ->
                                                              fail_parser};
                                                           Prelude.False ->
                                                            fail_parser};
                                                         Prelude.False ->
                                                          fail_parser}};
                                                     Prelude.False ->
                                                      fail_parser}};
                                                 Prelude.False -> fail_parser})
                                                a1}};
                                         Prelude.False -> fail_parser};
                                       Prelude.False -> fail_parser};
                                     Prelude.False -> fail_parser}}};
                               Prelude.False -> fail_parser}})
                            a0}};
                     Prelude.False -> fail_parser}};
                 Prelude.False -> fail_parser}};
             Prelude.False -> fail_parser}}})
        a})

parse_Nat :: Parser Expr
parse_Nat =
  parse_map (\x -> Nat x) parse_nat

parse_Eq :: (Parser Expr) -> Parser Expr
parse_Eq p =
  bind_discard_L (parse_keyword "{")
    (bind p (\a1 ->
      bind_discard_L (parse_keyword "==")
        (bind p (\a2 ->
          bind_discard_L (parse_keyword "}") (pure (Eq a1 a2))))))

parse_And :: Parser (Expr -> Expr -> Expr)
parse_And =
  bind_discard_L (parse_keyword "&&") (pure (\x x0 -> And x x0))

parse_Let :: (Parser Expr) -> Parser Expr
parse_Let p =
  bind_discard_L (parse_keyword "Let")
    (bind parse_var_name (\x ->
      bind_discard_L (parse_keyword ":=")
        (bind p (\f ->
          bind_discard_L (parse_keyword "In")
            (bind p (\f' -> pure (Let x f f')))))))

parse_Expr :: Prelude.Integer -> Parser Expr
parse_Expr n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> fail_parser)
    (\n' ->
    let {
     parse_Sub_Expr = bind_discard_L (parse_keyword "(")
                        (bind (parse_Expr n') (\x ->
                          bind_discard_L (parse_keyword ")") (pure x)))}
    in
    let {
     parse_Simple = alternative
                      (alternative
                        (alternative
                          (alternative
                            (alternative
                              (alternative
                                (alternative parse_Sub_Expr parse_Var)
                                (parse_Lambda (parse_Expr n'))) parse_Bool)
                            parse_Nat) (parse_Cond (parse_Expr n')))
                        (parse_Let (parse_Expr n')))
                      (parse_Eq (parse_Expr n'))}
    in
    let {
     parse_Complex = alternative
                       (alternative
                         (alternative (alternative parse_Add parse_Sub)
                           parse_Mul) parse_And) parse_Apply}
    in
    alternative
      (bind parse_Simple (\x ->
        bind parse_Complex (\op -> bind parse_Simple (\y -> pure (op x y)))))
      parse_Simple)
    n

execute :: Prelude.String -> Env -> Prelude.Integer -> Prelude.Either
           (([]) Prelude.String) Value
execute s e max =
  case parse
         (parse_Expr (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
           (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
           (Prelude.succ (Prelude.succ 0))))))))))) s of {
   Prelude.Left err -> Prelude.Left err;
   Prelude.Right p ->
    case p of {
     (,) f _ ->
      case eval f e max of {
       Prelude.Left err -> Prelude.Left (snd err);
       Prelude.Right v -> Prelude.Right v}}}

input_vars :: (([]) ((,) Prelude.String Prelude.Integer)) -> Env
input_vars assignments =
  fold_right (\assignment env ->
    case assignment of {
     (,) x n -> ExtendEnv x (V_Nat n) env}) EmptyEnv assignments

mult_str :: Prelude.String
mult_str =
  "Let mult := \\n -> \\m -> n * m In (mult . ione) . itwo"

parse_mult :: Prelude.Either (([]) Prelude.String)
              ((,) Expr (([]) Prelude.String))
parse_mult =
  parse
    (parse_Expr (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ 0))))))))))) mult_str

double_str :: Prelude.String
double_str =
  "Let double := \\n -> n * 2 In double . input"

parse_double :: Prelude.Either (([]) Prelude.String)
                ((,) Expr (([]) Prelude.String))
parse_double =
  parse
    (parse_Expr (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ 0))))))))))) double_str

parse_double_exec :: Prelude.Either (([]) Prelude.String) Value
parse_double_exec =
  execute double_str
    (input_vars ((:) ((,) "input" (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ 0))))))))))) ([]))) (Prelude.succ
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
    0))))))))))))))))))))))))))))))))))))))))))))))))))

factorial_str :: Prelude.String
factorial_str =
  "Let factorial :=\n      \\n ->\n        If {n == 1}\n        Then 1\n        Else n * (factorial . (n - 1))\n     In\n     factorial . input"

parse_factorial :: Prelude.Either (([]) Prelude.String)
                   ((,) Expr (([]) Prelude.String))
parse_factorial =
  parse
    (parse_Expr (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ 0))))))))))) factorial_str

parse_factorial_exec :: Prelude.Either (([]) Prelude.String) Value
parse_factorial_exec =
  execute factorial_str
    (input_vars ((:) ((,) "input" (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ 0)))))) ([]))) (Prelude.succ (Prelude.succ
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
    0))))))))))))))))))))))))))))))))))))))))))))))))))

