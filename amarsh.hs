{-# LANGUAGE MultiParamTypeClasses,FlexibleInstances #-}
import Prelude hiding ((.),id)
import Control.Category
import Control.Monad
import Data.Number.MPFR
import Numeric.Interval.Kaucher
import Control.Arrow

{------------ Basic types  ---------------------}

{- Approximations are represented with infinite lists. -}
data Approximate a = Cons a (Approximate a)
  deriving Show

{- Refining an approximation is the same as calling tail. -}
refine (Cons _ a) = a

{- We need to have bool class, since (&&), (||) work only on Bools. -}
class CBool a where
  (&.) :: a -> a -> a
  (|.) :: a -> a -> a
  top :: a
  bottom :: a

{- Strict ordering. TODO Try using two different types a b, so we can have for example an instance SOrd Real Q. -}
class CBool c => SOrd a c where
  (<.) :: a -> a -> c
  (>.) :: a -> a -> c
  x >. y = y <. x

{- First we tried putting a monad over approximations. In implementation
  of (>>=) we are forced to select an approximation, e.g. a diagonal over list of lists. -}

instance Functor Approximate where
  fmap f (Cons x xs) = Cons (f x) (fmap f xs)

instance Monad Approximate where
  return a = let l = Cons a l in l   {- infinite constant list -}
  (Cons x xs) >>= f = case f x of 
     (Cons y ys) -> (Cons y (xs >>= f))  {- TODO is this a diagonal? -}


{- To use an arrow, we need to approximate functions. We define a newtype, 
   because using a type alias prevents us from instantiating an Arrow over it. -}

newtype FunApprox b c = FunApprox (Approximate b -> Approximate c)

{- identity, composition -}
instance Category (FunApprox) where
  id = FunApprox (\x -> x)
  (FunApprox f) . (FunApprox g) = FunApprox (\x -> f (g x)) 

{- Helper functions for the next declaration. -}
appFA (FunApprox f) a = f a
firstFA (Cons (b,c) xs) = Cons b (firstFA xs)
secondFA (Cons (b,c) xs) = Cons c (secondFA xs)
zipFA (Cons b xs) (Cons c ys) = Cons (b,c) (zipFA xs ys)

{- The arrow.  -}
instance Arrow (FunApprox) where
  arr f = FunApprox (\(Cons x xs) -> Cons (f x) (appFA (arr f) xs))             {- Lift any function into approximation. -}
  first (FunApprox f) = FunApprox (\x -> zipFA (f (firstFA x)) (secondFA x))    {- TODO is this optimal? -}

{- Still being general. Adding lower and upper approximation -}
data LU a = LU { lo :: a, up :: a } deriving Show
type LUApproximate a = Approximate (LU a)
lower (Cons a _) = lo a
upper (Cons a _) = up a

{- By this point we have functions lower, upper and refine working on approximations. -}


{- Almost concrete types -}
type Q = MPFR
type Sigma = LUApproximate Bool
type DReal = LUApproximate (Interval Q)


{- Here is an example of an inferred type for a lower lambda in a cut. -}
test_delta :: (Num a, SOrd a b, CBool b) => a -> a -> b
test_delta x = (\l -> (l <. fromInteger 0) |. ((l*l) <. x))
test_epsilon x = (\u -> (u >. (fromInteger 0)) &. ((u*u) >. x)) 

{------------------- General implementation --------------------------------}
{- Types of following functions are all inferred -}

{- We use the following evaluation function on Sigma type -}

eval :: Eq a => Approximate (LU a) -> a
eval x = if (lower x) == (upper x) then lower x else eval (refine x)


{- Parallel or - returns which argument was selected, so it's stronger than the usual por. -}

data Selection = First | Second | Neither deriving Show

por :: Approximate (LU Bool) -> Approximate (LU Bool) -> Selection
por x y = case (lower x, lower y, upper x, upper y) of
  (True, _, _, _) -> First
  (_, True, _, _) -> Second
  (_, _, False, _)-> if eval y then Second else Neither
  (_, _, _, False)-> if eval x then First else Neither
  _               -> por (refine x) (refine y)


{- "either" - If we know the result of por is T, then we can use this. -}

eith :: Approximate (LU Bool) -> Approximate (LU Bool) -> Selection
eith x y = case (lower x, lower y, upper x, upper y) of
  (True, _, _, _) -> First
  (_, True, _, _) -> Second
  (_, _, False, _)-> Second
  (_, _, _, False)-> First 
  _              -> por (refine x) (refine y)
 

{- TODO trisection. This is a proper trisection only when the results are approximate -}

trisection :: Precision -> Interval Q -> (Q,Q)
trisection p i = let (a,b) = (inf i, sup i) in 
        (divi Down p (add Down p a b) 2, divi Up p (add Up p a b) 2)

back i = (sup i) ... (inf i)


liftq q = Cons ( LU { lo = q...q, up = q...q } ) (liftq q)

--liftq q = return (LU { lo = q...q, up = q...q }) :: DReal
cut :: (DReal -> Sigma) -> (DReal -> Sigma) -> Interval Q -> Precision -> DReal
cut d e i p =
  let i' = (let (m1,m2) = trisection p i in
             case eith (d (liftq m1)) (e (liftq m2)) of
               First ->   m1 ... (sup i)
               Second ->  (inf i) ... m2) in
    Cons LU {lo = i, up = back i} (cut d e i' (p+1))


{-------------------------------- Instances ----------------------------------}
{- We need to provide instances to morph test_delta :: (Num a, SOrd a b, CBool b) => a -> b
   into DReal -> Sigma -} 


{- Base case: Just for testing - a quick use of leaky MPFR, ignoring the roaunding -}
prec = fromInteger 10 :: Precision
instance Num Q where
  (+) = add Down prec
  (-) = sub Down prec
  (*) = mul Down prec
  negate = neg Down prec 
  abs = absD Down prec
  signum x = case sgn x of Just a -> fromInt Down prec a
  fromInteger = fromIntegerA Down prec

-- instance Num a => Num (Interval a)  -- already defined in Interval

{- This could be a monad -}
instance Num a => Num (LU a) where
  x + y = LU { lo = (lo x) + (lo y), up = (up x) + (up y) }
  x - y = LU { lo = (lo x) - (lo y), up = (up x) - (up y) }
  x * y = LU { lo = (lo x) * (lo y), up = (up x) * (up y) }
  negate x = LU { lo = negate (lo x), up = negate (up x) }
  fromInteger x = LU { lo = fromInteger x, up = fromInteger x }
  abs x = LU { lo = abs (lo x), up = abs (up x) }
  signum x = LU { lo = signum (lo x), up = signum (up x) }

{- Using a monad -}
instance Num a => Num (Approximate a) where
--instance (Monad m, Num a) => Num (m a) where  {- This instance causes problems. Haskell unifies m to LU -}
  (+) = liftM2 (+)
  (-) = liftM2 (-)
  (*) = liftM2 (*)
  negate = liftM negate
  abs = liftM abs
  signum = liftM signum
  fromInteger i = return (fromInteger i) 


instance Num b => Num (FunApprox a b) where
  e + f =  (arr (\(x,y)->x+y)) . (e &&& f)
  e - f =  (arr (\(x,y)->x-y)) . (e &&& f)
  e * f =  (arr (\(x,y)->x*y)) . (e &&& f)
  negate = arr negate
  abs = arr abs
  signum = arr signum
  fromInteger = arr fromInteger 


{- Base case -}
instance CBool Bool where
  (&.) = (&&)
  (|.) = (||)
  top = True
  bottom = False

{- Using a monad -}

--instance (Monad m, CBool b) => CBool (m b) where
instance CBool b => CBool (Approximate b) where
  (&.) = liftM2 (&.)
  (|.) = liftM2 (|.)
  top = return top
  bottom = return bottom


{- This could be a monad -}
instance CBool a => CBool (LU a) where
  x &. y = LU { lo = (lo x) &. (lo y), up = (up x) &. (up y) }
  x |. y = LU { lo = (lo x) |. (lo y), up = (up x) |. (up y) }
  top = LU { lo = top, up = top }
  bottom = LU { lo = bottom, up = bottom }

{- Base case -}
instance SOrd Q Bool where
  (<.) = less

{- Second base case -}
instance SOrd a b => SOrd (Interval a) b where
  x <. y = (sup x) <. (inf y)

{- This could be a monad. -}
instance SOrd a b => SOrd (LU (Interval a)) (LU b) where
  x <. y = LU { lo = (lo x) <. (lo y), up = (up x) <. (up y) }

{- Using a monad -}

instance SOrd a b => SOrd (Approximate a) (Approximate b) where
--instance (Monad m, SOrd a b) => SOrd (m a) (m b) where
  (<.) = liftM2 (<.)

--instance SOrd a b => SOrd (Approximate a) (Approximate b) where
--  x <. y = arr (\(x,y) -> x <. y) (x &&& y)

{--------------------------- Example -----------------------------------------------------}
thesqrt x = cut (\l -> (l <. (fromInteger 0)) |. ((l*l) <. x)) (\u -> (u >. (fromInteger 0)) &. ((u*u) >. x)) (0...10) (fromInteger 10)

approx n (Cons a as) = if n == 0 then [a] else a : approx (n-1) as

main  = print $ approx 10 (thesqrt 2)


loop :: (Approximate a -> Approximate a) -> a -> Approximate a
loop f i =
  let l = f (Cons i l) in l

 
