{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}

-- | Arithmetic with continued fractions.
--
-- The main type defined in this module is 'CFrac', which represents a real
-- number using a (simple) continued fraction.  Most of the use of 'CFrac'
-- happens via the standard numeric type classes, but there are some additional
-- functions defined here, as well.
--
-- Beware: A fundamental limitation of this approach is that exact arithmetic on
-- irrational numbers that should yield a rational result will instead fail to
-- terminate.  This happens because one must observe the entire infinitely long
-- irrational number in order to know with certainty that the result is, in
-- fact, exactly that rational number.
module CFrac
  ( -- * The 'CFrac' type
    CFrac (..),
    isCanonical,
    terms,
    fromTerms,
    convergents,
    toDecimal,

    -- * Common continued fractions
    sqrtInt,
    exactPi,
    exp1,

    -- * Generalized continued fractions
    GCFrac (..),
    toGCFrac,
    fromGCFrac,

    -- * Implementation details
    Mobius (..),
    cfMobius,
    Bimobius (..),
    cfBimobius,
    (<>||),
    (||<),
    (||>),
  )
where

import Data.Ratio (denominator, numerator, (%))
import Test.QuickCheck (Arbitrary (..))

-- | A real number represented as a sequence of terms, where each term is the
-- integer part of the value, and the tail represents the reciprocal of the
-- fractional part of the value.  @a :+/ b@ represents the value @a + 1 / b@.
--
-- Any rational number can be represented as a finite continued fraction, and
-- any real number can be represented as an infinite continued fraction, making
-- this a convenient representation for some forms of exact real arithmetic.
data CFrac where
  (:+/) :: Integer -> CFrac -> CFrac
  Inf :: CFrac

deriving instance Eq CFrac

deriving instance Show CFrac

infixr 5 :+/

instance Arbitrary CFrac where
  arbitrary = fromRational <$> arbitrary
  shrink = map fromRational . shrink . cfToRational

-- | The list of terms for a continued fraction.
terms :: CFrac -> [Integer]
terms Inf = []
terms (n :+/ x) = n : terms x

-- | The continued fraction with the given list of terms.
fromTerms :: [Integer] -> CFrac
fromTerms = foldr (:+/) Inf

cfFromFrac :: Integer -> Integer -> CFrac
cfFromFrac _ 0 = Inf
cfFromFrac n d = q :+/ cfFromFrac d r where (q, r) = n `quotRem` d
{-# INLINE [2] cfFromFrac #-}

cfNegate :: CFrac -> CFrac
cfNegate Inf = Inf
cfNegate (n :+/ x) = (-n) :+/ cfNegate x

-- | Euler's constant, as a continued fraction.
exp1 :: CFrac
exp1 = 2 :+/ fromTerms (concatMap (\n -> [1, 2 * n, 1]) [1 ..])

-- | Determines whether a continued fraction is in its canonical form.
isCanonical :: CFrac -> Bool
isCanonical Inf = True
isCanonical (_ :+/ Inf) = True
isCanonical (n :+/ cont@(m :+/ _))
  | n > 0 = isCanonicalPositive cont
  | n < 0 = isCanonicalNegative cont
  | m > 0 = isCanonicalPositive cont
  | m < 0 = isCanonicalNegative cont
  | otherwise = False

isCanonicalPositive :: CFrac -> Bool
isCanonicalPositive Inf = True
isCanonicalPositive (n :+/ _) | n <= 0 = False
isCanonicalPositive (1 :+/ Inf) = False
isCanonicalPositive (_ :+/ cont) = isCanonicalPositive cont

isCanonicalNegative :: CFrac -> Bool
isCanonicalNegative Inf = True
isCanonicalNegative (n :+/ _) | n >= 0 = False
isCanonicalNegative (-1 :+/ Inf) = False
isCanonicalNegative (_ :+/ cont) = isCanonicalNegative cont

-- | A mobius transformation, of the form @f(x) = (a * x + b) / (c * x + d)@.
-- This is part of the machinery for performing arithmetic on continued
-- fractions.
data Mobius where
  Mobius :: Integer -> Integer -> Integer -> Integer -> Mobius

deriving instance Eq Mobius

deriving instance Ord Mobius

deriving instance Show Mobius

instance Semigroup Mobius where
  Mobius a1 b1 c1 d1 <> Mobius a2 b2 c2 d2 =
    Mobius
      (a1 * a2 + b1 * c2)
      (a1 * b2 + b1 * d2)
      (c1 * a2 + d1 * c2)
      (c1 * b2 + d1 * d2)
  {-# INLINE (<>) #-}

instance Monoid Mobius where
  mempty = Mobius 1 0 0 1
  {-# INLINE mempty #-}

instance Arbitrary Mobius where
  arbitrary = do
    Mobius
      <$> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
  shrink (Mobius a b c d) =
    [Mobius a' b' c' d' | (a', b', c', d') <- shrink (a, b, c, d)]

-- | A list of convergents of a continued fraction.  These are, the best
-- rational approximations to a given value of each continued fraction length.
-- If the input is rational, the result is a finite list.  Otherwise, it's an
-- infinite list.
convergents :: CFrac -> [Rational]
convergents = go mempty
  where
    go _ Inf = []
    go m (n :+/ x) = mobiusLimit m' : go m' x
      where
        m' = m <> Mobius n 1 1 0
    mobiusLimit (Mobius a _ c _) = a % c

cfToRational :: CFrac -> Rational
cfToRational = go mempty
  where
    go (Mobius a _ c _) Inf = a % c
    go m (n :+/ x) = go (m <> Mobius n 1 1 0) x
{-# INLINE [2] cfToRational #-}

mobiusIntPart :: Integer -> Mobius -> Maybe Integer
mobiusIntPart sgn (Mobius a b c d)
  | signum c * sgn == signum d && c /= 0 && d /= 0 && n1 == n2 = Just n1
  | otherwise = Nothing
  where
    n1 = a `quot` c
    n2 = b `quot` d
{-# INLINE mobiusIntPart #-}

-- | Converts a continued fraction to a list of digits in the given base.  The
-- first element of the list is the whole number part, and the remainder are the
-- fractional digits.
toBase :: Int -> CFrac -> [Int]
toBase base = go mempty
  where
    go (Mobius 0 0 _ _) _ = []
    go m x
      | Just n <- mobiusIntPart (cfSignum x) m,
        let m' = Mobius (fromIntegral base) (-fromIntegral base * n) 0 1 <> m =
          fromInteger n : go m' x
    go m (n :+/ x) = go (m <> Mobius n 1 1 0) x
    go (Mobius a _ c _) Inf = go (Mobius a a c c) Inf

-- | Converts a continued fraction to its decimal representation.
toDecimal :: CFrac -> String
toDecimal Inf = "Inf"
toDecimal x
  | x >= 0 = case toBase 10 x of
      [] -> "0.0"
      [z] -> show z ++ ".0"
      (z : digits) -> show z ++ "." ++ concatMap show digits
  | otherwise = "-" ++ toDecimal (cfNegate x)

-- | A generalized continued fraction.  Whereas a standard continued fraction
-- (also knows as a simple continued fraction) has the form @n + 1 / x@, a
-- generalized continued fraction has the form @n + m / x@, which is here
-- written as @(n, m) :+#/ x@.
--
-- Not all generalized continued fractions converge at all, and when they do,
-- they are not unique.  However, some constants like pi, which don't have
-- obvious patterns as continued fractions, do have obvious patterns as
-- generalized continued fractions, making them a useful intermediate type for
-- defining some exact real numbers.
data GCFrac where
  (:+#/) :: (Integer, Integer) -> GCFrac -> GCFrac
  GInf :: GCFrac

deriving instance Show GCFrac

-- | Converts a simple continued fraction to a generalized continued fraction.
-- All numerators will be 1.
toGCFrac :: CFrac -> GCFrac
toGCFrac Inf = GInf
toGCFrac (n :+/ x) = (n, 1) :+#/ toGCFrac x

-- | Converts a generalized continued fraction to a simple continued fraction.
-- This will not terminate if the generalized continued fraction doesn't
-- converge.
fromGCFrac :: GCFrac -> CFrac
fromGCFrac = go mempty
  where
    go (Mobius a _ c _) GInf = cfFromFrac a c
    go m gcf@((int, numer) :+#/ denom)
      | Just n <- mobiusIntPart 1 m =
          n :+/ go (Mobius 0 1 1 (-n) <> m) gcf
      | otherwise = go (m <> Mobius int numer 1 0) denom

gcfPi :: GCFrac
gcfPi = (0, 4) :+#/ go 1
  where
    go i = (2 * i - 1, i * i) :+#/ go (i + 1)

-- | Pi, as a continued fraction.
exactPi :: CFrac
exactPi = fromGCFrac gcfPi

-- | The square root of a non-negative integer, as a continued fraction.
sqrtInt :: Integer -> CFrac
sqrtInt n
  | n < 0 = error "sqrtInt: negative argument"
  | otherwise = go 0 1
  where
    isqrt :: Integer -> Integer
    isqrt 0 = 0
    isqrt x =
      let y = 2 * isqrt (x `quot` 4)
       in if (y + 1) * (y + 1) > x then y else y + 1

    sqrtn = isqrt n

    go _ 0 = Inf
    go p q =
      let m = (p + sqrtn) `quot` q
          p' = m * q - p
          q' = (n - p' * p') `quot` q
       in m :+/ go p' q'

cfRecip :: CFrac -> CFrac
cfRecip (0 :+/ x) = x
cfRecip (1 :+/ Inf) = 1 :+/ Inf
cfRecip x = 0 :+/ x
{-# INLINE [2] cfRecip #-}

cfSignum :: CFrac -> Integer
cfSignum (n :+/ Inf) = signum n
cfSignum (a :+/ _) | a < 0 = -1
cfSignum (0 :+/ (a :+/ _)) | a < 0 = -1
cfSignum _ = 1
{-# INLINE cfSignum #-}

cfCompare :: CFrac -> CFrac -> Ordering
cfCompare a b | sgnCmp /= EQ = sgnCmp
  where
    sgnCmp = compare (cfSignum a) (cfSignum b)
cfCompare Inf Inf = EQ
cfCompare _ Inf = LT
cfCompare Inf _ = GT
cfCompare (a :+/ a') (b :+/ b') = case compare a b of
  EQ -> cfCompare b' a'
  result -> result

instance Ord CFrac where compare = cfCompare

-- | Computes the value of a mobius transformation on a continued fraction.
cfMobius :: Mobius -> CFrac -> CFrac
cfMobius (Mobius a _ c _) Inf = cfFromFrac a c
cfMobius (Mobius _ _ 0 0) _ = Inf
cfMobius (Mobius 0 b 0 d) _ = cfFromFrac b d
cfMobius m x
  | Just n <- mobiusIntPart (cfSignum x) m =
      n :+/ cfMobius (Mobius 0 1 1 (-n) <> m) x
cfMobius m (n :+/ x) = cfMobius (m <> Mobius n 1 1 0) x
{-# INLINE [2] cfMobius #-}

-- | A bimobius transformation, of the form @f(x, y) =
-- (a * x * y + b * x + c * y + d) / (e * x * y + f * x + g * y + h)@.
-- This is part of the machinery for performing arithmetic on continued
-- fractions.
data Bimobius where
  BM ::
    Integer ->
    Integer ->
    Integer ->
    Integer ->
    Integer ->
    Integer ->
    Integer ->
    Integer ->
    Bimobius

deriving instance Eq Bimobius

deriving instance Ord Bimobius

deriving instance Show Bimobius

instance Arbitrary Bimobius where
  arbitrary =
    BM
      <$> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
  shrink (BM a b c d e f g h) =
    [ BM a' b' c' d' e' f' g' h'
      | (a', b', c', d', e', f', g', h') <- shrink (a, b, c, d, e, f, g, h)
    ]

bimobiusIntPart :: Integer -> Integer -> Bimobius -> Maybe Integer
bimobiusIntPart sgnX sgnY (BM a b c d e f g h)
  | allEq [sgnX * sgnY * signum e, sgnX * signum f, sgnY * signum g, signum h],
    allEq [n1, n2, n3, n4] =
      Just n1
  | otherwise = Nothing
  where
    allEq (x : xs) = all (== x) xs
    allEq [] = True

    n1 = a `quot` e
    n2 = b `quot` f
    n3 = c `quot` g
    n4 = d `quot` h
{-# INLINE bimobiusIntPart #-}

-- | A composition that applies a mobius transformation to the output of a
-- bimobius transformation, to obtain a combined bimobius transformation.
--
-- @(mob <>|| bimob) x y = mob (bimob x y)@
(<>||) :: Mobius -> Bimobius -> Bimobius
Mobius a1 b1 c1 d1 <>|| BM a2 b2 c2 d2 e2 f2 g2 h2 =
  BM a b c d e f g h
  where
    a = a1 * a2 + b1 * e2
    b = a1 * b2 + b1 * f2
    c = a1 * c2 + b1 * g2
    d = a1 * d2 + b1 * h2
    e = c1 * a2 + d1 * e2
    f = c1 * b2 + d1 * f2
    g = c1 * c2 + d1 * g2
    h = c1 * d2 + d1 * h2
{-# INLINE (<>||) #-}

-- | A composition that applies a mobius transformation to the first argument of
-- a bimobius transformation, to obtain a combined bimobius transformation.
--
-- @(bimob ||< mob) x y = bimob (mob x) y@
(||<) :: Bimobius -> Mobius -> Bimobius
BM a1 b1 c1 d1 e1 f1 g1 h1 ||< Mobius a2 b2 c2 d2 =
  BM a b c d e f g h
  where
    a = a1 * a2 + c1 * c2
    b = b1 * a2 + d1 * c2
    c = a1 * b2 + c1 * d2
    d = b1 * b2 + d1 * d2
    e = e1 * a2 + g1 * c2
    f = f1 * a2 + h1 * c2
    g = e1 * b2 + g1 * d2
    h = f1 * b2 + h1 * d2
{-# INLINE (||<) #-}

-- | A composition that applies a mobius transformation to the second argument
-- of a bimobius transformation, to obtain a combined bimobius transformation.
--
-- @(bimob ||> mob) x y = bimob x (mob y)@
(||>) :: Bimobius -> Mobius -> Bimobius
BM a1 b1 c1 d1 e1 f1 g1 h1 ||> Mobius a2 b2 c2 d2 =
  BM a b c d e f g h
  where
    a = a1 * a2 + b1 * c2
    b = a1 * b2 + b1 * d2
    c = c1 * a2 + d1 * c2
    d = c1 * b2 + d1 * d2
    e = e1 * a2 + f1 * c2
    f = e1 * b2 + f1 * d2
    g = g1 * a2 + h1 * c2
    h = g1 * b2 + h1 * d2
{-# INLINE (||>) #-}

-- | Computes the value of a bimobius transformation on a pair of continued
-- fractions.
cfBimobius :: Bimobius -> CFrac -> CFrac -> CFrac
cfBimobius (BM a b _ _ e f _ _) Inf y = cfMobius (Mobius a b e f) y
cfBimobius (BM a _ c _ e _ g _) x Inf = cfMobius (Mobius a c e g) x
cfBimobius (BM _ _ _ _ 0 0 0 0) _ _ = Inf
cfBimobius (BM 0 0 c d 0 0 g h) _ y = cfMobius (Mobius c d g h) y
cfBimobius (BM 0 b 0 d 0 f 0 h) x _ = cfMobius (Mobius b d f h) x
cfBimobius bm x y
  | Just n <- bimobiusIntPart (cfSignum x) (cfSignum y) bm =
      let bm' = Mobius 0 1 1 (-n) <>|| bm in n :+/ cfBimobius bm' x y
cfBimobius bm@(BM _ b c d _ f g h) x@(x0 :+/ x') y@(y0 :+/ y')
  | g == 0 && h == 0 = consumeX
  | h == 0 || h == 0 = consumeY
  | abs (g * (h * b - f * d)) > abs (f * (h * c - g * d)) = consumeX
  | otherwise = consumeY
  where
    consumeX = cfBimobius (bm ||< Mobius x0 1 1 0) x' y
    consumeY = cfBimobius (bm ||> Mobius y0 1 1 0) x y'
{-# INLINE [2] cfBimobius #-}

instance Num CFrac where
  fromInteger n = n :+/ Inf
  {-# INLINE fromInteger #-}

  (+) = cfBimobius (BM 0 1 1 0 0 0 0 1)
  {-# INLINE (+) #-}

  (-) = cfBimobius (BM 0 1 (-1) 0 0 0 0 1)
  {-# INLINE (-) #-}

  (*) = cfBimobius (BM 1 0 0 0 0 0 0 1)
  {-# INLINE (*) #-}

  signum = fromInteger . cfSignum
  {-# INLINE signum #-}

  abs x
    | cfSignum x < 0 = cfNegate x
    | otherwise = x
  {-# INLINE abs #-}

  negate = cfNegate
  {-# INLINE negate #-}

-- | 'toRational' only terminates for rational inputs.
instance Real CFrac where
  toRational = cfToRational
  {-# INLINE toRational #-}

cfProperFraction :: Integral i => CFrac -> (i, CFrac)
cfProperFraction Inf = error "cfProperFraction: Inf"
cfProperFraction (x :+/ y) = (fromInteger x, 0 :+/ y)
{-# INLINE cfProperFraction #-}

instance RealFrac CFrac where
  properFraction = cfProperFraction
  {-# INLINE properFraction #-}

instance Fractional CFrac where
  fromRational r = cfFromFrac (numerator r) (denominator r)
  {-# INLINE fromRational #-}

  recip = cfRecip
  {-# INLINE recip #-}

  (/) = cfBimobius (BM 0 1 0 0 0 0 1 0)
  {-# INLINE (/) #-}

{-# RULES
"cfrac/cfRecip" forall x. cfRecip (cfRecip x) = x
"cfrac/intToRat" forall n. cfToRational (n :+/ Inf) = fromInteger n
"cfrac/ratToRat" forall p q.
  cfToRational (cfFromFrac p q) =
    fromInteger p / fromInteger q
  #-}

{-# RULES
"cfrac/cfMobiusInt" forall a b c d n.
  cfMobius (Mobius a b c d) (n :+/ Inf) =
    cfFromFrac (a * n + b) (c * n + d)
"cfrac/cfMobiusRat" forall a b c d p q.
  cfMobius (Mobius a b c d) (cfFromFrac p q) =
    cfFromFrac (a * p + b * q) (c * p + d * q)
"cfrac/cfBimobiusInt1" forall a b c d e f g h n y.
  cfBimobius (BM a b c d e f g h) (n :+/ Inf) y =
    cfMobius (Mobius (a * n + c) (b * n + d) (e * n + g) (f * n + h)) y
"cfrac/cfBimobiusRat1" forall a b c d e f g h p q y.
  cfBimobius (BM a b c d e f g h) (cfFromFrac p q) y =
    cfMobius
      ( Mobius
          (a * p + c * q)
          (b * p + d * q)
          (e * p + g * q)
          (f * p + h * q)
      )
      y
"cfrac/cfBimobiusInt2" forall a b c d e f g h n x.
  cfBimobius (BM a b c d e f g h) x (n :+/ Inf) =
    cfMobius (Mobius (a * n + b) (c * n + d) (e * n + f) (g * n + h)) x
"cfrac/cfBimobiusRat2" forall a b c d e f g h p q x.
  cfBimobius (BM a b c d e f g h) x (cfFromFrac p q) =
    cfMobius
      ( Mobius
          (a * p + b * q)
          (c * p + d * q)
          (e * p + f * q)
          (g * p + h * q)
      )
      x
  #-}

{-# RULES
"cfrac/mobius_o_mobius" forall m1 m2 x.
  cfMobius m1 (cfMobius m2 x) =
    cfMobius (m1 <> m2) x
"cfrac/mobius_o_bimobius" forall m bm x y.
  cfMobius m (cfBimobius bm x y) =
    cfBimobius (m <>|| bm) x y
"cfrac/bimobius_o_mobiusLeft" forall bm m x y.
  cfBimobius bm (cfMobius m x) y =
    cfBimobius (bm ||< m) x y
"cfrac/bimobius_o_mobiusRight" forall bm m x y.
  cfBimobius bm x (cfMobius m y) =
    cfBimobius (bm ||> m) x y
  #-}
