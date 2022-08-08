{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}

module CFrac where

import Data.Function (fix)
import Data.Ratio (denominator, numerator, (%))
import Numeric (showFFloat)
import Test.QuickCheck
  ( Arbitrary (..),
    NonNegative (..),
    Property,
    counterexample,
    discard,
    suchThat,
    (===),
    (==>),
  )

data CFrac where
  (:+/) :: Integer -> CFrac -> CFrac
  Inf :: CFrac

deriving instance Eq CFrac

deriving instance Show CFrac

infixr 5 :+/

terms :: CFrac -> [Integer]
terms Inf = []
terms (n :+/ x) = n : terms x

fromTerms :: [Integer] -> CFrac
fromTerms = foldr (:+/) Inf

cfFromFrac :: Integer -> Integer -> CFrac
cfFromFrac _ 0 = Inf
cfFromFrac n d = n `div` d :+/ cfFromFrac d (n `mod` d)
{-# INLINE [2] cfFromFrac #-}

cfFromRational :: Rational -> CFrac
cfFromRational r = cfFromFrac (numerator r) (denominator r)
{-# INLINE cfFromRational #-}

cycleTerms :: [Integer] -> CFrac
cycleTerms ns = fix (go ns)
  where
    go [] x = x
    go (t : ts) x = t :+/ go ts x

sqrt2 :: CFrac
sqrt2 = 1 :+/ cycleTerms [2]

sqrt3 :: CFrac
sqrt3 = 1 :+/ cycleTerms [1, 2]

sqrt5 :: CFrac
sqrt5 = 2 :+/ cycleTerms [4]

phi :: CFrac
phi = cycleTerms [1]

exp1 :: CFrac
exp1 = 2 :+/ fromTerms (concatMap (\n -> [1, 2 * n, 1]) [1 ..])

approxPi :: CFrac
approxPi = cfFromRational (realToFrac (pi :: Double))

isCanonical :: CFrac -> Bool
isCanonical Inf = True
isCanonical (n :+/ cont) = n >= 0 && isCanonicalCont cont

isCanonicalCont :: CFrac -> Bool
isCanonicalCont Inf = True
isCanonicalCont (1 :+/ Inf) = False
isCanonicalCont (n :+/ cont) = n > 0 && isCanonicalCont cont

-- prop> not (isCanonical (2 :+/ (-1) :+/ Inf))
-- +++ OK, passed 1 test.

-- prop> isCanonical (1 :+/ 2 :+/ Inf)
-- +++ OK, passed 1 test.

-- prop> not (isCanonical (1 :+/ 0 :+/ 2 :+/ Inf))
-- +++ OK, passed 1 test.

-- prop> isCanonical (3 :+/ Inf)
-- +++ OK, passed 1 test.

-- prop> not (isCanonical (1 :+/ 1 :+/ Inf))
-- +++ OK, passed 1 test.

-- prop> isCanonical (2 :+/ Inf)
-- +++ OK, passed 1 test.

-- prop> \(NonNegative x) -> isCanonical (cfFromRational x)
-- +++ OK, passed 100 tests.

naiveConvergents :: CFrac -> [Rational]
naiveConvergents Inf = []
naiveConvergents (n :+/ r) =
  fromInteger n :
  map (\x -> fromInteger n + 1 / x) (naiveConvergents r)

data Mobius where
  Mobius :: Integer -> Integer -> Integer -> Integer -> Mobius

deriving instance Eq Mobius

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
  arbitrary =
    suchThat
      ( Mobius
          <$> arbitrary
          <*> arbitrary
          <*> (getNonNegative <$> arbitrary)
          <*> (getNonNegative <$> arbitrary)
      )
      (\(Mobius _ _ c d) -> max c d > 0)
  shrink (Mobius a b c d) =
    [ Mobius a' b' c' d'
      | (a', b', NonNegative c', NonNegative d') <-
          shrink (a, b, NonNegative c, NonNegative d),
        max c' d' > 0
    ]

-- prop> \(m :: Mobius) -> mempty <> m == m
-- +++ OK, passed 100 tests.

-- prop> \(m :: Mobius) -> m <> mempty == m
-- +++ OK, passed 100 tests.

-- prop> \(m1 :: Mobius) m2 m3 -> m1 <> (m2 <> m3) == (m1 <> m2) <> m3
-- +++ OK, passed 100 tests.

convergents :: CFrac -> [Rational]
convergents = go mempty
  where
    go _ Inf = []
    go m (n :+/ x) = mobiusLimit m' : go m' x
      where
        m' = m <> Mobius n 1 1 0
    mobiusLimit (Mobius a _ c _) = a % c

-- prop> prop_convergents_matches_naive
-- +++ OK, passed 100 tests.
prop_convergents_matches_naive :: NonNegative Rational -> Property
prop_convergents_matches_naive (NonNegative r) =
  convergents (cfFromRational r)
    === naiveConvergents (cfFromRational r)

cfToRational :: CFrac -> Rational
cfToRational = go mempty
  where
    go (Mobius a _ c _) Inf = a % c
    go m (n :+/ x) = go (m <> Mobius n 1 1 0) x
{-# INLINE [2] cfToRational #-}

-- prop> \(NonNegative x) -> cfToRational (cfFromRational x) == x
-- +++ OK, passed 100 tests.

mobiusIntPart :: Mobius -> Maybe Integer
mobiusIntPart (Mobius a b c d)
  | c /= 0 && d /= 0 && n1 == n2 = Just n1
  | otherwise = Nothing
  where
    n1 = a `div` c
    n2 = b `div` d
{-# INLINE mobiusIntPart #-}

cfToBase :: Integer -> CFrac -> [Integer]
cfToBase base = go mempty
  where
    go (Mobius 0 0 _ _) _ = []
    go m x
      | Just n <- mobiusIntPart m,
        let m' = Mobius base (-base * n) 0 1 <> m =
          n : go m' x
    go m (n :+/ x) = go (m <> Mobius n 1 1 0) x
    go (Mobius a _ c _) Inf = go (Mobius a a c c) Inf

cfToDecimal :: CFrac -> String
cfToDecimal Inf = "Inf"
cfToDecimal x = case cfToBase 10 x of
  [] -> "0.0"
  [z] -> show z ++ ".0"
  (z : digits) -> show z ++ "." ++ concatMap show digits

-- prop> prop_cfToDecimal_matchesRational
-- +++ OK, passed 100 tests.
prop_cfToDecimal_matchesRational :: NonNegative Rational -> Property
prop_cfToDecimal_matchesRational (NonNegative r) =
  take n decFromRat === take n decFromCF
  where
    decFromRat = showFFloat Nothing (realToFrac r :: Double) ""
    decFromCF = cfToDecimal (cfFromRational r)
    n = max 10 (length decFromRat - 1)

data GCFrac where
  (:+#/) :: (Integer, Integer) -> GCFrac -> GCFrac
  GInf :: GCFrac

deriving instance Show GCFrac

cfToGCFrac :: CFrac -> GCFrac
cfToGCFrac Inf = GInf
cfToGCFrac (n :+/ x) = (n, 1) :+#/ cfToGCFrac x

gcfToCFrac :: GCFrac -> CFrac
gcfToCFrac = go mempty
  where
    go (Mobius a _ c _) GInf = cfFromFrac a c
    go m gcf@((int, numer) :+#/ denom)
      | Just n <- mobiusIntPart m =
          n :+/ go (Mobius 0 1 1 (-n) <> m) gcf
      | otherwise = go (m <> Mobius int numer 1 0) denom

-- prop> prop_GCFrac_roundtrip
-- +++ OK, passed 100 tests.
prop_GCFrac_roundtrip :: NonNegative Rational -> Property
prop_GCFrac_roundtrip (NonNegative r) =
  gcfToCFrac (cfToGCFrac x) === x
  where
    x = cfFromRational r

gcfPi :: GCFrac
gcfPi = (0, 4) :+#/ go 1
  where
    go i = (2 * i - 1, i * i) :+#/ go (i + 1)

exactPi :: CFrac
exactPi = gcfToCFrac gcfPi

-- prop> take 17 (cfToDecimal approxPi) === take 17 (cfToDecimal exactPi)
-- +++ OK, passed 1 test.

cfRecip :: CFrac -> CFrac
cfRecip (0 :+/ x) = x
cfRecip (1 :+/ Inf) = 1 :+/ Inf
cfRecip x = 0 :+/ x
{-# INLINE [2] cfRecip #-}

-- prop> prop_cfRecip_selfInverse
-- +++ OK, passed 100 tests.
prop_cfRecip_selfInverse :: NonNegative Rational -> Property
prop_cfRecip_selfInverse (NonNegative r) =
  cfRecip (cfRecip (cfFromRational r)) === cfFromRational r

-- prop> prop_cfRecip_canonical
-- +++ OK, passed 100 tests.
prop_cfRecip_canonical :: NonNegative Rational -> Bool
prop_cfRecip_canonical (NonNegative r) =
  isCanonical (cfRecip (cfFromRational r))

-- prop> prop_cfRecip_matchesRational
-- +++ OK, passed 100 tests; 10 discarded.
prop_cfRecip_matchesRational :: NonNegative Rational -> Property
prop_cfRecip_matchesRational (NonNegative r) =
  r /= 0 ==> cfRecip (cfFromRational r) == cfFromRational (recip r)

cfCompare :: CFrac -> CFrac -> Ordering
cfCompare Inf Inf = EQ
cfCompare _ Inf = LT
cfCompare Inf _ = GT
cfCompare (a :+/ a') (b :+/ b') = case compare a b of
  EQ -> cfCompare b' a'
  result -> result

-- prop> prop_cfCompare_matches_Rational
-- +++ OK, passed 100 tests.
prop_cfCompare_matches_Rational ::
  NonNegative Rational -> NonNegative Rational -> Property
prop_cfCompare_matches_Rational (NonNegative x) (NonNegative y) =
  compare x y === cfCompare (cfFromRational x) (cfFromRational y)

instance Ord CFrac where compare = cfCompare

cfMobius :: Mobius -> CFrac -> CFrac
cfMobius (Mobius a _ c _) Inf = cfFromFrac a c
cfMobius (Mobius _ _ 0 0) _ = Inf
cfMobius m x
  | Just n <- mobiusIntPart m =
      n :+/ cfMobius (Mobius 0 1 1 (-n) <> m) x
cfMobius m (n :+/ x) = cfMobius (m <> Mobius n 1 1 0) x
{-# INLINE [2] cfMobius #-}

mobius :: (Eq a, Fractional a) => Mobius -> a -> Maybe a
mobius (Mobius a b c d) x
  | q == 0 = Nothing
  | otherwise = Just (p / q)
  where
    p = fromInteger a * x + fromInteger b
    q = fromInteger c * x + fromInteger d

-- prop> prop_cfMobius_matches_Rational
-- +++ OK, passed 100 tests; 119 discarded.
prop_cfMobius_matches_Rational ::
  Mobius -> NonNegative Rational -> Property
prop_cfMobius_matches_Rational m (NonNegative r) =
  case mobius m r of
    Just x
      | x >= 0 ->
          cfMobius m (cfFromRational r) === cfFromRational x
    _ -> discard

-- prop> prop_cfMobius_isCanonical
-- +++ OK, passed 100 tests; 107 discarded.
prop_cfMobius_isCanonical ::
  Mobius -> NonNegative Rational -> Property
prop_cfMobius_isCanonical m (NonNegative r) =
  case mobius m r of
    Just rat
      | rat >= 0 ->
          let x = cfMobius m (cfFromRational r)
           in counterexample (show x) (isCanonical x)
    _ -> discard

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

deriving instance Show Bimobius

instance Arbitrary Bimobius where
  arbitrary =
    suchThat
      ( BM
          <$> arbitrary
          <*> arbitrary
          <*> arbitrary
          <*> arbitrary
          <*> (getNonNegative <$> arbitrary)
          <*> (getNonNegative <$> arbitrary)
          <*> (getNonNegative <$> arbitrary)
          <*> (getNonNegative <$> arbitrary)
      )
      (\(BM _ _ _ _ e f g h) -> maximum [e, f, g, h] > 0)
  shrink (BM a b c d e f g h) =
    [ BM a' b' c' d' e' f' g' h'
      | ( a',
          b',
          c',
          d',
          NonNegative e',
          NonNegative f',
          NonNegative g',
          NonNegative h'
          ) <-
          shrink
            ( a,
              b,
              c,
              d,
              NonNegative e,
              NonNegative f,
              NonNegative g,
              NonNegative h
            ),
        maximum [e', f', g', h'] > 0
    ]

bimobiusIntPart :: Bimobius -> Maybe Integer
bimobiusIntPart (BM a b c d e f g h)
  | e /= 0 && f /= 0 && g /= 0 && h /= 0
      && n2 == n1
      && n3 == n1
      && n4 == n1 =
      Just n1
  | otherwise = Nothing
  where
    n1 = a `div` e
    n2 = b `div` f
    n3 = c `div` g
    n4 = d `div` h
{-# INLINE bimobiusIntPart #-}

-- | @(mob <>|| bimob) x y = mob (bimob x y)@
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

-- | @(bimob ||< mob) x y = bimob (mob x) y@
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

-- | @(bimob ||> mob) x y = bimob x (mob y)@
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

bimobius :: (Eq a, Fractional a) => Bimobius -> a -> a -> Maybe a
bimobius (BM a b c d e f g h) x y
  | q == 0 = Nothing
  | otherwise = Just (p / q)
  where
    p =
      fromInteger a * x * y
        + fromInteger b * x
        + fromInteger c * y
        + fromInteger d
    q =
      fromInteger e * x * y
        + fromInteger f * x
        + fromInteger g * y
        + fromInteger h

-- prop> prop_mob_o_bimob
-- +++ OK, passed 100 tests; 1 discarded.
prop_mob_o_bimob ::
  Mobius -> Bimobius -> Rational -> Rational -> Property
prop_mob_o_bimob mob bimob r1 r2 =
  case mobius mob =<< bimobius bimob r1 r2 of
    Just ans -> bimobius (mob <>|| bimob) r1 r2 === Just ans
    Nothing -> discard

-- prop> prop_bimob_o_leftMob
-- +++ OK, passed 100 tests; 2 discarded.
prop_bimob_o_leftMob ::
  Bimobius -> Mobius -> Rational -> Rational -> Property
prop_bimob_o_leftMob bimob mob r1 r2 =
  case (\x -> bimobius bimob x r2) =<< mobius mob r1 of
    Just ans -> bimobius (bimob ||< mob) r1 r2 === Just ans
    Nothing -> discard

-- prop> prop_bimob_o_rightMob
-- +++ OK, passed 100 tests; 2 discarded.
prop_bimob_o_rightMob ::
  Bimobius -> Mobius -> Rational -> Rational -> Property
prop_bimob_o_rightMob bimob mob r1 r2 =
  case (\y -> bimobius bimob r1 y) =<< mobius mob r2 of
    Just ans -> bimobius (bimob ||> mob) r1 r2 === Just ans
    Nothing -> discard

cfBimobius :: Bimobius -> CFrac -> CFrac -> CFrac
cfBimobius (BM a b _ _ e f _ _) Inf y = cfMobius (Mobius a b e f) y
cfBimobius (BM a _ c _ e _ g _) x Inf = cfMobius (Mobius a c e g) x
cfBimobius (BM _ _ _ _ 0 0 0 0) _ _ = Inf
cfBimobius bm x y
  | Just n <- bimobiusIntPart bm =
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

-- prop> prop_cfBimobius_matches_Rational
-- +++ OK, passed 100 tests; 101 discarded.
prop_cfBimobius_matches_Rational ::
  NonNegative Rational ->
  NonNegative Rational ->
  Bimobius ->
  Property
prop_cfBimobius_matches_Rational
  (NonNegative r1)
  (NonNegative r2)
  bm =
    case bimobius bm r1 r2 of
      Just x
        | x >= 0 ->
            cfFromRational x
              === cfBimobius
                bm
                (cfFromRational r1)
                (cfFromRational r2)
      _ -> discard

-- prop> prop_cfBimobius_isCanonical
-- +++ OK, passed 100 tests; 121 discarded.
prop_cfBimobius_isCanonical ::
  NonNegative Rational ->
  NonNegative Rational ->
  Bimobius ->
  Bool
prop_cfBimobius_isCanonical
  (NonNegative r1)
  (NonNegative r2)
  bm =
    case bimobius bm r1 r2 of
      Just x
        | x >= 0 ->
            isCanonical
              (cfBimobius bm (cfFromRational r1) (cfFromRational r2))
      _ -> discard

checkNonNegative :: CFrac -> CFrac
checkNonNegative Inf = Inf
checkNonNegative x@(x0 :+/ x')
  | x < 0 = error "checkNonNegative: CFrac is negative"
  | x > 0 = x
  | otherwise = x0 :+/ checkNonNegative x'
{-# INLINE checkNonNegative #-}

cfFromInteger :: Integer -> CFrac
cfFromInteger n = n :+/ Inf
{-# INLINE [2] cfFromInteger #-}

instance Num CFrac where
  fromInteger n
    | n >= 0 = cfFromInteger n
    | otherwise = error "fromInteger: CFrac cannot be negative"
  {-# INLINE fromInteger #-}

  (+) = cfBimobius (BM 0 1 1 0 0 0 0 1)
  {-# INLINE (+) #-}

  x - y = checkNonNegative (cfBimobius (BM 0 1 (-1) 0 0 0 0 1) x y)
  {-# INLINE (-) #-}

  (*) = cfBimobius (BM 1 0 0 0 0 0 0 1)
  {-# INLINE (*) #-}

  signum (0 :+/ Inf) = 0
  signum _ = 1
  {-# INLINE signum #-}

  abs = id
  {-# INLINE abs #-}

  negate (0 :+/ Inf) = 0 :+/ Inf
  negate _ = error "negate: CFrac cannot be negative"
  {-# INLINE negate #-}

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
  fromRational x
    | x < 0 = error "fromRational: CFrac cannot be negative"
    | otherwise = cfFromRational x
  {-# INLINE fromRational #-}

  recip = cfRecip
  {-# INLINE recip #-}

  (/) = cfBimobius (BM 0 1 0 0 0 0 1 0)
  {-# INLINE (/) #-}

{-# RULES
"cfrac/cfRecip" forall x. cfRecip (cfRecip x) = x
"cfrac/intToRat" forall n. cfToRational (cfFromInteger n) = fromInteger n
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
