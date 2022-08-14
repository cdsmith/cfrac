{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore #-}

module Main (main) where

import CFrac
  ( Bimobius (..),
    CFrac (..),
    Mobius (..),
    cfBimobius,
    cfMobius,
    convergents,
    exactPi,
    fromGCFrac,
    isCanonical,
    phi,
    sqrtInt,
    toDecimal,
    toGCFrac,
    (<>||),
    (||<),
    (||>),
  )
import Numeric (showFFloat)
import Test.Hspec (describe, hspec, it, shouldBe)
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck
  ( Negative (..),
    NonNegative (..),
    NonZero (..),
    Positive (..),
    discard,
    (===),
  )

naiveConvergents :: CFrac -> [Rational]
naiveConvergents Inf = []
naiveConvergents (n :+/ r) =
  fromInteger n :
  map (\x -> fromInteger n + 1 / x) (naiveConvergents r)

rationalMobius :: Mobius -> Rational -> Maybe Rational
rationalMobius (Mobius a b c d) x
  | q == 0 = Nothing
  | otherwise = Just (p / q)
  where
    p = fromInteger a * x + fromInteger b
    q = fromInteger c * x + fromInteger d

rationalBimobius :: Bimobius -> Rational -> Rational -> Maybe Rational
rationalBimobius (BM a b c d e f g h) x y
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

main :: IO ()
main = hspec $ do
  describe "arithmetic properties" $ do
    prop "fromInteger" $ \n -> fromInteger n === n :+/ Inf
    prop "fromRational/toRational inverses #1" $
      \r -> toRational (fromRational r :: CFrac) === r
    prop "fromRational/toRational inverses #2" $
      \(cf :: CFrac) -> fromRational (toRational cf) === cf
    prop "+ is commutative" $ \(x :: CFrac) y -> x + y === y + x
    prop "+ is associative" $ \(x :: CFrac) y z -> (x + y) + z === x + (y + z)
    prop "+ has left identity" $ \(x :: CFrac) -> 0 + x === x
    prop "+ has right identity" $ \(x :: CFrac) -> x + 0 === x
    prop "negate is left inverse for +" $ \(x :: CFrac) -> negate x + x === 0
    prop "negate is right inverse for +" $ \(x :: CFrac) -> x + (negate x) === 0
    prop "negate 0 = 0" $ negate 0 === (0 :: CFrac)
    prop "negate Inf = Inf" $ negate Inf === Inf
    prop "negate 1 = -1" $ negate 1 === (-1 :: CFrac)
    prop "def. of subtraction" $ \(x :: CFrac) y -> x - y === x + negate y
    prop "subtract self is zero" $ \(x :: CFrac) -> x - x === 0
    prop "subtract is anti-commutative" $
      \(x :: CFrac) y -> x - y === negate (y - x)
    prop "negate via subtraction" $ \(x :: CFrac) -> 0 - x === negate x
    prop "negate self-inverse" $ \(x :: CFrac) -> negate (negate x) === x
    prop "* is commutative" $ \(x :: CFrac) y -> x * y === y * x
    prop "* is associative" $ \(x :: CFrac) y z -> (x * y) * z === x * (y * z)
    prop "* has left identity" $ \(x :: CFrac) -> 1 * x === x
    prop "* has right identity" $ \(x :: CFrac) -> x * 1 === x
    prop "* has left absorption" $ \(x :: CFrac) -> 0 * x === 0
    prop "* has right absorption" $ \(x :: CFrac) -> x * 0 === 0
    prop "* has left absorption Inf" $ \(x :: CFrac) -> Inf * x === Inf
    prop "* has right absorption Inf" $ \(x :: CFrac) -> x * Inf === Inf
    prop "negate via *" $ \(x :: CFrac) -> negate x === (-1) * x
    prop "recip is left inverse for *" $
      \(NonZero x :: NonZero CFrac) -> recip x * x === 1
    prop "recip is right inverse for *" $
      \(NonZero x :: NonZero CFrac) -> x * (recip x) === 1
    prop "recip 1 = 1" $ recip 1 === (1 :: CFrac)
    prop "recip 0 = Inf" $ recip 0 === Inf
    prop "recip Inf = 0" $ recip Inf === 0
    prop "def. of division" $ \(x :: CFrac) (NonZero y) -> x / y === x * recip y
    prop "divided by self is 1" $ \(NonZero x :: NonZero CFrac) -> x / x === 1
    prop "division by Inf is zero" $ \x -> x / Inf === 0
    prop "division is inverse-commutative" $
      \(NonZero x :: NonZero CFrac) (NonZero y) -> x / y === recip (y / x)
    prop "recip via division" $
      \(NonZero x :: NonZero CFrac) -> 1 / x === recip x
    prop "recip self-inverse" $ \(x :: CFrac) -> recip (recip x) === x
    prop "* distributes over +" $
      \(x :: CFrac) y z -> x * (y + z) === x * y + x * z
    prop "* distributes over -" $
      \(x :: CFrac) y z -> x * (y - z) === x * y - x * z
    prop "/ distributes over +" $
      \(x :: CFrac) y (NonZero z) -> (x + y) / z === x / z + y / z
    prop "/ distributes over -" $
      \(x :: CFrac) y (NonZero z) -> (x - y) / z === x / z - y / z
    prop "def. of abs" $ \(x :: CFrac) -> abs x >= 0
    prop "abs idempotent" $ \(x :: CFrac) -> abs (abs x) === abs x
    prop "abs non-neg" $ \(NonNegative x :: NonNegative CFrac) -> abs x === x
    prop "abs neg" $ \(Negative x :: Negative CFrac) -> abs x === negate x
    prop "abs Inf" $ abs Inf === Inf
    prop "def. of signum, positive" $
      \(Positive x :: Positive CFrac) -> signum x === 1
    prop "def. of signum, negative" $
      \(Negative x :: Negative CFrac) -> signum x === -1
    prop "def. of signum, zero" $ signum 0 === (0 :: CFrac)
    prop "signum Inf" $ signum Inf === 1
    prop "abs and signum" $ \(x :: CFrac) -> signum x * abs x === x

  describe "isCanonical" $ do
    it "checks for canonical representation" $ do
      isCanonical (2 :+/ (-1) :+/ Inf) `shouldBe` False
      isCanonical (1 :+/ 2 :+/ Inf) `shouldBe` True
      isCanonical (1 :+/ 0 :+/ 2 :+/ Inf) `shouldBe` False
      isCanonical (3 :+/ Inf) `shouldBe` True
      isCanonical (1 :+/ 1 :+/ Inf) `shouldBe` False
      isCanonical (2 :+/ Inf) `shouldBe` True
      isCanonical (-2 :+/ Inf) `shouldBe` True
      isCanonical (0 :+/ Inf) `shouldBe` True
      isCanonical (-2 :+/ (-3) :+/ Inf) `shouldBe` True
      isCanonical (-2 :+/ (-1) :+/ Inf) `shouldBe` False
      isCanonical Inf `shouldBe` True

    prop "fromRational" $ \x -> isCanonical (fromRational x)
    prop "recip" $ \x -> isCanonical (recip x)
    prop "cfMobius" $ \m x -> isCanonical (cfMobius m x)
    prop "cfBimobius" $ \m x y -> isCanonical (cfBimobius m x y)

  describe "Mobius" $ do
    prop "left identity" $ \(m :: Mobius) -> mempty <> m === m
    prop "right identity" $ \(m :: Mobius) -> m <> mempty === m
    prop "assoc" $
      \(m1 :: Mobius) m2 m3 -> (m1 <> m2) <> m3 === m1 <> (m2 <> m3)

  describe "convergents" $ do
    prop "ends at original" $ \r -> last (convergents (fromRational r)) === r
    it "gives expected answers" $ do
      take 4 (convergents exactPi) `shouldBe` [3, 22 / 7, 333 / 106, 355 / 113]
      take 6 (convergents phi) `shouldBe` [1, 2, 3 / 2, 5 / 3, 8 / 5, 13 / 8]
    prop "agrees with naive implementation" $
      \cf -> convergents cf === naiveConvergents cf

  describe "toDecimal" $ do
    prop "matches Rational" $ \r ->
      let decFromRat = showFFloat Nothing (realToFrac r :: Double) ""
          decFromCFrac = toDecimal (fromRational r)
          n = max 10 (length decFromRat - 1)
       in take n decFromRat == take n decFromCFrac
    it "gives known constants" $
      take 50 (toDecimal exactPi)
        `shouldBe` "3.141592653589793238462643383279502884197169399375"

  describe "GCFrac" $ do
    prop "roundtrips with CFrac" $ \cf -> fromGCFrac (toGCFrac cf) === cf

  describe "sqrtInt" $ do
    it "computes sqrt 2" $
      take 50 (toDecimal (sqrtInt 2))
        `shouldBe` "1.414213562373095048801688724209698078569671875376"
    it "computes sqrt 3" $
      take 50 (toDecimal (sqrtInt 3))
        `shouldBe` "1.732050807568877293527446341505872366942805253810"
    it "computes sqrt 5" $
      take 50 (toDecimal (sqrtInt 5))
        `shouldBe` "2.236067977499789696409173668731276235440618359611"

  describe "matches Rational" $ do
    prop "recip" $ \(NonZero r) ->
      recip (fromRational r :: CFrac) === fromRational (recip r)

    prop "signum" $ \r ->
      signum (fromRational r :: CFrac) === fromRational (signum r)

    prop "compare" $ \x y ->
      compare x y === compare (fromRational x :: CFrac) (fromRational y)

    prop "cfMobius" $ \m r ->
      case rationalMobius m r of
        Just x -> cfMobius m (fromRational r) === fromRational x
        Nothing -> cfMobius m (fromRational r) === Inf

    prop "<>||" $ \mob bimob (r1 :: Rational) r2 ->
      rationalBimobius (mob <>|| bimob) r1 r2
        === (rationalMobius mob =<< rationalBimobius bimob r1 r2)

    prop "||<" $ \bimob mob (r1 :: Rational) r2 ->
      case rationalMobius mob r1 of
        Just x ->
          rationalBimobius bimob x r2
            === rationalBimobius (bimob ||< mob) r1 r2
        Nothing -> discard

    prop "||<" $ \bimob mob (r1 :: Rational) r2 ->
      case rationalMobius mob r2 of
        Just y ->
          rationalBimobius bimob r1 y
            === rationalBimobius (bimob ||> mob) r1 r2
        Nothing -> discard

    prop "cfBimobius" $ \bm r1 r2 ->
      cfBimobius bm (fromRational r1) (fromRational r2)
        === maybe Inf fromRational (rationalBimobius bm r1 r2)
