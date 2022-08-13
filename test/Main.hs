{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore #-}

module Main where

import CFrac (CFrac (..))
import Test.Hspec (describe, hspec)
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck (Negative (..), NonNegative (..), NonZero (..), Positive (..), (===))

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
