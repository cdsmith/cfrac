{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeApplications #-}

module Main where

#if MIN_VERSION_base(4,15,0)

-- No imports

#else

import CFrac (Bimobius, CFrac (..), Mobius)
import QuickSpec (con, mono, prelude, quickSpec)

#endif

#if MIN_VERSION_base(4,15,0)

main :: IO ()
main = putStrLn "Sorry, QuickSpec requires GHC earlier than 9.0."

#else

main :: IO ()
main =
  quickSpec
    [ prelude,
      mono @Integer,
      mono @Rational,
      mono @CFrac,
      mono @Mobius,
      mono @Bimobius,
      con "fromInteger" (fromInteger :: Integer -> CFrac),
      con "0" (0 :: CFrac),
      con "1" (1 :: CFrac),
      con "-1" (-1 :: CFrac),
      con "Inf" (Inf :: CFrac),
      con "0_Q" (0 :: Rational),
      con "1_Q" (1 :: Rational),
      con "-1_Q" (-1 :: Rational),
      con "0_Z" (0 :: Integer),
      con "1_Z" (1 :: Integer),
      con "-1_Z" (-1 :: Integer),
      con "+" ((+) :: CFrac -> CFrac -> CFrac),
      con "-" ((-) :: CFrac -> CFrac -> CFrac),
      con "*" ((*) :: CFrac -> CFrac -> CFrac),
      con "/" ((/) :: CFrac -> CFrac -> CFrac),
      con "recip" (recip :: CFrac -> CFrac),
      con "signum" (signum :: CFrac -> CFrac),
      con "abs" (abs :: CFrac -> CFrac),
      con "negate" (negate :: CFrac -> CFrac),
      con "fromRational" (fromRational :: Rational -> CFrac),
      con "toRational" (toRational :: CFrac -> Rational),
      con "properFraction" (properFraction :: CFrac -> (Integer, CFrac))
    ]

#endif
