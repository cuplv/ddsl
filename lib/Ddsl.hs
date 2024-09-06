{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module Ddsl
  ( mkDType
  , alpTheory
  , alpFlat
  , alpAssert
  , alpSymbol
  , alpFun
  , verify
  , verify'
  , SolverConfig
  , useCVC4
  , useCVC5
  , useZ3
  , useMBQI
  , showTheory
  , showSMT
  , VerifyResult (..)
  , showResultSeconds
  , evaluate
  , module Ddsl.Base
  , module Ddsl.Base.Bool
  , module Ddsl.Base.Tuple
  , module Ddsl.Symbolic
  , module Ddsl.Term
  ) where

import Ddsl.Base
import Ddsl.Base.Bool
import Ddsl.Base.Tuple
import Ddsl.Internal
import Ddsl.Symbolic
import Ddsl.Term
import Ddsl.TH
