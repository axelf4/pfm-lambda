{-# OPTIONS --without-K #-}

module README where

import Everything

open import Context
open import Parameters as _ using (Parameters)
import IK

x = nf {· , ι} (app (abs (var zero)) (var zero))
  where open import Calculus record { IK } -- Instantiate the calculus IK

-- Show soundness and completeness of normalization for all parametrizations
module _ (params : Parameters) where
  open import Soundness params
  open import Completeness params
