{-# OPTIONS --without-K #-}

open import Context
open import Parameters as _ using (Parameters)
import IK

x = nf {· , ι} (app (abs (var zero)) (var zero))
  where open import Calculus record { IK }

module _ (params : Parameters) where
  open import Soundness params
  open import Completeness params
