{-# OPTIONS --without-K --safe #-}

open import Context
import IK

x = nf {· , ι} (app (abs (var zero)) (var zero))
  where open import Calculus record { IK }
