{-# OPTIONS --without-K --safe #-}

module Util where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Congruence w.r.t. the first argument of a binary function
cong1 : {A B C : Set} (f : A -> B -> C) {x x' : A} {y : B}
  -> x ≡ x' -> f x y ≡ f x' y
cong1 f refl = refl
