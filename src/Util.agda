{-# OPTIONS --without-K --safe #-}

module Util where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

-- Congruence w.r.t. the first argument of a binary function
cong1 : {A B C : Set} (f : A -> B -> C) {x x' : A} {y : B}
  -> x ≡ x' -> f x y ≡ f x' y
cong1 f refl = refl

module _ {a} {b} {c} {d} {e} where
  dcong₄ : ∀ {A : Set a} {B : A -> Set b} {C : A -> Set c} {D : A -> Set d} {E : Set e}
    (f : (w : A) -> B w -> C w -> D w -> E) {w₁ w₂ x₁ x₂ y₁ y₂ z₁ z₂}
    -> (p : w₁ ≡ w₂) -> subst B p x₁ ≡ x₂ -> subst C p y₁ ≡ y₂ -> subst D p z₁ ≡ z₂
    -> f w₁ x₁ y₁ z₁ ≡ f w₂ x₂ y₂ z₂
  dcong₄ _f refl refl refl refl = refl

module _ {a p} {A : Set a} {P : A -> Set p} (g : {x : A} -> P x) where
  subst-application'' : ∀ {x y} -> (eq : x ≡ y) -> subst P eq g ≡ g
  subst-application'' refl = refl
