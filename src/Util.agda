{-# OPTIONS --without-K --safe #-}

module Util where

open import Function using (Inverse)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Product.Properties using (Σ-≡,≡↔≡; ×-≡,≡↔≡)

-- Congruence w.r.t. the first argument of a binary function
cong1 : {A B C : Set} (f : A -> B -> C) {x x' : A} {y : B}
  -> x ≡ x' -> f x y ≡ f x' y
cong1 f refl = refl

module _ {a} {b} {c} {d} where
  dcong₃ : ∀ {A : Set a} {B : A -> Set b} {C : A -> Set c} {D : Set d}
    (f : (x : A) -> B x -> C x -> D) {x₁ x₂ y₁ y₂ z₁ z₂}
    -> (p : x₁ ≡ x₂) -> subst B p y₁ ≡ y₂ -> subst C p z₁ ≡ z₂
    -> f x₁ y₁ z₁ ≡ f x₂ y₂ z₂
  dcong₃ _f refl refl refl = refl

module _ {a p q} {A : Set a} {P : A -> Set p} {Q : A -> Set q}
  (g : {x : A} -> P x -> Q x) where
  subst-application' : ∀ {x₁ x₂ y} -> (eq : x₁ ≡ x₂)
    -> subst Q eq (g y) ≡ g (subst P eq y)
  subst-application' refl = refl

Σ×-≡,≡,≡→≡ : {A : Set} {B B' : A -> Set} {p₁@(a₁ , b₁ , b₁') p₂@(a₂ , b₂ , b₂') : Σ A λ a -> B a × B' a}
  -> (Σ (a₁ ≡ a₂) λ p -> subst B p b₁ ≡ b₂ × subst B' p b₁' ≡ b₂')
  -> p₁ ≡ p₂
Σ×-≡,≡,≡→≡ {A} {_B} {_B'} {p₁} {p₂} (p , q , q') = Σ-≡,≡↔≡ .Inverse.f (p
  , ×-≡,≡↔≡ .Inverse.f (trans (sym (subst-application' proj₁ p)) q
  , trans (sym (subst-application' proj₂ p)) q'))
