{-# OPTIONS --without-K --safe #-}

module Context where

open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero; suc)

data Ty : Set where
  ι : Ty
  _⟶_ : Ty -> Ty -> Ty
  □_ : Ty -> Ty

infixr 30 _⟶_
infix 30 □_

-- Typing context
data Ctx : Set where
  · : Ctx
  _,_ : (Γ : Ctx) -> (A : Ty) -> Ctx
  _,🔓 : (Γ : Ctx) -> Ctx

-- The type A can be found in the context at index n.
data _∈_ (A : Ty) : Ctx -> Set where
  zero : {Γ : Ctx} -> A ∈ (Γ , A)
  suc : {Γ : Ctx} {B : Ty} -> A ∈ Γ -> A ∈ (Γ , B)

-- Relation between contexts Γ and Γ' signifying that it is possible
-- to extend Γ to Γ', maybe adding any locks.
data Ext (🔓? : Set) (Γ : Ctx) : Ctx -> Set where
  nil : Ext 🔓? Γ Γ
  snoc : {Γ' : Ctx} {A : Ty} -> Ext 🔓? Γ Γ' -> Ext 🔓? Γ (Γ' , A)
  snoc🔓 : {Γ' : Ctx} -> {🔓?} -> Ext 🔓? Γ Γ' -> Ext 🔓? Γ (Γ' ,🔓)

LFExt = Ext ⊥
{-# DISPLAY Ext ⊥ = LFExt #-}

-- Order-preserving embedding (OPE).
--
-- For Γ ⊆ Δ, Δ is weaker than Γ since it has additional assumptions,
-- i.e. Γ is a subsequence of Δ.
data _⊆_ : Ctx -> Ctx -> Set where
  base : · ⊆ ·
  weak : ∀ {A Γ Δ} -> Γ ⊆ Δ -> Γ ⊆ Δ , A
  lift : ∀ {A Γ Δ} -> Γ ⊆ Δ -> Γ , A ⊆ Δ , A
  lift🔓 : ∀ {Γ Δ} -> Γ ⊆ Δ -> Γ ,🔓 ⊆ Δ ,🔓

infix 10 _⊆_

⊆-id : {Γ : Ctx} -> Γ ⊆ Γ
⊆-id {·} = base
⊆-id {Γ , A} = lift ⊆-id
⊆-id {Γ ,🔓} = lift🔓 ⊆-id

-- Composition of weakenings (and transitivity proof).
_●_ : {Γ Γ' Γ'' : Ctx} -> Γ ⊆ Γ' -> Γ' ⊆ Γ'' -> Γ ⊆ Γ''
x ● base = x
x ● (weak y) = weak (x ● y)
(weak x) ● (lift y) = weak (x ● y)
(lift x) ● (lift y) = lift (x ● y)
(lift🔓 x) ● (lift🔓 y) = lift🔓 (x ● y)

-- For every item in context Γ there is a replacement value in context Δ.
data Rpl (_◁_ : Ctx -> Ctx -> Set) (F : Ty -> Ctx -> Set)
  : Ctx -> Ctx -> Set where
  · : {Δ : Ctx} -> Rpl _◁_ F · Δ
  _,_ : {Γ Δ : Ctx} {A : Ty} -> Rpl _◁_ F Γ Δ -> F A Δ -> Rpl _◁_ F (Γ , A) Δ
  lock : {Γ Δ Δ' : Ctx} -> Rpl _◁_ F Γ Δ -> Δ ◁ Δ' -> Rpl _◁_ F (Γ ,🔓) Δ'
