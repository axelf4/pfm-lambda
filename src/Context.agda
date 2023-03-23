{-# OPTIONS --without-K --safe #-}

module Context where

open import Agda.Builtin.Sigma using (Σ; snd) renaming (_,_ to infix 20 _,_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl; cong)
open import Data.Empty using (⊥)
open import Data.Product using (_×_)

open import Util using (cong1)

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

-- Composition of weakenings (and transitivity proof)
_●_ : {Γ Γ' Γ'' : Ctx} -> Γ ⊆ Γ' -> Γ' ⊆ Γ'' -> Γ ⊆ Γ''
x ● base = x
x ● (weak y) = weak (x ● y)
(weak x) ● (lift y) = weak (x ● y)
(lift x) ● (lift y) = lift (x ● y)
(lift🔓 x) ● (lift🔓 y) = lift🔓 (x ● y)

module ⊆ where
  id : {Γ : Ctx} -> Γ ⊆ Γ
  id {·} = base
  id {Γ , A} = lift id
  id {Γ ,🔓} = lift🔓 id

  idl : {Γ Δ : Ctx} {w : Γ ⊆ Δ} -> id ● w ≡ w
  idl {w = base} = refl
  idl {w = weak w} = cong weak idl
  idl {w = lift w} = cong lift idl
  idl {w = lift🔓 w} = cong lift🔓 idl

  idr : {Γ Δ : Ctx} {w : Γ ⊆ Δ} -> w ● id ≡ w
  idr {w = base} = refl
  idr {w = weak w} = cong weak idr
  idr {w = lift w} = cong lift idr
  idr {w = lift🔓 w} = cong lift🔓 idr

wkVar : {A : Ty} {Γ Δ : Ctx} -> Γ ⊆ Δ -> A ∈ Γ -> A ∈ Δ
wkVar base x = x
wkVar (weak w) x = suc (wkVar w x)
wkVar (lift w) zero = zero
wkVar (lift w) (suc x) = suc (wkVar w x)

wkVarId : {A : Ty} {Γ : Ctx} -> (x : A ∈ Γ) -> wkVar ⊆.id x ≡ x
wkVarId zero = refl
wkVarId (suc x) = cong suc (wkVarId x)

module Replacement (_◁_ : Ctx -> Ctx -> Set) (F : Ty -> Ctx -> Set) where
  -- For every item in context Γ there is a replacement value in context Δ.
  data Rpl : Ctx -> Ctx -> Set where
    · : {Δ : Ctx} -> Rpl · Δ
    _,_ : {Γ Δ : Ctx} {A : Ty} -> Rpl Γ Δ -> F A Δ -> Rpl (Γ , A) Δ
    lock : {Γ Δ Δ' : Ctx} -> Rpl Γ Δ -> Δ ◁ Δ' -> Rpl (Γ ,🔓) Δ'

  module Properties
    (◁1 : {Γ : Ctx} -> Γ ◁ (Γ ,🔓))
    (rewind-⊆ : {Γ Γ' Δ : Ctx} -> (m : Γ' ◁ Γ) -> Γ ⊆ Δ
      -> Σ Ctx λ Δ' -> Δ' ◁ Δ × Γ' ⊆ Δ')
    (wkF : {A : Ty} {Γ Γ' : Ctx} -> Γ ⊆ Γ' -> F A Γ -> F A Γ')
    (head : {A : Ty} {Γ : Ctx} -> F A (Γ , A))
    where

    -- Composition of substitution and weakening
    wk : {Γ Δ Δ' : Ctx} -> Δ ⊆ Δ' -> Rpl Γ Δ -> Rpl Γ Δ'
    wk w · = ·
    wk w (σ , x) = wk w σ , wkF w x
    wk w (lock σ m)
      = let _ , (m' , w') = rewind-⊆ m w in lock (wk w' σ) m'

    drop : {Γ Δ : Ctx} {A : Ty} -> Rpl Γ Δ -> Rpl Γ (Δ , A)
    drop = wk (weak ⊆.id)

    liftRpl : {Γ Δ : Ctx} {A : Ty} -> Rpl Γ Δ -> Rpl (Γ , A) (Δ , A)
    liftRpl σ = drop σ , head

    id : {Γ : Ctx} -> Rpl Γ Γ
    id {·} = ·
    id {x , A} = liftRpl id
    id {x ,🔓} = lock id ◁1
