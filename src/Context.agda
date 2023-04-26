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

    -- Composition of weakening and substitution
    trim : {Γ Γ' Δ : Ctx} -> Γ ⊆ Γ' -> Rpl Γ' Δ -> Rpl Γ Δ
    trim base · = ·
    trim (weak w) (σ , _) = trim w σ
    trim (lift w) (σ , x) = trim w σ , x
    trim (lift🔓 w) (lock σ m) = lock (trim w σ) m

    drop : {Γ Δ : Ctx} {A : Ty} -> Rpl Γ Δ -> Rpl Γ (Δ , A)
    drop = wk (weak ⊆.id)

    liftRpl : {Γ Δ : Ctx} {A : Ty} -> Rpl Γ Δ -> Rpl (Γ , A) (Δ , A)
    liftRpl σ = drop σ , head

    id : {Γ : Ctx} -> Rpl Γ Γ
    id {·} = ·
    id {x , A} = liftRpl id
    id {x ,🔓} = lock id ◁1

    from-⊆ : {Γ Δ : Ctx} -> Γ ⊆ Δ -> Rpl Γ Δ
    from-⊆ base = ·
    from-⊆ (weak w) = drop (from-⊆ w)
    from-⊆ (lift w) = from-⊆ (weak w) , head
    from-⊆ (lift🔓 w) = lock (from-⊆ w) ◁1

    trimNat : {Γ Γ' Δ Δ' : Ctx} (w : Γ' ⊆ Γ) (w' : Δ ⊆ Δ') (σ : Rpl Γ Δ)
      -> wk w' (trim w σ) ≡ trim w (wk w' σ)
    trimNat base w' · = refl
    trimNat (weak w) w' (σ , x) = trimNat w w' σ
    trimNat (lift w) w' (σ , x) = cong1 _,_ (trimNat w w' σ)
    trimNat (lift🔓 w) w' (lock σ m) = cong1 lock (trimNat w _ σ)

    trimIdl : {Γ Δ : Ctx} -> (σ : Rpl Γ Δ) -> trim ⊆.id σ ≡ σ
    trimIdl · = refl
    trimIdl (s , x) = cong (_, x) (trimIdl s)
    trimIdl (lock s m) = cong1 lock (trimIdl s)

    trimIdr : {Γ Δ : Ctx} -> (w : Γ ⊆ Δ) -> trim w id ≡ from-⊆ w
    trimIdr base = refl
    trimIdr (weak w) = ≡.trans
      (≡.sym (trimNat w (weak ⊆.id) id))
      (cong drop (trimIdr w))
    trimIdr (lift w) = cong (_, head) (≡.trans
      (≡.sym (trimNat w (weak ⊆.id) id))
      (cong drop (trimIdr w)))
    trimIdr (lift🔓 w) = cong1 lock (trimIdr w)

  module Composition
    (rewind : {Γ Γ' Δ : Ctx} -> (m : Γ' ◁ Γ) -> Rpl Γ Δ
      -> Σ Ctx λ Δ' -> Δ' ◁ Δ × Rpl Γ' Δ')
    (apply : {A : Ty} {Γ Δ : Ctx} -> Rpl Γ Δ -> F A Γ -> F A Δ)
    where
    _∙_ : {Γ Γ' Γ'' : Ctx} -> Rpl Γ Γ' -> Rpl Γ' Γ'' -> Rpl Γ Γ''
    · ∙ y = ·
    (x , a) ∙ y = (x ∙ y) , apply y a
    lock x m ∙ y
      = let _ , (m' , y') = rewind m y in lock (x ∙ y') m'

module _ {_◁_ : Ctx -> Ctx -> Set} where
  open Replacement _◁_ using (Rpl; ·; _,_; lock)

  mapRpl : {F G : Ty -> Ctx -> Set} -> ({A : Ty} {Γ : Ctx} -> F A Γ -> G A Γ)
    -> {Γ Δ : Ctx} -> Rpl F Γ Δ -> Rpl G Γ Δ
  mapRpl f · = ·
  mapRpl f (σ , x) = mapRpl f σ , f x
  mapRpl f (lock σ m) = lock (mapRpl f σ) m
