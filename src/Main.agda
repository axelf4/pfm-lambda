{-# OPTIONS --without-K #-}

open import Agda.Builtin.Sigma using (Σ; snd) renaming (_,_ to infix 20 _,_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_)
open import Data.Nat using (ℕ; zero; suc)

data Ty : Set where
  ι : Ty
  _⟶_ : Ty -> Ty -> Ty
  □_ : Ty -> Ty

infixr 30 _⟶_
infix 30 □_

-- Preterms
data Tm : Set where
  var : ℕ -> Tm
  abs : Tm -> Tm
  app : Tm -> Tm -> Tm
  box : Tm -> Tm
  unbox : Tm -> Tm

-- Typing context
data Ctx : Set where
  · : Ctx
  _,_ : (Γ : Ctx) -> (A : Ty) -> Ctx
  _,🔓 : (Γ : Ctx) -> Ctx

←🔓_ : Ctx -> Ctx
←🔓 · = ·
←🔓 (x , A) = ←🔓 x
←🔓 (x ,🔓) = x

🔓←_ : Ctx -> Ctx
🔓← · = ·
🔓← (x , A) = 🔓← x
🔓← (x ,🔓) = x ,🔓

-- The type A can be found in the context at index n.
data Get (A : Ty) : Ctx -> ℕ -> Set where
  zero : {Γ : Ctx} -> Get A (Γ , A) 0
  suc : {Γ : Ctx} {n : ℕ} {B : Ty} -> Get A Γ n -> Get A (Γ , B) (suc n)

_::_∈_ : ℕ -> (A : Ty) -> (Γ : Ctx) -> Set
n :: A ∈ Γ = Get A Γ n

-- Relation between contexts Γ and Γ' signifying that it is possible
-- to extend Γ to Γ', maybe adding any locks.
data Ext (🔓? : Set) (Γ : Ctx) : Ctx -> Set where
  nil : Ext 🔓? Γ Γ
  snoc : {Γ' : Ctx} {A : Ty} -> Ext 🔓? Γ Γ' -> Ext 🔓? Γ (Γ' , A)
  snoc🔓 : {Γ' : Ctx} -> {🔓?} -> Ext 🔓? Γ Γ' -> Ext 🔓? Γ (Γ' ,🔓)

LFExt = Ext ⊥

←🔓-of-lfExt-is-base : {Γ Γ' : Ctx} -> LFExt (Γ ,🔓) Γ' -> ←🔓 Γ' ≡ Γ
←🔓-of-lfExt-is-base nil = refl
←🔓-of-lfExt-is-base (snoc lfext) = ←🔓-of-lfExt-is-base lfext

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

-- With the pair of contexts (Γ, Δ) and an extension from Γ' to Γ,
-- rewind Γ and Δ back for as many locks as there are in the extension.

Rewind : {Γ Γ' Δ : Ctx} {🔓? : Set} -> Ext 🔓? Γ' Γ -> Γ ⊆ Δ -> Ctx
Rewind {Δ = Δ} nil _ = Δ
Rewind e@(snoc _) (weak w) = Rewind e w
Rewind (snoc e) (lift w) = Rewind e w
Rewind e@(snoc🔓 _) (weak w) = Rewind e w
Rewind (snoc🔓 e) (lift🔓 w) = Rewind e w

-- Drops the part of the OPE that pertains to the context extension
rewind-⊆ : {Γ Γ' Δ : Ctx} {🔓? : Set} -> (e : Ext 🔓? Γ' Γ) -> (w : Γ ⊆ Δ) -> Γ' ⊆ Rewind e w
rewind-⊆ nil w = w
rewind-⊆ e@(snoc _) (weak w) = rewind-⊆ e w
rewind-⊆ (snoc e) (lift w) = rewind-⊆ e w
rewind-⊆ e@(snoc🔓 _) (weak w) = rewind-⊆ e w
rewind-⊆ (snoc🔓 e) (lift🔓 w) = rewind-⊆ e w

lfext-to-⊆ : {Γ Γ' : Ctx} -> LFExt Γ Γ' -> Γ ⊆ Γ'
lfext-to-⊆ nil = ⊆-id
lfext-to-⊆ (snoc x) = weak (lfext-to-⊆ x)

wkExt : {ΓL Γ Δ : Ctx} {🔓? : Set} -> (w : Γ ⊆ Δ) -> (e : Ext 🔓? ΓL Γ) -> Ext 🔓? (Rewind e w) Δ
wkExt w nil = nil
wkExt (weak w) e@(snoc _) = snoc (wkExt w e)
wkExt (lift w) (snoc e) = snoc (wkExt w e)
wkExt (weak w) e@(snoc🔓 _) = snoc (wkExt w e)
wkExt (lift🔓 w) (snoc🔓 {Γ' = _} {θ} e) = snoc🔓 {Γ' = _} {θ} (wkExt w e)
  
module _
  -- Modal accessibility relation on contexts
  -- (\lhd -> ◁)
  (_◁_ : Ctx -> Ctx -> Set)
  (wk-◁ : {Γ Γ' Δ : Ctx} -> (w : Γ ⊆ Δ) -> (e : Ext ⊤ Γ' Γ) -> Γ' ◁ Γ -> Rewind e w ◁ Δ)
  (◁1 : {Γ : Ctx} -> Γ ◁ (Γ ,🔓))
  where

  -- Typing judgement: Term t is of type A in context Γ.
  data _⊢_::_ : Ctx -> Tm -> Ty -> Set where
    var : {n : ℕ} {A : Ty} {Γ : Ctx}
      -> n :: A ∈ Γ
      -> Γ ⊢ var n :: A
  
    abs : {A B : Ty} {Γ : Ctx} {t : Tm}
      -> Γ , A ⊢ t :: B
      -> Γ ⊢ abs t :: A ⟶ B
  
    app : {A B : Ty} {Γ : Ctx} {t u : Tm}
      -> Γ ⊢ t :: A ⟶ B -> Γ ⊢ u :: A
      -> Γ ⊢ app t u :: B
  
    box : {A : Ty} {Γ : Ctx} {t : Tm}
      -> (Γ ,🔓) ⊢ t :: A
      -> Γ ⊢ box t :: (□ A)
  
    unbox : {A : Ty} {Γ Δ : Ctx} {t : Tm}
      -> Δ ⊢ t :: (□ A)
      -> Ext ⊤ Δ Γ -> Δ ◁ Γ
      -> Γ ⊢ unbox t :: A
  
  infix 10 _⊢_::_
  
  wk-var : ∀ {Γ Δ A n} -> (w : Γ ⊆ Δ) -> n :: A ∈ Γ -> Σ ℕ (_:: A ∈ Δ)
  wk-var {n = n} base x = n , x
  wk-var (weak w) x = let m , y = wk-var w x in suc m , suc y
  wk-var (lift w) zero = 0 , zero
  wk-var (lift w) (suc x) = let m , y = wk-var w x in suc m , suc y
  
  -- Variable weakening
  wk : ∀ {Γ Δ t A} -> (w : Γ ⊆ Δ)
    -> Γ ⊢ t :: A -> Σ Tm λ t' -> Δ ⊢ t' :: A
  wk w (var x) = let m , y = wk-var w x in var m , var y
  wk w (abs t) = let t' , x = wk (lift w) t in abs t' , abs x
  wk w (app t s) = let
    t' , x = wk w t
    s' , y = wk w s
    in app t' s' , app x y
  wk w (box t) = let t' , x = wk (lift🔓 w) t in box t' , box x
  wk {Δ = Δ} {A = A} w (unbox t e acc) = let
    t' , x = wk (rewind-⊆ e w) t
    in unbox t' , unbox x (wkExt w e) (wk-◁ w e acc)
  
  -- Substitution from variables in context Γ to terms in context Δ.
  data Sub : Ctx -> Ctx -> Set where
    base : {Δ : Ctx} -> Sub · Δ
    sub : {Γ Δ : Ctx} {A : Ty} {t : Tm}
      -> (σ : Sub Γ Δ)
      -> Δ ⊢ t :: A
      -> Sub (Γ , A) Δ
    lock : {Γ Δ Δ' : Ctx} -> (σ : Sub Γ Δ) -> Ext ⊤ Δ Δ' -> Sub (Γ ,🔓) Δ'
  
  wkSub : {Γ Δ Δ' : Ctx} -> Δ ⊆ Δ' -> Sub Γ Δ -> Sub Γ Δ'
  wkSub w base = base
  wkSub w (sub σ x) = sub (wkSub w σ) (snd (wk w x))
  wkSub w (lock σ e) = lock (wkSub (rewind-⊆ e w) σ) (wkExt w e)
  
  lift-sub : {Γ Δ : Ctx} {A : Ty} -> Sub Γ Δ -> Sub (Γ , A) (Δ , A)
  lift-sub σ = sub (wkSub (weak ⊆-id) σ) (var zero)
  
  id-sub : {Γ : Ctx} -> Sub Γ Γ
  id-sub {·} = base
  id-sub {Γ , A} = lift-sub id-sub
  id-sub {Γ ,🔓} = lock id-sub (snoc🔓 nil)
  
  subst : {Γ Δ : Ctx} {A : Ty} {t : Tm}
    -> Sub Γ Δ -> Γ ⊢ t :: A -> Σ Tm λ t' -> Δ ⊢ t' :: A
  subst σ (abs x) = let t , y = subst (lift-sub σ) x in abs t , abs y
  subst σ (app x y) = let
    t , x' = subst σ x
    s , y' = subst σ y
    in app t s , app x' y'
  subst σ (box x) = let t , y = subst (lock σ (snoc🔓 nil)) x in box t , box y
  subst σ (unbox x ext acc) = let t , y = subst (rewindSub ext σ) x
    in unbox t , unbox y (wkExtSub ext σ) {!!}
    where
      RewindSub : {Γ Γ' Δ : Ctx} {🔓? : Set} -> (e : Ext 🔓? Γ' Γ) -> (σ : Sub Γ Δ) -> Ctx
      RewindSub {Δ = Δ} nil _ = Δ
      RewindSub (snoc e) (sub σ _) = RewindSub e σ
      RewindSub (snoc🔓 e) (lock σ _) = RewindSub e σ

      -- This is wkExt but with a substitution instead of an OPE.
      -- Note: This will not be a "weakening" in the general case.
      wkExtSub : {Γ Γ' Δ : Ctx} {🔓? : Set} -> (e : Ext 🔓? Γ' Γ) -> (σ : Sub Γ Δ) -> Ext 🔓? (RewindSub e σ) Δ
      wkExtSub nil _ = nil
      wkExtSub (snoc e) (sub σ _) = wkExtSub e σ
      wkExtSub (snoc🔓 e) (lock σ nil) = wkExtSub e σ
      wkExtSub {🔓? = 🔓?} (snoc🔓 {_} {θ} e) (lock {Δ = Δ'} σ (snoc🔓 ext))
        = snoc🔓 {Γ' = _} {θ} (go ext)
        where
          go : {Δ : Ctx} -> Ext ⊤ Δ' Δ -> Ext 🔓? _ Δ
          go nil = wkExtSub e σ
          go (snoc e) = snoc (go e)
          go (snoc🔓 e) = snoc🔓 {Γ' = _} {θ} (go e)
      wkExtSub e@(snoc🔓 _) (lock σ (snoc lfext)) = snoc (wkExtSub e (lock σ lfext))
  
      rewindSub : {Γ Γ' Δ : Ctx} {🔓? : Set} -> (e : Ext 🔓? Γ' Γ) -> (σ : Sub Γ Δ) -> Sub Γ' (RewindSub e σ)
      rewindSub nil σ = σ
      rewindSub (snoc e) (sub σ x) = rewindSub e σ
      rewindSub (snoc🔓 e) (lock σ lfext) = rewindSub e σ
  subst (sub {t = t'} σ x) (var zero) = t' , x
  subst (sub σ x) (var (suc g)) = subst σ (var g)
  
  -- Applies unit substitution.
  _[_] : {Γ : Ctx} {t s : Tm} {A B : Ty}
    -> Γ , B ⊢ t :: A
    -> Γ ⊢ s :: B
    -> Σ Tm λ t' -> Γ ⊢ t' :: A
  _[_] x y = subst (sub id-sub y) x
  
  -- Equivalence of terms-in-context
  data _≅_ : {Γ : Ctx} {t s : Tm} {A : Ty}
    -> Γ ⊢ t :: A -> Γ ⊢ s :: A -> Set where
    ≅-refl : ∀ {Γ t A} {x : Γ ⊢ t :: A}
      -> x ≅ x
    ≅-sym : ∀ {Γ t s A} {x : Γ ⊢ t :: A} {y : Γ ⊢ s :: A}
      -> x ≅ y -> y ≅ x
    ≅-trans : ∀ {Γ t s u A} {x : Γ ⊢ t :: A} {y : Γ ⊢ s :: A} {z : Γ ⊢ u :: A}
      -> x ≅ y -> y ≅ z -> x ≅ z
  
    β : ∀ {Γ t A B} -> (x : Γ , A ⊢ t :: B) -> (y : Γ ⊢ t :: A)
      -> app (abs x) y ≅ snd (x [ y ])
    η : ∀ {Γ t A B} {x : Γ ⊢ t :: A ⟶ B}
      -> x ≅ abs (app (snd (wk (weak ⊆-id) x)) (var zero))
  
    □-red : ∀ {Γ Γ' t A} {x : Γ ,🔓 ⊢ t :: A} {e : Ext ⊤ Γ Γ'} {acc : Γ ◁ Γ'}
      -> unbox (box x) e acc ≅ snd (subst (lock id-sub e) x)
    □-conv : ∀ {Γ t A} -> {x : Γ ⊢ t :: □ A}
      -> x ≅ box (unbox x (snoc🔓 nil) ◁1)
  
    -- Congruence rules
    cong-abs : ∀ {Γ t t' A B} {x : Γ , A ⊢ t :: B} {y : Γ , A ⊢ t' :: B}
      -> x ≅ y -> abs x ≅ abs y
