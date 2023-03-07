{-# OPTIONS --without-K --safe #-}

open import Agda.Builtin.Sigma using (Σ; snd) renaming (_,_ to infix 20 _,_)
open import Data.Product using (_×_)
open import Data.Nat using (ℕ; zero; suc)

open import Context

module _
  -- Modal accessibility relation on contexts
  -- (\lhd -> ◁)
  (_◁_ : Ctx -> Ctx -> Set)
  (◁1 : {Γ : Ctx} -> Γ ◁ (Γ ,🔓))
  -- Trim OPE:s and substitutions/environments
  (rewind-⊆ : {Γ Γ' Δ : Ctx}
    -> (m : Γ' ◁ Γ) -> (w : Γ ⊆ Δ)
    -> Σ Ctx λ Δ' -> Δ' ◁ Δ × Γ' ⊆ Δ')
  (rewindRpl : {F : Ty -> Ctx -> Set} {Γ Γ' Δ : Ctx}
    -> (m : Γ' ◁ Γ) -> (x : Rpl _◁_ F Γ Δ)
    -> Σ Ctx λ Δ' -> Δ' ◁ Δ × Rpl _◁_ F Γ' Δ')
  where

-- Preterms
data Tm : Set where
  var : ℕ -> Tm
  abs : Tm -> Tm
  app : Tm -> Tm -> Tm
  box : Tm -> Tm
  unbox : Tm -> Tm

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
    -> Δ ◁ Γ
    -> Γ ⊢ unbox t :: A

infix 10 _⊢_::_

wkVar : ∀ {Γ Δ A n} -> (w : Γ ⊆ Δ) -> n :: A ∈ Γ -> Σ ℕ (_:: A ∈ Δ)
wkVar base x = _ , x
wkVar (weak w) x = _ , suc (snd (wkVar w x))
wkVar (lift w) zero = 0 , zero
wkVar (lift w) (suc x) = _ , suc (snd (wkVar w x))

-- Variable weakening
wk : ∀ {Γ Δ t A} -> Γ ⊆ Δ -> Γ ⊢ t :: A -> Σ Tm (Δ ⊢_:: A)
wk w (var x) = _ , var (snd (wkVar w x))
wk w (abs t) = _ , abs (snd (wk (lift w) t))
wk w (app t s) = _ , app (snd (wk w t)) (snd (wk w s))
wk w (box t) = _ , box (snd (wk (lift🔓 w) t))
wk w (unbox t m) = let _ , (m' , w') = rewind-⊆ m w
  in _ , unbox (snd (wk w' t)) m'

-- Substitution from variables in context Γ to terms in context Δ
Sub = Rpl _◁_ λ A Δ -> Σ Tm (Δ ⊢_:: A)

wkSub : {Γ Δ Δ' : Ctx} -> Δ ⊆ Δ' -> Sub Γ Δ -> Sub Γ Δ'
wkSub w · = ·
wkSub w (σ , x) = wkSub w σ , wk w (snd x)
wkSub w (lock σ m)
  = let _ , (m' , w') = rewind-⊆ m w in lock (wkSub w' σ) m'

lift-sub : {Γ Δ : Ctx} {A : Ty} -> Sub Γ Δ -> Sub (Γ , A) (Δ , A)
lift-sub σ = wkSub (weak ⊆-id) σ , (var 0 , var zero)

id-sub : {Γ : Ctx} -> Sub Γ Γ
id-sub {·} = ·
id-sub {Γ , A} = lift-sub id-sub
id-sub {Γ ,🔓} = lock id-sub ◁1

subst : {Γ Δ : Ctx} {A : Ty} {t : Tm}
  -> Sub Γ Δ -> Γ ⊢ t :: A -> Σ Tm (Δ ⊢_:: A)
subst σ (abs x) = _ , abs (snd (subst (lift-sub σ) x))
subst σ (app x y) = _ , app (snd (subst σ x)) (snd (subst σ y))
subst σ (box x) = _ , box (snd (subst (lock σ ◁1) x))
subst σ (unbox x m) = let _ , (m' , σ') = rewindRpl m σ
  in _ , unbox (snd (subst σ' x)) m'
subst (σ , x) (var zero) = x
subst (σ , _) (var (suc g)) = subst σ (var g)

-- Applies unit substitution.
_[_] : {Γ : Ctx} {t s : Tm} {A B : Ty}
  -> Γ , B ⊢ t :: A
  -> Γ ⊢ s :: B
  -> Σ Tm (Γ ⊢_:: A)
_[_] {s = s} x y = subst (id-sub , (s , y)) x

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

  □-β : ∀ {Γ Γ' t A} {x : Γ ,🔓 ⊢ t :: A} {m : Γ ◁ Γ'}
    -> unbox (box x) m ≅ snd (subst (lock id-sub m) x)
  □-η : ∀ {Γ t A} -> {x : Γ ⊢ t :: □ A}
    -> x ≅ box (unbox x ◁1)

  -- Congruence rules
  cong-abs : ∀ {Γ t t' A B} {x : Γ , A ⊢ t :: B} {y : Γ , A ⊢ t' :: B}
    -> x ≅ y -> abs x ≅ abs y
  cong-app1 : ∀ {Γ t t' t'' A B} {x : Γ ⊢ t :: A ⟶ B} {x' : Γ ⊢ t' :: A ⟶ B} {y : Γ ⊢ t'' :: A}
    -> x ≅ x' -> app x y ≅ app x' y
  cong-app2 : ∀ {Γ t t' t'' A B} {x : Γ ⊢ t :: A ⟶ B} {y : Γ ⊢ t' :: A} {y' : Γ ⊢ t'' :: A}
    -> y ≅ y' -> app x y ≅ app x y'
  cong-box : ∀ {Γ t t' A} {x : Γ ,🔓 ⊢ t :: A} {y : Γ ,🔓 ⊢ t' :: A}
    -> x ≅ y -> box x ≅ box y
  cong-unbox : ∀ {Γ Δ t t' A} {x : Δ ⊢ t :: □ A} {y : Δ ⊢ t' :: □ A} {m : Δ ◁ Γ}
    -> x ≅ y -> unbox x m ≅ unbox y m
