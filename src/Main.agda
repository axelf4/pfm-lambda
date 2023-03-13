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

open Rpl using (·; _,_; lock)

-- Intrinsically typed terms of type A in context Γ
data _⊢_ : Ctx -> Ty -> Set where
  var : {A : Ty} {Γ : Ctx}
    -> A ∈ Γ
    -> Γ ⊢ A
  abs : {A B : Ty} {Γ : Ctx}
    -> Γ , A ⊢ B
    -> Γ ⊢ A ⟶ B
  app : {A B : Ty} {Γ : Ctx}
    -> Γ ⊢ A ⟶ B -> Γ ⊢ A
    -> Γ ⊢ B
  box : {A : Ty} {Γ : Ctx}
    -> (Γ ,🔓) ⊢ A
    -> Γ ⊢ (□ A)
  unbox : {A : Ty} {Γ Δ : Ctx}
    -> Δ ⊢ (□ A)
    -> Δ ◁ Γ
    -> Γ ⊢ A

infix 10 _⊢_

wkVar : ∀ {Γ Δ A} -> (w : Γ ⊆ Δ) -> A ∈ Γ -> A ∈ Δ
wkVar base x = x
wkVar (weak w) x = suc (wkVar w x)
wkVar (lift w) zero = zero
wkVar (lift w) (suc x) = suc (wkVar w x)

-- Variable weakening
wk : ∀ {Γ Δ A} -> Γ ⊆ Δ -> Γ ⊢ A -> Δ ⊢ A
wk w (var x) = var (wkVar w x)
wk w (abs t) = abs (wk (lift w) t)
wk w (app t s) = app (wk w t) (wk w s)
wk w (box t) = box (wk (lift🔓 w) t)
wk w (unbox t m) = let _ , (m' , w') = rewind-⊆ m w
  in unbox (wk w' t) m'

-- Substitution from variables in context Γ to terms in context Δ
Sub = Rpl _◁_ λ A Δ -> Δ ⊢ A

wkSub : {Γ Δ Δ' : Ctx} -> Δ ⊆ Δ' -> Sub Γ Δ -> Sub Γ Δ'
wkSub w · = ·
wkSub w (σ , x) = wkSub w σ , wk w x
wkSub w (lock σ m)
  = let _ , (m' , w') = rewind-⊆ m w in lock (wkSub w' σ) m'

lift-sub : {Γ Δ : Ctx} {A : Ty} -> Sub Γ Δ -> Sub (Γ , A) (Δ , A)
lift-sub σ = wkSub (weak ⊆-id) σ , var zero

id-sub : {Γ : Ctx} -> Sub Γ Γ
id-sub {·} = ·
id-sub {Γ , A} = lift-sub id-sub
id-sub {Γ ,🔓} = lock id-sub ◁1

subst : {Γ Δ : Ctx} {A : Ty} -> Sub Γ Δ -> Γ ⊢ A -> Δ ⊢ A
subst σ (abs x) = abs (subst (lift-sub σ) x)
subst σ (app x y) = app (subst σ x) (subst σ y)
subst σ (box x) = box (subst (lock σ ◁1) x)
subst σ (unbox x m) = let _ , (m' , σ') = rewindRpl m σ
  in unbox (subst σ' x) m'
subst (σ , x) (var zero) = x
subst (σ , _) (var (suc g)) = subst σ (var g)

-- Applies unit substitution.
_[_] : {Γ : Ctx} {A B : Ty} -> Γ , B ⊢ A -> Γ ⊢ B -> Γ ⊢ A
_[_] x y = subst (id-sub , y) x

-- Equivalence of terms-in-contexts
data _~_ : {Γ : Ctx} {A : Ty} -> (t s : Γ ⊢ A) -> Set where
  β : ∀ {Γ A B} -> (x : Γ , A ⊢ B) -> (y : Γ ⊢ A)
    -> app (abs x) y ~ (x [ y ])
  η : ∀ {Γ A B} {x : Γ ⊢ A ⟶ B}
    -> x ~ abs (app (wk (weak ⊆-id) x) (var zero))

  □-β : ∀ {Γ Γ' A} {x : Γ ,🔓 ⊢ A} {m : Γ ◁ Γ'}
    -> unbox (box x) m ~ subst (lock id-sub m) x
  □-η : ∀ {Γ A} -> {x : Γ ⊢ □ A}
    -> x ~ box (unbox x ◁1)

  ~-refl : ∀ {Γ A} {x : Γ ⊢ A}
    -> x ~ x
  ~-sym : ∀ {Γ A} {x y : Γ ⊢ A}
    -> x ~ y -> y ~ x
  ~-trans : ∀ {Γ A} {x y z : Γ ⊢ A}
    -> x ~ y -> y ~ z -> x ~ z

  -- Congruence rules
  cong-abs : ∀ {Γ A B} {x y : Γ , A ⊢ B}
    -> x ~ y -> abs x ~ abs y
  cong-app : ∀ {Γ A B} {x x' : Γ ⊢ A ⟶ B} {y y' : Γ ⊢ A}
    -> x ~ x' -> y ~ y' -> app x y ~ app x' y'
  cong-box : ∀ {Γ A} {x y : Γ ,🔓 ⊢ A}
    -> x ~ y -> box x ~ box y
  cong-unbox : ∀ {Γ Δ A} {x y : Δ ⊢ □ A} {m : Δ ◁ Γ}
    -> x ~ y -> unbox x m ~ unbox y m

mutual
  -- Normal forms
  data _⊢nf_ (Γ : Ctx) : Ty -> Set where
    nt : {A : Ty} -> Γ ⊢nt A -> Γ ⊢nf A
    abs : {A B : Ty} -> Γ , A ⊢nf B -> Γ ⊢nf A ⟶ B
    box : {A : Ty} -> Γ ,🔓 ⊢nf A -> Γ ⊢nf □ A
  -- Neutral terms
  data _⊢nt_ (Γ : Ctx) : Ty -> Set where
    var : {A : Ty} -> A ∈ Γ -> Γ ⊢nt A
    app : {A B : Ty} -> Γ ⊢nt A ⟶ B -> Γ ⊢nf A -> Γ ⊢nt B
    unbox : {A : Ty} {Γ' : Ctx} -> Γ' ⊢nt □ A -> Γ' ◁ Γ -> Γ ⊢nt A

infix 10 _⊢nf_ _⊢nt_

wk-nf : {Γ Δ : Ctx} {A : Ty} -> Γ ⊆ Δ -> Γ ⊢nf A -> Δ ⊢nf A
wk-nt : {Γ Δ : Ctx} {A : Ty} -> Γ ⊆ Δ -> Γ ⊢nt A -> Δ ⊢nt A
wk-nf w (nt x) = nt (wk-nt w x)
wk-nf w (abs x) = abs (wk-nf (lift w) x)
wk-nf w (box x) = box (wk-nf (lift🔓 w) x)
wk-nt w (var x) = var (wkVar w x)
wk-nt w (app x y) = app (wk-nt w x) (wk-nf w y)
wk-nt w (unbox x m) = let _ , (m' , w') = rewind-⊆ m w
  in unbox (wk-nt w' x) m'

-- Quotation of normal forms/neutrals back into terms
⌜_⌝nf : {Γ : Ctx} {A : Ty} -> Γ ⊢nf A -> Γ ⊢ A
⌜_⌝nt : {Γ : Ctx} {A : Ty} -> Γ ⊢nt A -> Γ ⊢ A
⌜ nt x ⌝nf = ⌜ x ⌝nt
⌜ abs x ⌝nf = abs ⌜ x ⌝nf
⌜ box x ⌝nf = box ⌜ x ⌝nf
⌜ var x ⌝nt = var x
⌜ app x y ⌝nt = app ⌜ x ⌝nt ⌜ y ⌝nf
⌜ unbox x m ⌝nt = unbox ⌜ x ⌝nt m

record Box' (A' : Ctx -> Set) (Γ : Ctx) : Set where
  constructor box'
  field
    unbox' : {Γ' Δ : Ctx} ->  Γ ⊆ Γ' -> Γ' ◁ Δ -> A' Δ

-- Interpret a type to a presheaf
⟦_⟧ty : Ty -> Ctx -> Set
⟦ ι ⟧ty Γ = Γ ⊢nf ι
⟦ A ⟶ B ⟧ty Γ = {Δ : Ctx} -> Γ ⊆ Δ -> ⟦ A ⟧ty Δ -> ⟦ B ⟧ty Δ
⟦ □ A ⟧ty Γ = Box' ⟦ A ⟧ty Γ

wkTy' : {A : Ty} {Γ Δ : Ctx} -> Γ ⊆ Δ -> ⟦ A ⟧ty Γ -> ⟦ A ⟧ty Δ
wkTy' {ι} w A' = wk-nf w A'
wkTy' {A ⟶ B} w A⟶B' w2 A' = A⟶B' (w ● w2) A'
wkTy' {□ A} w (box' f) = box' λ w2 -> f (w ● w2)

reify : {A : Ty} {Γ : Ctx} -> ⟦ A ⟧ty Γ -> Γ ⊢nf A
reflect : {A : Ty} {Γ : Ctx} -> Γ ⊢nt A -> ⟦ A ⟧ty Γ
reify {ι} A' = A'
reify {A ⟶ B} A⟶B' = abs (reify (A⟶B' (weak ⊆-id) (reflect (var zero))))
reify {□ A} (box' f) = let A' = f ⊆-id ◁1 in box (reify A')
reflect {ι} x = nt x
reflect {A ⟶ B} x w A' = reflect (app (wk-nt w x) (reify A'))
reflect {□ A} x = box' λ w m -> reflect (unbox (wk-nt w x) m)

-- Interpret context to a presheaf
Env = Rpl _◁_ ⟦_⟧ty
⟦_⟧ctx = Env

wkEnv : {Γ Δ Δ' : Ctx} -> Δ ⊆ Δ' -> ⟦ Γ ⟧ctx Δ -> ⟦ Γ ⟧ctx Δ'
wkEnv w · = ·
wkEnv w (Γ' , A') = wkEnv w Γ' , wkTy' w A'
wkEnv w (lock Γ' m)
  = let _ , (m' , w') = rewind-⊆ m w in lock (wkEnv w' Γ') m'

-- Interpret terms-in-contexts as natural transformations
⟦_⟧tm : {Γ : Ctx} {A : Ty} -> Γ ⊢ A -> {Δ : Ctx} -> ⟦ Γ ⟧ctx Δ -> ⟦ A ⟧ty Δ
⟦ var A∈Γ ⟧tm Γ' = lookup A∈Γ Γ'
  where
    lookup : ∀ {A Γ Δ} -> A ∈ Γ -> ⟦ Γ ⟧ctx Δ -> ⟦ A ⟧ty Δ
    lookup zero (_ , A') = A'
    lookup (suc x) (Γ' , _) = lookup x Γ'
⟦ abs x ⟧tm Γ' e y' = ⟦ x ⟧tm (wkEnv e Γ' , y')
⟦ app x y ⟧tm Γ' = ⟦ x ⟧tm Γ' ⊆-id (⟦ y ⟧tm Γ')
⟦ box x ⟧tm Γ' = box' λ w m -> ⟦ x ⟧tm (lock (wkEnv w Γ') m)
⟦_⟧tm (unbox x m) Γ' = let
  _ , (m' , Δ') = rewindRpl m Γ'
  box' f = ⟦ x ⟧tm Δ'
  in f ⊆-id m'

-- Normalization function
nf : {Γ : Ctx} {A : Ty} -> Γ ⊢ A -> Γ ⊢nf A
nf x = reify (⟦ x ⟧tm freshEnv)
  where
    -- Initial environment consisting of all neutrals
    freshEnv : {Γ : Ctx} -> ⟦ Γ ⟧ctx Γ
    freshEnv {·} = ·
    freshEnv {Γ , A} = wkEnv (weak ⊆-id) freshEnv , reflect (var zero)
    freshEnv {Γ ,🔓} = lock freshEnv ◁1
