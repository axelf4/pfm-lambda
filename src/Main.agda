open import Agda.Builtin.Sigma using (Σ; snd) renaming (_,_ to _,,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
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

infixl 40 _,_
infix 40 _,🔓

←🔓_ : Ctx -> Ctx
←🔓 · = ·
←🔓 (x , A) = ←🔓 x
←🔓 (x ,🔓) = x

🔓←_ : Ctx -> Ctx
🔓← · = ·
🔓← (x , A) = 🔓← x
🔓← (x ,🔓) = x ,🔓


infix 30 ←🔓_ -- TODO

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

nil-lfExt-eq : {Γ Γ' : Ctx} -> LFExt (Γ ,🔓) (Γ' ,🔓) -> Γ ≡ Γ'
nil-lfExt-eq nil = refl

←🔓-of-lfExt-is-base : {Γ Γ' : Ctx} -> LFExt (Γ ,🔓) Γ' -> ←🔓 Γ' ≡ Γ
←🔓-of-lfExt-is-base nil = refl
←🔓-of-lfExt-is-base (snoc lfext) = ←🔓-of-lfExt-is-base lfext

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

  unbox : {A : Ty} {Γ Γ' : Ctx} {t : Tm}
    -> Γ ⊢ t :: (□ A)
    -> LFExt (Γ ,🔓) Γ'
    -> Γ' ⊢ unbox t :: A

-- Weakening relation.
--
-- For Γ ⊆ Δ, Δ is weaker than Γ since it has additional assumptions.
data _⊆_ : Ctx -> Ctx -> Set where
  base : · ⊆ ·
  push : ∀ {A Γ Δ} -> Γ ⊆ Δ -> Γ ⊆ Δ , A
  lift : ∀ {A Γ Δ} -> Γ ⊆ Δ -> Γ , A ⊆ Δ , A
  lift🔓 : ∀ {Γ Δ} -> Γ ⊆ Δ -> Γ ,🔓 ⊆ Δ ,🔓

idWk : {Γ : Ctx} -> Γ ⊆ Γ
idWk {·} = base
idWk {Γ , A} = lift idWk
idWk {Γ ,🔓} = lift🔓 idWk

lfext-to-wk : {Γ Γ' : Ctx} -> LFExt Γ Γ' -> Γ ⊆ Γ'
lfext-to-wk nil = idWk
lfext-to-wk (snoc x) = push (lfext-to-wk x)

wkLFExt : {ΓL Γ Δ : Ctx} -> Γ ⊆ Δ -> LFExt (ΓL ,🔓) Γ -> LFExt ((←🔓 Δ) ,🔓) Δ
wkLFExt (push w) e = snoc (wkLFExt w e)
wkLFExt (lift w) (snoc e) = snoc (wkLFExt w e)
wkLFExt (lift🔓 w) e = nil

-- Variable weakening
wk : ∀ {Γ Δ t A} -> (w : Γ ⊆ Δ)
  -> Γ ⊢ t :: A -> Σ Tm λ t' -> Δ ⊢ t' :: A
wk w (var x) = let m ,, y = go w x in var m ,, var y
  where
    go : ∀ {Γ Δ A n} -> (w : Γ ⊆ Δ) -> Get A Γ n -> Σ ℕ (Get A Δ)
    go {n = n} base x = n ,, x
    go (push w) x = let m ,, y = go w x in suc m ,, suc y
    go (lift w) zero = 0 ,, zero
    go (lift w) (suc x) = let m ,, y = go w x in suc m ,, suc y
wk w (abs t) = let t' ,, x = wk (lift w) t in abs t' ,, abs x
wk w (app t s) = let
  t' ,, x = wk w t
  s' ,, y = wk w s
  in app t' s' ,, app x y
wk w (box t) = let t' ,, x = wk (lift🔓 w) t in box t' ,, box x
wk {Δ = Δ} {A = A} w (unbox t lfext) = let
  t' ,, x = wk (dropLFExt lfext w) t
  in unbox t' ,, unbox x (wkLFExt w lfext)
  where
    -- Drop the part of the weakening that pertains to the lock-free extension.
    dropLFExt : ∀ {Γ Γ' Δ} -> LFExt (Γ ,🔓) Γ' -> Γ' ⊆ Δ -> Γ ⊆ ←🔓 Δ
    dropLFExt lfext (push w) = dropLFExt lfext w
    dropLFExt (snoc lfext) (lift w) = dropLFExt lfext w
    dropLFExt lfext (lift🔓 w) rewrite nil-lfExt-eq lfext = w

-- -- TODO Naming
-- slice-wk-left-of-🔓 : {Γ Γ' Γ'' : Ctx} -> LFExt (Γ' ,🔓) Γ -> Γ ⊆ Γ'' -> Γ' ⊆ ←🔓 Γ''
-- slice-wk-left-of-🔓 lfext (push w) = slice-wk-left-of-🔓 lfext w
-- slice-wk-left-of-🔓 (snoc lfext) (lift w) = slice-wk-left-of-🔓 lfext w
-- slice-wk-left-of-🔓 nil (lift🔓 w) = w

-- Substitution from variables in context Γ to terms in context Δ.
data Sub : Ctx -> Ctx -> Set where
  -- base : Sub · ·
  -- sub : {Γ Δ : Ctx} -> (σ : Sub (🔓← Γ) (🔓← Δ))
  --   -> (∀ {A n} -> n :: A ∈ Γ -> Σ Tm λ t -> Δ ⊢ t :: A)
  --   -> Sub Γ Δ
  -- lock : {Γ Δ : Ctx} -> (σ : Sub Γ Δ) -> Sub (Γ ,🔓) (Δ ,🔓)
  base : {Δ : Ctx} -> Sub · Δ
  sub : {Γ Δ : Ctx} {A : Ty} {t : Tm}
    -> (σ : Sub Γ Δ)
    -> Δ ⊢ t :: A
    -> Sub (Γ , A) Δ
  lock : {Γ Δ Δ' : Ctx} -> (σ : Sub Γ Δ) -> LFExt (Δ ,🔓) Δ' -> Sub (Γ ,🔓) Δ'

-- wkSub : {Γ Δ Δ' : Ctx} -> Δ ⊆ Δ' -> Sub Γ Δ -> Sub Γ Δ'
-- wkSub w base = base
-- wkSub w (sub σ f) = sub (wkSub w σ) λ x -> wk w (snd (f x))
-- -- wkSub w (lock σ ext) = lock (wkSub (slice-wk-left-of-🔓 ext w) σ) (wkLFExt w ext)

lift-sub : {Γ Δ : Ctx} {A : Ty} -> Sub Γ Δ -> Sub (Γ , A) (Δ , A)
-- -- lift-sub σ = wkSub (push idWk) (keep σ)
-- -- lift-sub base = sub base (λ x -> var 0 ,, {!var x!})
-- lift-sub base = sub base λ { zero → var 0 ,, var zero }
-- lift-sub (sub σ f) = sub σ λ
--   { zero → var 0 ,, var zero
--   ; (suc x) → wk (push idWk) (snd (f x))
--   }
-- lift-sub x@(lock σ) = sub x λ { zero → var 0 ,, var zero }
lift-sub σ = sub (wk-sub σ) (var zero)
  where
    wk-sub : ∀ {Γ Δ A} -> Sub Γ Δ -> Sub Γ (Δ , A)
    wk-sub base = base
    wk-sub (sub s x) = sub (wk-sub s) (snd (wk (push idWk) x))
    wk-sub (lock s ext) = lock s (snoc ext)

id-sub : {Γ : Ctx} -> Sub Γ Γ
id-sub {·} = base
id-sub {Γ , A} = lift-sub id-sub
id-sub {Γ ,🔓} = lock id-sub nil

subst : {Γ Δ : Ctx} {A : Ty} {t : Tm}
  -> Sub Γ Δ -> Γ ⊢ t :: A -> Σ Tm λ t' -> Δ ⊢ t' :: A
subst σ (abs x) = let t ,, y = subst (lift-sub σ) x in abs t ,, abs y
subst σ (app x y) = let
  t ,, x' = subst σ x
  s ,, y' = subst σ y
  in app t s ,, app x' y'
subst σ (box x) = let t ,, y = subst (lock σ nil) x in box t ,, box y
subst σ (unbox x ext) = let t ,, y = subst (rewind-sub ext σ) x
  in unbox t ,, unbox y (rewind-sub-ext ext σ)
  where
    -- With the pair of contexts (Γ', Δ) and an extension from Γ to Γ',
    -- rewind Δ back for as many locks as there are in the extension.

    rewind-sub-ty : {Γ Γ' Δ : Ctx} -> (e : LFExt (Γ ,🔓) Γ') -> (σ : Sub Γ' Δ) -> Ctx
    rewind-sub-ty nil (lock {Δ = Δ} _σ _ext) = Δ
    rewind-sub-ty (snoc e) (sub σ _) = rewind-sub-ty e σ

    rewind-sub-ext : {Γ Γ' Δ : Ctx} -> (e : LFExt (Γ ,🔓) Γ') -> (σ : Sub Γ' Δ) -> LFExt ((rewind-sub-ty e σ) ,🔓) Δ
    rewind-sub-ext nil (lock {Δ = Δ} _σ ext) = ext
    rewind-sub-ext (snoc e) (sub σ _) = rewind-sub-ext e σ

    rewind-sub : {Γ Γ' Δ : Ctx} -> (e : LFExt (Γ ,🔓) Γ') -> (σ : Sub Γ' Δ) -> Sub Γ (rewind-sub-ty e σ)
    rewind-sub nil (lock σ ext) = σ
    rewind-sub (snoc lfext) (sub σ x) = rewind-sub lfext σ
subst (sub {t = t'} σ x) (var zero) = t' ,, x
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

  β-red : ∀ {Γ t A B} -> (x : Γ , A ⊢ t :: B) -> (y : Γ ⊢ t :: A)
    -> app (abs x) y ≅ snd (x [ y ])
  η-conv : ∀ {Γ t A B} {x : Γ ⊢ t :: A ⟶ B}
    -> x ≅ abs (app (snd (wk (push idWk) x)) (var zero))

  □-red : ∀ {Γ Γ' t A} {x : Γ ,🔓 ⊢ t :: A} {ext : LFExt (Γ ,🔓) Γ'}
    -> unbox (box x) ext ≅ snd (wk (lfext-to-wk ext) x)
  □-conv : ∀ {Γ t A} -> {x : Γ ⊢ t :: □ A}
    -> x ≅ box (unbox x nil)

  -- Congruence rules
  cong-abs : ∀ {Γ t t' A B} {x : Γ , A ⊢ t :: B} {y : Γ , A ⊢ t' :: B}
    -> x ≅ y -> abs x ≅ abs y

mutual
  -- Neutral forms
  data _⊢nt_ : Ctx -> Ty -> Set where
    var : {Γ : Ctx} {A : Ty} -> (n : ℕ) -> Get A Γ n -> Γ ⊢nt A
    app : {Γ : Ctx} {A B : Ty} -> Γ ⊢nt A ⟶ B -> Γ ⊢nf A -> Γ ⊢nt B
  -- Normal forms
  data _⊢nf_ : Ctx -> Ty -> Set where
    abs : {Γ : Ctx} {A B : Ty} -> Γ , A ⊢nf B -> Γ ⊢nf A ⟶ B

-- -- Normalization function
-- nf : Γ ⊢ t :: A -> Γ ⊢nf A
