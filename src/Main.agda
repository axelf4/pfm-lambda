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

infix 10 _⊢_::_

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

-- Composition of weakenings (also transitivity proof).
_●_ : {Γ Γ' Γ'' : Ctx} -> Γ ⊆ Γ' -> Γ' ⊆ Γ'' -> Γ ⊆ Γ''
x ● base = x
x ● (weak y) = weak (x ● y)
(weak x) ● (lift y) = weak (x ● y)
(lift x) ● (lift y) = lift (x ● y)
(lift🔓 x) ● (lift🔓 y) = lift🔓 (x ● y)

-- Drop the part of the OPE that pertains to the context extension
rewind-⊆ : {Γ Γ' Γ'' : Ctx} -> LFExt (Γ' ,🔓) Γ -> Γ ⊆ Γ'' -> Γ' ⊆ ←🔓 Γ''
rewind-⊆ lfext (weak w) = rewind-⊆ lfext w
rewind-⊆ (snoc lfext) (lift w) = rewind-⊆ lfext w
rewind-⊆ nil (lift🔓 w) = w

lfext-to-⊆ : {Γ Γ' : Ctx} -> LFExt Γ Γ' -> Γ ⊆ Γ'
lfext-to-⊆ nil = ⊆-id
lfext-to-⊆ (snoc x) = weak (lfext-to-⊆ x)

wkLFExt : {ΓL Γ Δ : Ctx} -> Γ ⊆ Δ -> LFExt (ΓL ,🔓) Γ -> LFExt ((←🔓 Δ) ,🔓) Δ
wkLFExt (weak w) e = snoc (wkLFExt w e)
wkLFExt (lift w) (snoc e) = snoc (wkLFExt w e)
wkLFExt (lift🔓 w) e = nil

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
wk {Δ = Δ} {A = A} w (unbox t lfext) = let
  t' , x = wk (rewind-⊆ lfext w) t
  in unbox t' , unbox x (wkLFExt w lfext)

-- Substitution from variables in context Γ to terms in context Δ.
data Sub : Ctx -> Ctx -> Set where
  base : {Δ : Ctx} -> Sub · Δ
  sub : {Γ Δ : Ctx} {A : Ty} {t : Tm}
    -> (σ : Sub Γ Δ)
    -> Δ ⊢ t :: A
    -> Sub (Γ , A) Δ
  lock : {Γ Δ Δ' : Ctx} -> (σ : Sub Γ Δ) -> LFExt (Δ ,🔓) Δ' -> Sub (Γ ,🔓) Δ'

wkSub : {Γ Δ Δ' : Ctx} -> Δ ⊆ Δ' -> Sub Γ Δ -> Sub Γ Δ'
wkSub w base = base
wkSub w (sub σ x) = sub (wkSub w σ) (snd (wk w x))
wkSub w (lock σ ext) = lock (wkSub (rewind-⊆ ext w) σ) (wkLFExt w ext)

lift-sub : {Γ Δ : Ctx} {A : Ty} -> Sub Γ Δ -> Sub (Γ , A) (Δ , A)
lift-sub σ = sub (wkSub (weak ⊆-id) σ) (var zero)

id-sub : {Γ : Ctx} -> Sub Γ Γ
id-sub {·} = base
id-sub {Γ , A} = lift-sub id-sub
id-sub {Γ ,🔓} = lock id-sub nil

subst : {Γ Δ : Ctx} {A : Ty} {t : Tm}
  -> Sub Γ Δ -> Γ ⊢ t :: A -> Σ Tm λ t' -> Δ ⊢ t' :: A
subst σ (abs x) = let t , y = subst (lift-sub σ) x in abs t , abs y
subst σ (app x y) = let
  t , x' = subst σ x
  s , y' = subst σ y
  in app t s , app x' y'
subst σ (box x) = let t , y = subst (lock σ nil) x in box t , box y
subst σ (unbox x ext) = let t , y = subst (rewind-sub ext σ) x
  in unbox t , unbox y (rewind-sub-ext ext σ)
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

  □-red : ∀ {Γ Γ' t A} {x : Γ ,🔓 ⊢ t :: A} {ext : LFExt (Γ ,🔓) Γ'}
    -> unbox (box x) ext ≅ snd (wk (lfext-to-⊆ ext) x)
  □-conv : ∀ {Γ t A} -> {x : Γ ⊢ t :: □ A}
    -> x ≅ box (unbox x nil)

  -- Congruence rules
  cong-abs : ∀ {Γ t t' A B} {x : Γ , A ⊢ t :: B} {y : Γ , A ⊢ t' :: B}
    -> x ≅ y -> abs x ≅ abs y

mutual
  -- Normal forms
  data _⊢nf_ (Γ : Ctx) : Ty -> Set where
    nt : {A : Ty} -> Γ ⊢nt A -> Γ ⊢nf A
    abs : {A B : Ty} -> Γ , A ⊢nf B -> Γ ⊢nf A ⟶ B
    box : {A : Ty} -> Γ ,🔓 ⊢nf A -> Γ ⊢nf □ A
  -- Neutral terms
  data _⊢nt_ (Γ : Ctx) : Ty -> Set where
    var : {A : Ty} -> {n : ℕ} -> Get A Γ n -> Γ ⊢nt A
    app : {A B : Ty} -> Γ ⊢nt A ⟶ B -> Γ ⊢nf A -> Γ ⊢nt B
    unbox : {A : Ty} {Γ' : Ctx} -> Γ' ⊢nt □ A -> LFExt (Γ' ,🔓) Γ -> Γ ⊢nt A

infix 10 _⊢nf_ _⊢nt_

wk-nf : {Γ Δ : Ctx} {A : Ty} -> Γ ⊆ Δ -> Γ ⊢nf A -> Δ ⊢nf A
wk-nt : {Γ Δ : Ctx} {A : Ty} -> Γ ⊆ Δ -> Γ ⊢nt A -> Δ ⊢nt A
wk-nf w (nt x) = nt (wk-nt w x)
wk-nf w (abs x) = abs (wk-nf (lift w) x)
wk-nf w (box x) = box (wk-nf (lift🔓 w) x)
wk-nt w (var x) = var (snd (wk-var w x))
wk-nt w (app x y) = app (wk-nt w x) (wk-nf w y)
wk-nt w (unbox x e) = unbox (wk-nt (rewind-⊆ e w) x) (wkLFExt w e)

-- Natural transformation between presheafs
_→̇_ : (Ctx → Set) → (Ctx → Set) → Set
_→̇_ A B = {Δ : Ctx} → A Δ → B Δ

record Box' (A' : Ctx -> Set) (Γ : Ctx) : Set where
  constructor box'
  field
    unbox' : A' (Γ ,🔓)

-- Interpret a type to a presheaf
⟦_⟧ty : Ty -> Ctx -> Set
⟦ ι ⟧ty = _⊢nf ι
⟦ A ⟶ B ⟧ty Γ = {Δ : Ctx} -> Γ ⊆ Δ -> ⟦ A ⟧ty Δ -> ⟦ B ⟧ty Δ
⟦ □ A ⟧ty Γ = Box' ⟦ A ⟧ty Γ

-- Interpret context to a presheaf
data Env : (Γ Δ : Ctx) -> Set where
  · : {Δ : Ctx} -> Env · Δ
  _,_ : {Γ Δ : Ctx} {A : Ty} -> Env Γ Δ -> ⟦ A ⟧ty Δ -> Env (Γ , A) Δ
  lock : {Γ Δ Δ' : Ctx} -> Env Γ Δ -> LFExt (Δ ,🔓) Δ' -> Env (Γ ,🔓) Δ'

⟦_⟧ctx = Env

wk-ty' : {A : Ty} {Γ Δ : Ctx} -> Γ ⊆ Δ -> ⟦ A ⟧ty Γ -> ⟦ A ⟧ty Δ
wk-ty' {ι} w A' = wk-nf w A'
wk-ty' {A ⟶ B} w A⟶B' w2 A' = A⟶B' (w ● w2) A'
wk-ty' {□ A} w (box' A') = box' (wk-ty' {A} (lift🔓 w) A')

wk-env : {Γ Δ Δ' : Ctx} -> Δ ⊆ Δ' -> ⟦ Γ ⟧ctx Δ -> ⟦ Γ ⟧ctx Δ'
wk-env {·} w · = ·
wk-env {Γ , A} w (Γ' , A') = wk-env {Γ} w Γ' , wk-ty' {A} w A'
wk-env {Γ ,🔓} w (lock Γ' e) = lock (wk-env (rewind-⊆ e w) Γ') (wkLFExt w e)

-- Interpret terms-in-contexts as natural transformations
⟦_⟧tm : {Γ : Ctx} {t : Tm} {A : Ty} -> Γ ⊢ t :: A -> {Δ : Ctx} -> ⟦ Γ ⟧ctx Δ -> ⟦ A ⟧ty Δ
⟦ var A∈Γ ⟧tm Γ' = lookup A∈Γ Γ'
  where
    lookup : ∀ {A Γ n} {Δ : Ctx} -> Get A Γ n -> ⟦ Γ ⟧ctx Δ -> ⟦ A ⟧ty Δ
    lookup zero (_ , A') = A'
    lookup (suc x) (Γ' , _) = lookup x Γ'
⟦ abs x ⟧tm Γ' e y' = ⟦ x ⟧tm (wk-env e Γ' , y')
⟦ app x y ⟧tm Γ' = ⟦ x ⟧tm Γ' ⊆-id (⟦ y ⟧tm Γ')
⟦ box x ⟧tm Γ' = box' (⟦ x ⟧tm (lock Γ' nil))
⟦_⟧tm {A = A} (unbox x e) Γ' = let box' y' = ⟦ x ⟧tm (rewind-env e Γ')
  in wk-ty' {A} (lfext-to-⊆ (←🔓-lfext e Γ')) y'
  where
    ←🔓-lfext : {Γ Γ' Δ : Ctx} -> LFExt (Γ ,🔓) Γ' -> Env Γ' Δ -> LFExt ((←🔓 Δ) ,🔓) Δ
    ←🔓-lfext (snoc e) (env , _) = ←🔓-lfext e env
    ←🔓-lfext nil (lock env nil) = nil
    ←🔓-lfext nil (lock env (snoc lfext)) = snoc (←🔓-lfext nil (lock env lfext))

    rewind-env : {Γ Γ' Δ : Ctx} -> LFExt (Γ ,🔓) Γ' -> Env Γ' Δ -> Env Γ (←🔓 Δ)
    rewind-env (snoc e) (env , _) = rewind-env e env
    rewind-env nil (lock env lfext) rewrite ←🔓-of-lfExt-is-base lfext = env

reify : {A : Ty} {Γ : Ctx} -> ⟦ A ⟧ty Γ -> Γ ⊢nf A
reflect : {A : Ty} {Γ : Ctx} -> Γ ⊢nt A -> ⟦ A ⟧ty Γ
reify {ι} A' = A'
reify {A ⟶ B} A⟶B' = abs (reify (A⟶B' (weak ⊆-id) (reflect {A} (var zero))))
reify {□ A} (box' A') = box (reify A')
reflect {ι} x = nt x
reflect {A ⟶ B} x e A' = reflect (app (wk-nt e x) (reify A'))
reflect {□ A} x = box' (reflect (unbox x nil))

-- Normalization function
nf : {Γ : Ctx} {t : Tm} {A : Ty} -> Γ ⊢ t :: A -> Γ ⊢nf A
nf x = reify (⟦ x ⟧tm Γ')
  where
    -- Initial environment consisting of all neutrals
    Γ' : {Γ : Ctx} -> ⟦ Γ ⟧ctx Γ
    Γ' {·} = ·
    Γ' {Γ , A} = wk-env (weak ⊆-id) Γ' , reflect {A} (var zero)
    Γ' {Γ ,🔓} = lock Γ' nil
