{-# OPTIONS --without-K --safe #-}

open import Parameters as _ using (Parameters)

module Calculus (params : Parameters) where

open import Agda.Builtin.Sigma using (Σ; fst; snd) renaming (_,_ to infix 20 _,_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl; cong; cong₂)

open import Util using (cong1)
open import Context

open Parameters params
open Replacement _◁_ using (Rpl; ·; _,_; lock)

--- Syntax

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

-- Variable weakening
wk : ∀ {Γ Δ A} -> Γ ⊆ Δ -> Γ ⊢ A -> Δ ⊢ A
wk w (var x) = var (wkVar w x)
wk w (abs t) = abs (wk (lift w) t)
wk w (app t s) = app (wk w t) (wk w s)
wk w (box t) = box (wk (lift🔓 w) t)
wk w (unbox t m) = let _ , (m' , w') = rewind-⊆ m w
  in unbox (wk w' t) m'

wkId : {A : Ty} {Γ : Ctx} -> (t : Γ ⊢ A) -> wk ⊆.id t ≡ t
wkId (var x) = cong var (wkVarId x)
wkId (abs t) = cong abs (wkId t)
wkId (app t s) = cong₂ app (wkId t) (wkId s)
wkId (box t) = cong box (wkId t)
wkId (unbox t m) = ≡.trans
  (cong (λ (_ , (m' , w')) -> unbox (wk w' t) m') (rewind-⊆-presId m))
  (cong1 unbox (wkId t))

wkPres-● : ∀ {A Γ Δ Ξ} -> (w1 : Γ ⊆ Δ) (w2 : Δ ⊆ Ξ) (x : Γ ⊢ A)
  -> wk (w1 ● w2) x ≡ wk w2 (wk w1 x)
wkPres-● {A} w1 w2 (var x) = cong var (wkVarPres-● w1 w2 x)
wkPres-● w1 w2 (abs x) = cong abs (wkPres-● (lift w1) (lift w2) x)
wkPres-● w1 w2 (app x y) = cong₂ app (wkPres-● w1 w2 x) (wkPres-● w1 w2 y)
wkPres-● w1 w2 (box x) = cong box (wkPres-● (lift🔓 w1) (lift🔓 w2) x)
wkPres-● w1 w2 (unbox x m) = ≡.trans
  (cong (λ (_ , (m' , w')) -> unbox (wk w' x) m') (rewind-⊆-pres-● m w1 w2))
  (cong1 unbox (wkPres-● _ _ _))

-- Substitution from variables in context Γ to terms in context Δ
Sub = Rpl (λ A Δ -> Δ ⊢ A)
module Sub = Rpl.Properties
  (λ A Δ -> Δ ⊢ A)
  ◁1 rewind-⊆
  wk (var zero)

subst : {Γ Δ : Ctx} {A : Ty} -> Sub Γ Δ -> Γ ⊢ A -> Δ ⊢ A
subst σ (var x) = substVar σ x
  where
    substVar : {Γ Δ : Ctx} {A : Ty} -> Sub Γ Δ -> A ∈ Γ -> Δ ⊢ A
    substVar (_ , x) zero = x
    substVar (σ , _) (suc x) = substVar σ x
subst σ (abs x) = abs (subst (Sub.liftRpl σ) x)
subst σ (app x y) = app (subst σ x) (subst σ y)
subst σ (box x) = box (subst (lock σ ◁1) x)
subst σ (unbox x m) = let _ , (m' , σ') = rewind m σ
  in unbox (subst σ' x) m'

-- Applies unit substitution.
_[_] : {Γ : Ctx} {A B : Ty} -> Γ , B ⊢ A -> Γ ⊢ B -> Γ ⊢ A
_[_] x y = subst (Sub.id , y) x

wkSubPres-● : {Γ Δ Δ' Δ'' : Ctx} (w : Δ ⊆ Δ') (w' : Δ' ⊆ Δ'') (σ : Sub Γ Δ)
  -> Sub.wk (w ● w') σ ≡ Sub.wk w' (Sub.wk w σ)
wkSubPres-● w w' · = refl
wkSubPres-● w w' (s , x) = cong₂ _,_ (wkSubPres-● w w' s) (wkPres-● w w' x)
wkSubPres-● w w' (lock s m) = ≡.trans
  (cong (λ (_ , (m' , w'')) -> lock (Sub.wk w'' s) m')
    (rewind-⊆-pres-● m w w'))
  (cong1 lock (wkSubPres-● _ _ s))

wkSubId : {Γ Δ : Ctx} -> (w : Γ ⊆ Δ) -> Sub.wk w Sub.id ≡ Sub.from-⊆ w
wkSubId base = refl
wkSubId (weak w) = ≡.trans
  (cong (λ x -> Sub.wk (weak x) Sub.id) (≡.sym ⊆.idr))
  (≡.trans (wkSubPres-● w (weak ⊆.id) Sub.id)
    (cong (Sub.wk _) (wkSubId w)))
wkSubId (lift w) = cong (_, var zero)
  (≡.trans (≡.sym (wkSubPres-● (weak ⊆.id) (lift w) Sub.id))
    (≡.trans
      (cong (λ x -> Sub.wk (weak x) Sub.id)
        (≡.trans ⊆.idl (≡.sym ⊆.idr)))
      (≡.trans (wkSubPres-● w (weak ⊆.id) Sub.id)
        (cong (Sub.wk _) (wkSubId w)))))
wkSubId (lift🔓 w) rewrite rewind-⊆-◁1 w = cong1 lock (wkSubId w)

substNat : {A : Ty} {Γ Δ Δ' : Ctx} (w : Δ ⊆ Δ') (σ : Sub Γ Δ) (t : Γ ⊢ A)
  -> subst (Sub.wk w σ) t ≡ wk w (subst σ t)
substNat w s (abs t) = cong abs (≡.trans
  (cong (λ x -> subst (x , var zero) t)
    (≡.trans (≡.sym (wkSubPres-● w (weak ⊆.id) s))
      (≡.trans
        (cong (λ x -> Sub.wk (weak x) s) (≡.trans ⊆.idr (≡.sym ⊆.idl)))
        (wkSubPres-● (weak ⊆.id) (lift w) s))))
  (substNat (lift w) (Sub.liftRpl s) t))
substNat w s (app x y) = cong₂ app (substNat w s x) (substNat w s y)
substNat w σ (box x) = cong box (≡.trans
  (cong (λ (_ , (m' , w')) -> subst (lock (Sub.wk w' σ) m') x)
    (≡.sym (rewind-⊆-◁1 w)))
  (substNat (lift🔓 w) (lock σ ◁1) x))
substNat w s (unbox t m) = ≡.trans
  (cong (λ (_ , (m' , s')) -> unbox (subst s' t) m')
    (rewindWk m s w {head = var zero}))
  (cong1 unbox (substNat _ _ t))
substNat w (s , x) (var zero) = refl
substNat w (s , _) (var (suc x)) = substNat w s (var x)

cohTrimWk : {A : Ty} {Γ Γ' Γ'' : Ctx} (w : Γ ⊆ Γ') (σ : Sub Γ' Γ'') (t : Γ ⊢ A)
  -> subst (Sub.trim w σ) t ≡ subst σ (wk w t)
cohTrimWk w s (abs t) = cong abs (≡.trans
  (cong (λ x -> subst (x , var zero) t) (Sub.trimNat w (weak ⊆.id) s))
  (cohTrimWk (lift w) (Sub.liftRpl s) t))
cohTrimWk w s (app x y) = cong₂ app (cohTrimWk w s x) (cohTrimWk w s y)
cohTrimWk w s (box x) = cong box (cohTrimWk (lift🔓 w) (lock s ◁1) x)
cohTrimWk w s (unbox t m) = ≡.trans
  (cong (λ (_ , (m' , s')) -> unbox (subst s' t) m')
    (rewindTrim m w s {wk} {head = var zero}))
  (cong1 unbox (cohTrimWk _ _ t))
cohTrimWk (weak w) (s , _) (var zero) = cohTrimWk w s (var zero)
cohTrimWk (lift w) (s , x) (var zero) = refl
cohTrimWk (weak w) (s , _) x@(var (suc _)) = cohTrimWk w s x
cohTrimWk (lift w) (s , _) (var (suc x)) = cohTrimWk w s (var x)

substId : {Γ : Ctx} {A : Ty} (t : Γ ⊢ A) -> subst Sub.id t ≡ t
substId (var zero) = refl
substId (var (suc x)) = ≡.trans
  (substNat (weak ⊆.id) Sub.id (var x))
  (≡.trans
    (cong (wk (weak ⊆.id)) (substId (var x)))
    (cong (λ x -> var (suc x)) (wkVarId x)))
substId (abs x) = cong abs (substId x)
substId (app x y) = cong₂ app (substId x) (substId y)
substId (box x) = cong box (substId x)
substId (unbox x m) = ≡.trans
  (cong (λ (_ , (m' , σ')) -> unbox (subst σ' x) m') (rewindPresId m wkId))
  (cong1 unbox (substId x))

open Rpl.Composition (λ A Δ -> Δ ⊢ A) rewind subst using (_∙_) public

idrSub : {Γ Δ : Ctx} {σ : Sub Γ Δ} -> σ ∙ Sub.id ≡ σ
idrSub {σ = ·} = refl
idrSub {σ = σ , x} = cong₂ _,_ idrSub (substId x)
idrSub {σ = lock σ m} = ≡.trans
  (cong (λ (_ , (m' , σ')) -> lock (σ ∙ σ') m') (rewindPresId m wkId))
  (cong1 lock idrSub)

-- See: coh-wkSub-∙ₛ
assocSSW : ∀ {Γ Δ Δ' Ξ} (σ : Sub Γ Δ) (δ : Sub Δ Δ') (w : Δ' ⊆ Ξ)
  -> Sub.wk w (σ ∙ δ) ≡ σ ∙ Sub.wk w δ
assocSSW · s' w = refl
assocSSW (s , t) s' w = cong₂ _,_ (assocSSW s s' w) (≡.sym (substNat w s' t))
assocSSW (lock s m) s' w = ≡.trans (cong1 lock (assocSSW s _ _))
  (cong (λ (_ , (m' , σ')) -> lock (s ∙ σ') m')
    (≡.sym (rewindWk m s' w {head = var zero})))

-- See: coh-trimSub-wkSub
assocSWS : ∀ {Γ Δ Δ' Ξ} (σ : Sub Γ Δ) (w : Δ ⊆ Δ') (δ : Sub Δ' Ξ)
  -> Sub.wk w σ ∙ δ ≡ σ ∙ Sub.trim w δ
assocSWS · w s' = refl
assocSWS (s , x) w s' = cong₂ _,_ (assocSWS s w s') (≡.sym (cohTrimWk w s' x))
assocSWS (lock s m) w s' = ≡.trans
  (cong1 lock (assocSWS s _ _))
  (cong (λ (_ , (m' , σ')) -> lock (s ∙ σ') m')
    (≡.sym (rewindTrim m w s' {wk} {head = var zero})))

substPres-∙ : {A : Ty} {Γ Γ' Γ'' : Ctx} (σ : Sub Γ Γ') (δ : Sub Γ' Γ'') (t : Γ ⊢ A)
  -> subst (σ ∙ δ) t ≡ subst δ (subst σ t)
substPres-∙ s s' (abs t) = cong abs (≡.trans
  (cong (λ x -> subst (x , var zero) t)
    (≡.trans (assocSSW s s' (weak ⊆.id))
      (≡.trans (cong (s ∙_) (≡.sym (Sub.trimIdl (Sub.drop s'))))
        (≡.sym (assocSWS s (weak ⊆.id) (Sub.liftRpl s'))))))
  (substPres-∙ (Sub.liftRpl s) (Sub.liftRpl s') t))
substPres-∙ s s' (app x y) = cong₂ app (substPres-∙ s s' x) (substPres-∙ s s' y)
substPres-∙ s s' (box x) = cong box (≡.trans
  (cong (λ (_ , (m' , σ')) -> subst (lock (s ∙ σ') m') x)
    (≡.sym (rewind-◁1 s')))
  (substPres-∙ (lock s ◁1) (lock s' ◁1) x))
substPres-∙ s s' (unbox x m) = ≡.trans
  (cong (λ (_ , (m' , σ')) -> unbox (subst σ' x) m') (rewindPres-∙ m s s'))
  (cong1 unbox (substPres-∙ _ _ x))
substPres-∙ (s , x) s' (var zero) = refl
substPres-∙ (s , _) s' (var (suc x)) = substPres-∙ s s' (var x)

-- Equivalence of terms-in-contexts
data _~_ : {Γ : Ctx} {A : Ty} -> (t s : Γ ⊢ A) -> Set where
  β : {Γ : Ctx} {A B : Ty} (x : Γ , A ⊢ B) (y : Γ ⊢ A)
    -> app (abs x) y ~ (x [ y ])
  η : {Γ : Ctx} {A B : Ty} (x : Γ ⊢ A ⟶ B)
    -> x ~ abs (app (wk (weak ⊆.id) x) (var zero))

  □-β : {Γ Γ' : Ctx} {A : Ty} (x : Γ ,🔓 ⊢ A) (m : Γ ◁ Γ')
    -> unbox (box x) m ~ subst (lock Sub.id m) x
  □-η : {Γ : Ctx} {A : Ty} (x : Γ ⊢ □ A)
    -> x ~ box (unbox x ◁1)

  ~-refl : {Γ : Ctx} {A : Ty} {x : Γ ⊢ A}
    -> x ~ x
  ~-sym : {Γ : Ctx} {A : Ty} {x y : Γ ⊢ A}
    -> x ~ y -> y ~ x
  ~-trans : {Γ : Ctx} {A : Ty} {x y z : Γ ⊢ A}
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

lemmaLiftFresh : {Γ Δ : Ctx} {A B : Ty} (w : Γ ⊆ Δ) (t : Γ ⊢ A ⟶ B)
    -> wk (lift w) (wk (weak {A} ⊆.id) t) ≡ wk (weak ⊆.id) (wk w t)
lemmaLiftFresh _ _ = ≡.trans (≡.sym (wkPres-● _ _ _))
  (≡.trans
    (cong (λ x -> wk (weak x) _) (≡.trans ⊆.idl (≡.sym ⊆.idr)))
    (wkPres-● _ _ _))

wk-~ : {Γ Δ : Ctx} {A : Ty} {x : Γ ⊢ A} {y : Γ ⊢ A} (w : Γ ⊆ Δ)
  -> x ~ y -> wk w x ~ wk w y
wk-~ w (β x y) = ≡.subst
  (app (abs (wk (lift w) x)) (wk w y) ~_)
  (≡.trans
    (≡.trans (≡.sym (cohTrimWk (lift w) (Sub.id , wk w y) x))
      (cong (λ z -> subst (z , wk w y) x)
        (≡.trans (Sub.trimIdr w) (≡.sym (wkSubId w)))))
    (substNat w (Sub.id , y) x))
  (β _ _)
wk-~ w (η x) rewrite lemmaLiftFresh w x = η (wk w x)
wk-~ w (□-β x m) = ≡.subst
  (unbox (box (wk (lift🔓 (snd (snd (rewind-⊆ m w)))) x))
    (fst (snd (rewind-⊆ m w)))
    ~_)
  (≡.trans
    (≡.trans (≡.sym (cohTrimWk _ _ x))
      (cong (λ y -> subst (lock y (fst (snd (rewind-⊆ m w)))) x)
        (≡.trans (Sub.trimIdr (snd (snd (rewind-⊆ m w)))) (≡.sym (wkSubId _)))))
    (substNat _ _ x))
  (□-β _ _)
wk-~ w (□-η x) rewrite rewind-⊆-◁1 w = □-η _
wk-~ _ ~-refl = ~-refl
wk-~ w (~-sym x) = ~-sym (wk-~ w x)
wk-~ w (~-trans x y) = ~-trans (wk-~ w x) (wk-~ w y)
wk-~ w (cong-abs x) = cong-abs (wk-~ (lift w) x)
wk-~ w (cong-app x y) = cong-app (wk-~ w x) (wk-~ w y)
wk-~ w (cong-box x) = cong-box (wk-~ (lift🔓 w) x)
wk-~ _ (cong-unbox x) = cong-unbox (wk-~ _ x)

--- Semantics

mutual
  -- Normal forms
  data _⊢nf_ (Γ : Ctx) : Ty -> Set where
    ne : Γ ⊢ne ι -> Γ ⊢nf ι
    abs : {A B : Ty} -> Γ , A ⊢nf B -> Γ ⊢nf A ⟶ B
    box : {A : Ty} -> Γ ,🔓 ⊢nf A -> Γ ⊢nf □ A
  -- Neutral terms
  data _⊢ne_ (Γ : Ctx) : Ty -> Set where
    var : {A : Ty} -> A ∈ Γ -> Γ ⊢ne A
    app : {A B : Ty} -> Γ ⊢ne A ⟶ B -> Γ ⊢nf A -> Γ ⊢ne B
    unbox : {A : Ty} {Γ' : Ctx} -> Γ' ⊢ne □ A -> Γ' ◁ Γ -> Γ ⊢ne A

infix 10 _⊢nf_ _⊢ne_

-- Quotation of normal forms/neutrals back into terms
⌜_⌝nf : {Γ : Ctx} {A : Ty} -> Γ ⊢nf A -> Γ ⊢ A
⌜_⌝ne : {Γ : Ctx} {A : Ty} -> Γ ⊢ne A -> Γ ⊢ A
⌜ ne x ⌝nf = ⌜ x ⌝ne
⌜ abs x ⌝nf = abs ⌜ x ⌝nf
⌜ box x ⌝nf = box ⌜ x ⌝nf

⌜ var x ⌝ne = var x
⌜ app x y ⌝ne = app ⌜ x ⌝ne ⌜ y ⌝nf
⌜ unbox x m ⌝ne = unbox ⌜ x ⌝ne m

wkNf : {Γ Δ : Ctx} {A : Ty} -> Γ ⊆ Δ -> Γ ⊢nf A -> Δ ⊢nf A
wkNe : {Γ Δ : Ctx} {A : Ty} -> Γ ⊆ Δ -> Γ ⊢ne A -> Δ ⊢ne A
wkNf w (ne x) = ne (wkNe w x)
wkNf w (abs x) = abs (wkNf (lift w) x)
wkNf w (box x) = box (wkNf (lift🔓 w) x)

wkNe w (var x) = var (wkVar w x)
wkNe w (app x y) = app (wkNe w x) (wkNf w y)
wkNe w (unbox x m) = let _ , (m' , w') = rewind-⊆ m w
  in unbox (wkNe w' x) m'

⌜⌝nf-nat : {Γ Δ : Ctx} {A : Ty} -> (w : Γ ⊆ Δ) -> (n : Γ ⊢nf A)
  -> ⌜ wkNf w n ⌝nf ≡ wk w ⌜ n ⌝nf
⌜⌝ne-nat : {Γ Δ : Ctx} {A : Ty} -> (w : Γ ⊆ Δ) -> (n : Γ ⊢ne A)
  -> ⌜ wkNe w n ⌝ne ≡ wk w ⌜ n ⌝ne
⌜⌝nf-nat w (ne x) = ⌜⌝ne-nat w x
⌜⌝nf-nat w (abs x) = cong abs (⌜⌝nf-nat (lift w) x)
⌜⌝nf-nat w (box x) = cong box (⌜⌝nf-nat (lift🔓 w) x)

⌜⌝ne-nat w (var x) = refl
⌜⌝ne-nat w (app x y) = cong₂ app (⌜⌝ne-nat w x) (⌜⌝nf-nat w y)
⌜⌝ne-nat w (unbox x m) = cong1 unbox (⌜⌝ne-nat _ _)

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
wkTy' {ι} w = wkNf w
wkTy' {A ⟶ B} w A⟶B' w2 = A⟶B' (w ● w2)
wkTy' {□ A} w (box' f) = box' λ w2 -> f (w ● w2)

reify : {A : Ty} {Γ : Ctx} -> ⟦ A ⟧ty Γ -> Γ ⊢nf A
reflect : {A : Ty} {Γ : Ctx} -> Γ ⊢ne A -> ⟦ A ⟧ty Γ
reify {ι} A' = A'
reify {A ⟶ B} A⟶B' = abs (reify (A⟶B' (weak ⊆.id) (reflect (var zero))))
reify {□ A} (box' f) = let A' = f ⊆.id ◁1 in box (reify A')
reflect {ι} x = ne x
reflect {A ⟶ B} x w A' = reflect (app (wkNe w x) (reify A'))
reflect {□ A} x = box' λ w m -> reflect (unbox (wkNe w x) m)

-- Interpret context to a presheaf
Env = Rpl ⟦_⟧ty
⟦_⟧ctx = Env
module Env = Rpl.Properties
  ⟦_⟧ty
  ◁1 rewind-⊆
  wkTy' (reflect (var zero))

-- Interpret terms-in-contexts as natural transformations
⟦_⟧tm : {Γ : Ctx} {A : Ty} -> Γ ⊢ A -> {Δ : Ctx} -> ⟦ Γ ⟧ctx Δ -> ⟦ A ⟧ty Δ
⟦ var A∈Γ ⟧tm Γ' = lookup A∈Γ Γ'
  where
    lookup : ∀ {A Γ Δ} -> A ∈ Γ -> ⟦ Γ ⟧ctx Δ -> ⟦ A ⟧ty Δ
    lookup zero (_ , A') = A'
    lookup (suc x) (Γ' , _) = lookup x Γ'
⟦ abs x ⟧tm Γ' w y' = ⟦ x ⟧tm (Env.wk w Γ' , y')
⟦ app x y ⟧tm Γ' = ⟦ x ⟧tm Γ' ⊆.id (⟦ y ⟧tm Γ')
⟦ box x ⟧tm Γ' = box' λ w m -> ⟦ x ⟧tm (lock (Env.wk w Γ') m)
⟦_⟧tm (unbox x m) Γ' = let _ , (m' , Δ') = rewind m Γ'
  in ⟦ x ⟧tm Δ' .Box'.unbox' ⊆.id m'

-- Normalization function
nf : {Γ : Ctx} {A : Ty} -> Γ ⊢ A -> Γ ⊢nf A
-- Evaluate in fresh environment consisting of all neutrals
nf t = reify (⟦ t ⟧tm Env.id)
