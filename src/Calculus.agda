{-# OPTIONS --without-K #-}

open import Parameters as _ using (Parameters)

module Calculus (params : Parameters) where

open import Level using (0ℓ)
open import Axiom.Extensionality.Propositional using (Extensionality; implicit-extensionality)
open import Axiom.UniquenessOfIdentityProofs using (UIP)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl; cong; cong₂)
open import Function using (_∘_; _$_; Inverse)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; proj₁; proj₂) renaming (_,_ to infix 20 _,_)

open import Util using (cong1)
open import Context

open Parameters params
open Replacement _◁_ using (Rpl; ·; _,_; lock)

private
  postulate funext : Extensionality 0ℓ 0ℓ

  funexti = implicit-extensionality funext

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
wkPres-● w1 w2 (var x) = cong var (wkVarPres-● w1 w2 x)
wkPres-● w1 w2 (abs t) = cong abs (wkPres-● (lift w1) (lift w2) t)
wkPres-● w1 w2 (app t s) = cong₂ app (wkPres-● w1 w2 t) (wkPres-● w1 w2 s)
wkPres-● w1 w2 (box t) = cong box (wkPres-● (lift🔓 w1) (lift🔓 w2) t)
wkPres-● w1 w2 (unbox t m) = ≡.trans
  (cong (λ (_ , (m' , w')) -> unbox (wk w' t) m') (rewind-⊆-pres-● m w1 w2))
  (cong1 unbox (wkPres-● _ _ t))

-- Substitution from variables in context Γ to terms in context Δ
Sub = Rpl (λ A Δ -> Δ ⊢ A)
module Sub = Rpl.Properties (λ A Δ -> Δ ⊢ A) ◁1 rewind-⊆ wk (var zero)

subst : {Γ Δ : Ctx} {A : Ty} -> Sub Γ Δ -> Γ ⊢ A -> Δ ⊢ A
subst σ (var x) = Sub.replaceVar σ x
subst σ (abs t) = abs (subst (Sub.liftRpl σ) t)
subst σ (app t s) = app (subst σ t) (subst σ s)
subst σ (box t) = box (subst (lock σ ◁1) t)
subst σ (unbox t m) = let _ , (m' , σ') = rewind m σ
  in unbox (subst σ' t) m'

-- Applies unit substitution.
_[_] : {Γ : Ctx} {A B : Ty} -> Γ , B ⊢ A -> Γ ⊢ B -> Γ ⊢ A
_[_] x y = subst (Sub.id , y) x

wkSubPres-● = Sub.wkPres-● rewind-⊆-pres-● wkPres-●

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
substNat w σ (abs t) = cong abs (≡.trans
  (cong (λ x -> subst (x , var zero) t)
    (≡.trans (≡.sym (wkSubPres-● w (weak ⊆.id) σ))
      (≡.trans
        (cong (λ x -> Sub.wk (weak x) σ) (≡.trans ⊆.idr (≡.sym ⊆.idl)))
        (wkSubPres-● (weak ⊆.id) (lift w) σ))))
  (substNat (lift w) (Sub.liftRpl σ) t))
substNat w σ (app t s) = cong₂ app (substNat w σ t) (substNat w σ s)
substNat w σ (box t) = cong box (≡.trans
  (cong (λ (_ , (m' , w')) -> subst (lock (Sub.wk w' σ) m') t)
    (≡.sym (rewind-⊆-◁1 w)))
  (substNat (lift🔓 w) (lock σ ◁1) t))
substNat w σ (unbox t m) = ≡.trans
  (cong (λ (_ , (m' , s')) -> unbox (subst s' t) m')
    (rewindWk m σ w {head = var zero}))
  (cong1 unbox (substNat _ _ t))
substNat w (_ , t) (var zero) = refl
substNat w (σ , _) (var (suc x)) = substNat w σ (var x)

cohTrimWk : {A : Ty} {Γ Γ' Γ'' : Ctx} (w : Γ ⊆ Γ') (σ : Sub Γ' Γ'') (t : Γ ⊢ A)
  -> subst (Sub.trim w σ) t ≡ subst σ (wk w t)
cohTrimWk w σ (abs t) = cong abs (≡.trans
  (cong (λ x -> subst (x , var zero) t) (Sub.trimNat w (weak ⊆.id) σ))
  (cohTrimWk (lift w) (Sub.liftRpl σ) t))
cohTrimWk w σ (app t s) = cong₂ app (cohTrimWk w σ t) (cohTrimWk w σ s)
cohTrimWk w σ (box t) = cong box (cohTrimWk (lift🔓 w) (lock σ ◁1) t)
cohTrimWk w σ (unbox t m) = ≡.trans
  (cong (λ (_ , (m' , s')) -> unbox (subst s' t) m')
    (rewindTrim m w σ {wk} {head = var zero}))
  (cong1 unbox (cohTrimWk _ _ t))
cohTrimWk (weak w) (σ , _) (var zero) = cohTrimWk w σ (var zero)
cohTrimWk (lift w) (_ , t) (var zero) = refl
cohTrimWk (weak w) (σ , _) t@(var (suc _)) = cohTrimWk w σ t
cohTrimWk (lift w) (σ , _) (var (suc x)) = cohTrimWk w σ (var x)

substId : {Γ : Ctx} {A : Ty} (t : Γ ⊢ A) -> subst Sub.id t ≡ t
substId (var zero) = refl
substId (var (suc x)) = ≡.trans
  (substNat (weak ⊆.id) Sub.id (var x))
  (≡.trans
    (cong (wk (weak ⊆.id)) (substId (var x)))
    (cong (λ x -> var (suc x)) (wkVarId x)))
substId (abs t) = cong abs (substId t)
substId (app t s) = cong₂ app (substId t) (substId s)
substId (box t) = cong box (substId t)
substId (unbox t m) = ≡.trans
  (cong (λ (_ , (m' , σ')) -> unbox (subst σ' t) m') (rewindPresId m wkId))
  (cong1 unbox (substId t))

open Rpl.Composition (λ A Δ -> Δ ⊢ A) (λ A Δ -> Δ ⊢ A) rewind subst
  using (_∙_) public

idrSub : {Γ Δ : Ctx} {σ : Sub Γ Δ} -> σ ∙ Sub.id ≡ σ
idrSub {σ = ·} = refl
idrSub {σ = σ , t} = cong₂ _,_ idrSub (substId t)
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
substPres-∙ σ δ (abs t) = cong abs (≡.trans
  (cong (λ x -> subst (x , var zero) t)
    (≡.trans (assocSSW σ δ (weak ⊆.id))
      (≡.trans (cong (σ ∙_) (≡.sym (Sub.trimIdl (Sub.drop δ))))
        (≡.sym (assocSWS σ (weak ⊆.id) (Sub.liftRpl δ))))))
  (substPres-∙ (Sub.liftRpl σ) (Sub.liftRpl δ) t))
substPres-∙ σ δ (app t s) = cong₂ app (substPres-∙ σ δ t) (substPres-∙ σ δ s)
substPres-∙ σ δ (box t) = cong box (≡.trans
  (cong (λ (_ , (m' , σ')) -> subst (lock (σ ∙ σ') m') t)
    (≡.sym (rewind-◁1 δ)))
  (substPres-∙ (lock σ ◁1) (lock δ ◁1) t))
substPres-∙ σ δ (unbox t m) = ≡.trans
  (cong (λ (_ , (m' , σ')) -> unbox (subst σ' t) m') (rewindPres-∙ m σ δ))
  (cong1 unbox (substPres-∙ _ _ t))
substPres-∙ (σ , t) δ (var zero) = refl
substPres-∙ (σ , _) δ (var (suc x)) = substPres-∙ σ δ (var x)

-- Equivalence of terms-in-contexts
data _~_ : {Γ : Ctx} {A : Ty} -> (t s : Γ ⊢ A) -> Set where
  β : {Γ : Ctx} {A B : Ty} (t : Γ , A ⊢ B) (s : Γ ⊢ A)
    -> app (abs t) s ~ (t [ s ])
  η : {Γ : Ctx} {A B : Ty} (t : Γ ⊢ A ⟶ B)
    -> t ~ abs (app (wk (weak ⊆.id) t) (var zero))

  □-β : {Γ Γ' : Ctx} {A : Ty} (t : Γ ,🔓 ⊢ A) (m : Γ ◁ Γ')
    -> unbox (box t) m ~ subst (lock Sub.id m) t
  □-η : {Γ : Ctx} {A : Ty} (t : Γ ⊢ □ A)
    -> t ~ box (unbox t ◁1)

  ~-refl : {Γ : Ctx} {A : Ty} {t : Γ ⊢ A}
    -> t ~ t
  ~-sym : {Γ : Ctx} {A : Ty} {t s : Γ ⊢ A}
    -> t ~ s -> s ~ t
  ~-trans : {Γ : Ctx} {A : Ty} {t s u : Γ ⊢ A}
    -> t ~ s -> s ~ u -> t ~ u

  -- Congruence rules
  cong-abs : ∀ {Γ A B} {t s : Γ , A ⊢ B}
    -> t ~ s -> abs t ~ abs s
  cong-app : ∀ {Γ A B} {t t' : Γ ⊢ A ⟶ B} {s s' : Γ ⊢ A}
    -> t ~ t' -> s ~ s' -> app t s ~ app t' s'
  cong-box : ∀ {Γ A} {t s : Γ ,🔓 ⊢ A}
    -> t ~ s -> box t ~ box s
  cong-unbox : ∀ {Γ Δ A} {t s : Δ ⊢ □ A} {m : Δ ◁ Γ}
    -> t ~ s -> unbox t m ~ unbox s m

lemmaLiftFresh : {Γ Δ : Ctx} {A B : Ty} (w : Γ ⊆ Δ) (t : Γ ⊢ A ⟶ B)
    -> wk (lift w) (wk (weak {A} ⊆.id) t) ≡ wk (weak ⊆.id) (wk w t)
lemmaLiftFresh _ _ = ≡.trans (≡.sym (wkPres-● _ _ _))
  (≡.trans
    (cong (λ x -> wk (weak x) _) (≡.trans ⊆.idl (≡.sym ⊆.idr)))
    (wkPres-● _ _ _))

wk-~ : {Γ Δ : Ctx} {A : Ty} {t s : Γ ⊢ A} (w : Γ ⊆ Δ) -> t ~ s -> wk w t ~ wk w s
wk-~ w (β t s) = ≡.subst
  (app (abs (wk (lift w) t)) (wk w s) ~_)
  (≡.trans
    (≡.trans (≡.sym (cohTrimWk (lift w) (Sub.id , wk w s) t))
      (cong (λ x -> subst (x , wk w s) t)
        (≡.trans (Sub.trimIdr w) (≡.sym (wkSubId w)))))
    (substNat w (Sub.id , s) t))
  (β _ _)
wk-~ w (η t) rewrite lemmaLiftFresh w t = η (wk w t)
wk-~ w (□-β t m) = ≡.subst
  (unbox (box (wk (lift🔓 (proj₂ (proj₂ (rewind-⊆ m w)))) t))
    (proj₁ (proj₂ (rewind-⊆ m w)))
    ~_)
  (≡.trans
    (≡.trans (≡.sym (cohTrimWk _ _ t))
      (cong (λ x -> subst (lock x (proj₁ (proj₂ (rewind-⊆ m w)))) t)
        (≡.trans (Sub.trimIdr (proj₂ (proj₂ (rewind-⊆ m w)))) (≡.sym (wkSubId _)))))
    (substNat _ _ t))
  (□-β _ _)
wk-~ w (□-η t) rewrite rewind-⊆-◁1 w = □-η _
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
    unbox : {A : Ty} {Δ : Ctx} -> Δ ⊢ne □ A -> Δ ◁ Γ -> Γ ⊢ne A

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

wkNfId : {Γ : Ctx} {A : Ty} (x : Γ ⊢nf A) -> wkNf ⊆.id x ≡ x
wkNeId : {Γ : Ctx} {A : Ty} (x : Γ ⊢ne A) -> wkNe ⊆.id x ≡ x
wkNfId (ne x) = cong ne (wkNeId x)
wkNfId (abs x) = cong abs (wkNfId x)
wkNfId (box x) = cong box (wkNfId x)

wkNeId (var v) = cong var (wkVarId v)
wkNeId (app x y) = cong₂ app (wkNeId x) (wkNfId y)
wkNeId (unbox x m) = ≡.trans
  (cong (λ (_ , (m' , w')) -> unbox (wkNe w' x) m') (rewind-⊆-presId m))
  (cong1 unbox (wkNeId x))

wkNfPres-● : ∀ {A Γ Δ Ξ} -> (w1 : Γ ⊆ Δ) (w2 : Δ ⊆ Ξ) (x : Γ ⊢nf A)
  -> wkNf (w1 ● w2) x ≡ wkNf w2 (wkNf w1 x)
wkNePres-● : ∀ {A Γ Δ Ξ} -> (w1 : Γ ⊆ Δ) (w2 : Δ ⊆ Ξ) (x : Γ ⊢ne A)
  -> wkNe (w1 ● w2) x ≡ wkNe w2 (wkNe w1 x)
wkNfPres-● w1 w2 (ne x) = cong ne (wkNePres-● w1 w2 x)
wkNfPres-● w1 w2 (abs x) = cong abs (wkNfPres-● (lift w1) (lift w2) x)
wkNfPres-● w1 w2 (box x) = cong box (wkNfPres-● (lift🔓 w1) (lift🔓 w2) x)
wkNePres-● w1 w2 (var x) = cong var (wkVarPres-● w1 w2 x)
wkNePres-● w1 w2 (app x y) = cong₂ app (wkNePres-● w1 w2 x) (wkNfPres-● w1 w2 y)
wkNePres-● w1 w2 (unbox x m) = ≡.trans
  (cong (λ (_ , (m' , w')) -> unbox (wkNe w' x) m') (rewind-⊆-pres-● m w1 w2))
  (cong1 unbox (wkNePres-● _ _ x))

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

record ⟶' (A' B' : Ctx -> Set) {wkA' : {Γ Δ : Ctx} (w : Γ ⊆ Δ) -> A' Γ -> A' Δ} {wkB' : {Γ Δ : Ctx} (w : Γ ⊆ Δ) -> B' Γ -> B' Δ} (Γ : Ctx) : Set where
  constructor fun'
  field
    apply' : {Δ : Ctx} -> Γ ⊆ Δ -> A' Δ -> B' Δ
    natural : {Δ Ξ : Ctx} (w : Γ ⊆ Δ) (w' : Δ ⊆ Ξ) (a' : A' Δ) -> apply' (w ● w') (wkA' w' a') ≡ wkB' w' (apply' w a')

record Box' (A' : Ctx -> Set) {wkA' : {Γ Δ : Ctx} (w : Γ ⊆ Δ) -> A' Γ -> A' Δ} (Γ : Ctx) : Set where
  constructor box'
  field
    unbox' : {Γ' Δ : Ctx} ->  Γ ⊆ Γ' -> Γ' ◁ Δ -> A' Δ
    natural : {Γ' Δ Δ' : Ctx} (w : Γ ⊆ Γ') (m : Γ' ◁ Δ) (w' : Δ ⊆ Δ')
      -> let _ , (m' , w'') = rewind-⊆ m w'
         in unbox' (w ● w'') m' ≡ wkA' w' (unbox' w m)

-- Interpret a type to a presheaf
⟦_⟧ty : Ty -> Ctx -> Set
wkTy' : {A : Ty} {Γ Δ : Ctx} -> Γ ⊆ Δ -> ⟦ A ⟧ty Γ -> ⟦ A ⟧ty Δ

⟦ ι ⟧ty Γ = Γ ⊢nf ι
⟦ A ⟶ B ⟧ty Γ = ⟶' ⟦ A ⟧ty ⟦ B ⟧ty {wkTy'} {wkTy'} Γ
⟦ □ A ⟧ty Γ = Box' ⟦ A ⟧ty {wkTy'} Γ

wkTy' {ι} w = wkNf w
wkTy' {A ⟶ B} w (fun' t' t'-nat) = fun' (λ w' -> t' (w ● w'))
  λ w' w'' a' -> ≡.trans (cong1 t' (≡.sym (●-assoc w w' w''))) (t'-nat (w ● w') w'' a')
wkTy' {□ A} w (box' t' t'-nat) = box' (λ w' -> t' (w ● w'))
  λ w2 m w3 -> ≡.trans (cong1 t' (≡.sym (●-assoc w w2 _))) (t'-nat (w ● w2) m w3)

private postulate Ty'UIP : {A : Ty} {Γ : Ctx} -> UIP (⟦ A ⟧ty Γ)

⟶'≡ : {A B : Ty} {Γ : Ctx} {f f' : ⟦ A ⟶ B ⟧ty Γ}
  -> ({Δ : Ctx} (w : Γ ⊆ Δ) (a' : ⟦ A ⟧ty Δ) -> f .⟶'.apply' w a' ≡ f' .⟶'.apply' w a')
  -> f ≡ f'
⟶'≡ {f = f} {f'} eq = ⟶'-cong₂
  (funext λ tt -> (funexti (funext λ w -> funext λ a' -> eq w a')))
  (funext λ tt -> (funexti (funexti (funext (λ w -> funext λ w' -> funext λ a' -> Ty'UIP _ _)))))
  where
    -- Take ⊤ as first parameter to avoid eagerly applying the implicits
    ⟶'-cong₂ : {A B : Ty} {Γ : Ctx}
      {apply'1 apply'2 : ⊤ -> {Δ : Ctx} -> Γ ⊆ Δ -> ⟦ A ⟧ty Δ -> ⟦ B ⟧ty Δ}
      {natural1 : ⊤ -> {Δ Ξ : Ctx} (w : Γ ⊆ Δ) (w' : Δ ⊆ Ξ) (a' : ⟦ A ⟧ty Δ) -> apply'1 tt (w ● w') (wkTy' w' a') ≡ wkTy' w' (apply'1 tt w a')}
      {natural2 : ⊤ -> {Δ Ξ : Ctx} (w : Γ ⊆ Δ) (w' : Δ ⊆ Ξ) (a' : ⟦ A ⟧ty Δ) -> apply'2 tt (w ● w') (wkTy' w' a') ≡ wkTy' w' (apply'2 tt w a')}
      -> (p : apply'1 ≡ apply'2) -> ≡.subst (λ apply' -> _) p natural1 ≡ natural2
      -> fun' (apply'1 tt) (natural1 tt) ≡ fun' (apply'2 tt) (natural2 tt)
    ⟶'-cong₂ refl refl = refl

□'≡ : {A : Ty} {Γ : Ctx} {b b' : ⟦ □ A ⟧ty Γ}
  -> ({Γ' Δ : Ctx} (w : Γ ⊆ Γ') (m : Γ' ◁ Δ) -> Box'.unbox' b w m ≡ Box'.unbox' b' w m)
  -> b ≡ b'
□'≡ {b = b} {b'} eq = □'-cong₂
  (funext λ tt -> funexti (funexti (funext λ w -> funext λ m -> eq w m)))
  (funext λ tt -> funexti (funexti (funexti (funext (λ w -> funext λ m -> funext λ w' -> Ty'UIP _ _))))) 
  where
    □'-cong₂ : {A : Ty} {Γ : Ctx}
      {a1 a2 : ⊤ -> {Γ' Δ : Ctx} -> Γ ⊆ Γ' -> Γ' ◁ Δ -> ⟦ A ⟧ty Δ}
      {b1 : ⊤ -> {Γ' Δ Δ' : Ctx} (w : Γ ⊆ Γ') (m : Γ' ◁ Δ) (w' : Δ ⊆ Δ')
        -> let _ , (m' , w'') = rewind-⊆ m w'
           in a1 tt (w ● w'') m' ≡ wkTy' w' (a1 tt w m)}
      {b2 : ⊤ -> {Γ' Δ Δ' : Ctx} (w : Γ ⊆ Γ') (m : Γ' ◁ Δ) (w' : Δ ⊆ Δ')
        -> let _ , (m' , w'') = rewind-⊆ m w'
           in a2 tt (w ● w'') m' ≡ wkTy' w' (a2 tt w m)}
      -> (p : a1 ≡ a2) -> ≡.subst (λ unbox' -> _) p b1 ≡ b2
      -> box' (a1 tt) (b1 tt) ≡ box' (a2 tt) (b2 tt)
    □'-cong₂ refl refl = refl

wkTy'Id : {Γ : Ctx} {A : Ty} (t' : ⟦ A ⟧ty Γ) -> wkTy' ⊆.id t' ≡ t'
wkTy'Id {A = ι} t' = wkNfId t'
wkTy'Id {A = A ⟶ B} t' = ⟶'≡ λ w a' -> cong1 (⟶'.apply' t') ⊆.idl
wkTy'Id {A = □ A} t' = □'≡ λ w m -> cong1 (Box'.unbox' t') ⊆.idl

wkTy'Pres-● : {A : Ty} {Γ Δ Ξ : Ctx} (w1 : Γ ⊆ Δ) (w2 : Δ ⊆ Ξ) (t' : ⟦ A ⟧ty Γ)
  -> wkTy' (w1 ● w2) t' ≡ wkTy' w2 (wkTy' w1 t')
wkTy'Pres-● {ι} w1 w2 t' = wkNfPres-● w1 w2 t'
wkTy'Pres-● {A ⟶ B} w1 w2 t' = ⟶'≡ λ w a' -> cong1 (⟶'.apply' t') (●-assoc w1 w2 w)
wkTy'Pres-● {□ A} w1 w2 t' = □'≡ λ w _m -> cong1 (Box'.unbox' t') (●-assoc w1 w2 w)

reify : {A : Ty} {Γ : Ctx} -> ⟦ A ⟧ty Γ -> Γ ⊢nf A
reifyNat : {A : Ty} {Γ Δ : Ctx} (w : Γ ⊆ Δ) (t' : ⟦ A ⟧ty Γ)
  -> wkNf w (reify t') ≡ reify (wkTy' w t')
reflect : {A : Ty} {Γ : Ctx} -> Γ ⊢ne A -> ⟦ A ⟧ty Γ
reflectNat : {A : Ty} {Γ Δ : Ctx} (w : Γ ⊆ Δ) (x : Γ ⊢ne A)
  -> wkTy' w (reflect x) ≡ reflect (wkNe w x)

reify {ι} A' = A'
reify {A ⟶ B} (fun' f _) = abs (reify (f (weak ⊆.id) (reflect (var zero))))
reify {□ A} (box' f nat) = let A' = f ⊆.id ◁1 in box (reify A')
reifyNat {ι} w t' = refl
reifyNat {A ⟶ B} w (fun' t' t'-nat) = cong abs (≡.trans
  (reifyNat (lift w) (t' (weak ⊆.id) (reflect (var zero))))
  (cong reify (≡.trans
    (≡.sym (t'-nat (weak ⊆.id) (lift w) (reflect (var zero))))
    (cong₂ _$_ (cong (t' ∘ weak) (≡.trans ⊆.idl  (≡.sym ⊆.idr)))
      (reflectNat (lift w) (var zero))))))
reifyNat {□ A} w (box' t' t'-nat) = cong box (≡.trans
  (reifyNat (lift🔓 w) (t' ⊆.id ◁1))
  (cong reify (≡.trans
    (≡.sym (t'-nat ⊆.id ◁1 (lift🔓 w)))
    (≡.trans (cong (λ (_ , (m' , w')) -> t' (⊆.id ● w') m') (rewind-⊆-◁1 w))
      (cong1 t' (≡.trans ⊆.idl (≡.sym ⊆.idr)))))))

reflect {ι} x = ne x
reflect {A ⟶ B} x = fun' (λ w a' -> reflect (app (wkNe w x) (reify a')))
  λ w w' a' -> ≡.trans (cong₂ _$_ (cong (λ x y -> reflect (app x y)) (wkNePres-● w w' x)) (≡.sym (reifyNat w' a')))
    (≡.sym (reflectNat w' (app (wkNe w x) (reify a'))))
reflect {□ A} x = box' (λ w m -> reflect (unbox (wkNe w x) m))
  λ w m w' -> ≡.trans (cong reflect (cong1 unbox (wkNePres-● w _ x)))
    (≡.sym (reflectNat w' (unbox (wkNe w x) m)))
reflectNat {ι} w x = refl
reflectNat {A ⟶ B} w x = ⟶'≡ λ w' _a' -> cong reflect (cong1 app (wkNePres-● w w' x))
reflectNat {□ A} w x = □'≡ λ w' _m -> cong reflect (cong1 unbox (wkNePres-● w w' x))

-- Interpret context to a presheaf
Env = Rpl ⟦_⟧ty
⟦_⟧ctx = Env
module Env = Rpl.Properties ⟦_⟧ty ◁1 rewind-⊆ wkTy' (reflect (var zero))

wkEnvId : {Γ Δ : Ctx} (γ : Env Γ Δ) -> Env.wk ⊆.id γ ≡ γ
wkEnvId · = refl
wkEnvId (γ , t') = cong₂ _,_ (wkEnvId γ) (wkTy'Id t')
wkEnvId (lock γ m) = ≡.trans
  (cong (λ (_ , (m' , w')) -> lock (Env.wk w' γ) m') (rewind-⊆-presId m))
  (cong1 lock (wkEnvId γ))

wkEnvPres-● = Env.wkPres-● rewind-⊆-pres-● wkTy'Pres-●

lookup : {A : Ty} {Γ Δ : Ctx} -> A ∈ Γ -> ⟦ Γ ⟧ctx Δ -> ⟦ A ⟧ty Δ
lookup x γ = Env.replaceVar γ x

-- Evaluation: Interpret terms-in-contexts as natural transformations
⟦_⟧tm : {Γ : Ctx} {A : Ty} -> Γ ⊢ A -> {Δ : Ctx} -> ⟦ Γ ⟧ctx Δ -> ⟦ A ⟧ty Δ
⟦_⟧tm-nat : {A : Ty} {Γ Δ Ξ : Ctx} (t : Γ ⊢ A) (w : Δ ⊆ Ξ) (γ : ⟦ Γ ⟧ctx Δ)
  -> ⟦ t ⟧tm (Env.wk w γ) ≡ wkTy' w (⟦ t ⟧tm γ)
⟦ var A∈Γ ⟧tm γ = lookup A∈Γ γ
⟦ abs t ⟧tm γ = fun' (λ w y' -> ⟦ t ⟧tm (Env.wk w γ , y'))
  λ w w' y' -> ≡.trans (cong (λ γ -> ⟦ t ⟧tm (γ , wkTy' w' y')) (wkEnvPres-● w w' γ))
    (⟦ t ⟧tm-nat w' (Env.wk w γ , y'))
⟦ app t s ⟧tm γ = ⟦ t ⟧tm γ .⟶'.apply' ⊆.id (⟦ s ⟧tm γ)
⟦ box t ⟧tm γ = box' (λ w m -> ⟦ t ⟧tm (lock (Env.wk w γ) m))
  λ w m w' -> ≡.trans (cong (λ γ -> ⟦ t ⟧tm (lock γ _)) (wkEnvPres-● w _ γ))
    (⟦ t ⟧tm-nat w' (lock (Env.wk w γ) m))
⟦_⟧tm (unbox t m) γ = let _ , (m' , γ') = rewind m γ
  in ⟦ t ⟧tm γ' .Box'.unbox' ⊆.id m'

⟦ abs t ⟧tm-nat w γ = ⟶'≡ λ w' a' -> cong ⟦ t ⟧tm (cong1 _,_ (≡.sym (wkEnvPres-● w w' γ)))
⟦ app t s ⟧tm-nat w γ rewrite ⟦ t ⟧tm-nat w γ | ⟦ s ⟧tm-nat w γ = ≡.trans
  (cong1 (⟶'.apply' (⟦ t ⟧tm γ)) (≡.trans (⊆.idr) (≡.sym ⊆.idl)))
  (⟦ t ⟧tm γ .⟶'.natural ⊆.id w (⟦ s ⟧tm γ))
⟦ box t ⟧tm-nat w γ = □'≡ λ w' m -> cong ⟦ t ⟧tm (cong1 lock (≡.sym (wkEnvPres-● w w' γ)))
⟦ unbox t m ⟧tm-nat w γ rewrite
    rewindWk m γ w {wkF = wkTy'} {head = reflect (var zero)}
  | let
      _ , (m' , γ') = rewind m γ
      _ , (m'' , w') = rewind-⊆ m' w
    in ⟦ t ⟧tm-nat w' γ'
  = let _ , (m' , γ') = rewind m γ in ≡.trans
    (cong1 (⟦ t ⟧tm γ' .Box'.unbox') (≡.trans ⊆.idr (≡.sym ⊆.idl)))
    (⟦ t ⟧tm γ' .Box'.natural ⊆.id m' w)
⟦ var zero ⟧tm-nat w (_ , _) = refl
⟦ var (suc x) ⟧tm-nat w (γ , _) = ⟦ var x ⟧tm-nat w γ

-- Normalization function
nf : {Γ : Ctx} {A : Ty} -> Γ ⊢ A -> Γ ⊢nf A
-- Evaluate in fresh environment consisting of all neutrals
nf t = reify (⟦ t ⟧tm Env.id)
