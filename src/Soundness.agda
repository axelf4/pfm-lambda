{-# OPTIONS --without-K #-}

open import Parameters as _ using (Parameters)

-- Soundness proof of normalization.
module Soundness (params : Parameters) where

open import Data.Product using (Σ; proj₁; proj₂) renaming (_,_ to infix 20 _,_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl; cong)
open ≡.≡-Reasoning

open import Util using (cong1; dcong₃)
open import Context

open Parameters params
open Replacement _◁_ using (Rpl; ·; _,_; lock)
open import Calculus params

-- Kripke logical relation
_≈_ : {A : Ty} {Γ : Ctx} -> Γ ⊢ A -> ⟦ A ⟧ty Γ -> Set
_≈_ {ι} t t' = t ~ ⌜ t' ⌝nf
_≈_ {A ⟶ B} {Γ} t t' = {Δ : Ctx} -> (w : Γ ⊆ Δ)
  -> {a : Δ ⊢ A} {a' : ⟦ A ⟧ty Δ}
  -> a ≈ a' -> app (wk w t) a ≈ proj₁ t' w a'
_≈_ {□ A} {Γ} t t' = {Γ' Δ : Ctx} -> (w : Γ ⊆ Γ') -> (m : Γ' ◁ Δ)
  -> unbox (wk w t) m ≈ Box'.unbox' t' w m

-- Transitivity between ~ and ≈ (≈-cons)
_~◼≈_ : ∀ {A Γ t s} {t' : ⟦ A ⟧ty Γ} -> t ~ s -> s ≈ t' -> t ≈ t'
_~◼≈_ {ι} p q = ~-trans p q
_~◼≈_ {A ⟶ B} p q w a≈a' = cong-app (wk-~ w p) ~-refl ~◼≈ q w a≈a'
_~◼≈_ {□ A} p q w m = cong-unbox (wk-~ w p) ~◼≈ q w m

reify≈ : {A : Ty} {Γ : Ctx} {t : Γ ⊢ A} {t' : ⟦ A ⟧ty Γ}
  -> t ≈ t' -> t ~ ⌜ reify t' ⌝nf
reflect≈ : {A : Ty} {Γ : Ctx} (t' : Γ ⊢ne A) -> ⌜ t' ⌝ne ≈ reflect t'

reify≈ {ι} t≈t' = t≈t'
reify≈ {A ⟶ B} t≈t' = ~-trans (η _) (cong-abs (reify≈ (t≈t' (weak ⊆.id) (reflect≈ (var zero)))))
reify≈ {□ A} {t = t} t≈t' = ~-trans (□-η t) (cong-box (reify≈
  (≡.subst (λ x -> unbox x _ ≈ _) (wkId t) (t≈t' ⊆.id ◁1))))

reflect≈ {ι} t' = ~-refl
reflect≈ {A ⟶ B} t' w {a} {a'} a≈a' rewrite ≡.sym (⌜⌝ne-nat w t')
  = cong-app ~-refl (reify≈ a≈a') ~◼≈ reflect≈ (app (wkNe w t') (reify a'))
reflect≈ {□ A} t' w m rewrite ≡.sym (⌜⌝ne-nat w t')
  = reflect≈ (unbox (wkNe w t') m)

record A≈A' (A : Ty) (Γ : Ctx) : Set where
  field
    t : Γ ⊢ A
    t' : ⟦ A ⟧ty Γ
    t≈t' : t ≈ t'

wk-≈ : {A : Ty} {Γ Δ : Ctx} {t : Γ ⊢ A} {t' : ⟦ A ⟧ty Γ}
  -> (w : Γ ⊆ Δ) -> t ≈ t' -> wk w t ≈ wkTy' w t'
wk-≈ {ι} {t' = t'} w t≈t'
  = ≡.subst (_ ~_) (≡.sym (⌜⌝nf-nat w t')) (wk-~ w t≈t')
wk-≈ {A ⟶ B} {t = t} w t≈t' w2 rewrite ≡.sym (wkPres-● w w2 t) = t≈t' (w ● w2)
wk-≈ {□ A} {t = t} w t≈t' w2 rewrite ≡.sym (wkPres-● w w2 t) = t≈t' (w ● w2)

wk-A≈A' : {A : Ty} {Γ Δ : Ctx} -> (w : Γ ⊆ Δ) -> A≈A' A Γ -> A≈A' A Δ
wk-A≈A' w record { t = t ; t' = t' ; t≈t' = t≈t' } = record
  { t = wk w t; t' = wkTy' w t'; t≈t' = wk-≈ w t≈t' }

Ctx≈ = Rpl A≈A'
module Ctx≈ where
  open module Props = Rpl.Properties A≈A' ◁1 rewind-⊆ wk-A≈A'
    record { t = var zero; t' = reflect (var zero); t≈t' = reflect≈ (var zero) }
    public

  toSub : {Γ Δ : Ctx} -> Ctx≈ Γ Δ -> Sub Γ Δ
  toSub = Rpl.map A≈A'.t
  toEnv : {Γ Δ : Ctx} -> Ctx≈ Γ Δ -> Env Γ Δ
  toEnv = Rpl.map A≈A'.t'

  toSubWk : {Γ Δ Δ' : Ctx} (σ≈δ : Ctx≈ Γ Δ) {w : Δ ⊆ Δ'} -> toSub (Props.wk w σ≈δ) ≡ Sub.wk w (toSub σ≈δ)
  toSubWk · = refl
  toSubWk (r , x) = cong (_, _) (toSubWk r)
  toSubWk (lock r m) = cong1 lock (toSubWk r)
  toEnvWk : {Γ Δ Δ' : Ctx} (σ≈δ : Ctx≈ Γ Δ) {w : Δ ⊆ Δ'} -> toEnv (Props.wk w σ≈δ) ≡ Env.wk w (toEnv σ≈δ)
  toEnvWk · = refl
  toEnvWk (r , x) = cong (_, _) (toEnvWk r)
  toEnvWk (lock r m) = cong1 lock (toEnvWk r)

  toSubId : {Γ : Ctx} -> toSub id ≡ Sub.id {Γ}
  toSubId {·} = refl
  toSubId {Γ , A} = cong1 _,_ (≡.trans (toSubWk id {weak ⊆.id})
    (cong (Sub.wk _) toSubId))
  toSubId {Γ ,🔓} = cong1 lock toSubId
  toEnvId : {Γ : Ctx} -> toEnv id ≡ Env.id {Γ}
  toEnvId {·} = refl
  toEnvId {Γ , A} = cong1 _,_ (≡.trans (toEnvWk id {weak ⊆.id})
    (cong (Env.wk _) toEnvId))
  toEnvId {Γ ,🔓} = cong1 lock toEnvId

fund : {A : Ty} {Γ Δ : Ctx} (t : Γ ⊢ A) -> (σ≈δ : Ctx≈ Γ Δ) -> let
  σ = Ctx≈.toSub σ≈δ
  δ = Ctx≈.toEnv σ≈δ
  in subst σ t ≈ ⟦ t ⟧tm δ
fund (abs t) σ≈δ w {a} {a'} a≈a' = ≡.subst
  (app (abs (wk (lift w) (subst (Sub.liftRpl σ) t))) a ~_)
  (≡.trans (≡.sym (cohTrimWk (lift w) (Sub.id , a) (subst _ t)))
    (≡.trans (≡.sym (substPres-∙ (Sub.liftRpl σ) (Sub.trim w Sub.id , a) t))
      (cong (λ x -> subst (x , a) t)
        (≡.trans (assocSWS σ (weak ⊆.id) (Sub.trim w Sub.id , a))
          (≡.trans (cong (σ ∙_) (Sub.trimIdl _))
            (≡.trans (≡.sym (assocSWS σ w Sub.id)) idrSub))))))
  (β (wk (lift w) (subst (Sub.liftRpl σ) t)) a)
  ~◼≈ ≡.subst₂ (λ p q -> subst (p , a) t ≈ ⟦ t ⟧tm (q , a')) (Ctx≈.toSubWk σ≈δ) (Ctx≈.toEnvWk σ≈δ) ih
  where
    σ = Ctx≈.toSub σ≈δ
    ih = fund t (Ctx≈.wk w σ≈δ , record { t = a; t' = a'; t≈t' = a≈a' })
fund (app t s) σ≈δ rewrite ≡.sym (wkId (subst (Ctx≈.toSub σ≈δ) t))
  = fund t σ≈δ ⊆.id (fund s σ≈δ)
fund (box t) σ≈δ w m = ≡.subst
  (unbox (wk w (subst σ (box t))) m ~_)
  (begin
    subst (lock Sub.id m) (wk (lift🔓 w) (subst (lock σ ◁1) t))
    ≡˘⟨ cong (subst _) (substNat (lift🔓 w) _ t) ⟩
    subst (lock Sub.id m) (subst (Sub.wk (lift🔓 w) (lock σ ◁1)) t)
    ≡⟨ cong (λ (_ , (m' , w')) -> subst (lock Sub.id m) (subst (lock (Sub.wk w' σ) m') t))
      (rewind-⊆-◁1 w) ⟩
    subst (lock Sub.id m) (subst (lock (Sub.wk w σ) ◁1) t)
    ≡˘⟨ substPres-∙ (lock (Sub.wk w σ) ◁1) (lock Sub.id m) t ⟩
    subst (lock (Sub.wk w σ) ◁1 ∙ lock Sub.id m) t
    ≡⟨ cong (λ (_ , (m' , δ)) -> subst (lock ((Sub.wk w σ) ∙ δ) m') t)
      (rewind-◁1 _) ⟩
    subst (lock (Sub.wk w σ ∙ Sub.id) m) t
    ≡⟨ cong (λ x -> subst (lock x m) t) idrSub ⟩
    subst (lock (Sub.wk w σ) m) t ∎)
  (□-β (wk (lift🔓 w) (subst (lock σ ◁1) t)) m)
  ~◼≈ ≡.subst₂ (λ p q -> subst (lock p m) t ≈ ⟦ t ⟧tm (lock q m)) (Ctx≈.toSubWk σ≈δ) (Ctx≈.toEnvWk σ≈δ) ih
  where
    σ = Ctx≈.toSub σ≈δ
    ih = fund t (lock (Ctx≈.wk w σ≈δ) m)
fund (unbox t m) σ≈δ rewrite ≡.sym (wkId (subst (proj₂ (proj₂ (rewind m (Ctx≈.toSub σ≈δ)))) t))
  = let
    Ξ≡Ξ'1 , (m≡m'1 , σ≡σ') = rewindCommMap A≈A'.t m σ≈δ
    Ξ≡Ξ'2 , (m≡m'2 , δ≡δ') = rewindCommMap A≈A'.t' m σ≈δ
  in ≡.subst₂ (_≈_)
    (dcong₃ (λ _Ξ σ' m' -> unbox (wk ⊆.id (subst σ' t)) m') Ξ≡Ξ'1 σ≡σ' m≡m'1)
    (dcong₃ (λ Ξ δ' m' -> ⟦ t ⟧tm {Ξ} δ' .Box'.unbox' ⊆.id m') Ξ≡Ξ'2 δ≡δ' m≡m'2)
    (fund t (proj₂ (proj₂ (rewind m σ≈δ))) ⊆.id (proj₁ (proj₂ (rewind m σ≈δ))))
-- Lookup witnesses for variables in σ≈δ
fund (var zero) (σ≈δ , record { t≈t' = a≈a' }) = a≈a'
fund (var (suc x)) (σ≈δ , _) = fund (var x) σ≈δ

sound : {Γ : Ctx} {A : Ty} (t : Γ ⊢ A) -> t ~ ⌜ nf t ⌝nf
sound t = ≡.subst (_~ ⌜ reify (⟦ t ⟧tm Env.id) ⌝nf) (substId t) (reify≈
  (≡.subst₂ (λ σ δ -> subst σ t ≈ ⟦ t ⟧tm δ) Ctx≈.toSubId Ctx≈.toEnvId
    (fund t Ctx≈.id)))
