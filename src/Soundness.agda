{-# OPTIONS --without-K #-}

open import Parameters as _ using (Parameters)

module Soundness (params : Parameters) where

open import Agda.Builtin.Sigma using (Σ; fst; snd) renaming (_,_ to infix 20 _,_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl; cong; cong₂)

open import Util using (cong1)
open import Context

open Parameters params
open Replacement _◁_ using (Rpl; ·; _,_; lock)
open import Calculus params

-- Interpret OPE:s as natural transformations between semantic contexts
OPE' = Env.trim

wkTm' : {Γ Δ Ξ : Ctx} {A : Ty} (w : Γ ⊆ Δ) (t : Γ ⊢ A) (Γ' : Env Δ Ξ)
  -> ⟦ wk w t ⟧tm Γ' ≡ ⟦ t ⟧tm (OPE' w Γ')
wkTm' w (var v) Γ' = wk-∈' w v Γ'
  where
    wk-∈' : {Γ Δ Ξ : Ctx} {A : Ty} (w : Γ ⊆ Δ) (v : A ∈ Γ) (Γ' : Env Δ Ξ)
      -> lookup (wkVar w v) Γ' ≡ lookup v (OPE' w Γ')
    wk-∈' (weak w) v (Γ' , _) = wk-∈' w v Γ'
    wk-∈' (lift w) zero (Γ' , t') = refl
    wk-∈' (lift w) (suc v) (Γ' , _) = wk-∈' w v Γ'
wkTm' w (abs t) Γ' = ⟶'≡ λ w' a' -> ≡.trans
  (wkTm' (lift w) t (Env.wk w' Γ' , a'))
  (cong (λ x -> ⟦ t ⟧tm (x , a')) (≡.sym (Env.trimNat w w' Γ')))
wkTm' w (app t s) Γ' rewrite wkTm' w t Γ' | wkTm' w s Γ' = refl
wkTm' w (box t) Γ' = □'≡ λ w' m -> ≡.trans
  (wkTm' (lift🔓 w) t (lock (Env.wk w' Γ') m))
  (cong (λ x -> ⟦ t ⟧tm (lock x m)) (≡.sym (Env.trimNat w w' Γ')))
wkTm' w (unbox t m) Γ' rewrite
    rewindTrim m w Γ' {wkF = wkTy'} {head = reflect (var zero)}
  | let
      _ , (m' , w') = rewind-⊆ m w
      _ , (m'' , Δ') = rewind m' Γ'
    in wkTm' w' t Δ'
  = refl

-- Interpret substitutions as natural transformations between semantic contexts
open Rpl.Composition (λ A Γ -> Γ ⊢ A) ⟦_⟧ty
  rewind (λ Γ' t -> ⟦ t ⟧tm Γ') renaming (_∙_ to Sub')

Sub'-nat : {Γ Γ' Δ Δ' : Ctx} (σ : Sub Γ' Γ) (w : Δ ⊆ Δ') (Γ' : Env Γ Δ)
  -> Env.wk w (Sub' σ Γ') ≡ Sub' σ (Env.wk w Γ')
Sub'-nat · w Γ' = refl
Sub'-nat (σ , t) w Γ' = cong₂ _,_ (Sub'-nat σ w Γ') (≡.sym (⟦ t ⟧tm-nat w Γ'))
Sub'-nat (lock σ m) w Γ' rewrite rewindWk m Γ' w {wkF = wkTy'} {head = reflect (var zero)}
  = cong1 lock (Sub'-nat σ _ _)

wkSub' : {Γ Γ' Δ Ξ : Ctx} (σ : Sub Ξ Γ') (w : Γ' ⊆ Γ) (Γ' : Env Γ Δ)
  -> Sub' (Sub.wk w σ) Γ' ≡ Sub' σ (OPE' w Γ')
wkSub' · _ _ = refl
wkSub' (σ , t) w Γ' = cong₂ _,_ (wkSub' σ w Γ') (wkTm' w t Γ')
wkSub' (lock σ m) w Γ' rewrite rewindTrim m w Γ' {wkF = wkTy'} {head = reflect (var zero)}
  = cong1 lock (wkSub' σ _ _)

Sub'-id : {Γ Δ : Ctx} (Γ' : Env Γ Δ) -> Sub' Sub.id Γ' ≡ Γ'
Sub'-id · = refl
Sub'-id (Γ' , t') = cong (_, t') (≡.trans
  (wkSub' Sub.id (weak ⊆.id) (Γ' , t'))
  (≡.trans (Sub'-id (OPE' ⊆.id Γ')) (Env.trimIdl Γ')))
Sub'-id (lock Γ' m) = ≡.trans
  (cong (λ (_ , (m' , Δ')) -> lock (Sub' Sub.id Δ') m') (rewind-◁1 Γ'))
  (cong1 lock (Sub'-id Γ'))

substTm' : {Γ Δ Ξ : Ctx} {A : Ty} (σ : Sub Γ Δ) (t : Γ ⊢ A) (Γ' : Env Δ Ξ)
  -> ⟦ subst σ t ⟧tm Γ' ≡ ⟦ t ⟧tm (Sub' σ Γ')
substTm' σ (abs t) Γ' = ⟶'≡ λ w t' -> ≡.trans (substTm' (Sub.liftRpl σ) t (Env.wk w Γ' , t'))
  (cong (λ x -> ⟦ t ⟧tm (x , t')) (≡.trans
    (wkSub' σ (weak ⊆.id) (Env.wk w Γ' , t'))
    (≡.trans
      (cong (Sub' σ) (Env.trimIdl (Env.wk w Γ')))
      (≡.sym (Sub'-nat σ w Γ')))))
substTm' σ (app t s) Γ' rewrite substTm' σ t Γ' | substTm' σ s Γ' = refl
substTm' σ (box t) Γ' = □'≡ λ w m -> ≡.trans (substTm' (lock σ ◁1) t (lock (Env.wk w Γ') m))
  (≡.trans
    (cong (λ (_ , (m' , Δ')) -> ⟦ t ⟧tm (lock (Sub' σ Δ') m'))
      (rewind-◁1 (Env.wk w Γ')))
    (cong (λ x → ⟦ t ⟧tm (lock x m)) (≡.sym (Sub'-nat σ w Γ'))))
substTm' σ (unbox t m) Γ' rewrite let
    _ , (m' , σ') = rewind m σ
  in substTm' σ' t (snd (snd (rewind m' Γ')))
  = cong (λ (_ , (m'' , Γ'')) -> ⟦ t ⟧tm Γ'' .Box'.unbox' ⊆.id m'')
    (≡.sym (rewindPres-∙ m σ Γ'))
substTm' (σ , t) (var zero) Γ' = refl
substTm' (σ , _) (var (suc v)) Γ' = substTm' σ (var v) Γ'

-- Soundness of evaluation wrt. conversion
evalSound : {A : Ty} {Γ Δ : Ctx} {t t' : Γ ⊢ A} -> t ~ t' -> (Γ' : Env Γ Δ)
  -> ⟦ t ⟧tm Γ' ≡ ⟦ t' ⟧tm Γ'
evalSound (β t s) Γ' = ≡.trans
  (cong (λ x -> ⟦ t ⟧tm (x , ⟦ s ⟧tm Γ')) (≡.trans (wkEnvId Γ') (≡.sym (Sub'-id Γ'))))
  (≡.sym (substTm' (Sub.id , s) t Γ'))
evalSound (η t) Γ' = ⟶'≡ λ w a' -> ≡.trans
  (cong1 (⟦ t ⟧tm Γ' .fst) (≡.sym ⊆.idr))
  (cong (λ x -> fst x ⊆.id a') (≡.sym (≡.trans
    (wkTm' (weak ⊆.id) t (Env.wk w Γ' , a'))
    (≡.trans (cong ⟦ t ⟧tm (Env.trimIdl (Env.wk w Γ')))
      (⟦ t ⟧tm-nat w Γ')))))
evalSound (□-β t m) Γ' = ≡.trans
  (cong (λ x → ⟦ t ⟧tm (lock x (fst (snd (rewind m Γ')))))
    (≡.trans (wkEnvId _) (≡.sym (Sub'-id _))))
  (≡.sym (substTm' (lock Sub.id m) t Γ'))
evalSound (□-η t) Γ' = □'≡ λ w m -> ≡.trans
  (≡.trans (cong1 (⟦ t ⟧tm Γ' .Box'.unbox') (≡.sym ⊆.idr))
    (cong (λ x -> Box'.unbox' x ⊆.id m) (≡.sym (⟦ t ⟧tm-nat w Γ'))))
  (cong (λ (_ , (m' , Δ')) -> ⟦ t ⟧tm Δ' .Box'.unbox' ⊆.id m')
     (≡.sym (rewind-◁1 (Env.wk w Γ'))))
evalSound ~-refl _ = refl
evalSound (~-sym t'~t) Γ' = ≡.sym (evalSound t'~t Γ')
evalSound (~-trans t~t' t'~t'') Γ' = ≡.trans (evalSound t~t' Γ') (evalSound t'~t'' Γ')
evalSound (cong-abs t~t') Γ' = ⟶'≡ (λ w a' -> evalSound t~t' (Env.wk w Γ' , a'))
evalSound (cong-app t~t' a~a') Γ'
  = cong₂ (λ f -> fst f ⊆.id) (evalSound t~t' Γ') (evalSound a~a' Γ')
evalSound (cong-box t~t') Γ' = □'≡ (λ w m → evalSound t~t' (lock (Env.wk w Γ') m))
evalSound (cong-unbox {m = m} t~t') Γ'
  rewrite evalSound t~t' (snd (snd (rewind m Γ'))) = refl

sound : {Γ : Ctx} {A : Ty} {t t' : Γ ⊢ A} -> t ~ t' -> nf t ≡ nf t'
sound t~t' = cong reify (evalSound t~t' Env.id)
