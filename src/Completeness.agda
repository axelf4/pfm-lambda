{-# OPTIONS --without-K #-}

open import Parameters as _ using (Parameters)

module Completeness (params : Parameters) where

open import Agda.Builtin.Sigma using (Σ; fst; snd) renaming (_,_ to infix 20 _,_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl; cong; cong₂)

open import Util using (cong1)
open import Context

open Parameters params
open Replacement _◁_ using (Rpl; ·; _,_; lock)
open import Calculus params

-- Interpret OPE:s as natural transformations between semantic contexts
OPE' = Env.trim

wkTm' : {Γ Δ Ξ : Ctx} {A : Ty} (w : Γ ⊆ Δ) (t : Γ ⊢ A) (γ : Env Δ Ξ)
  -> ⟦ wk w t ⟧tm γ ≡ ⟦ t ⟧tm (OPE' w γ)
wkTm' w (var v) γ = wk-∈' w v γ
  where
    wk-∈' : {Γ Δ Ξ : Ctx} {A : Ty} (w : Γ ⊆ Δ) (v : A ∈ Γ) (γ : Env Δ Ξ)
      -> lookup (wkVar w v) γ ≡ lookup v (OPE' w γ)
    wk-∈' (weak w) v (γ , _) = wk-∈' w v γ
    wk-∈' (lift w) zero (γ , t') = refl
    wk-∈' (lift w) (suc v) (γ , _) = wk-∈' w v γ
wkTm' w (abs t) γ = ⟶'≡ λ w' a' -> ≡.trans
  (wkTm' (lift w) t (Env.wk w' γ , a'))
  (cong (λ x -> ⟦ t ⟧tm (x , a')) (≡.sym (Env.trimNat w w' γ)))
wkTm' w (app t s) γ rewrite wkTm' w t γ | wkTm' w s γ = refl
wkTm' w (box t) γ = □'≡ λ w' m -> ≡.trans
  (wkTm' (lift🔓 w) t (lock (Env.wk w' γ) m))
  (cong (λ x -> ⟦ t ⟧tm (lock x m)) (≡.sym (Env.trimNat w w' γ)))
wkTm' w (unbox t m) γ rewrite
    rewindTrim m w γ {wkF = wkTy'} {head = reflect (var zero)}
  | let
      _ , (m' , w') = rewind-⊆ m w
      _ , (m'' , Δ') = rewind m' γ
    in wkTm' w' t Δ'
  = refl

-- Interpret substitutions as natural transformations between semantic contexts
open Rpl.Composition (λ A Γ -> Γ ⊢ A) ⟦_⟧ty
  rewind (λ γ t -> ⟦ t ⟧tm γ) renaming (_∙_ to Sub')

Sub'-nat : {Γ Γ' Δ Δ' : Ctx} (σ : Sub Γ' Γ) (w : Δ ⊆ Δ') (γ : Env Γ Δ)
  -> Env.wk w (Sub' σ γ) ≡ Sub' σ (Env.wk w γ)
Sub'-nat · w γ = refl
Sub'-nat (σ , t) w γ = cong₂ _,_ (Sub'-nat σ w γ) (≡.sym (⟦ t ⟧tm-nat w γ))
Sub'-nat (lock σ m) w γ rewrite rewindWk m γ w {wkF = wkTy'} {head = reflect (var zero)}
  = cong1 lock (Sub'-nat σ _ _)

wkSub' : {Γ Γ' Δ Ξ : Ctx} (σ : Sub Ξ Γ') (w : Γ' ⊆ Γ) (γ : Env Γ Δ)
  -> Sub' (Sub.wk w σ) γ ≡ Sub' σ (OPE' w γ)
wkSub' · _ _ = refl
wkSub' (σ , t) w γ = cong₂ _,_ (wkSub' σ w γ) (wkTm' w t γ)
wkSub' (lock σ m) w γ rewrite rewindTrim m w γ {wkF = wkTy'} {head = reflect (var zero)}
  = cong1 lock (wkSub' σ _ _)

Sub'-id : {Γ Δ : Ctx} (γ : Env Γ Δ) -> Sub' Sub.id γ ≡ γ
Sub'-id · = refl
Sub'-id (γ , t') = cong (_, t') (≡.trans
  (wkSub' Sub.id (weak ⊆.id) (γ , t'))
  (≡.trans (Sub'-id (OPE' ⊆.id γ)) (Env.trimIdl γ)))
Sub'-id (lock γ m) = ≡.trans
  (cong (λ (_ , (m' , Δ')) -> lock (Sub' Sub.id Δ') m') (rewind-◁1 γ))
  (cong1 lock (Sub'-id γ))

substTm' : {Γ Δ Ξ : Ctx} {A : Ty} (σ : Sub Γ Δ) (t : Γ ⊢ A) (γ : Env Δ Ξ)
  -> ⟦ subst σ t ⟧tm γ ≡ ⟦ t ⟧tm (Sub' σ γ)
substTm' σ (abs t) γ = ⟶'≡ λ w t' -> ≡.trans
  (substTm' (Sub.liftRpl σ) t (Env.wk w γ , t'))
  (cong (λ x -> ⟦ t ⟧tm (x , t')) (≡.trans
    (wkSub' σ (weak ⊆.id) (Env.wk w γ , t'))
    (≡.trans
      (cong (Sub' σ) (Env.trimIdl (Env.wk w γ)))
      (≡.sym (Sub'-nat σ w γ)))))
substTm' σ (app t s) γ rewrite substTm' σ t γ | substTm' σ s γ = refl
substTm' σ (box t) γ = □'≡ λ w m -> ≡.trans
  (substTm' (lock σ ◁1) t (lock (Env.wk w γ) m))
  (≡.trans
    (cong (λ (_ , (m' , Δ')) -> ⟦ t ⟧tm (lock (Sub' σ Δ') m'))
      (rewind-◁1 (Env.wk w γ)))
    (cong (λ x → ⟦ t ⟧tm (lock x m)) (≡.sym (Sub'-nat σ w γ))))
substTm' σ (unbox t m) γ rewrite let
    _ , (m' , σ') = rewind m σ
  in substTm' σ' t (snd (snd (rewind m' γ)))
  = cong (λ (_ , (m'' , γ')) -> ⟦ t ⟧tm γ' .Box'.unbox' ⊆.id m'')
    (≡.sym (rewindPres-∙ m σ γ))
substTm' (σ , t) (var zero) γ = refl
substTm' (σ , _) (var (suc v)) γ = substTm' σ (var v) γ

-- Soundness of evaluation wrt. conversion
evalSound : {A : Ty} {Γ Δ : Ctx} {t t' : Γ ⊢ A} -> t ~ t' -> (γ : Env Γ Δ)
  -> ⟦ t ⟧tm γ ≡ ⟦ t' ⟧tm γ
evalSound (β t s) γ = ≡.trans
  (cong (λ x -> ⟦ t ⟧tm (x , ⟦ s ⟧tm γ)) (≡.trans (wkEnvId γ) (≡.sym (Sub'-id γ))))
  (≡.sym (substTm' (Sub.id , s) t γ))
evalSound (η t) γ = ⟶'≡ λ w a' -> ≡.trans
  (cong1 (⟦ t ⟧tm γ .fst) (≡.sym ⊆.idr))
  (cong (λ x -> fst x ⊆.id a') (≡.sym (≡.trans
    (wkTm' (weak ⊆.id) t (Env.wk w γ , a'))
    (≡.trans (cong ⟦ t ⟧tm (Env.trimIdl (Env.wk w γ)))
      (⟦ t ⟧tm-nat w γ)))))
evalSound (□-β t m) γ = ≡.trans
  (cong (λ x → ⟦ t ⟧tm (lock x (fst (snd (rewind m γ)))))
    (≡.trans (wkEnvId _) (≡.sym (Sub'-id _))))
  (≡.sym (substTm' (lock Sub.id m) t γ))
evalSound (□-η t) γ = □'≡ λ w m -> ≡.trans
  (≡.trans (cong1 (⟦ t ⟧tm γ .Box'.unbox') (≡.sym ⊆.idr))
    (cong (λ x -> Box'.unbox' x ⊆.id m) (≡.sym (⟦ t ⟧tm-nat w γ))))
  (cong (λ (_ , (m' , Δ')) -> ⟦ t ⟧tm Δ' .Box'.unbox' ⊆.id m')
     (≡.sym (rewind-◁1 (Env.wk w γ))))
evalSound ~-refl _ = refl
evalSound (~-sym t'~t) γ = ≡.sym (evalSound t'~t γ)
evalSound (~-trans t~t' t'~t'') γ = ≡.trans (evalSound t~t' γ) (evalSound t'~t'' γ)
evalSound (cong-abs t~t') γ = ⟶'≡ (λ w a' -> evalSound t~t' (Env.wk w γ , a'))
evalSound (cong-app t~t' a~a') γ
  = cong₂ (λ f -> fst f ⊆.id) (evalSound t~t' γ) (evalSound a~a' γ)
evalSound (cong-box t~t') γ = □'≡ (λ w m → evalSound t~t' (lock (Env.wk w γ) m))
evalSound (cong-unbox {m = m} t~t') γ
  rewrite evalSound t~t' (snd (snd (rewind m γ))) = refl

complete : {Γ : Ctx} {A : Ty} {t t' : Γ ⊢ A} -> t ~ t' -> nf t ≡ nf t'
complete t~t' = cong reify (evalSound t~t' Env.id)
