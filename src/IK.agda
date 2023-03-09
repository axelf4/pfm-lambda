-- Instantiation of Intuitionistic K.
module IK where

open import Agda.Builtin.Sigma using (Σ; snd) renaming (_,_ to infix 20 _,_)
open import Data.Product using (_×_)
open import Context

_◁_ : Ctx -> Ctx -> Set
_◁_ Γ Δ = LFExt (Γ ,🔓) Δ

◁1 : {Γ : Ctx} -> Γ ◁ (Γ ,🔓)
◁1 = nil

rewind-⊆ : {Γ Γ' Δ : Ctx}
  -> (m : Γ' ◁ Γ) -> (w : Γ ⊆ Δ)
  -> Σ Ctx λ Δ' -> Δ' ◁ Δ × Γ' ⊆ Δ'
rewind-⊆ m (weak w)
  = let Δ' , (m' , w') = rewind-⊆ m w in Δ' , (snoc m' , w')
rewind-⊆ (snoc m) (lift w)
  = let Δ' , (m' , w') = rewind-⊆ m w in Δ' , (snoc m' , w')
rewind-⊆ nil (lift🔓 w) = _ , (nil , w)

rewindRpl : {F : Ty -> Ctx -> Set} {Γ Γ' Δ : Ctx}
  -> (m : Γ' ◁ Γ) -> (x : Rpl _◁_ F Γ Δ)
  -> Σ Ctx λ Δ' -> Δ' ◁ Δ × Rpl _◁_ F Γ' Δ'
rewindRpl nil (lock x m') = _ , (m' , x)
rewindRpl (snoc m) (x , _)
  = let Δ' , (m' , x') = rewindRpl m x in Δ' , (m' , x')

open import Main
  _◁_ ◁1
  rewind-⊆
  rewindRpl
  public

x = nf {· , ι} (app (abs (var zero)) (var zero))
