{-# OPTIONS --without-K --safe #-}

open import Agda.Builtin.Sigma using (Σ; fst; snd) renaming (_,_ to infix 20 _,_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Data.Product using (_×_)

open import Context

record Parameters : Set1 where
  field
    -- Modal accessibility relation on contexts
    -- (\lhd -> ◁)
    _◁_ : Ctx -> Ctx -> Set
    ◁1 : {Γ : Ctx} -> Γ ◁ (Γ ,🔓)

  open module Rpl = Replacement _◁_ using (Rpl; ·; _,_; lock)

  field
    -- Trim OPE:s and substitutions/environments
    rewind-⊆ : {Γ Γ' Δ : Ctx} -> (m : Γ' ◁ Γ) -> Γ ⊆ Δ
      -> Σ Ctx λ Δ' -> Δ' ◁ Δ × Γ' ⊆ Δ'
    rewind : ∀ {F} {Γ Γ' Δ : Ctx} -> (m : Γ' ◁ Γ) -> Rpl F Γ Δ
      -> Σ Ctx λ Δ' -> Δ' ◁ Δ × Rpl F Γ' Δ'

    rewind-⊆-◁1 : {Γ Δ : Ctx} (w : Γ ⊆ Δ)
      -> rewind-⊆ ◁1 (lift🔓 w) ≡ _ , (◁1 , w)
    rewind-◁1 : ∀ {F} {Γ Δ Δ' : Ctx} (σ : Rpl F Γ Δ) {m : Δ ◁ Δ'}
      -> rewind ◁1 (lock σ m) ≡ _ , (m , σ)

    rewind-⊆-pres-● : {Δ Γ Γ' Γ'' : Ctx} (m : Δ ◁ Γ) (w1 : Γ ⊆ Γ') (w2 : Γ' ⊆ Γ'')
      -> let _ , (m' , w1') = rewind-⊆ m w1
             _ , (m'' , w2') = rewind-⊆ m' w2
         in rewind-⊆ m (w1 ● w2) ≡ (_ , (m'' , (w1' ● w2')))
    rewindPres-∙ : ∀ {F G} {Δ Γ Γ' Γ'' : Ctx} (m : Δ ◁ Γ) (σ : Rpl F Γ Γ') (δ : Rpl G Γ' Γ'')
      {apply : {A : Ty} {Γ Δ : Ctx} -> Rpl G Γ Δ -> F A Γ -> G A Δ}
      -> let open Rpl.Composition F G rewind apply using (_∙_)
             _ , (m' , σ') = rewind m σ
             _ , (m'' , δ') = rewind m' δ
         in rewind m (σ ∙ δ) ≡ (_ , (m'' , (σ' ∙ δ')))

    rewind-⊆-presId : {Γ Δ : Ctx} (m : Δ ◁ Γ) -> rewind-⊆ m ⊆.id ≡ Δ , (m , ⊆.id)
    rewindPresId : ∀ {F} {Γ Δ : Ctx} -> (m : Δ ◁ Γ)
      {wkF : {A : Ty} {Γ Γ' : Ctx} -> Γ ⊆ Γ' -> F A Γ -> F A Γ'}
      {head : {A : Ty} {Γ : Ctx} -> F A (Γ , A)}
      (let open Rpl.Properties F ◁1 rewind-⊆ wkF head using (id))
      (wkFId : {A : Ty} {Γ : Ctx} (x : F A Γ) -> wkF ⊆.id x ≡ x)
        -> rewind m id ≡ Δ , (m , id)

    -- Weakening a substitution works the same before and after rewinding
    rewindWk : ∀ {F} {Γ Γ' Γ'' Δ : Ctx} (m : Δ ◁ Γ) (σ : Rpl F Γ Γ') (w : Γ' ⊆ Γ'')
      {wkF : {A : Ty} {Γ Γ' : Ctx} -> Γ ⊆ Γ' -> F A Γ -> F A Γ'}
      {head : {A : Ty} {Γ : Ctx} -> F A (Γ , A)}
      -> let open Rpl.Properties F ◁1 rewind-⊆ wkF head using (wk)
             _ , (m' , σ') = rewind m σ
             _ , (m'' , w') = rewind-⊆ m' w
         in rewind m (wk w σ) ≡ _ , (m'' , wk w' σ')
    rewindTrim : ∀ {F} {Γ Γ' Γ'' Δ : Ctx} (m : Δ ◁ Γ) (w : Γ ⊆ Γ') (σ : Rpl F Γ' Γ'')
      {wkF : {A : Ty} {Γ Γ' : Ctx} -> Γ ⊆ Γ' -> F A Γ -> F A Γ'}
      {head : {A : Ty} {Γ : Ctx} -> F A (Γ , A)}
      -> let open Rpl.Properties F ◁1 rewind-⊆ wkF head using (trim)
             _ , (m' , w') = rewind-⊆ m w
             _ , (m'' , σ') = rewind m' σ
         in rewind m (trim w σ) ≡ _ , (m'' , trim w' σ')

    -- Rewind commutes with map
    rewindCommMap : {F G : Ty -> Ctx -> Set} {Γ Γ' Δ : Ctx}
      (f : {A : Ty} {Γ : Ctx} -> F A Γ -> G A Γ) (m : Γ' ◁ Γ) (σ : Rpl F Γ Δ)
      -> let σ' = Rpl.map f σ in Σ (fst (rewind m σ) ≡ fst (rewind m σ')) λ p ->
        (≡.subst (_◁ Δ) p (fst (snd (rewind m σ))) ≡ fst (snd (rewind m σ')))
          × (≡.subst (Rpl G Γ') p (Rpl.map f (snd (snd (rewind m σ))))
            ≡ snd (snd (rewind m σ')))
