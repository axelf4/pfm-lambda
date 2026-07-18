{-# OPTIONS --without-K --safe #-}

-- Instantiation of Intuitionistic K.
module IK where

open import Data.Product using (Σ; proj₁; proj₂) renaming (_,_ to infix 20 _,_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl; cong; cong₂)
open import Data.Product using (_×_)

open import Context
open import Util using (cong1; subst-application'; Σ×-≡,≡,≡→≡)

_◁_ : Ctx -> Ctx -> Set
Γ ◁ Δ = LFExt (Γ ,🔓) Δ

◁1 : {Γ : Ctx} -> Γ ◁ (Γ ,🔓)
◁1 = nil

open module Rpl = Replacement _◁_ using (Rpl; ·; _,_; lock)

rewind-⊆ : {Γ Γ' Δ : Ctx}
  -> (m : Γ' ◁ Γ) -> (w : Γ ⊆ Δ)
  -> Σ Ctx λ Δ' -> Δ' ◁ Δ × Γ' ⊆ Δ'
rewind-⊆ m (weak w)
  = let Δ' , (m' , w') = rewind-⊆ m w in Δ' , (snoc m' , w')
rewind-⊆ (snoc m) (lift w)
  = let Δ' , (m' , w') = rewind-⊆ m w in Δ' , (snoc m' , w')
rewind-⊆ nil (lift🔓 w) = _ , (nil , w)

rewind : {F : Ty -> Ctx -> Set} {Γ Γ' Δ : Ctx}
  -> (m : Γ' ◁ Γ) -> (σ : Rpl F Γ Δ)
  -> Σ Ctx λ Δ' -> Δ' ◁ Δ × Rpl F Γ' Δ'
rewind nil (lock σ m') = _ , (m' , σ)
rewind (snoc m) (σ , _) = rewind m σ

rewind-⊆-◁1 : {Γ Δ : Ctx} (w : Γ ⊆ Δ) -> rewind-⊆ ◁1 (lift🔓 w) ≡ _ , (◁1 , w)
rewind-⊆-◁1 w = refl
rewind-◁1 : ∀ {F} {Γ Δ Δ' : Ctx} (σ : Rpl F Γ Δ) {m : Δ ◁ Δ'}
  -> rewind ◁1 (lock σ m) ≡ _ , (m , σ)
rewind-◁1 σ = refl

rewind-⊆-pres-● : {Δ Γ Γ' Γ'' : Ctx} (m : Δ ◁ Γ) (w1 : Γ ⊆ Γ') (w2 : Γ' ⊆ Γ'')
  -> let _ , (m' , w1') = rewind-⊆ m w1
         _ , (m'' , w2') = rewind-⊆ m' w2
     in rewind-⊆ m (w1 ● w2) ≡ (_ , (m'' , (w1' ● w2')))
rewind-⊆-pres-● nil w1@(weak _) (weak w2) rewrite rewind-⊆-pres-● nil w1 w2 = refl
rewind-⊆-pres-● m@(snoc _) w1@(weak _) (weak w2) rewrite rewind-⊆-pres-● m w1 w2 = refl
rewind-⊆-pres-● m@(snoc _) w1@(lift _) (weak w2) rewrite rewind-⊆-pres-● m w1 w2  = refl
rewind-⊆-pres-● nil w1@(lift🔓 _) (weak w2) rewrite rewind-⊆-pres-● nil w1 w2 = refl
rewind-⊆-pres-● nil (weak w1) (lift w2) = rewind-⊆-pres-● nil w1 (weak w2)
rewind-⊆-pres-● m@(snoc _) (weak w1) (lift w2) = rewind-⊆-pres-● m w1 (weak w2)
rewind-⊆-pres-● (snoc m) (lift w1) (lift w2) = rewind-⊆-pres-● m w1 (weak w2)
rewind-⊆-pres-● nil (lift🔓 w1) (lift🔓 w2) = refl

rewindPres-∙ : ∀ {F G} {Δ Γ Γ' Γ'' : Ctx} (m : Δ ◁ Γ) (σ : Rpl F Γ Γ') (δ : Rpl G Γ' Γ'')
  {apply : {A : Ty} {Γ Δ : Ctx} -> Rpl G Γ Δ -> F A Γ -> G A Δ}
  -> let open Rpl.Composition F G rewind apply using (_∙_)
         _ , (m' , σ') = rewind m σ
         _ , (m'' , δ') = rewind m' δ
     in rewind m (σ ∙ δ) ≡ (_ , (m'' , (σ' ∙ δ')))
rewindPres-∙ (snoc m) (σ , _) δ = rewindPres-∙ m σ δ
rewindPres-∙ nil (lock σ _) δ = refl

rewind-⊆-presId : {Γ Δ : Ctx} (m : Δ ◁ Γ) -> rewind-⊆ m ⊆.id ≡ Δ , (m , ⊆.id)
rewind-⊆-presId nil = refl
rewind-⊆-presId (snoc m) rewrite rewind-⊆-presId m = refl

rewindPresId : ∀ {F} {Γ Δ : Ctx} -> (m : Δ ◁ Γ)
  {wkF : {A : Ty} {Γ Γ' : Ctx} -> Γ ⊆ Γ' -> F A Γ -> F A Γ'}
  {head : {A : Ty} {Γ : Ctx} -> F A (Γ , A)}
  (let open Rpl.Properties F ◁1 rewind-⊆ wkF head using (id))
  (wkFId : {A : Ty} {Γ : Ctx} (x : F A Γ) -> wkF ⊆.id x ≡ x)
    -> rewind m id ≡ Δ , (m , id)
rewindPresId nil _ = refl
rewindPresId {F} (snoc m) {wkF} {head} wkFId = let
    x1 , (x2 , x3) = rewindDrop m id
    y1 , y2 = Σ-≡,≡↔≡ .Inverse.from (rewindPresId m {wkF} {head} wkFId)
    m≡m' = ≡.trans (substTrans x1 y1 x2) (≡.trans (subst-application' snoc y1)
      (cong snoc (≡.trans (subst-application' proj₁ y1) (cong proj₁ y2))))
    σ≡σ' = ≡.trans (substTrans x1 y1 x3) (≡.trans (subst-application' proj₂ y1) (cong proj₂ y2))
  in Σ×-≡,≡,≡→≡ (≡.trans x1 y1 , (m≡m' , σ≡σ'))
  where
    open import Function using (Inverse)
    open import Data.Product.Properties using (Σ-≡,≡↔≡)
    open Rpl.Properties F ◁1 rewind-⊆ wkF head using (wk; shift; id)

    wkId : {Γ Δ : Ctx} {σ : Rpl F Γ Δ} -> wk ⊆.id σ ≡ σ
    wkId {σ = ·} = refl
    wkId {σ = σ , x} = cong₂ _,_ wkId (wkFId x)
    wkId {σ = lock σ m} rewrite rewind-⊆-presId m = cong1 lock wkId

    rewindDrop : ∀ {Γ Γ' Δ A} -> (m : Δ ◁ Γ) (σ : Rpl F Γ Γ')
      -> let Δ'2 , (m'2 , σ'2) = rewind m (shift {A} σ)
             Δ'1 , (m'1 , σ'1) = rewind m σ
         in Σ (Δ'2 ≡ Δ'1) λ p ->
           ≡.subst (_◁ _) p m'2 ≡ snoc m'1 × ≡.subst (Rpl F Δ) p σ'2 ≡ σ'1
    rewindDrop nil (lock σ m) rewrite rewind-⊆-presId m = refl , (refl , wkId)
    rewindDrop (snoc m) (σ , _) = rewindDrop m σ

    substTrans : {A : Set} {P : A -> Set} {x y z : A}
      (x≡y : x ≡ y) (y≡z : y ≡ z) {p : P x} {q : P y}
      -> ≡.subst P x≡y p ≡ q
      -> ≡.subst P (≡.trans x≡y y≡z) p ≡ ≡.subst P y≡z q
    substTrans refl refl refl = refl

rewindWk : ∀ {F} {Γ Γ' Γ'' Δ : Ctx} (m : Δ ◁ Γ) (σ : Rpl F Γ Γ') (w : Γ' ⊆ Γ'')
  {wkF : {A : Ty} {Γ Γ' : Ctx} -> Γ ⊆ Γ' -> F A Γ -> F A Γ'}
  {head : {A : Ty} {Γ : Ctx} -> F A (Γ , A)}
  -> let open Rpl.Properties F ◁1 rewind-⊆ wkF head using (wk)
         _ , (m' , σ') = rewind m σ
         _ , (m'' , w') = rewind-⊆ m' w
     in rewind m (wk w σ) ≡ _ , (m'' , wk w' σ')
rewindWk nil (lock s x) w = refl
rewindWk (snoc m) (s , x) w {wkF} {head} = rewindWk m s w {wkF} {head}

rewindTrim : ∀ {F} {Γ Γ' Γ'' Δ : Ctx} (m : Δ ◁ Γ) (w : Γ ⊆ Γ') (σ : Rpl F Γ' Γ'')
  {wkF : {A : Ty} {Γ Γ' : Ctx} -> Γ ⊆ Γ' -> F A Γ -> F A Γ'}
  {head : {A : Ty} {Γ : Ctx} -> F A (Γ , A)}
  -> let open Rpl.Properties F ◁1 rewind-⊆ wkF head using (trim)
         _ , (m' , w') = rewind-⊆ m w
         _ , (m'' , σ') = rewind m' σ
     in rewind m (trim w σ) ≡ _ , (m'' , trim w' σ')
rewindTrim nil (weak w) (s , x) {wkF} {head} = rewindTrim nil w s {wkF} {head}
rewindTrim nil (lift🔓 w) (lock s x) = refl
rewindTrim m@(snoc _) (weak w) (s , x) {wkF} {head} = rewindTrim m w s {wkF} {head}
rewindTrim (snoc m) (lift w) (s , x) {wkF} {head} = rewindTrim m w s {wkF} {head}

rewindCommMap : {F G : Ty -> Ctx -> Set} {Γ Γ' Δ : Ctx}
  (f : {A : Ty} {Γ : Ctx} -> F A Γ -> G A Γ) (m : Γ' ◁ Γ) (σ : Rpl F Γ Δ)
  -> let σ' = Rpl.map f σ in Σ (proj₁ (rewind m σ) ≡ proj₁ (rewind m σ')) λ p ->
    (≡.subst (_◁ Δ) p (proj₁ (proj₂ (rewind m σ))) ≡ proj₁ (proj₂ (rewind m σ')))
      × (≡.subst (Rpl G Γ') p (Rpl.map f (proj₂ (proj₂ (rewind m σ))))
        ≡ proj₂ (proj₂ (rewind m σ')))
rewindCommMap f nil (lock s m) = refl , (refl , refl)
rewindCommMap f (snoc m) (s , _) = rewindCommMap f m s
