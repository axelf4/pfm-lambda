{-# OPTIONS --without-K --safe #-}

-- Instantiation of Intuitionistic S4.
module IS4 where

open import Agda.Builtin.Sigma using (Σ; fst; snd) renaming (_,_ to infix 20 _,_)
open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)
open import Function using (Inverse)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl; cong; cong₂)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_)
open import Data.Product.Properties using (Σ-≡,≡↔≡)

open import Context
open import Util using (cong1; substTrans; subst-application'; Σ×-≡,≡,≡→≡)

data _◁_ (Γ : Ctx) : Ctx -> Set where
  refl : Γ ◁ Γ
  ext : {Δ : Ctx} -> Ext ⊤ (Γ ,🔓) Δ -> Γ ◁ Δ

module ◁ where
  trans : {Γ Γ' Γ'' : Ctx} -> Γ ◁ Γ' -> Γ' ◁ Γ'' -> Γ ◁ Γ''
  trans m1 refl = m1
  {-# CATCHALL #-}
  trans refl m2 = m2
  trans (ext m1) (ext m2) = ext (extConcat (snoc🔓 tt m1) m2)

  transRefl : {Γ Δ : Ctx} (m : Γ ◁ Δ) -> trans refl m ≡ m
  transRefl refl = refl
  transRefl (ext m) = refl

  assoc : {Γ Γ' Γ'' Γ''' : Ctx} (m1 : Γ ◁ Γ') (m2 : Γ' ◁ Γ'') (m3 : Γ'' ◁ Γ''')
    -> trans (trans m1 m2) m3 ≡ trans m1 (trans m2 m3)
  assoc m1 m2 refl = refl
  assoc refl m2 m3@(ext _) = ≡.trans
    (cong (λ x -> trans x m3) (transRefl m2))
    (≡.sym (transRefl (trans m2 m3)))
  assoc (ext m1) refl (ext m3) = refl
  assoc (ext m1) (ext m2) (ext m3) = cong ext (extAssoc (snoc🔓 tt m1) (snoc🔓 tt m2) m3)

◁1 : {Γ : Ctx} -> Γ ◁ (Γ ,🔓)
◁1 = ext nil

open module Rpl = Replacement _◁_ using (Rpl; ·; _,_; lock)

rewindExt-⊆ : {Γ Γ' Δ : Ctx} -> Ext ⊤ (Γ' ,🔓) Γ -> Γ ⊆ Δ
  -> Σ Ctx λ Δ' -> Ext ⊤ (Δ' ,🔓) Δ × Γ' ⊆ Δ'
rewindExt-⊆ m (weak w) = let Δ' , (m , w') = rewindExt-⊆ m w in Δ' , (snoc m , w')
rewindExt-⊆ (snoc m) (lift w) = let Δ' , (m , w') = rewindExt-⊆ m w in Δ' , (snoc m , w')
rewindExt-⊆ nil (lift🔓 w) = _ , (nil , w)
rewindExt-⊆ (snoc🔓 l m) (lift🔓 w) = let Δ' , (m , w') = rewindExt-⊆ m w in Δ' , (snoc🔓 l m , w')

rewind-⊆ : {Γ Γ' Δ : Ctx}
  -> (m : Γ' ◁ Γ) -> (w : Γ ⊆ Δ)
  -> Σ Ctx λ Δ' -> Δ' ◁ Δ × Γ' ⊆ Δ'
rewind-⊆ refl w = _ , (refl , w)
rewind-⊆ {_} {Γ'} (ext m) w = let Δ' , (m' , w') = rewindExt-⊆ m w in Δ' , (ext m' , w')

rewind : {F : Ty -> Ctx -> Set} {Γ Γ' Δ : Ctx}
  -> (m : Γ' ◁ Γ) -> (σ : Rpl F Γ Δ)
  -> Σ Ctx λ Δ' -> Δ' ◁ Δ × Rpl F Γ' Δ'
rewind refl σ = _ , (refl , σ)
rewind (ext (snoc m)) (σ , x) = rewind (ext m) σ
rewind (ext nil) (lock σ m) = _ , (m , σ)
rewind (ext (snoc🔓 _ m)) (lock σ m2)
  = let Δ' , (m' , σ') = rewind (ext m) σ in Δ' , (◁.trans m' m2 , σ')

rewind-⊆-◁1 : {Γ Δ : Ctx} (w : Γ ⊆ Δ) -> rewind-⊆ ◁1 (lift🔓 w) ≡ _ , (◁1 , w)
rewind-⊆-◁1 w = refl
rewind-◁1 : ∀ {F} {Γ Δ Δ' : Ctx} (σ : Rpl F Γ Δ) {m : Δ ◁ Δ'}
  -> rewind ◁1 (lock σ m) ≡ _ , (m , σ)
rewind-◁1 σ = refl

rewindExt-⊆-pres-● : {Δ Γ Γ' Γ'' : Ctx} (m : Ext ⊤ (Δ ,🔓) Γ) (w1 : Γ ⊆ Γ') (w2 : Γ' ⊆ Γ'')
  -> let _ , (m' , w1') = rewindExt-⊆ m w1
         _ , (m'' , w2') = rewindExt-⊆ m' w2
     in rewindExt-⊆ m (w1 ● w2) ≡ (_ , (m'' , (w1' ● w2')))
rewindExt-⊆-pres-● nil w1@(weak _) (weak w2) rewrite rewindExt-⊆-pres-● nil w1 w2 = refl
rewindExt-⊆-pres-● m@(snoc _) w1@(weak _) (weak w2) rewrite rewindExt-⊆-pres-● m w1 w2 = refl
rewindExt-⊆-pres-● m@(snoc _) w1@(lift _) (weak w2) rewrite rewindExt-⊆-pres-● m w1 w2 = refl
rewindExt-⊆-pres-● m@(snoc🔓 _ _) w1@(weak _) (weak w2) rewrite rewindExt-⊆-pres-● m w1 w2 = refl
rewindExt-⊆-pres-● nil w1@(lift🔓 _) (weak w2) rewrite rewindExt-⊆-pres-● nil w1 w2 = refl
rewindExt-⊆-pres-● m@(snoc🔓 _ _) w1@(lift🔓 _) (weak w2) rewrite rewindExt-⊆-pres-● m w1 w2 = refl
rewindExt-⊆-pres-● nil (weak w1) (lift w2) = rewindExt-⊆-pres-● nil w1 (weak w2)
rewindExt-⊆-pres-● m@(snoc _) (weak w1) (lift w2) = rewindExt-⊆-pres-● m w1 (weak w2)
rewindExt-⊆-pres-● m@(snoc🔓 _ _) (weak w1) (lift w2) = rewindExt-⊆-pres-● m w1 (weak w2)
rewindExt-⊆-pres-● (snoc m) (lift w1) (lift w2) = rewindExt-⊆-pres-● m w1 (weak w2)
rewindExt-⊆-pres-● nil (lift🔓 w1) (lift🔓 w2) = refl
rewindExt-⊆-pres-● (snoc🔓 _ m) (lift🔓 w1) (lift🔓 w2) rewrite rewindExt-⊆-pres-● m w1 w2 = refl

rewind-⊆-pres-● : {Δ Γ Γ' Γ'' : Ctx} (m : Δ ◁ Γ) (w1 : Γ ⊆ Γ') (w2 : Γ' ⊆ Γ'')
  -> let _ , (m' , w1') = rewind-⊆ m w1
         _ , (m'' , w2') = rewind-⊆ m' w2
     in rewind-⊆ m (w1 ● w2) ≡ (_ , (m'' , (w1' ● w2')))
rewind-⊆-pres-● refl w1 w2 = refl
rewind-⊆-pres-● (ext m) w1 w2 rewrite rewindExt-⊆-pres-● m w1 w2 = refl

private
  rewind-⊆-presTransAux : ∀ {Γ Δ Ξ Δ'1 Δ'2 : Ctx} {m1 m2 w1 w2}
    (f : {Γ : Ctx} -> Ext ⊤ (Γ ,🔓) Δ -> Ext ⊤ (Γ ,🔓) Ξ)
    -> (Σ (Δ'1 ≡ Δ'2) λ p
      -> ≡.subst (_◁ Δ) p (ext m1) ≡ ext m2 × ≡.subst (Γ ⊆_) p w1 ≡ w2)
    -> (Σ (Δ'1 ≡ Δ'2) λ p
      -> ≡.subst (_◁ Ξ) p (ext (f m1)) ≡ ext (f m2) × ≡.subst (Γ ⊆_) p w1 ≡ w2)
  rewind-⊆-presTransAux {w1 = w1} f (p , (q , s)) = p
    , (≡.trans
      (subst-application' (λ x -> ext (f x)) p)
      (cong (λ x -> ext (f x)) (ext-inj (≡.trans (≡.sym (subst-application' ext p)) q)))
      , s)
    where
      ext-inj : ∀ {Γ Δ} {x y : Ext ⊤ (Γ ,🔓) Δ} -> ext x ≡ ext y -> x ≡ y
      ext-inj refl = refl

  rewind-⊆-presTrans : {Γ Γ' Γ'' Δ : Ctx} (m1 : Γ ◁ Γ') (m2 : Γ' ◁ Γ'') (w : Γ'' ⊆ Δ)
    -> let _ , (m2' , w') = rewind-⊆ m2 w
           Δ'1 , (m'1 , w'1) = rewind-⊆ m1 w'
           Δ'2 , x@(m'2 , w'2) = rewind-⊆ (◁.trans m1 m2) w
       in Σ (Δ'1 ≡ Δ'2) λ p
         -> (≡.subst (_◁ Δ) p (◁.trans m'1 m2') ≡ m'2) × (≡.subst (Γ ⊆_) p w'1 ≡ w'2)
  rewind-⊆-presTrans m1 refl w = refl , (refl , refl)
  rewind-⊆-presTrans refl (ext m2) w = refl , (refl , refl)
  rewind-⊆-presTrans m1@(ext _) m2@(ext nil) (weak w)
    = rewind-⊆-presTransAux snoc (rewind-⊆-presTrans m1 m2 w)
  rewind-⊆-presTrans m1@(ext _) (ext nil) (lift🔓 w) = refl , (refl , refl)
  rewind-⊆-presTrans m1@(ext _) m2@(ext (snoc _)) (weak w)
    = rewind-⊆-presTransAux snoc (rewind-⊆-presTrans m1 m2 w)
  rewind-⊆-presTrans m1@(ext _) (ext (snoc m2)) (lift w)
    = rewind-⊆-presTransAux snoc (rewind-⊆-presTrans m1 (ext m2) w)
  rewind-⊆-presTrans m1@(ext _) m2@(ext (snoc🔓 _ _)) (weak w)
    = rewind-⊆-presTransAux snoc (rewind-⊆-presTrans m1 m2 w)
  rewind-⊆-presTrans m1@(ext _) (ext (snoc🔓 l m2)) (lift🔓 w)
    = rewind-⊆-presTransAux (snoc🔓 l) (rewind-⊆-presTrans m1 (ext m2) w)

  rewindPresTrans : ∀ {F} {Γ Γ' Γ'' Δ : Ctx} (m1 : Γ ◁ Γ') (m2 : Γ' ◁ Γ'') (σ : Rpl F Γ'' Δ)
    -> let _ , (m2' , σ') = rewind m2 σ
           Δ'1 , (m'1 , σ'1) = rewind m1 σ'
           Δ'2 , x@(_m'2 , _σ'2) = rewind (◁.trans m1 m2) σ
       in Σ (Δ'1 ≡ Δ'2) λ p
         -> ≡.subst (λ Δ' -> (Δ' ◁ Δ) × Rpl F Γ Δ') p (◁.trans m'1 m2' , σ'1) ≡ x
  rewindPresTrans m1 refl σ = refl , refl
  rewindPresTrans refl (ext m2) (lock σ m)
    rewrite ◁.transRefl (fst (snd (rewind (ext m2) (lock σ m)))) = refl , refl
  rewindPresTrans m1@refl (ext (snoc m2)) (σ , _) = rewindPresTrans m1 (ext m2) σ
  rewindPresTrans (ext m1) (ext nil) (lock σ m) = refl , refl
  rewindPresTrans {F} {Γ} {Δ = Δ} m1@(ext m3) (ext (snoc🔓 _ m2)) (lock σ m) = let
    x1 , x2 = rewindPresTrans m1 (ext m2) σ
    in x1 , ≡.trans
      (cong (λ x -> ≡.subst (λ Δ' → (Δ' ◁ Δ) × Rpl F Γ Δ') x1 (x , _))
        (≡.sym (◁.assoc _ _ m)))
      (≡.trans
        (subst-application' {P = λ Δ' → (Δ' ◁ _) × Rpl F Γ Δ'} (λ (x , y) -> ◁.trans x m , y) x1)
        (cong (λ (x , y) -> ◁.trans x m , y) x2))
  rewindPresTrans m1@(ext _) (ext (snoc m2)) (σ , _) = rewindPresTrans m1 (ext m2) σ

rewindPres-∙ : ∀ {F G} {Δ Γ Γ' Γ'' : Ctx} (m : Δ ◁ Γ) (σ : Rpl F Γ Γ') (δ : Rpl G Γ' Γ'')
  {apply : {A : Ty} {Γ Δ : Ctx} -> Rpl G Γ Δ -> F A Γ -> G A Δ}
  -> let open Rpl.Composition F G rewind apply using (_∙_)
         _ , (m' , σ') = rewind m σ
         _ , (m'' , δ') = rewind m' δ
     in rewind m (σ ∙ δ) ≡ (_ , (m'' , (σ' ∙ δ')))
rewindPres-∙ refl s1 s2 = refl
rewindPres-∙ (ext (snoc m)) (s1 , _) s2 = rewindPres-∙ (ext m) s1 s2
rewindPres-∙ (ext nil) (lock s1 _) s2 = refl
rewindPres-∙ {F} {G} {Δ} (ext (snoc🔓 _ m)) (lock s1 m2) s2 {apply}
  rewrite rewindPres-∙ (ext m) s1 (snd (snd (rewind m2 s2))) {apply}
  = let
      open Rpl.Composition F G rewind apply using (_∙_)
      x1 , x2 = rewindPresTrans (fst (snd (rewind (ext m) s1))) m2 s2
    in Σ×-≡,≡,≡→≡ (x1 , (≡.trans (subst-application' fst x1) (cong fst x2)
      , ≡.trans
        (subst-application' (λ x -> snd (snd (rewind (ext m) s1)) ∙ snd x) x1)
        (cong (λ x -> snd (snd (rewind (ext m) s1)) ∙ snd x) x2)))

rewindExt-⊆-presId : {Γ Δ : Ctx} (m : Ext ⊤ (Δ ,🔓) Γ) -> rewindExt-⊆ m ⊆.id ≡ Δ , (m , ⊆.id)
rewindExt-⊆-presId nil = refl
rewindExt-⊆-presId (snoc m) rewrite rewindExt-⊆-presId m = refl
rewindExt-⊆-presId (snoc🔓 _ m) rewrite rewindExt-⊆-presId m = refl

rewind-⊆-presId : {Γ Δ : Ctx} (m : Δ ◁ Γ) -> rewind-⊆ m ⊆.id ≡ Δ , (m , ⊆.id)
rewind-⊆-presId refl = refl
rewind-⊆-presId (ext m) rewrite rewindExt-⊆-presId m = refl

rewindWk : ∀ {F} {Γ Γ' Γ'' Δ : Ctx} (m : Δ ◁ Γ) (σ : Rpl F Γ Γ') (w : Γ' ⊆ Γ'')
  {wkF : {A : Ty} {Γ Γ' : Ctx} -> Γ ⊆ Γ' -> F A Γ -> F A Γ'}
  {head : {A : Ty} {Γ : Ctx} -> F A (Γ , A)}
  -> let open Rpl.Properties F ◁1 rewind-⊆ wkF head using (wk)
         _ , (m' , σ') = rewind m σ
         _ , (m'' , w') = rewind-⊆ m' w
     in rewind m (wk w σ) ≡ _ , (m'' , wk w' σ')
rewindWk refl s w = refl
rewindWk (ext nil) (lock σ _) w = refl
rewindWk (ext (snoc m)) (s , _) w {wkF} {head} = rewindWk (ext m) s w {wkF} {head}
rewindWk {F} {Γ} {Γ'} {Γ''} {Δ} (ext (snoc🔓 _ m)) (lock s m2) w {wkF} {head} = let
    open Rpl.Properties F ◁1 rewind-⊆ wkF head using (wk)
    ih = rewindWk (ext m) s (snd (snd (rewind-⊆ m2 w))) {wkF} {head}
    y1 , y2 = Σ-≡,≡↔≡ .Inverse.from ih
    x1 , (x2 , x3) = rewind-⊆-presTrans (fst (snd (rewind (ext m) s))) m2 w
  in
    Σ×-≡,≡,≡→≡ (≡.trans y1 x1 , (≡.trans (substTrans y1 x1
      (≡.trans
        (subst-application' (λ x -> ◁.trans (fst x) (fst (snd (rewind-⊆ m2 w)))) y1)
        (cong (λ x -> ◁.trans (fst x) (fst (snd (rewind-⊆ m2 w)))) y2)))
      x2
      , ≡.trans (substTrans y1 x1 (≡.trans (subst-application' snd y1) (cong snd y2)))
        (≡.trans (subst-application' (λ x -> wk x (snd (snd (rewind (ext m) s)))) x1)
          (cong1 wk x3))))

rewindPresId : ∀ {F} {Γ Δ : Ctx} -> (m : Δ ◁ Γ)
  {wkF : {A : Ty} {Γ Γ' : Ctx} -> Γ ⊆ Γ' -> F A Γ -> F A Γ'}
  {head : {A : Ty} {Γ : Ctx} -> F A (Γ , A)}
  (let open Rpl.Properties F ◁1 rewind-⊆ wkF head using (id))
  (wkFId : {A : Ty} {Γ : Ctx} (x : F A Γ) -> wkF ⊆.id x ≡ x)
    -> rewind m id ≡ Δ , (m , id)
rewindPresId refl _ = refl
rewindPresId (ext nil) _ = refl
rewindPresId {F} {Γ , A} {Δ} (ext (snoc m)) {wkF} {head} wkFId =
  ≡.trans
    (rewindWk (ext m) id (weak ⊆.id) {wkF} {head})
    (helper (rewind (ext m) id) (rewindPresId (ext m) {wkF} {head} wkFId))
  where
    open Rpl.Properties F ◁1 rewind-⊆ wkF head using (wk; id)

    wkId : {Γ Δ : Ctx} {σ : Rpl F Γ Δ} -> wk ⊆.id σ ≡ σ
    wkId {σ = ·} = refl
    wkId {σ = σ , x} = cong₂ _,_ wkId (wkFId x)
    wkId {σ = lock σ m} rewrite rewind-⊆-presId m = cong1 lock wkId

    rewind-⊆-weak-id : rewind-⊆ (ext m) (weak ⊆.id) ≡ Δ , (ext (snoc m) , ⊆.id)
    rewind-⊆-weak-id rewrite rewindExt-⊆-presId m = refl

    helper : (r : Σ Ctx λ Δ' → (Δ' ◁ Γ) × Rpl F Δ Δ')
      -> r ≡ Δ , (ext m , id)
      -> (let _ , (m' , σ') = r
              _ , (m'' , w') = rewind-⊆ m' (weak ⊆.id)
          in _ , (m'' , wk w' σ'))
         ≡ Δ , (ext (snoc m) , id)
    helper _ refl = ≡.trans
      (cong (λ (_ , (m'' , w')) → _ , (m'' , wk w' id)) rewind-⊆-weak-id)
      (cong (λ σ → Δ , (ext (snoc m) , σ)) wkId)
rewindPresId (ext (snoc🔓 _ m)) {wkF} {head} wkFId
  rewrite rewindPresId (ext m) {wkF} {head} wkFId = refl

rewindTrim : ∀ {F} {Γ Γ' Γ'' Δ : Ctx} (m : Δ ◁ Γ) (w : Γ ⊆ Γ') (σ : Rpl F Γ' Γ'')
  {wkF : {A : Ty} {Γ Γ' : Ctx} -> Γ ⊆ Γ' -> F A Γ -> F A Γ'}
  {head : {A : Ty} {Γ : Ctx} -> F A (Γ , A)}
  -> let open Rpl.Properties F ◁1 rewind-⊆ wkF head using (trim)
         _ , (m' , w') = rewind-⊆ m w
         _ , (m'' , σ') = rewind m' σ
     in rewind m (trim w σ) ≡ _ , (m'' , trim w' σ')
rewindTrim refl w s = refl
rewindTrim (ext nil) (weak w) (s , _) {wkF} {head} = rewindTrim (ext nil) w s {wkF} {head}
rewindTrim (ext nil) (lift🔓 w) (lock s _) = refl
rewindTrim m@(ext (snoc _)) (weak w) (s , _) {wkF} {head} = rewindTrim m w s {wkF} {head}
rewindTrim (ext (snoc m)) (lift w) (s , _) {wkF} {head} = rewindTrim (ext m) w s {wkF} {head}
rewindTrim m@(ext (snoc🔓 _ _)) (weak w) (s , _) {wkF} {head} = rewindTrim m w s {wkF} {head}
rewindTrim (ext (snoc🔓 _ m)) (lift🔓 w) (lock s _) {wkF} {head}
  rewrite rewindTrim (ext m) w s {wkF} {head} = refl

rewindCommMap : {F G : Ty -> Ctx -> Set} {Γ Γ' Δ : Ctx}
  (f : {A : Ty} {Γ : Ctx} -> F A Γ -> G A Γ) (m : Γ' ◁ Γ) (σ : Rpl F Γ Δ)
  -> let σ' = Rpl.map f σ in Σ (fst (rewind m σ) ≡ fst (rewind m σ')) λ p ->
    (≡.subst (_◁ Δ) p (fst (snd (rewind m σ))) ≡ fst (snd (rewind m σ')))
      × (≡.subst (Rpl G Γ') p (Rpl.map f (snd (snd (rewind m σ))))
        ≡ snd (snd (rewind m σ')))
rewindCommMap f refl σ = refl , (refl , refl)
rewindCommMap f (ext (snoc m)) (σ , _) = rewindCommMap f (ext m) σ
rewindCommMap f (ext nil) (lock σ m) = refl , (refl , refl)
rewindCommMap f (ext (snoc🔓 _ m)) (lock σ m2) = let
  Ξ≡Ξ' , (m≡m' , δ≡δ') = rewindCommMap f (ext m) σ
  in Ξ≡Ξ' , (≡.trans
    (subst-application' (λ x -> ◁.trans x m2) Ξ≡Ξ') (cong (λ x -> ◁.trans x m2) m≡m')
    , δ≡δ')
