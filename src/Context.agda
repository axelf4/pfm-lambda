{-# OPTIONS --without-K --safe #-}

module Context where

open import Data.Product using (Σ) renaming (_,_ to infix 20 _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl; cong; cong₂)
open import Data.Empty using (⊥)
open import Data.Product using (_×_)

open import Util using (cong1)

data Ty : Set where
  ι : Ty
  _⟶_ : Ty -> Ty -> Ty
  □_ : Ty -> Ty

infixr 30 _⟶_
infix 30 □_

_≡Ty?_ : DecidableEquality Ty
ι ≡Ty? ι = yes refl
ι ≡Ty? (_ ⟶ _) = no λ ()
ι ≡Ty? (□ _) = no λ ()
(_ ⟶ _) ≡Ty? ι = no λ ()
(A1 ⟶ B1) ≡Ty? (A2 ⟶ B2) with A1 ≡Ty? A2 | B1 ≡Ty? B2
... | yes A1≡A2 | yes B1≡B2 = yes (cong₂ _⟶_ A1≡A2 B1≡B2)
... | yes A1≡A2 | no ¬B1≡B2 = no (λ { refl → ¬B1≡B2 refl })
... | no ¬A1≡A2 | q = no (λ { refl → ¬A1≡A2 refl })
(_ ⟶ _) ≡Ty? (□ _) = no λ ()
(□ _) ≡Ty? ι = no λ ()
(□ _) ≡Ty? (_ ⟶ _) = no λ ()
(□ A) ≡Ty? (□ B) with A ≡Ty? B
... | yes A≡B = yes (cong □_ A≡B)
... | no ¬A≡B = no λ { refl → ¬A≡B refl }

-- Typing context
data Ctx : Set where
  · : Ctx
  _,_ : (Γ : Ctx) -> (A : Ty) -> Ctx
  _,🔓 : (Γ : Ctx) -> Ctx

_≡Ctx?_ : DecidableEquality Ctx
· ≡Ctx? · = yes refl
· ≡Ctx? (_ , _) = no λ ()
· ≡Ctx? (_ ,🔓) = no λ ()
(_ , _) ≡Ctx? · = no λ ()
(Γ , A) ≡Ctx? (Δ , B) with Γ ≡Ctx? Δ | A ≡Ty? B
... | yes Γ≡Δ | yes A≡B = yes (cong₂ _,_ Γ≡Δ A≡B)
... | yes Γ≡Δ | no ¬A≡B = no λ { refl → ¬A≡B refl }
... | no ¬Γ≡Δ | _ = no λ { refl → ¬Γ≡Δ refl }
(G , A) ≡Ctx? (C ,🔓) = no λ ()
(_ ,🔓) ≡Ctx? · = no λ ()
(_ ,🔓) ≡Ctx? (_ , _) = no λ ()
(Γ ,🔓) ≡Ctx? (Δ ,🔓) with Γ ≡Ctx? Δ
... | yes Γ≡Δ = yes (cong _,🔓 Γ≡Δ)
... | no ¬Γ≡Δ = no λ { refl → ¬Γ≡Δ refl }

-- The type A can be found in the context at index n.
data _∈_ (A : Ty) : Ctx -> Set where
  zero : {Γ : Ctx} -> A ∈ (Γ , A)
  suc : {Γ : Ctx} {B : Ty} -> A ∈ Γ -> A ∈ (Γ , B)

-- Relation between contexts Γ and Γ' signifying that it is possible
-- to extend Γ to Γ', maybe adding any locks.
data Ext (🔓? : Set) (Γ : Ctx) : Ctx -> Set where
  nil : Ext 🔓? Γ Γ
  snoc : {Γ' : Ctx} {A : Ty} -> Ext 🔓? Γ Γ' -> Ext 🔓? Γ (Γ' , A)
  snoc🔓 : 🔓? -> {Γ' : Ctx} -> Ext 🔓? Γ Γ' -> Ext 🔓? Γ (Γ' ,🔓)

LFExt = Ext ⊥ -- Lock-free context extension

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

-- Composition of weakenings (and transitivity proof)
_●_ : {Γ Γ' Γ'' : Ctx} -> Γ ⊆ Γ' -> Γ' ⊆ Γ'' -> Γ ⊆ Γ''
x ● base = x
x ● (weak y) = weak (x ● y)
(weak x) ● (lift y) = weak (x ● y)
(lift x) ● (lift y) = lift (x ● y)
(lift🔓 x) ● (lift🔓 y) = lift🔓 (x ● y)

●-assoc : {Γ1 Γ2 Γ3 Γ4 : Ctx} (w1 : Γ1 ⊆ Γ2) (w2 : Γ2 ⊆ Γ3) (w3 : Γ3 ⊆ Γ4)
  -> (w1 ● w2) ● w3 ≡ w1 ● (w2 ● w3)
●-assoc w1 w2 base = refl
●-assoc w1 w2 (weak w3) = cong weak (●-assoc w1 w2 w3)
●-assoc w1 (weak w2) (lift w3) = cong weak (●-assoc w1 w2 w3)
●-assoc (weak w1) (lift w2) (lift w3) = cong weak (●-assoc w1 w2 w3)
●-assoc (lift w1) (lift w2) (lift w3) = cong lift (●-assoc w1 w2 w3)
●-assoc (lift🔓 w1) (lift🔓 w2) (lift🔓 w3) = cong lift🔓 (●-assoc w1 w2 w3)

module ⊆ where
  id : {Γ : Ctx} -> Γ ⊆ Γ
  id {·} = base
  id {Γ , A} = lift id
  id {Γ ,🔓} = lift🔓 id

  idl : {Γ Δ : Ctx} {w : Γ ⊆ Δ} -> id ● w ≡ w
  idl {w = base} = refl
  idl {w = weak w} = cong weak idl
  idl {w = lift w} = cong lift idl
  idl {w = lift🔓 w} = cong lift🔓 idl

  idr : {Γ Δ : Ctx} {w : Γ ⊆ Δ} -> w ● id ≡ w
  idr {w = base} = refl
  idr {w = weak w} = cong weak idr
  idr {w = lift w} = cong lift idr
  idr {w = lift🔓 w} = cong lift🔓 idr

wkVar : {A : Ty} {Γ Δ : Ctx} -> Γ ⊆ Δ -> A ∈ Γ -> A ∈ Δ
wkVar base x = x
wkVar (weak w) x = suc (wkVar w x)
wkVar (lift w) zero = zero
wkVar (lift w) (suc x) = suc (wkVar w x)

wkVarId : {A : Ty} {Γ : Ctx} -> (x : A ∈ Γ) -> wkVar ⊆.id x ≡ x
wkVarId zero = refl
wkVarId (suc x) = cong suc (wkVarId x)

wkVarPres-● : {Γ Δ Ξ : Ctx} {A : Ty} -> (w1 : Γ ⊆ Δ) (w2 : Δ ⊆ Ξ) (x : A ∈ Γ)
  -> wkVar (w1 ● w2) x ≡ wkVar w2 (wkVar w1 x)
wkVarPres-● w1 (weak w2) x = cong suc (wkVarPres-● w1 w2 x)
wkVarPres-● base base x = refl
wkVarPres-● (weak w1) (lift w2) x = cong suc (wkVarPres-● w1 w2 x)
wkVarPres-● (lift w1) (lift w2) zero = refl
wkVarPres-● (lift w1) (lift w2) (suc x) = cong suc (wkVarPres-● w1 w2 x)
wkVarPres-● (lift🔓 w1) (lift🔓 w2) ()

module Replacement (_◁_ : Ctx -> Ctx -> Set) where
  -- For every item in context Γ there is a replacement value in context Δ.
  data Rpl (F : Ty -> Ctx -> Set) : Ctx -> Ctx -> Set where
    · : {Δ : Ctx} -> Rpl F · Δ
    _,_ : {Γ Δ : Ctx} {A : Ty} -> Rpl F Γ Δ -> F A Δ -> Rpl F (Γ , A) Δ
    lock : {Γ Δ Δ' : Ctx} -> Rpl F Γ Δ -> Δ ◁ Δ' -> Rpl F (Γ ,🔓) Δ'

  map : {F G : Ty -> Ctx -> Set} -> ({A : Ty} {Γ : Ctx} -> F A Γ -> G A Γ)
    -> {Γ Δ : Ctx} -> Rpl F Γ Δ -> Rpl G Γ Δ
  map f · = ·
  map f (σ , x) = map f σ , f x
  map f (lock σ m) = lock (map f σ) m

  module Properties
    (F : Ty -> Ctx -> Set)
    (◁1 : {Γ : Ctx} -> Γ ◁ (Γ ,🔓))
    (rewind-⊆ : {Γ Γ' Δ : Ctx} -> (m : Γ' ◁ Γ) -> Γ ⊆ Δ
      -> Σ Ctx λ Δ' -> Δ' ◁ Δ × Γ' ⊆ Δ')
    (wkF : {A : Ty} {Γ Γ' : Ctx} -> Γ ⊆ Γ' -> F A Γ -> F A Γ')
    (head : {A : Ty} {Γ : Ctx} -> F A (Γ , A))
    where

    -- Looking up a variable in a replacement
    replaceVar : {Γ Δ : Ctx} {A : Ty} -> Rpl F Γ Δ -> A ∈ Γ → F A Δ
    replaceVar (_ , x) zero = x
    replaceVar (σ , _) (suc x) = replaceVar σ x

    -- Composition of substitution and weakening
    wk : {Γ Δ Δ' : Ctx} -> Δ ⊆ Δ' -> Rpl F Γ Δ -> Rpl F Γ Δ'
    wk w · = ·
    wk w (σ , x) = wk w σ , wkF w x
    wk w (lock σ m)
      = let _ , (m' , w') = rewind-⊆ m w in lock (wk w' σ) m'

    -- Composition of weakening and substitution
    trim : {Γ Γ' Δ : Ctx} -> Γ ⊆ Γ' -> Rpl F Γ' Δ -> Rpl F Γ Δ
    trim base · = ·
    trim (weak w) (σ , _) = trim w σ
    trim (lift w) (σ , x) = trim w σ , x
    trim (lift🔓 w) (lock σ m) = lock (trim w σ) m

    shift : {A : Ty} {Γ Δ : Ctx} -> Rpl F Γ Δ -> Rpl F Γ (Δ , A)
    shift = wk (weak ⊆.id)

    liftRpl : {A : Ty} {Γ Δ : Ctx} -> Rpl F Γ Δ -> Rpl F (Γ , A) (Δ , A)
    liftRpl σ = shift σ , head

    id : {Γ : Ctx} -> Rpl F Γ Γ
    id {·} = ·
    id {x , A} = liftRpl id
    id {x ,🔓} = lock id ◁1

    from-⊆ : {Γ Δ : Ctx} -> Γ ⊆ Δ -> Rpl F Γ Δ
    from-⊆ base = ·
    from-⊆ (weak w) = shift (from-⊆ w)
    from-⊆ (lift w) = shift (from-⊆ w) , head
    from-⊆ (lift🔓 w) = lock (from-⊆ w) ◁1

    trimNat : {Γ Γ' Δ Δ' : Ctx} (w : Γ' ⊆ Γ) (w' : Δ ⊆ Δ') (σ : Rpl F Γ Δ)
      -> wk w' (trim w σ) ≡ trim w (wk w' σ)
    trimNat base w' · = refl
    trimNat (weak w) w' (σ , x) = trimNat w w' σ
    trimNat (lift w) w' (σ , x) = cong1 _,_ (trimNat w w' σ)
    trimNat (lift🔓 w) w' (lock σ m) = cong1 lock (trimNat w _ σ)

    trimIdl : {Γ Δ : Ctx} -> (σ : Rpl F Γ Δ) -> trim ⊆.id σ ≡ σ
    trimIdl · = refl
    trimIdl (s , x) = cong (_, x) (trimIdl s)
    trimIdl (lock s m) = cong1 lock (trimIdl s)

    trimIdr : {Γ Δ : Ctx} -> (w : Γ ⊆ Δ) -> trim w id ≡ from-⊆ w
    trimIdr base = refl
    trimIdr (weak w) = ≡.trans
      (≡.sym (trimNat w (weak ⊆.id) id))
      (cong shift (trimIdr w))
    trimIdr (lift w) = cong (_, head) (≡.trans
      (≡.sym (trimNat w (weak ⊆.id) id))
      (cong shift (trimIdr w)))
    trimIdr (lift🔓 w) = cong1 lock (trimIdr w)

    module _
      (rewind-⊆-pres-● : {Δ Γ Γ' Γ'' : Ctx} (m : Δ ◁ Γ) (w1 : Γ ⊆ Γ') (w2 : Γ' ⊆ Γ'')
        -> let _ , (m' , w1') = rewind-⊆ m w1
               _ , (m'' , w2') = rewind-⊆ m' w2
           in rewind-⊆ m (w1 ● w2) ≡ (_ , (m'' , (w1' ● w2'))))
      (wkFPres-● : {A : Ty} {Γ Δ Ξ : Ctx} (w : Γ ⊆ Δ) (w' : Δ ⊆ Ξ) (x : F A Γ)
        -> wkF (w ● w') x ≡ wkF w' (wkF w x))
      where
      wkPres-● : {Γ Δ Δ' Δ'' : Ctx} (w : Δ ⊆ Δ') (w' : Δ' ⊆ Δ'') (σ : Rpl F Γ Δ)
        -> wk (w ● w') σ ≡ wk w' (wk w σ)
      wkPres-● w w' · = refl
      wkPres-● w w' (s , x) = cong₂ _,_ (wkPres-● w w' s) (wkFPres-● w w' x)
      wkPres-● w w' (lock s m) = ≡.trans
        (cong (λ (_ , (m' , w'')) -> lock (wk w'' s) m') (rewind-⊆-pres-● m w w'))
        (cong1 lock (wkPres-● _ _ s))

  module Composition
    (F G : Ty -> Ctx -> Set)
    (rewind : {Γ Γ' Δ : Ctx} -> (m : Γ' ◁ Γ) -> Rpl G Γ Δ
      -> Σ Ctx λ Δ' -> Δ' ◁ Δ × Rpl G Γ' Δ')
    (apply : {A : Ty} {Γ Δ : Ctx} -> Rpl G Γ Δ -> F A Γ -> G A Δ)
    where
    _∙_ : {Γ Γ' Γ'' : Ctx} -> Rpl F Γ Γ' -> Rpl G Γ' Γ'' -> Rpl G Γ Γ''
    · ∙ δ = ·
    (σ , a) ∙ δ = (σ ∙ δ) , apply δ a
    lock σ m ∙ δ
      = let _ , (m' , δ') = rewind m δ in lock (σ ∙ δ') m'
