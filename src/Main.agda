open import Data.Nat using (ℕ; zero; suc)

data Ty : Set where
  ι : Ty
  _⟶_ : Ty -> Ty -> Ty
  □_ : Ty -> Ty

infixr 30 _⟶_

data Tm : Set where
  var : (n : ℕ) -> Tm 
  abs : Tm -> Tm
  app : Tm -> Tm -> Tm
  box : Tm -> Tm
  unbox : Tm -> Tm

-- Typing context
data Ctx : Set where
  · : Ctx
  _,_ : (Γ : Ctx) -> (A : Ty) -> Ctx
  _,🔓 : (Γ : Ctx) -> Ctx

infixl 40 _,_

-- A term of type A can be found in the context at index n.
data Get (A : Ty) : Ctx -> ℕ -> Set where
  i0 : {Γ : Ctx} -> Get A (Γ , A) 0
  is : {Γ : Ctx} {n : ℕ} -> {B : Ty} -> Get A Γ n -> Get A (Γ , B) (suc n)

-- Relation between contexts Γ and Γ' signifying that it is possible
-- to extend Γ to Γ' without adding any locks.
data LFExt (Γ : Ctx) : Ctx -> Set where
  zero : LFExt Γ Γ
  suc : {Γ' : Ctx} -> LFExt Γ Γ' -> (A : Ty) -> LFExt Γ (Γ' , A)

-- Typing judgement: Term t is of type A in context Γ.
data _⊢_::_ : Ctx -> Tm -> Ty -> Set where
  ⊢-var : {n : ℕ} {A : Ty} {Γ : Ctx}
    -> Get A Γ n
    -> Γ ⊢ var n :: A

  ⊢-abs : {A B : Ty} {Γ : Ctx} {t : Tm}
    -> Γ , A ⊢ t :: B
    -> Γ ⊢ abs t :: A ⟶ B

  ⊢-app : {A B : Ty} {Γ : Ctx} {t u : Tm}
    -> Γ ⊢ t :: A ⟶ B -> Γ ⊢ u :: A
    -> Γ ⊢ app t u :: B

  ⊢-box : {A : Ty} {Γ : Ctx} {t : Tm}
    -> (Γ ,🔓) ⊢ t :: A
    -> Γ ⊢ box t :: (□ A)

  ⊢-unbox : {A : Ty} {Γ Γ' : Ctx} {t : Tm}
    -> Γ ⊢ t :: (□ A)
    -> LFExt (Γ ,🔓) Γ'
    -> Γ' ⊢ unbox t :: A

-- Equivalence of terms-in-context (including β-red/η-conv)
data _≅_
  : {Γ Γ' : Ctx} {t s : Tm} {A B : Ty}
  -> Γ ⊢ t :: A -> Γ' ⊢ s :: B -> Set where
