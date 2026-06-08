open import GpdCont.Prelude

module GpdCont.GroupAction.Adjoint (ℓ : Level) where

open import GpdCont.HomotopySet using (_→Set_)
open import GpdCont.GroupAction.Base
open import GpdCont.GroupAction.Category ℓ
open import GpdCont.GroupAction.Product
open import GpdCont.Group.SymmetricGroup
open import GpdCont.Group.DirProd as GroupDirProd using (module DirProd ; DirProd)

open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Exponentials

private
  module GroupAction = Category GroupAction

  variable
    σ τ ρ : GroupAction.ob

open Action

-- XXX: In this definition, it is Gᵒᵖ × H that has to act.
adjointAction : (σ τ : GroupAction.ob) → GroupAction.ob
adjointAction ((G , X) , σ) ((H , Y) , τ) = [σ,τ] where
  H×G = DirProd H G

  module G = GroupStr (str G)
  module H = GroupStr (str H)

  module H×G where
    open GroupStr (str H×G) using () renaming (_·_ to _⊗_) public
    open DirProd H G public


  X←Y = Y →Set X

  σ* : Action H×G X
  σ* = GroupHomPreCompAction H×G.sndHom σ

  τ* : Action H×G Y
  τ* = GroupHomPreCompAction H×G.fstHom τ

  adj : ⟨ H ⟩ × ⟨ G ⟩ → ⟨ 𝔖 X←Y ⟩
  adj (h , g) = equiv→ (τ .action h) (σ .action g)

  opaque
    adj· : ((h₀ , g₀) (h₁ , g₁) : ⟨ H ⟩ × ⟨ G ⟩) → adj (h₀ H.· h₁ , g₀ G.· g₁) ≡ adj (h₀ , g₀) ∙ₑ adj (h₁ , g₁)
    adj· (h₀ , g₀) (h₁ , g₁) =
      equiv→ (τ .action $ h₀ H.· h₁) (σ .action $ g₀ G.· g₁) ≡⟨ cong₂ equiv→ (τ .pres· _ _) (σ .pres· _ _) ⟩
      equiv→ (τ .action h₀ ∙ₑ τ .action h₁) (σ .action g₀ ∙ₑ σ .action g₁) ≡⟨ equivEq refl ⟩
      equiv→ _ _ ∙ₑ equiv→ _ _ ∎

  σ⇒τ : Action H×G X←Y
  σ⇒τ .action = adj
  σ⇒τ .pres· = adj·

  [σ,τ] : GroupAction.ob
  [σ,τ] .fst .fst = H×G
  [σ,τ] .fst .snd = X←Y
  [σ,τ] .snd = σ⇒τ

private
  _⇒_ : (τ σ : GroupAction.ob) → GroupAction.ob
  _⇒_ = flip adjointAction

  _⊗_ = productAction ℓ

-- hom-iso : Iso (GroupAction [ σ ⊗ τ , ρ ]) (GroupAction [ σ , τ ⇒ ρ ])
-- hom-iso {σ = σ@((G , X), σ′)} {τ = τ@((H , Y), τ′)} {ρ = ρ@((K , Z), ρ′)} = go where
--   curry' : (GroupAction [ σ ⊗ τ , ρ ]) → (GroupAction [ σ , τ ⇒ ρ ])
--   curry' e using ((φ , f) , is-eqva) ← e = mkGroupActionHom curry-hom {! !} {! !} where
--     _ : GroupHom (DirProd G H) K
--     _ = φ

--     curry-hom : GroupHom G (DirProd H K)
--     curry-hom .fst g = {! !}
--     curry-hom .snd = {! !}

--   go : Iso _ _
--   go .Iso.fun = curry'
--   go .Iso.inv = {! !}
--   go .Iso.sec = {! !}
--   go .Iso.ret = {! !}

eval : GroupAction [ (σ ⇒ τ) ⊗ σ , τ ]
eval {σ = σ*@((G , X) , σ)} {τ = τ*@((H , Y) , τ)} = eval-at where
  eval-hom : GroupHom (DirProd (DirProd G H) G) H
  eval-hom = compGroupHom (DirProd.fstHom (DirProd G H) G) (DirProd.sndHom G H)

  eval-fun : ⟨ Y ⟩ → (⟨ X ⟩ → ⟨ Y ⟩) ⊎ ⟨ X ⟩
  eval-fun y = inl $ const y

  eval-at : GroupAction [ (σ* ⇒ τ*) ⊗ σ* , τ* ]
  eval-at .fst .fst = eval-hom
  eval-at .fst .snd = eval-fun
  eval-at .snd hgg = refl

GroupActionExponentials : AllExponentiable GroupAction (GroupActionBinProducts ℓ)
GroupActionExponentials σ@((G , X) , σ') τ@((H , Y) , τ') = ue where
  open import Cubical.Foundations.Isomorphism
  open import Cubical.Categories.Limits.BinProduct.More
  open import Cubical.Categories.Presheaf.Representable using (UniversalElement)

  module G = GroupStr (str G)
  module H = GroupStr (str H)

  -- intro : ∀ ω → GroupAction [ ω , σ ] × GroupAction [ ω , τ ] → GroupAction [ ω , productAction σ τ ]
  -- intro ω (g₁ , g₂) = prodEquivariant {ω = ω} {σ = σ} {τ = τ} g₁ g₂

  intro : ∀ ω → GroupAction [ ω ⊗ σ , τ ] → GroupAction [ ω , σ ⇒ τ ]
  intro ω*@((K , Z) , ω) (((φ , φ-hom) , f) , is-eqva) = intro-at where
    module K = GroupStr (str K)
    intro-at : GroupAction [ ω* , σ ⇒ τ ]
    intro-at .fst .fst .fst k = G.1g , φ (k , G.1g)
    intro-at .fst .fst .snd = makeIsGroupHom λ k₁ k₂ → ≡-× (sym (G.·IdL _)) $
      φ (k₁ K.· k₂ , G.1g)
        ≡⟨ cong (λ g → φ (k₁ K.· k₂ , g)) $ sym (G.·IdL _) ⟩
      φ (k₁ K.· k₂ , G.1g G.· G.1g)
        ≡⟨ φ-hom .IsGroupHom.pres· (k₁ , G.1g) (k₂ , G.1g) ⟩
      φ (k₁ , G.1g) H.· φ (k₂ , G.1g)
        ∎
    intro-at .fst .snd = ev* where
      ev* : (⟨ X ⟩ → ⟨ Y ⟩) → ⟨ Z ⟩
      ev* g = {!f!}
    intro-at .snd = {! !}

  ue : Exponential GroupAction σ τ (BinProducts→BinProductsWith GroupAction σ (GroupActionBinProducts _))
  ue .UniversalElement.vertex = σ ⇒ τ
  ue .UniversalElement.element = eval {σ = σ} {τ = τ}
  ue .UniversalElement.universal ω = isoToIsEquiv λ where
    .Iso.fun → _
    .Iso.inv → intro ω
    .Iso.sec g → {! !}
    .Iso.ret f → {! !}
