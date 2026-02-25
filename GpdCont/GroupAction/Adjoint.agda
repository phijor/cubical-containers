open import GpdCont.Prelude

module GpdCont.GroupAction.Adjoint (ℓ : Level) where

open import GpdCont.HomotopySet using (_→Set_)
open import GpdCont.GroupAction.Base
open import GpdCont.GroupAction.Category ℓ
open import GpdCont.GroupAction.Product
open import GpdCont.Group.SymmetricGroup
open import GpdCont.Group.DirProd as GroupDirProd using (module DirProd ; DirProd)

open import Cubical.Foundations.Equiv
open import Cubical.Data.Sum
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Categories.Category.Base

private
  module GroupAction = Category GroupAction

  variable
    σ τ ρ : GroupAction.ob

open Action

adjointAction : (σ τ : GroupAction.ob) → GroupAction.ob
adjointAction ((G , X) , σ) ((H , Y) , τ) = [σ,τ] where
  G×H = DirProd G H

  module G = GroupStr (str G)
  module H = GroupStr (str H)

  module G×H where
    open GroupStr (str G×H) using () renaming (_·_ to _⊗_) public
    open DirProd G H public


  X←Y = Y →Set X

  σ* : Action G×H X
  σ* = GroupHomPreCompAction G×H.fstHom σ

  τ* : Action G×H Y
  τ* = GroupHomPreCompAction G×H.sndHom τ

  adj : ⟨ G ⟩ × ⟨ H ⟩ → ⟨ 𝔖 X←Y ⟩
  adj (g , h) = equiv→ (τ .action h) (σ .action g)

  opaque
    adj· : ((g₀ , h₀) (g₁ , h₁) : ⟨ G ⟩ × ⟨ H ⟩) → adj (g₀ G.· g₁ , h₀ H.· h₁) ≡ adj (g₀ , h₀) ∙ₑ adj (g₁ , h₁)
    adj· (g₀ , h₀) (g₁ , h₁) =
      equiv→ (τ .action $ h₀ H.· h₁) (σ .action $ g₀ G.· g₁) ≡⟨ cong₂ equiv→ (τ .pres· _ _) (σ .pres· _ _) ⟩
      equiv→ (τ .action h₀ ∙ₑ τ .action h₁) (σ .action g₀ ∙ₑ σ .action g₁) ≡⟨ equivEq refl ⟩
      equiv→ _ _ ∙ₑ equiv→ _ _ ∎

  σ⇒τ : Action G×H X←Y
  σ⇒τ .action = adj
  σ⇒τ .pres· = adj·

  [σ,τ] : GroupAction.ob
  [σ,τ] .fst .fst = G×H
  [σ,τ] .fst .snd = X←Y
  [σ,τ] .snd = σ⇒τ

private
  _⇒_ = adjointAction
  _⊗_ = productAction ℓ

hom-iso : Iso (GroupAction [ σ ⊗ τ , ρ ]) (GroupAction [ σ , τ ⇒ ρ ])
hom-iso {σ = σ@((G , X), σ′)} {τ = τ@((H , Y), τ′)} {ρ = ρ@((K , Z), ρ′)} = go where
  curry' : (GroupAction [ σ ⊗ τ , ρ ]) → (GroupAction [ σ , τ ⇒ ρ ])
  curry' e using ((φ , f) , is-eqva) ← e = mkGroupActionHom curry-hom {! !} {! !} where
    _ : GroupHom (DirProd G H) K
    _ = φ

    curry-hom : GroupHom G (DirProd H K)
    curry-hom .fst g = {! !}
    curry-hom .snd = {! !}

  go : Iso _ _
  go .Iso.fun = curry'
  go .Iso.inv = {! !}
  go .Iso.sec = {! !}
  go .Iso.ret = {! !}

eval' : GroupAction [ (τ ⇒ σ) ⊗ σ , τ ]
eval' {τ = τ*@((H , Y) , τ)} {σ = σ*@((G , X) , σ)} = eval-at where
  eval-hom : GroupHom (DirProd (DirProd H G) G) H
  eval-hom = compGroupHom (DirProd.fstHom _ G) (DirProd.fstHom H G)

  eval-fun : ⟨ Y ⟩ → (⟨ X ⟩ → ⟨ Y ⟩) ⊎ ⟨ X ⟩
  eval-fun y = inl $ const y

  eval-at : GroupAction [ (τ* ⇒ σ*) ⊗ σ* , τ* ]
  eval-at .fst .fst = eval-hom
  eval-at .fst .snd = eval-fun
  eval-at .snd hgg = refl

eval : GroupAction [ (σ ⇒ τ) ⊗ σ , τ ]
eval {σ = σ*@((G , X) , σ)} {τ = τ*@((H , Y) , τ)} = eval-at where
  eval-hom : GroupHom (DirProd (DirProd G H) G) H
  eval-hom = {! !}

  eval-fun : ⟨ Y ⟩ → (⟨ Y ⟩ → ⟨ X ⟩) ⊎ ⟨ X ⟩
  eval-fun = {! !}

  eval-at : GroupAction [ (σ* ⇒ τ*) ⊗ σ* , τ* ]
  eval-at .fst .fst = eval-hom
  eval-at .fst .snd = eval-fun
  eval-at .snd = {! !}
