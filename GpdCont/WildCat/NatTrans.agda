module GpdCont.WildCat.NatTrans where

open import GpdCont.Prelude renaming (id to idfun)

open import Cubical.Foundations.Function using (flip) renaming (_∘_ to _∘fun_)
open import Cubical.Foundations.HLevels
open import Cubical.WildCat.Base using (WildCat ; _[_,_] ; seq')
open import Cubical.WildCat.Functor as Functor using (WildFunctor ; WildNatTrans)

private
  variable
    ℓo ℓh : Level
    C D : WildCat ℓo ℓh

open WildCat
open WildFunctor
open WildNatTrans

WildNatTransPath : {F G : WildFunctor C D} {α β : WildNatTrans C D F G}
  → (ob-path : ∀ (x : C .ob) → α .N-ob x ≡ β .N-ob x)
  → (hom-path : ∀ {x y} (f : C [ x , y ])
      → PathP (λ i → (F .F-hom f) ⋆⟨ D ⟩ ob-path y i ≡ ob-path x i ⋆⟨ D ⟩ (G .F-hom f)) (α .N-hom f) (β .N-hom f)
    )
  → α ≡ β
WildNatTransPath ob-path hom-path i .N-ob x = ob-path x i
WildNatTransPath ob-path hom-path i .N-hom f = hom-path f i
