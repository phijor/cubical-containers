module GpdCont.KanExtension.Left where

open import GpdCont.Prelude

open import Cubical.Foundations.HLevels hiding (extend)
open import Cubical.Data.Sigma.Base
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Functor.Compose using (precomposeF)
open import Cubical.Categories.NaturalTransformation.Base renaming (_●ᵛ_ to _∙ᵛ_)
open import Cubical.Categories.Instances.Sets using (SET)
open import Cubical.Categories.Instances.Functors using () renaming (FUNCTOR to FunctorCat)
open import Cubical.Categories.Adjoint using (module UnitCounit)

private
  variable
    ℓo ℓh : Level
    C C′ D : Category ℓo ℓh

  ∙ᵛ-idL : ∀ {F G : Functor C C′} (α : NatTrans F G) → idTrans F ∙ᵛ α ≡ α
  ∙ᵛ-idL {C′} α = makeNatTransPath $ funExt λ c → C′ .Category.⋆IdL (α .NatTrans.N-ob c)

module Lan {ℓCo ℓCh ℓEo ℓEh}
  {C : Category ℓCo ℓCh}
  {E : Category ℓEo ℓEh}
  (J : Functor C E) where
  open Category

  module _ {ℓDo ℓDh} {D : Category ℓDo ℓDh} (F : Functor C D) where
    private
      ℓ = (ℓ-suc (ℓ-max (ℓ-max ℓCo ℓCh) (ℓ-max (ℓ-max ℓEo ℓEh) (ℓ-max ℓDo ℓDh))))

    record Extension : Type ℓ where
      field
        {ext} : Functor E D
        ext-filler : NatTrans F (ext ∘F J)

    open Extension

    isLan : (η : Extension) → Type ℓ
    isLan η =
      ∀ (α : Extension)
      → ∃![ α* ∈ NatTrans (η .ext) (α .ext) ] α .ext-filler ≡ η .ext-filler ∙ᵛ (α* ∘ˡ J)

    isPropIsLan : (η : Extension) → isProp (isLan η)
    isPropIsLan η = isPropΠ λ α → isPropIsContr

    record Lan : Type ℓ where
      field
        extension : Extension
        is-lan-extension : isLan extension

      lan : Functor E D
      lan = extension .ext

      lan-filler : NatTrans F (lan ∘F J)
      lan-filler = extension .ext-filler

      mediator : (α : Extension) → NatTrans lan (α .ext)
      mediator α = is-lan-extension α .fst .fst

      mediator-factorization : ∀ (α : Extension) → α .ext-filler ≡ lan-filler ∙ᵛ (mediator α ∘ˡ J)
      mediator-factorization α = is-lan-extension α .fst .snd

      mediator-self : mediator extension ≡ idTrans lan
      mediator-self = {! !}

  module _ {ℓDo ℓDh} {D : Category ℓDo ℓDh} (has-lan : (F : Functor C D) → Lan F) where
    open Functor
    open Extension

    extend : Functor C D → Functor E D
    extend F = has-lan F .Lan.extension .ext

    module _ {F F′ : Functor C D} (α : NatTrans F F′) where
      private
        open module LanF = Lan (has-lan F) renaming (extension to η ; is-lan-extension to η-is-lan)
        open module LanF′ = Lan (has-lan F′) renaming (extension to η′ ; is-lan-extension to η′-is-lan)

      extend-nat-extension : Extension F
      extend-nat-extension .ext = LanF′.lan
      extend-nat-extension .ext-filler = α ∙ᵛ LanF′.lan-filler

      extend-nat : NatTrans (extend F) (extend F′)
      extend-nat = LanF.mediator extend-nat-extension

    opaque
      extend-nat-id : ∀ {F : Functor C D} → extend-nat (idTrans F) ≡ idTrans (extend F)
      extend-nat-id {F} =
        extend-nat (idTrans F) ≡⟨⟩
        LanF.mediator (extend-nat-extension (idTrans F))  ≡⟨ cong LanF.mediator p ⟩
        LanF.mediator LanF.extension                      ≡⟨ LanF.mediator-self ⟩
        idTrans (extend F) ∎
        where
          module LanF = Lan (has-lan F)

          p : extend-nat-extension (idTrans F) ≡ LanF.extension
          p i .ext = LanF.lan
          p i .ext-filler = ∙ᵛ-idL LanF.lan-filler i

      extend-nat-seq : ∀ {F G H : Functor C D} (α : NatTrans F G) (β : NatTrans G H) → extend-nat (α ∙ᵛ β) ≡ (extend-nat α) ∙ᵛ (extend-nat β)
      extend-nat-seq α β = {! !}

    LanFunctor : Functor (FunctorCat C D) (FunctorCat E D)
    LanFunctor .F-ob = extend
    LanFunctor .F-hom = extend-nat
    LanFunctor .F-id = extend-nat-id
    LanFunctor .F-seq = extend-nat-seq

    open UnitCounit using (_⊣_)

    private
      J* : Functor (FunctorCat E D) (FunctorCat C D)
      J* = precomposeF D J

    η : NatTrans 𝟙⟨ FunctorCat C D ⟩ (J* ∘F LanFunctor)
    η .NatTrans.N-ob F = Lan.lan-filler (has-lan F)
    η .NatTrans.N-hom = {! !}

    ε : NatTrans (LanFunctor ∘F J*) 𝟙⟨ FunctorCat E D ⟩
    ε .NatTrans.N-ob L = Lan.mediator (has-lan (J* ⟅ L ⟆)) e where
      e : Extension (J* ⟅ L ⟆)
      e .ext = L
      e .ext-filler = idTrans (J* ⟅ L ⟆)
    ε .NatTrans.N-hom = {! !}

    universalProperty : LanFunctor ⊣ J*
    universalProperty ._⊣_.η = η
    universalProperty ._⊣_.ε = ε
    universalProperty ._⊣_.triangleIdentities = {! !}
  
--module LanSet {ℓ}
--  (C E : Category ℓ ℓ)
--  (J : Functor C E)
--  (F : Functor C (SET ℓ))
--  where

--  open import Cubical.HITs.SetQuotients as SQ using (_/_)

--  open Lan J renaming (Lan to LanJ)
--  open Category

--  module Ext where
--    module _ (e : E .ob) where
--      ExtRaw : Type ℓ
--      ExtRaw = Σ[ c ∈ C .ob ] (E [ J ⟅ c ⟆ , e ]) × (⟨ F ⟅ c ⟆ ⟩)

--      _∼_ : (x y : ExtRaw) → Type ℓ
--      (c , g , p) ∼ (c′ , g′ , p′) =
--        Σ[ f ∈ C [ c , c′ ] ]
--        -- Σ[ h ∈ E 
--        (g ≡ J ⟪ f ⟫  ⋆⟨ E ⟩ g′) × {! !}

--      Ext₀ = ExtRaw / _∼_

--    ext : Functor E (SET ℓ)
--    ext .Functor.F-ob e = Ext₀ e , SQ.squash/
--    ext .Functor.F-hom = {! !}
--    ext .Functor.F-id = {! !}
--    ext .Functor.F-seq = {! !}

--    ext-filler : NatTrans F (ext ∘F J)
--    ext-filler = {! !}

--  Ext : Extension F
--  Ext = record { Ext }

--  LanSet : LanJ F
--  LanSet .Lan.Lan.extension = Ext
--  LanSet .Lan.Lan.is-lan-extension = {! !}


----module Lan {ℓo ℓh} {C : Category ℓo ℓh} (J : Functor C (SET ℓ)) (P : Functor C (SET ℓ)) where
----  open Category

----  data Coend (X : SET ℓ .ob) : Type (ℓ-max ℓ ℓo) where
----    coend : (c : C .ob) (g : SET ℓ [ P ⟅ c ⟆ , X ]) (d : ⟨ J ⟅ c ⟆ ⟩) → Coend X
----    -- coend-eq : 
----    --
----    isSetCoend : isSet (Coend X)

----  open Functor

----  Ext : Functor (SET ℓ) (SET (ℓ-max ℓ ℓo))
----  Ext .F-ob X = Coend X , isSetCoend
----  Ext .F-hom = {! !}
----  Ext .F-id = {! !}
----  Ext .F-seq = {! !}

