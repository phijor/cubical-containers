module GpdCont.KanExtension.Left where

open import GpdCont.Prelude

open import Cubical.Foundations.HLevels hiding (extend)
open import Cubical.Data.Sigma.Base
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Functor.Compose using (precomposeF)
open import Cubical.Categories.NaturalTransformation.Base renaming (_●ᵛ_ to _∙ᵛ_)
open import Cubical.Categories.Instances.Sets using (SET ; _[-,_] ; _[_,-])
open import Cubical.Categories.Instances.Functors using () renaming (FUNCTOR to FunctorCat)
open import Cubical.Categories.Adjoint using (module UnitCounit)
open import Cubical.Tactics.CategorySolver.Reflection using (solveCat!)

private
  variable
    ℓo ℓh : Level
    C C′ D : Category ℓo ℓh

  ∙ᵛ-idL : ∀ {F G : Functor C C′} (α : NatTrans F G) → idTrans F ∙ᵛ α ≡ α
  ∙ᵛ-idL {C′} α = makeNatTransPath $ funExt λ c → C′ .Category.⋆IdL (α .NatTrans.N-ob c)

  ∙ᵛ-idR : ∀ {F G : Functor C C′} (α : NatTrans F G) → α ∙ᵛ idTrans G ≡ α
  ∙ᵛ-idR {C′} α = makeNatTransPath $ funExt λ c → C′ .Category.⋆IdR (α .NatTrans.N-ob c)

  ∙ᵛ-Assoc : ∀ {F G H K : Functor C C′} (α : NatTrans F G) (β : NatTrans G H) (γ : NatTrans H K)  → (α ∙ᵛ β) ∙ᵛ γ ≡ α ∙ᵛ (β ∙ᵛ γ)
  ∙ᵛ-Assoc {C′} α β γ = makeNatTransPath $ funExt λ c → C′ .Category.⋆Assoc (α ⟦ c ⟧) (β ⟦ c ⟧) (γ ⟦ c ⟧)

module Lan {ℓCo ℓCh ℓEo ℓEh}
  {C : Category ℓCo ℓCh}
  {E : Category ℓEo ℓEh}
  (J : Functor C E) where
  open Category hiding (ob)

  module _ {ℓDo ℓDh} {D : Category ℓDo ℓDh} (F : Functor C D) where
    private
      ℓ = (ℓ-suc (ℓ-max (ℓ-max ℓCo ℓCh) (ℓ-max (ℓ-max ℓEo ℓEh) (ℓ-max ℓDo ℓDh))))

    record Extension : Type ℓ where
      constructor mkExtension
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

      mediator-unique : ∀ (α : Extension) (α* : NatTrans lan (α .ext)) → (α .ext-filler ≡ lan-filler ∙ᵛ (α* ∘ˡ J)) → mediator α ≡ α*
      mediator-unique α α* α*-filler = cong fst (is-lan-extension α .snd (α* , α*-filler))

      mediator-self : mediator extension ≡ idTrans lan
      mediator-self = mediator-unique extension (idTrans lan) filler-path where
        abstract
          -- idTrans lan ∘ˡ J ≡ idTrans _
          filler-path : lan-filler ≡ lan-filler ∙ᵛ (idTrans lan ∘ˡ J)
          filler-path = sym (∙ᵛ-idR lan-filler)

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
        extend-nat-factorization : α ∙ᵛ LanF′.lan-filler ≡ LanF.lan-filler ∙ᵛ (extend-nat ∘ˡ J)
        extend-nat-factorization = LanF.mediator-factorization extend-nat-extension

        extend-nat-unique : (α* : NatTrans LanF.lan LanF′.lan) → α ∙ᵛ LanF′.lan-filler ≡ LanF.lan-filler ∙ᵛ (α* ∘ˡ J) → extend-nat ≡ α*
        extend-nat-unique = LanF.mediator-unique extend-nat-extension

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
      extend-nat-seq {F} {G} {H} α β =
        extend-nat (α ∙ᵛ β) ≡⟨⟩
        LanF.mediator (extend-nat-extension (α ∙ᵛ β)) ≡⟨ LanF.mediator-unique (mkExtension (α ∙ᵛ β ∙ᵛ LanH.lan-filler)) _ mediator' ⟩
        (LanF.mediator (extend-nat-extension α)) ∙ᵛ (LanG.mediator (extend-nat-extension β)) ≡⟨⟩
        (extend-nat α) ∙ᵛ (extend-nat β) ∎
        where
          module LanF = Lan (has-lan F)
          module LanG = Lan (has-lan G)
          module LanH = Lan (has-lan H)

          𝔽 : Category (ℓ-max (ℓ-max (ℓ-max ℓCo ℓCh) ℓDo) ℓDh) (ℓ-max (ℓ-max ℓCo ℓCh) ℓDh)
          𝔽 = FunctorCat C D

          open Category 𝔽 using () renaming (_⋆_ to _*_)

          mediator' : α ∙ᵛ β ∙ᵛ LanH.lan-filler ≡ LanF.lan-filler ∙ᵛ ((extend-nat α ∙ᵛ extend-nat β) ∘ˡ J)
          mediator' =
            (α ∙ᵛ β) ∙ᵛ LanH.lan-filler                   ≡⟨ ∙ᵛ-Assoc α β LanH.lan-filler ⟩
            α ∙ᵛ (β ∙ᵛ LanH.lan-filler)                   ≡⟨ cong (α ∙ᵛ_) (extend-nat-factorization β) ⟩
            α ∙ᵛ (LanG.lan-filler ∙ᵛ (extend-nat β ∘ˡ J)) ≡⟨ sym $ ∙ᵛ-Assoc α LanG.lan-filler _ ⟩
            (α ∙ᵛ LanG.lan-filler) ∙ᵛ (extend-nat β ∘ˡ J) ≡⟨ cong (_∙ᵛ (extend-nat β ∘ˡ J)) (extend-nat-factorization α) ⟩
            (LanF.lan-filler ∙ᵛ (extend-nat α ∘ˡ J)) ∙ᵛ (extend-nat β ∘ˡ J) ≡⟨ ∙ᵛ-Assoc LanF.lan-filler _ (extend-nat β ∘ˡ J) ⟩
            LanF.lan-filler ∙ᵛ ((extend-nat α ∘ˡ J) ∙ᵛ (extend-nat β ∘ˡ J)) ≡⟨⟩
            LanF.lan-filler ∙ᵛ ((extend-nat α ∙ᵛ extend-nat β) ∘ˡ J) ∎

    LanFunctor : Functor (FunctorCat C D) (FunctorCat E D)
    LanFunctor .F-ob = extend
    LanFunctor .F-hom = extend-nat
    LanFunctor .F-id = extend-nat-id
    LanFunctor .F-seq = extend-nat-seq

    private
      -∘J : Functor (FunctorCat E D) (FunctorCat C D)
      -∘J = precomposeF D J

      Lan[-]∘J : Functor (FunctorCat C D) (FunctorCat C D)
      Lan[-]∘J = -∘J ∘F LanFunctor

      Lan[-∘J] : Functor (FunctorCat E D) (FunctorCat E D)
      Lan[-∘J] = LanFunctor ∘F -∘J

    module η (F : Functor C D) where
      private
        module lan = Lan (has-lan F)
          
      ob : NatTrans F (Lan[-]∘J ⟅ F ⟆)
      ob = lan.lan-filler

      _ = {! lan.mediator !}


    η : NatTrans 𝟙⟨ FunctorCat C D ⟩ Lan[-]∘J
    η .NatTrans.N-ob = η.ob
    η .NatTrans.N-hom = η-hom _ _ where
      opaque
        η-hom : ∀ (F G : Functor C D) (α : NatTrans F G) → α ∙ᵛ η.ob G ≡ η.ob F ∙ᵛ (extend-nat α ∘ˡ J)
        η-hom F G = extend-nat-factorization {F} {G}

    module ε (L : Functor E D) where
      private
        open module lan = Lan (has-lan $ L ∘F J) using ()
          renaming (lan-filler to filler) public

      Λ : Extension $ L ∘F J
      Λ .ext = L
      Λ .ext-filler = idTrans (L ∘F J)

      ob : NatTrans (Lan[-∘J] ⟅ L ⟆) L
      ob = lan.mediator Λ

      ob-factorization : idTrans (L ∘F J) ≡ filler ∙ᵛ (ob ∘ˡ J)
      ob-factorization = lan.mediator-factorization Λ

    opaque
      ε-hom : (L K : Functor E D) (α : NatTrans L K) → Lan[-∘J] ⟪ α ⟫ ∙ᵛ ε.ob K ≡ ε.ob L ∙ᵛ α
      ε-hom L K α =
        extend-nat (α ∘ˡ J) ∙ᵛ ε.ob K ≡⟨ cong (_∙ᵛ ε.ob K) (extend-nat-unique (α ∘ˡ J) {! !} {! !}) ⟩
        {! !} ∙ᵛ ε.ob K ≡⟨ {!extend-nat-unique!} ⟩
        ε.ob L ∙ᵛ α ∎

    ε : NatTrans Lan[-∘J] 𝟙⟨ FunctorCat E D ⟩
    ε .NatTrans.N-ob = ε.ob
    ε .NatTrans.N-hom = ε-hom _ _

    opaque
      Δ₁ : (F : Functor C D) → LanFunctor ⟪ η ⟦ F ⟧ ⟫ ∙ᵛ ε ⟦ LanFunctor ⟅ F ⟆ ⟧ ≡ idTrans (LanFunctor ⟅ F ⟆)
      Δ₁ F =
        extend-nat (η.ob F) ∙ᵛ ε.ob (extend F) ≡⟨ {! ε.ob $ extend F !} ⟩
        idTrans (extend F) ∎
        where
          fact : idTrans F ∙ᵛ η.ob F ≡ η.ob F ∙ᵛ (extend-nat (idTrans F) ∘ˡ J)
          fact = extend-nat-factorization (idTrans F)

      Δ₂ : (L : Functor E D) → (η ⟦ -∘J ⟅ L ⟆ ⟧) ∙ᵛ (-∘J ⟪ ε ⟦ L ⟧ ⟫) ≡ idTrans (-∘J ⟅ L ⟆)
      Δ₂ L =
        η.ob (L ∘F J) ∙ᵛ (ε.ob L ∘ˡ J) ≡⟨ cong (_∙ᵛ (ε.ob L ∘ˡ J)) η-ε-lemma ⟩
        ε.filler L ∙ᵛ (ε.ob L ∘ˡ J) ≡⟨ sym $ ε.ob-factorization L ⟩
        idTrans (L ∘F J) ∎

        where
          η-ε-lemma : η.ob (L ∘F J) ≡ ε.filler L
          η-ε-lemma = makeNatTransPath refl

    Δ : UnitCounit.TriangleIdentities LanFunctor -∘J η ε
    Δ .UnitCounit.TriangleIdentities.Δ₁ = Δ₁
    Δ .UnitCounit.TriangleIdentities.Δ₂ = Δ₂

    open UnitCounit using (_⊣_)

    universalProperty : LanFunctor ⊣ -∘J
    universalProperty ._⊣_.η = η
    universalProperty ._⊣_.ε = ε
    universalProperty ._⊣_.triangleIdentities = Δ

{-
module LocalLan {ℓo ℓh} {ℓDo ℓDh}
  {C : Category ℓo ℓh}
  {E : Category ℓo ℓh}
  (J : Functor C E)
  (D : Category ℓDo ℓDh)
  (F : Functor C D)
  (lanF : Lan.Lan J F)
  where
  open Lan using (mkExtension)
  open module LanF = Lan.Lan lanF using () renaming (lan to LanF ; lan-filler to η)

  private
    ℓ = ℓ-max (ℓ-max ℓo ℓh) ℓDh

    [E,D] : Category _ _
    [E,D] = FunctorCat E D

    [C,D] : Category _ _
    [C,D] = FunctorCat C D

    [E,D][LanF,-] : Functor [E,D] (SET ℓ)
    [E,D][LanF,-] = [E,D] [ LanF ,-]

    J* : Functor (FunctorCat E D) (FunctorCat C D)
    J* = precomposeF D J

    [C,D][F,-∘J] : Functor [E,D] (SET ℓ)
    [C,D][F,-∘J] = ([C,D] [ F ,-]) ∘F J*

  natTrans' : NatTrans [E,D][LanF,-] [C,D][F,-∘J]
  natTrans' = α where
    α : NatTrans _ _
    α .NatTrans.N-ob G ξ = {! LanF.mediator !}
    α .NatTrans.N-hom = {! !}

  natTrans'' : NatTrans [C,D][F,-∘J] [E,D][LanF,-]
  natTrans'' = foo where
    _* : ∀ {G : Functor E D} → (α : NatTrans F (G ∘F J)) → NatTrans LanF G
    _* α = LanF.mediator (mkExtension α)


    ⟨_,_⟩* : ∀ (G : Functor E D) → (α : NatTrans F (G ∘F J)) → NatTrans LanF G
    ⟨_,_⟩* G = _*

    foo : NatTrans _ _
    foo .NatTrans.N-ob = ⟨_,_⟩*
    foo .NatTrans.N-hom {x = G} {y = G′} = goal where
      goal : (γ : [E,D] [ G , G′ ]) → ⟨ G′ ,_⟩* ∘ [C,D][F,-∘J] ⟪ γ ⟫ ≡ [E,D][LanF,-] ⟪ γ ⟫ ∘ ⟨ G ,_⟩*
      goal γ = funExt λ (α : NatTrans F (G ∘F J)) →
        ⟨ G′ , α ∙ᵛ (γ ∘ˡ J) ⟩* ≡⟨ {!LanF.mediator-unique (mkExtension α) !} ⟩
        {!_!} ∙ᵛ γ ≡⟨ sym $ cong (_∙ᵛ γ) {! LanF.mediator-unique (mkExtension α)  !} ⟩
        ⟨ G , α ⟩* ∙ᵛ γ ∎
-}
  
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
