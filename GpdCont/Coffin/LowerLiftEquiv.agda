open import GpdCont.Prelude
open import GpdCont.Coffin.Base

module GpdCont.Coffin.LowerLiftEquiv {ℓ} (C : Coffin ℓ) where
  open import GpdCont.SetTruncation using (componentEquiv ; isConnected-fiber-∣-∣₂)
  open import GpdCont.Univalence
  open import GpdCont.Groups.Base
  open import GpdCont.Groups.Equiv
  open import GpdCont.Image.Large using (postCompEquiv→imagesEquiv ; preCompSurjection→imagesEquiv)
  open import GpdCont.Delooping.Base using (𝔹)
  open import GpdCont.Embedding using (isCancellable→isEmbedding)
  open import GpdCont.Skeleton using (Skeleton)
  open import GpdCont.QuotientContainer.Base using (QCont)
  open import GpdCont.SetTruncation using (PathSetTrunc≃PropTruncPath)
  import GpdCont.Coffin.Lower

  open import Cubical.Foundations.Equiv
  open import Cubical.Foundations.HLevels
  open import Cubical.Foundations.Isomorphism
  open import Cubical.Foundations.Transport using (substEquiv)
  open import Cubical.Data.Sigma.Properties as Sigma using ()
  open import Cubical.Functions.Embedding
  open import Cubical.Functions.Image
  open import Cubical.Functions.Surjection using (_↠_ ; isSurjection)
  open import Cubical.HITs.SetTruncation as ST using (∥_∥₂ ; ∣_∣₂)
  open import Cubical.HITs.PropositionalTruncation as PT using ()
  open import Cubical.Homotopy.Loopspace using (Ω)

  module C = Coffin C

  module LowerC = GpdCont.Coffin.Lower C

  module ↓C = QCont (LowerC.↓)

  import GpdCont.QuotientContainer.Base
  import GpdCont.QuotientContainer.Lift

  open module ↑↓C = GpdCont.QuotientContainer.Lift LowerC.↓
    using ()
    renaming (↑ to ↑↓C)

  private
    FiberGroupStr : ∀ {ℓ} {A : Type ℓ} → isGroupoid A → (⋆ : A) → GroupStr (fiber ∣_∣₂ ∣ ⋆ ∣₂)
    FiberGroupStr gpd-A ⋆ = grp-str where
      grp-str : GroupStr _
      grp-str .GroupStr.is-connected = isConnected-fiber-∣-∣₂ ∣ ⋆ ∣₂
      grp-str .GroupStr.is-groupoid = isGroupoidΣ gpd-A λ a → isProp→isOfHLevelSuc 2 (ST.isSetSetTrunc ∣ a ∣₂ ∣ ⋆ ∣₂)
      grp-str .GroupStr.pt = ⋆ , refl

    cong′ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (x y : A) (f : A → B) (p : x ≡ y) → f x ≡ f y
    cong′ _ _ = cong

  delooping-equiv' : (2-trunc-Pos : ∀ s t → isEmbedding (cong {x = s} {y = t} C.Pos))
    → (c : ∥ C.Shape ∥₂) → 𝔹 (↓C.SymmGroup c) ≃ (fiber ∣_∣₂ c)
  delooping-equiv' 2-trunc-Pos c = GroupEquiv→Equiv group-equiv where
    ⋆ : C.Shape
    ⋆ = C.sk c

    ShapeFiberGroup⋆ : Group _
    ShapeFiberGroup⋆ .fst = fiber ∣_∣₂ ∣ ⋆ ∣₂
    ShapeFiberGroup⋆ .snd = FiberGroupStr C.is-groupoid-shape ⋆

    ShapeFiberGroup : Group _
    ShapeFiberGroup .fst = fiber ∣_∣₂ c
    ShapeFiberGroup .snd = subst (GroupStr ∘ fiber ∣_∣₂) (C.sk-section c) (ShapeFiberGroup⋆ .snd)

    𝔹SymmGroup : Group _
    𝔹SymmGroup .fst = 𝔹 (↓C.SymmGroup c)
    𝔹SymmGroup .snd = ↑↓C.↑SymmElim.deloopingGroupStr c

    module Γ = 𝔹 (↓C.SymmGroup c)

    hom : 𝔹 (↓C.SymmGroup c) → fiber ∣_∣₂ c
    hom = ↑↓C.↑SymmElim.rec c (ShapeFiberGroup .snd .GroupStr.is-groupoid)
      (C.component-section c)
      loop
      {! !} where

      φ : (p : C.sk c ≡ C.sk c) → (C.component-section c) ≡ (C.component-section c)
      φ p = Sigma.ΣPathP (p , isProp→PathP (λ i → ST.isSetSetTrunc ∣ p i ∣₂ c) _ _)

      has-prop-fibers : hasPropFibers (pathToEquiv ∘ cong′ (C.sk c) (C.sk c) C.Pos)
      has-prop-fibers = isEmbedding→hasPropFibers (isEmbedding-∘ (isEquiv→isEmbedding isEquivPathToEquiv) (2-trunc-Pos (C.sk c) (C.sk c)))

      loop : (σ : ↓C.Symm c) → Path (fiber ∣_∣₂ c) (C.component-section c) (C.component-section c)
      loop σ = φ (fib∞ .fst) where
        fib∞ : fiber (pathToEquiv ∘ cong C.Pos) (σ .fst)
        fib∞ = equivFun (PT.propTruncIdempotent≃ (has-prop-fibers (σ .fst))) (σ .snd)

    group-equiv : GroupEquiv 𝔹SymmGroup ShapeFiberGroup
    group-equiv .GroupEquiv.hom = hom
    group-equiv .GroupEquiv.is-emb-hom = {! !}
    group-equiv .GroupEquiv.pres-pt = sym (fromPathP {A = λ i → fiber ∣_∣₂ (C.component-section c .snd i)} {! !})

  delooping-equiv : (c : ∥ C.Shape ∥₂) → (fiber ∣_∣₂ c) ≃ 𝔹 (↓C.SymmGroup c)
  delooping-equiv c = GroupEquiv→Equiv group-equiv where
    ⋆ : C.Shape
    ⋆ = C.sk c

    ShapeFiberGroup⋆ : Group _
    ShapeFiberGroup⋆ .fst = fiber ∣_∣₂ ∣ ⋆ ∣₂
    ShapeFiberGroup⋆ .snd = FiberGroupStr C.is-groupoid-shape ⋆

    ShapeFiberGroup : Group _
    ShapeFiberGroup .fst = fiber ∣_∣₂ c
    ShapeFiberGroup .snd = subst (GroupStr ∘ fiber ∣_∣₂) (C.sk-section c) (ShapeFiberGroup⋆ .snd)

    𝔹SymmGroup : Group _
    𝔹SymmGroup .fst = 𝔹 (↓C.SymmGroup c)
    𝔹SymmGroup .snd = ↑↓C.↑SymmElim.deloopingGroupStr c

    hom : ∀ {c} → fiber ∣_∣₂ c → ⟨ 𝔹SymmGroup ⟩
    hom (s , ∣s∣≡c) = 𝔹.⋆

    assumption : isEmbedding (C.sk ∘ ∣_∣₂)
    assumption = isCancellable→isEmbedding cancel where
      cancel : (s t : C.Shape) → (s ≡ t) ≃ (C.sk ∣ s ∣₂ ≡ C.sk ∣ t ∣₂)
      cancel s t = {! !}
    -- assumption = hasPropFibers→isEmbedding prop-fibers where
    --   prop-fibers : (s : C.Shape) → isProp (fiber (C.sk ∘ ∣_∣₂) s)
    --   prop-fibers s (s₁ , p₁) (s₂ , p₂) = Sigma.ΣPathP ({! !} , {! !}) where
    --     foo : C.sk ∣ s₁ ∣₂ ≡ C.sk ∣ s₂ ∣₂
    --     foo = p₁ ∙ sym p₂

    conn-path-equivariant' : ∀ (s : C.Shape) → (x y : fiber ∣_∣₂ ∣ s ∣₂) → (x .fst ≡ y .fst) ≃ (C.sk ∣ s ∣₂ ≡ C.sk ∣ s ∣₂)
    conn-path-equivariant' s (s₀ , p₀) (s₁ , p₁) =
        (s₀ ≡ s₁) ≃⟨ cong (C.sk ∘ ∣_∣₂) , assumption _ _ ⟩
        (C.sk ∣ s₀ ∣₂ ≡ C.sk ∣ s₁ ∣₂) ≃⟨ substEquiv (λ · → C.sk · ≡ C.sk ∣ s₁ ∣₂) p₀ ⟩
        (C.sk ∣ s ∣₂ ≡ C.sk ∣ s₁ ∣₂) ≃⟨  substEquiv (λ · → C.sk ∣ s ∣₂ ≡ C.sk · ) p₁  ⟩
        (C.sk ∣ s ∣₂ ≡ C.sk ∣ s ∣₂) ≃∎

    conn-path-equivariant : ∀ c → (x y : fiber ∣_∣₂ c) → (x .fst ≡ y .fst) ≃ (C.sk c ≡ C.sk c)
    conn-path-equivariant = ST.elim
      (λ _ → isSetΠ2 λ x y → isOfHLevel⁺≃ᵣ 1 (C.is-groupoid-shape (C.sk _) (C.sk _)))
      conn-path-equivariant'

    -- Pos-β : ∀ (s : C.Shape) → (p : s ≡ s) → cong C.Pos p ≡ refl {x = C.Pos s}
    -- Pos-β s p =
    --   cong C.Pos p ≡⟨⟩
    --   cong (⟨_⟩ ∘ C.PosSetTotal ∘ equivFun C.TotalEquiv) p ≡⟨ {! !} ⟩
    --   refl ∎

    {- C.Pos is a 2-truncated map (cong C.Pos is an embedding) -}
    is-2-trunc-Pos : ∀ {s : C.Shape} → isEmbedding (cong {x = s} {y = s} C.Pos)
    -- is-2-trunc-Pos {s} = injEmbedding (isOfHLevel≡ 2 (C.isSetPos s) (C.isSetPos s)) {!C.Pos !}
    is-2-trunc-Pos {s} = hasPropFibers→isEmbedding prop-fibers where
      prop-fibers : (q : C.Pos s ≡ C.Pos s) → isProp (fiber (cong C.Pos) q)
      prop-fibers q = isPropΣ {! !} {! !}

    congPosEmbedding : ∀ {s : C.Shape} → (s ≡ s) ↪ (C.Pos s ≡ C.Pos s)
    congPosEmbedding .fst = cong C.Pos
    congPosEmbedding .snd = is-2-trunc-Pos

    ShapePath≃PosImage : ∀ {s : C.Shape} → (s ≡ s) ≃ Image (cong {x = s} {y = s} C.Pos)
    ShapePath≃PosImage .fst = restrictToImage (cong C.Pos)
    ShapePath≃PosImage .snd = isEquivEmbeddingOntoImage congPosEmbedding

    bruteforce : ∀ {c : ∥ C.Shape ∥₂} → (fiber ∣_∣₂ c) ≃ Image (cong {x = C.sk c} {y = C.sk c} C.Pos)
    bruteforce {c} =
      (fiber ∣_∣₂ c) ≃⟨ substEquiv (fiber ∣_∣₂) (sym $ C.sk-section c) ⟩
      (fiber ∣_∣₂ ∣ C.sk c ∣₂) ≃⟨ Sigma.Σ-cong-equiv-snd (λ _ → PathSetTrunc≃PropTruncPath) ⟩
      (Σ[ s ∈ C.Shape ] PT.∥ s ≡ C.sk c ∥₁) ≃⟨ Sigma.Σ-cong-equiv-prop go {! !} {! !} {! !} {! !} ⟩
      Σ[ σ ∈ C.Pos (C.sk c) ≡ C.Pos (C.sk c) ] ∃[ p ∈ C.sk c ≡ C.sk c ] cong C.Pos p ≡ σ ≃⟨⟩
      Image (cong {x = C.sk c} {y = C.sk c} C.Pos) ≃∎
      where
        go : C.Shape ≃ (↓C.Pos c ≡ ↓C.Pos c)
        go .fst s = {! !}
        go .snd = {! !}

    group-equiv : GroupEquiv ShapeFiberGroup 𝔹SymmGroup
    group-equiv .GroupEquiv.hom = hom
    group-equiv .GroupEquiv.is-emb-hom = isCancellable→isEmbedding equiv where
      equiv : ∀ (w x : Σ[ s ∈ C.Shape ] ∣ s ∣₂ ≡ c) → (w ≡ x) ≃ (𝔹.⋆ ≡ 𝔹.⋆)
      equiv w x =
        (w ≡ x)                                                             ≃⟨ invEquiv (Sigma.Σ≡PropEquiv λ s → ST.isSetSetTrunc _ _) ⟩
        ((w .fst) ≡ (x .fst))                                               ≃⟨ conn-path-equivariant c w x ⟩
        C.sk c ≡ C.sk c                                                     ≃⟨ ShapePath≃PosImage ⟩
        Image (cong {x = C.sk c} {y = C.sk c} C.Pos)                        ≃⟨ invEquiv $ postCompEquiv→imagesEquiv univalence ⟩
        Image (pathToEquiv ∘ cong {x = C.sk c} {y = C.sk c} C.Pos)          ≃⟨⟩
        Σ[ σ ∈ ↓C.Pos c ≃ ↓C.Pos c ] isInImage (pathToEquiv ∘ cong C.Pos) σ ≃⟨⟩
        (↓C.Symm c)                                                         ≃⟨ invEquiv (↑↓C.↑SymmElim.ΩDelooping≃ c) ⟩
        (𝔹.⋆ ≡ 𝔹.⋆) ≃∎
    group-equiv .GroupEquiv.pres-pt = refl {x = 𝔹.⋆}

  shape-path : ↑↓C.↑Shape ≡ C.Shape
  shape-path = sym $ ua equiv where
    equiv : C.Shape ≃ Σ ∥ C.Shape ∥₂ ↑↓C.↑Symm
    equiv =
      C.Shape ≃⟨ componentEquiv C.Shape ⟩
      Σ ∥ C.Shape ∥₂ (fiber ∣_∣₂) ≃⟨ Sigma.Σ-cong-equiv-snd delooping-equiv ⟩
      Σ ∥ C.Shape ∥₂ ↑↓C.↑Symm ≃∎

  -- thm : ↑↓C ≡ C
  -- thm i .Coffin.Shape = shape-path i
  -- thm i .Coffin.is-groupoid-shape = {! !}
  -- thm i .Coffin.shape-skeleton = {! !}
  -- thm i .Coffin.componentGroupSet = {! !}

