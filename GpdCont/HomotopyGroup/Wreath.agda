module GpdCont.HomotopyGroup.Wreath where

open import GpdCont.Prelude
open import GpdCont.Embedding
open import GpdCont.Equiv
open import GpdCont.Connectivity
open import GpdCont.HomotopySet
open import GpdCont.HomotopyGroup.Base
open import GpdCont.HomotopyGroup.Aut
open import GpdCont.HomotopyGroup.Morphism
open import GpdCont.HomotopyGroup.Equiv
open import GpdCont.HomotopyGroup.Action
open import GpdCont.HomotopyGroup.Subgroup
open import GpdCont.HomotopyGroup.Subaction
open import GpdCont.HomotopyGroup.Pi
import      GpdCont.SetTruncation as ST

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (equivAdjointEquiv)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.CartesianKanOps
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)
import      Cubical.HITs.PropositionalTruncation as PT

private
  variable
    ℓ ℓ′ ℓX ℓY : Level

open hGroupHom using (fun)
open hGroupMono using (hom ; fun ; is-mono)

module _ (G : hGroup ℓ) (H : ⟨ G ⟩ᵗ → hGroup ℓ′) where
  private
    module G = hGroup G
    module H g = hGroup (H g)

  _⋉_ : hGroup (ℓ-max ℓ ℓ′)
  _⋉_ = pointedConnectedGroupoid→hGroup ΣGH pt is-conn-ΣGH is-groupoid-ΣGH where
    ΣGH : Type _
    ΣGH = Σ[ g ∈ ⟨ G ⟩ᵗ ] ⟨ H g ⟩ᵗ

    pt : ΣGH
    pt .fst = G.pt₀
    pt .snd = H.pt₀ _

    is-conn-ΣGH : isPathConnected ΣGH
    is-conn-ΣGH = isPathConnectedΣ G.is-connected H.is-connected

    is-groupoid-ΣGH : isGroupoid ΣGH
    is-groupoid-ΣGH = isGroupoidΣ G.is-groupoid H.is-groupoid

  private
    G⋉H = _⋉_
    {-# INLINE G⋉H #-}

  ⋉-projl : hGroupHom G⋉H G
  ⋉-projl .fun = fst
  ⋉-projl .hGroupHom.pres-pt₀ = refl

  ⋉-inlr : hGroupHom (H G.pt₀) G⋉H
  ⋉-inlr .fun h = _ , h
  ⋉-inlr .hGroupHom.pres-pt₀ = refl

{-# INJECTIVE_FOR_INFERENCE _⋉_ #-}

⋉-syntax : (G : hGroup ℓ) (H : ⟨ G ⟩ᵗ → hGroup ℓ′) → hGroup (ℓ-max ℓ ℓ′)
⋉-syntax = _⋉_

infix 5 ⋉-syntax
syntax ⋉-syntax G (λ g → H) = ⋉[ g ∈ G ] H

module _ {ℓG₀ ℓG₁ ℓH}
  {G₀ : hGroup ℓG₀}
  {G₁ : hGroup ℓG₁}
  (H : ⟨ G₁ ⟩ᵗ → hGroup ℓH)
  where

  ⋉-map-fst : (φ : hGroupHom G₀ G₁) → hGroupHom (G₀ ⋉ (H ∘ φ .fun)) (G₁ ⋉ H)
  ⋉-map-fst φ .fun = Σ-map-fst (φ .fun)
  ⋉-map-fst φ .hGroupHom.pres-pt₀ = ΣPathP λ where
    .fst → hGroupHom.pres-pt₀ φ
    .snd i → hGroup.pt₀ (H _)

  ⋉-map-fst-mono : (ι : hGroupMono G₀ G₁) → hGroupMono (G₀ ⋉ (H ∘ (hGroupMono.fun ι))) (G₁ ⋉ H)
  ⋉-map-fst-mono ι .hom = ⋉-map-fst (ι .hom)
  ⋉-map-fst-mono ι .is-mono = isOfHLevelFunMapFst 2 (ι .fun) (ι .is-mono)
  {-# INJECTIVE_FOR_INFERENCE ⋉-map-fst-mono #-}

⋉FstMono : ∀ {ℓ₀} (G : hGroup ℓ) (H : ⟨ G ⟩ᵗ → hGroup ℓ′)
  → (G₀ : Mono ℓ₀ G)
  → Mono (ℓ-max ℓ′ ℓ₀) (G ⋉ H)
⋉FstMono G H (G₀ , ι) .fst = G₀ ⋉ (H ∘ ι .hGroupMono.fun)
⋉FstMono G H (G₀ , ι) .snd = ⋉-map-fst-mono H ι

module _ {ℓG ℓH₀ ℓH₁}
  (G : hGroup ℓG)
  {H₀ : ⟨ G ⟩ᵗ → hGroup ℓH₀}
  {H₁ : ⟨ G ⟩ᵗ → hGroup ℓH₁}
  where
  private
    module G = hGroup G

  ⋉-map-snd : (φ : ∀ g → hGroupHom (H₀ g) (H₁ g)) → hGroupHom (G ⋉ H₀) (G ⋉ H₁)
  ⋉-map-snd φ .fun = Σ-map-snd (hGroupHom.fun ∘ φ)
  ⋉-map-snd φ .hGroupHom.pres-pt₀ = ΣPathP λ where
    .fst → refl′ G.pt₀
    .snd → hGroupHom.pres-pt₀ (φ G.pt₀)

  ⋉-map-snd-mono : (ι : ∀ g → hGroupMono (H₀ g) (H₁ g)) → hGroupMono (G ⋉ H₀) (G ⋉ H₁)
  ⋉-map-snd-mono ι .hom = ⋉-map-snd (hom ∘ ι)
  ⋉-map-snd-mono ι .is-mono = isOfHLevelFunMapSnd 2 (hGroupMono.fun ∘ ι) (is-mono ∘ ι)
  {-# INJECTIVE_FOR_INFERENCE ⋉-map-snd-mono #-}

module _ {ℓG₀ ℓG₁ ℓH₀ ℓH₁}
  (G₀ : hGroup ℓG₀)
  (G₁ : hGroup ℓG₁)
  (H₀ : ⟨ G₀ ⟩ᵗ → hGroup ℓH₀)
  (H₁ : ⟨ G₁ ⟩ᵗ → hGroup ℓH₁)
  where
  ⋉-map : (φ : hGroupHom G₀ G₁) (ψ : ∀ g → hGroupHom (H₀ g) (H₁ (φ .fun g))) → hGroupHom (G₀ ⋉ H₀) (G₁ ⋉ H₁)
  ⋉-map φ ψ = (⋉-map-snd G₀ ψ) ∙ᴳ (⋉-map-fst H₁ φ)

  ⋉-map-mono : (ι : hGroupMono G₀ G₁) (κ : ∀ g → hGroupMono (H₀ g) (H₁ (hGroupMono.fun ι g))) → hGroupMono (G₀ ⋉ H₀) (G₁ ⋉ H₁)
  ⋉-map-mono ι κ = compHGroupMono
    (⋉-map-snd-mono G₀ κ)
    (⋉-map-fst-mono H₁ ι)

⋉-contractSnd : (G : hGroup ℓ) (H : ⟨ G ⟩ᵗ → hGroup ℓ′)
  → (∀ g → isTrivial (H g))
  → hGroupEquiv (G ⋉ H) G
⋉-contractSnd G H is-contr-H = mkHGroupEquiv (G ⋉ H) G (Σ-contractSnd is-contr-H) pres-pt₀ where
  pres-pt₀ : hGroup.pt₀ (G ⋉ H) .fst ≡ hGroup.pt₀ G
  pres-pt₀ = refl

module _ (G : hGroup ℓ) (H : ⟨ G ⟩ᵗ → hGroup ℓ′) where
  private
    module G = hGroup G
    module H g = hGroup (H g)

  isContrFst→⋉-contractFst : ((g₀ , _) : isContr ⟨ G ⟩ᵗ) → hGroupEquiv (G ⋉ H) (H g₀)
  isContrFst→⋉-contractFst is-contr-G@(g₀ , _) = mkHGroupEquiv _ _ contr-equiv pres-pt₀
    where
      contr-equiv : ⟨ G ⋉ H ⟩ᵗ ≃ ⟨ H g₀ ⟩ᵗ
      contr-equiv = Σ-contractFst is-contr-G

      pres-pt⁻ : (G.pt₀ , H.pt₀ (G.pt₀)) ≡ (g₀ , H.pt₀ g₀)
      pres-pt⁻ = sym $ ΣPathP λ where
        .fst → is-contr-G .snd G.pt₀
        .snd i → H.pt₀ _

      pres-pt₀ : equivFun contr-equiv (G.pt₀ , H.pt₀ _) ≡ H.pt₀ g₀
      pres-pt₀ = equivFun (equivAdjointEquiv contr-equiv) pres-pt⁻

  ⋉-contractFst : isTrivial G → hGroupEquiv (G ⋉ H) (H G.pt₀)
  ⋉-contractFst is-contr-G = isContrFst→⋉-contractFst (inhProp→isContr G.pt₀ (isContr→isProp is-contr-G))

module _
  (G : hGroup ℓ)
  (X : hAction ℓX G)
  (H : ⟨ G ⟩ᵗ → hGroup ℓ′)
  (Y : {g : ⟨ G ⟩ᵗ} → ⟨ X g ⟩ → hAction ℓY (H g))
  where
  ⋉Action : hAction (ℓ-max ℓX ℓY) (G ⋉ H)
  ⋉Action (g , h) = ΣSet (X g) λ x → Y x h

  {-
  isFaithful-⋉Action
    : isFaithful G X
    → (∀ g x → isFaithful (H g) (Y x))
    → isFaithful (G ⋉ H) ⋉Action
  isFaithful-⋉Action is-faithful-X is-faithful-Y Z = isOfHLevelRespectEquiv 2 (invEquiv fiber-equiv) {! !} where
    fiber-equiv : fiber ⋉Action Z ≃ {! !}
    fiber-equiv =
      fiber ⋉Action Z ≃⟨ {! !} ⟩
      Σ[ (g , h) ∈ ⟨ G ⋉ H ⟩ᵗ ] (ΣSet (X g) (λ x → Y x h)) ≡ Z ≃⟨ Σ-assoc-≃ ⟩
      Σ[ g ∈ ⟨ G ⟩ᵗ ] Σ[ h ∈ ⟨ H g ⟩ᵗ ] (ΣSet (X g) (λ x → Y x h)) ≡ Z ≃⟨ {!Z!} ⟩
      Σ[ g ∈ ⟨ G ⟩ᵗ ] Σ[ (X' , p) ∈ Σ[ X' ∈ hSet _ ] X g ≡ X' ] Σ[ h ∈ ⟨ H g ⟩ᵗ ] (ΣSet X' (λ x → Y (subst ⟨_⟩ (sym p) x) h)) ≡ Z ≃⟨ {!Z!} ⟩
      {! !} ≃∎

  ⋉Subgroup' : Subgroup {! !} (Sym {! ΣSet !})
  ⋉Subgroup' = {! !}
  -}


module _ (G : hGroup ℓ) (X : hAction ℓX G) (H : hGroup ℓ′) where
  private
    module G = hGroup G
    module H = hGroup H

    [X,H] : ⟨ G ⟩ᵗ → hGroup _
    [X,H] g = FunGroup ⟨ X g ⟩ H
    {-# INLINE [X,H] #-}

    [X,H]-embedding : ∀ g → ⟨ [X,H] g ⟩ᵗ ↪ (⟨ X g ⟩ → ⟨ H ⟩ᵗ)
    [X,H]-embedding g = FunGroupEmbedding ⟨ X g ⟩ H

  Wr : hGroup _
  Wr = G ⋉ [X,H]

  _≀[_]_ : hGroup (ℓ-max (ℓ-max ℓ ℓX) ℓ′)
  _≀[_]_ = Wr

  Wr-projl : hGroupHom Wr G
  Wr-projl = ⋉-projl G [X,H]

  Wr-projr : (x : ∀ g → ⟨ X g ⟩) → hGroupHom Wr H
  Wr-projr x .fun (g , aut η) = η (x g)
  Wr-projr x .hGroupHom.pres-pt₀ = refl

  module _ {ℓY} (Y : hAction ℓY H) where
    private
      Y* : {g : ⟨ G ⟩ᵗ} → ⟨ X g ⟩ → hAction _ ([X,H] g)
      Y* {g} x = uncurry λ (f : ⟨ X g ⟩ → ⟨ H ⟩ᵗ) _ → Y (f x)
      {-# INLINE Y* #-}

    {-
      is-transitive-Y* : isTransitive H Y → ∀ g x → isTransitive ([X,H] g) (Y* x)
      is-transitive-Y* trans-Y g x = {! isPathConnectedRespectEquiv' {! !} $
        ⟨ ∫ ([X,H] g) (Y* x) ⟩ ≃⟨⟩
        Σ[ (h , _) ∈ ⟨ [X,H] g ⟩ᵗ ] ⟨ Y (h x) ⟩ ≃⟨ Σ-assoc-≃ ⟩
        Σ[ h ∈ (⟨ X g ⟩ → ⟨ H ⟩ᵗ) ] (∣ h ∣₂ ≡ ∣ const H.pt₀ ∣₂) × ⟨ Y (h x) ⟩ ≃⟨ {! !} ⟩
        {! !} ≃∎
        !}

      is-faithful-Y* : isFaithful H Y → ∀ g x → isFaithful ([X,H] g) (Y* x)
      is-faithful-Y* is-faithful-Y = G.elimProp (λ g → isPropΠ λ x → isPropIsFaithful ([X,H] g) _) goal where
        module _ (x₀ : ⟨ X (G.pt₀) ⟩) (Z : hSet ℓY) where
          -- IDEA: Embed the fibers into a set (by dropping the second component of (h : ⟨ [X,H] ⟩ᵗ))
          fiber-embed : fiber (Y* x₀) Z ↪ (Σ[ h ∈ (⟨ X (G.pt₀) ⟩ → ⟨ H ⟩ᵗ) ] Y (h x₀) ≡ Z)
          fiber-embed = Σ-embed-fst ([X,H]-embedding _)

          ev₀ : (⟨ X (G.pt₀) ⟩ → ⟨ H ⟩ᵗ) → ⟨ H ⟩ᵗ
          ev₀ f = f x₀

          ev₀-fiber-equiv : (fiber ev₀ H.pt₀) ≃ {! !}
          ev₀-fiber-equiv =
            Σ[ f ∈ _ ] f x₀ ≡ H.pt₀ ≃⟨ {! !} ⟩
            {! !} ≃∎

          is-set-fiber-ev₀ : ∀ h → isSet (fiber ev₀ h)
          is-set-fiber-ev₀ = H.elimProp {! !} λ where
            (f₀ , p₀) → {! !}

          -- ev₀-fiber : ∀ h → fiber ev₀ h ≃ {! !}
          -- ev₀-fiber h =
          --   Σ[ f ∈ _ ] f x₀ ≡ h ≃⟨ {! !} ⟩
          --   {! !} ≃∎

          charac : (Σ[ h ∈ (⟨ X (G.pt₀) ⟩ → ⟨ H ⟩ᵗ) ] Y (h x₀) ≡ Z) ≃ Unit
          charac =
            (Σ[ f ∈ (⟨ X (G.pt₀) ⟩ → ⟨ H ⟩ᵗ) ] Y (f x₀) ≡ Z) ≃⟨ {! !} ⟩
            (Σ[ f ∈ (⟨ X (G.pt₀) ⟩ → ⟨ H ⟩ᵗ) ] Σ[ (h , _) ∈ singl (f x₀) ] Y h ≡ Z) ≃⟨ {! !} ⟩
            (Σ[ f ∈ (⟨ X (G.pt₀) ⟩ → ⟨ H ⟩ᵗ) ] Σ[ (h , _) ∈ fiber Y Z ] h ≡ f x₀) ≃⟨ {! !} ⟩
            (Σ[ (h , _) ∈ fiber Y Z ] Σ[ f ∈ (⟨ X (G.pt₀) ⟩ → ⟨ H ⟩ᵗ) ] h ≡ f x₀) ≃⟨ {! !} ⟩
            (Σ[ (h , _) ∈ fiber Y Z ] fiber ev₀ h) ≃⟨ {! !} ⟩
            {! !} ≃∎

          ev₀' : ⟨ [X,H] G.pt₀ ⟩ᵗ → ⟨ H ⟩ᵗ
          ev₀' (f , _) = f x₀

          fiber-equiv : (fiber (Y* x₀) Z) ≃ Unit
          fiber-equiv =
            (Σ[ (f , _) ∈ ⟨ [X,H] G.pt₀ ⟩ᵗ ] Y (f x₀) ≡ Z) ≃⟨ {! !} ⟩
            (Σ[ (f , _) ∈ ⟨ [X,H] G.pt₀ ⟩ᵗ ] Σ[ (h , _) ∈ singl (f x₀) ] Y h ≡ Z) ≃⟨ {! !} ⟩
            (Σ[ (f , _) ∈ ⟨ [X,H] G.pt₀ ⟩ᵗ ] Σ[ (h , _) ∈ fiber Y Z ] h ≡ f x₀) ≃⟨ {! !} ⟩
            (Σ[ (h , _) ∈ fiber Y Z ] Σ[ (f , _) ∈ ⟨ [X,H] G.pt₀ ⟩ᵗ ] h ≡ f x₀) ≃⟨ {! !} ⟩
            (Σ[ (h , _) ∈ fiber Y Z ] fiber ev₀' h) ≃⟨ {! !} ⟩
            Unit ≃∎

          goal : isSet (fiber (Y* x₀) Z)
          goal = Embedding-into-hLevel→hLevel 1 fiber-embed {! !}
    -}

    WrAction : hAction (ℓ-max ℓX ℓY) Wr
    WrAction = ⋉Action G X [X,H] Y*

    WrAction× : hAction (ℓ-max ℓX ℓY) Wr
    WrAction× (g , (f , _)) = ΣSet (X g) (Y ∘ f)

    _ : (g : ⟨ G ⟩ᵗ) (h : ⟨ [X,H] g ⟩ᵗ) → ⟨ WrAction (g , h) ⟩ ≡ ⟨ WrAction× (g , h) ⟩
    _ = λ g h → refl

    {-
    isFaithfulWrAction :
        isFaithful G X
      → isFaithful H Y
      → isFaithful Wr WrAction
    isFaithfulWrAction is-faithful-X is-faithful-Y Z = {! isOfHLevelRespectEquiv 2 !} where
      fiber-equiv : fiber WrAction Z ≃ {! !}
      fiber-equiv =
        Σ[ x ∈ ⟨ Wr ⟩ᵗ ] WrAction x ≡ Z ≃⟨ Σ-assoc-≃ ⟩
        Σ[ g ∈ ⟨ G ⟩ᵗ ] Σ[ h ∈ ⟨ [X,H] g ⟩ᵗ ] (WrAction (g , h) ≡ Z) ≃⟨⟩
        Σ[ g ∈ ⟨ G ⟩ᵗ ] Σ[ h ∈ ⟨ [X,H] g ⟩ᵗ ] (ΣSet (X g) (Y ∘ (h .fst)) ≡ Z) ≃⟨ {! !} ⟩
        Σ[ g ∈ ⟨ G ⟩ᵗ ] Σ[ (Xᵍ , pᵍ) ∈ singl (X g) ] Σ[ h ∈ ⟨ [X,H] g ⟩ᵗ ] Σ[ (Yʰ , _) ∈ singl (Y ∘ (h .fst)) ] (ΣSet Xᵍ (Yʰ ∘ subst ⟨_⟩ (sym pᵍ)) ≡ Z) ≃⟨ {! fiber X  !} ⟩
        -- Σ[ Xᵍ ∈ ⟨ G ⟩ᵗ ] Σ[ (Xᵍ , pᵍ) ∈ singl (X g) ] Σ[ h ∈ ⟨ [X,H] g ⟩ᵗ ] Σ[ (Yʰ , _) ∈ singl (Y ∘ (h .fst)) ] (ΣSet Xᵍ (Yʰ ∘ subst ⟨_⟩ (sym pᵍ)) ≡ Z) ≃⟨ {! !} ⟩
        {! !} ≃∎

    isFaithfulWrAction' :
        isFaithful G X
      → isFaithful H Y
      → isFaithful Wr WrAction
    isFaithfulWrAction' is-faithful-X is-faithful-Y Z w₀@((g₀ , h₀) , p₀) w₁@((g₁ , h₁) , p₁) = goal where
      goal : isProp (w₀ ≡ w₁)
      goal = {! !}

      path-equiv : (w₀ ≡ w₁) ≃ {! !}
      path-equiv =
        (w₀ ≡ w₁) ≃⟨ {! !} ⟩
        Σ[ q ∈ (g₀ , h₀) ≡ (g₁ , h₁) ] PathP (λ i → WrAction (q i) ≡ Z) p₀ p₁ ≃⟨ {! !} ⟩
        Σ[ qᵍ ∈ g₀ ≡ g₁ ] Σ[ qʰ ∈ PathP (λ i → ⟨ [X,H] (qᵍ i) ⟩ᵗ) h₀ h₁ ] PathP (λ i → WrAction (qᵍ i , qʰ i) ≡ Z) p₀ p₁ ≃⟨ {! !} ⟩
        {! !} ≃∎

    module _ (trans-X : isTransitive G X) (trans-Y : isTransitive H Y) where
      isTransitiveWrAction : isTransitive Wr WrAction
      isTransitiveWrAction = goal where
        shuffle : (Σ[ (g , x) ∈ ⟨ ∫ G X ⟩ ] ⟨ ∫ ([X,H] g) (Y* x) ⟩) ≃ ⟨ ∫ Wr WrAction ⟩
        shuffle = strictEquiv
          (λ { ((g , x) , (h , y)) → ((g , h) , (x , y)) })
          (λ { ((g , h) , (x , y)) → ((g , x) , (h , y)) })

        goal : isPathConnected ⟨ ∫ Wr WrAction ⟩
        goal = isPathConnectedRespectEquiv shuffle $ isPathConnectedΣ trans-X $ uncurry $ is-transitive-Y* trans-Y

      {-
        WrSubgroup : Subgroup (ℓ-max ℓX ℓY) Wr
        WrSubgroup .fst = WrAction
        WrSubgroup .snd .fst = {! !} , {! !}
        WrSubgroup .snd .snd = isTransitiveWrAction
      -}
    -}

  WrMono : ∀ {ℓG₀} → Mono ℓG₀ G → Mono (ℓ-max (ℓ-max ℓX ℓ′) ℓG₀) Wr
  WrMono = ⋉FstMono G [X,H]

  WrContractSnd : isTrivial H → hGroupEquiv Wr G
  WrContractSnd is-contr-H = ⋉-contractSnd G [X,H] is-contr-[X,H] where
    is-contr-[X,H] : ∀ g → isTrivial ([X,H] g)
    is-contr-[X,H] g = isContrFunGroup ⟨ X g ⟩ H is-contr-H

  WrContractFst : isTrivial G → hGroupEquiv Wr (FunGroup ⟨ X G.pt₀ ⟩ H)
  WrContractFst is-contr-G = ⋉-contractFst G [X,H] is-contr-G

  isTrivialAction→WrContractFst : isTrivial G → isContr ⟨ X G.pt₀ ⟩ → hGroupEquiv Wr H
  isTrivialAction→WrContractFst is-contr-G is-contr-X =
    Wr          ≃ᴳ⟨ WrContractFst is-contr-G ⟩
    [X,H] G.pt₀ ≃ᴳ⟨ FunGroupContractDomain ⟨ X G.pt₀ ⟩ H is-contr-X ⟩
    H ∎ᴳ

{- TODO: Figure out why the definitions below are so slow to typecheck
module _ {ℓG₀ ℓG₁ ℓX ℓH}
  {G₀ : hGroup ℓG₀}
  {G₁ : hGroup ℓG₁}
  (X : hAction ℓX G₁)
  (H : hGroup ℓH)
  where
  private
    module H = hGroup H

  ≀-map-fst : ∀ (φ : hGroupHom G₀ G₁) → hGroupHom (G₀ ≀[ X ∘ φ .fun ] H) (G₁ ≀[ X ] H)
  ≀-map-fst φ = ⋉-map-fst {G₀ = G₀} {G₁} (λ g₁ → FunGroup ⟨ X g₁ ⟩ H) φ

  ≀-map-fst-mono : ∀ (φ : hGroupMono G₀ G₁) → hGroupMono (G₀ ≀[ X ∘ hGroupMono.fun φ ] H) (G₁ ≀[ X ] H)
  ≀-map-fst-mono φ = {! ⋉-map-fst-mono (λ g₁ → FunGroup ⟨ X g₁ ⟩ H) φ !}

module _ {ℓG ℓX₀ ℓX₁ ℓH₀ ℓH₁}
  (G : hGroup ℓG)
  (X₀ : hAction ℓX₀ G)
  (X₁ : hAction ℓX₁ G)
  (H₀ : hGroup ℓH₀)
  (H₁ : hGroup ℓH₁)
  where
  private
    module G = hGroup G
    module H₀ = hGroup H₀
    module H₁ = hGroup H₁

  ≀-map-snd :
    ∀ (f : ∀ g → ⟨ X₁ g ⟩ → ⟨ X₀ g ⟩)
    → (ψ : hGroupHom H₀ H₁)
    → hGroupHom (G ≀[ X₀ ] H₀) (G ≀[ X₁ ] H₁)
  ≀-map-snd f ψ = ⋉-map-snd G (λ g → FunGroup ⟨ X₀ g ⟩ H₀) (λ g → FunGroup ⟨ X₁ g ⟩ H₁) ψ* module ≀-map-snd where
    ψ* : ∀ g → hGroupHom (FunGroup ⟨ X₀ g ⟩ H₀) (FunGroup ⟨ X₁ g ⟩ H₁)
    ψ* g = aut-map _ _ (λ η₀ → ψ .fun ∘ η₀ ∘ f g) (funExt λ _ → hGroupHom.pres-pt₀ ψ)

  ≀-map-snd-mono :
    ∀ (f : ∀ g → ⟨ X₁ g ⟩ → ⟨ X₀ g ⟩)
    → (∀ g → isEquiv (f g))
    → (ψ : hGroupMono H₀ H₁)
    → hGroupMono (G ≀[ X₀ ] H₀) (G ≀[ X₁ ] H₁)
  ≀-map-snd-mono f is-equiv-f ψ = ⋉-map-snd-mono G (λ g → FunGroup ⟨ X₀ g ⟩ H₀) (λ g → FunGroup ⟨ X₁ g ⟩ H₁) ψ* where
    fiber-equiv : ∀ g → ((x₀ : ⟨ X₀ g ⟩) → fiber (hGroupMono.fun ψ) H₁.pt₀) ≃ fiber (λ η₀ → hGroupMono.fun ψ ∘ η₀ ∘ f g) (const H₁.pt₀)
    fiber-equiv g =
      ((x₀ : ⟨ X₀ g ⟩) → Σ[ h₀ ∈ ⟨ H₀ ⟩ᵗ ] (hGroupMono.fun ψ h₀ ≡ H₁.pt₀))
        ≃⟨ Σ-Π-≃ ⟩
      Σ[ η₀ ∈ (⟨ X₀ g ⟩ → ⟨ H₀ ⟩ᵗ) ] (∀ x₀ → hGroupMono.fun ψ (η₀ x₀) ≡ H₁.pt₀)
        ≃⟨ Σ-cong-equiv-snd (λ η₀ → equivΠDomain (f g , is-equiv-f g)) ⟩
      Σ[ η₀ ∈ (⟨ X₀ g ⟩ → ⟨ H₀ ⟩ᵗ) ] (∀ x₁ → hGroupMono.fun ψ (η₀ (f g x₁)) ≡ H₁.pt₀)
        ≃⟨ Σ-cong-equiv-snd (λ η₀ → funExtEquiv) ⟩
      Σ[ η₀ ∈ (⟨ X₀ g ⟩ → ⟨ H₀ ⟩ᵗ) ] (hGroupMono.fun ψ ∘ η₀ ∘ f g ≡ const H₁.pt₀)
        ≃∎

    is-set-fiber-f* : ∀ g → isSet (fiber (λ η₀ → hGroupMono.fun ψ ∘ η₀ ∘ f g) (const H₁.pt₀))
    is-set-fiber-f* g = isOfHLevelRespectEquiv 2 (fiber-equiv g) $ isSetΠ λ x₀ → ψ .snd _

    ψ* : ∀ g → hGroupMono (FunGroup ⟨ X₀ g ⟩ H₀) (FunGroup ⟨ X₁ g ⟩ H₁)
    ψ* g = aut-map-mono _ _ (λ η₀ → hGroupMono.fun ψ ∘ η₀ ∘ f g)
      (funExt λ _ → hGroupHom.pres-pt₀ (ψ .fst))
      (is-set-fiber-f* g)

module _ {ℓG₀ ℓG₁ ℓX₀ ℓX₁ ℓH₀ ℓH₁}
  (G₀ : hGroup ℓG₀)
  (G₁ : hGroup ℓG₁)
  (X₀ : hAction ℓX₀ G₀)
  (X₁ : hAction ℓX₁ G₁)
  (H₀ : hGroup ℓH₀)
  (H₁ : hGroup ℓH₁)
  where
  private
    module H₀ = hGroup H₀
    module H₁ = hGroup H₁

  ≀-map :
    ∀ (φ : hGroupHom G₀ G₁)
    → (f : ∀ g → ⟨ X₁ (φ .fun g) ⟩ → ⟨ X₀ g ⟩)
    → (ψ : hGroupHom H₀ H₁)
    → hGroupHom (G₀ ≀[ X₀ ] H₀) (G₁ ≀[ X₁ ] H₁)
  ≀-map φ f ψ = ⋉-map G₀ G₁ (λ g₀ → FunGroup ⟨ X₀ g₀ ⟩ H₀) (λ g₁ → FunGroup ⟨ X₁ g₁ ⟩ H₁) φ ψ* module ≀-map where
    module _ (g : ⟨ G₀ ⟩ᵗ) where
      f* : (⟨ X₀ g ⟩ → ⟨ H₀ ⟩ᵗ) → (⟨ X₁ (φ .fun g) ⟩ → ⟨ H₁ ⟩ᵗ)
      f* η₀ = ψ .fun ∘ η₀ ∘ (f g)

      f*-pres-pt₀ : f* (λ _ → hGroup.pt₀ H₀) ≡ (λ _ → H₁.pt₀)
      f*-pres-pt₀ = funExt λ _ → hGroupHom.pres-pt₀ ψ

      ψ* : hGroupHom (FunGroup ⟨ X₀ g ⟩ H₀) (FunGroup ⟨ X₁ (φ .fun g) ⟩ H₁)
      ψ* = aut-map _ _ f* f*-pres-pt₀

  ≀-map-mono :
    ∀ (φ : hGroupMono G₀ G₁)
    → (f : ∀ g → ⟨ X₁ (hGroupMono.fun φ g) ⟩ ≃ ⟨ X₀ g ⟩)
    → (ψ : hGroupMono H₀ H₁)
    → hGroupMono (G₀ ≀[ X₀ ] H₀) (G₁ ≀[ X₁ ] H₁)
  ≀-map-mono φ f ψ = compHGroupMono (G₀ ≀[ X₀ ] H₀) (G₀ ≀[ X₁ ∘ _ ] H₁) (G₁ ≀[ X₁ ] H₁)
      (≀-map-snd-mono G₀ X₀ (X₁ ∘ _) H₀ H₁ (fst ∘ f) (snd ∘ f) ψ)
      (≀-map-fst-mono G₀ G₁ X₁ H₁ φ)
-}
