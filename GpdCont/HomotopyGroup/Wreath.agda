module GpdCont.HomotopyGroup.Wreath where

open import GpdCont.Prelude
open import GpdCont.Embedding
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

open import GpdCont.StrictGroupoid.Base
import      GpdCont.SetTruncation as ST

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.CartesianKanOps
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)
import      Cubical.HITs.PropositionalTruncation as PT

private
  variable
    ℓ ℓ′ ℓX ℓY : Level

_⋉_ : (G : hGroup ℓ) (H : ⟨ G ⟩ᵗ → hGroup ℓ′) → hGroup (ℓ-max ℓ ℓ′)
G ⋉ H = pointedConnectedGroupoid→hGroup ΣGH pt is-conn-ΣGH is-groupoid-ΣGH where
  module G = hGroup G
  module H g = hGroup (H g)

  ΣGH : Type _
  ΣGH = Σ[ g ∈ ⟨ G ⟩ᵗ ] ⟨ H g ⟩ᵗ

  pt : ΣGH
  pt .fst = G.pt₀
  pt .snd = H.pt₀ _

  is-conn-ΣGH : isPathConnected ΣGH
  is-conn-ΣGH = isPathConnectedΣ G.is-connected H.is-connected

  is-groupoid-ΣGH : isGroupoid ΣGH
  is-groupoid-ΣGH = isGroupoidΣ G.is-groupoid H.is-groupoid

⋉Mono : ∀ {ℓ₀} (G : hGroup ℓ) (H : ⟨ G ⟩ᵗ → hGroup ℓ′)
  → (G₀ : Mono ℓ₀ G)
  → Mono (ℓ-max ℓ′ ℓ₀) (G ⋉ H)
⋉Mono G H (G₀ , ((ι , ι-hom) , ι-mono)) = goal where
  module G₀ = hGroup G₀
  module G = hGroup G
  module H g = hGroup (H g)

  G₀⋉H : hGroup _
  G₀⋉H = G₀ ⋉ (H ∘ ι)

  ι* : ⟨ G₀⋉H ⟩ᵗ → ⟨ G ⋉ H ⟩ᵗ
  ι* = Σ-map-fst ι

  ι*-hom : hGroupHom G₀⋉H (G ⋉ H)
  ι*-hom = mkHGroupHom G₀⋉H (G ⋉ H) ι* pres-pt₀ where
    ι-pres-pt : ι G₀.pt₀ ≡ G.pt₀
    ι-pres-pt = hGroupHom.pres-pt₀ G₀ G (ι , ι-hom)

    pres-pt₀ : ι* (G₀.pt₀ , H.pt₀ _) ≡ (G.pt₀ , H.pt₀ _)
    pres-pt₀ = ΣPathP λ where
      .fst → ι-pres-pt
      .snd i → H.pt (ι-pres-pt i) $
        isProp→PathP {B = λ i → H.Tr (ι-pres-pt i)} (λ i → isContr→isProp (H.is-connected _)) (H.center (ι G₀.pt₀)) (hGroup.center (H G.pt₀)) i

  ι*-mono : isMono G₀⋉H (G ⋉ H) ι*-hom
  ι*-mono = isOfHLevelFunMapFst 2 ι ι-mono

  goal : Mono _ (G ⋉ H)
  goal .fst = G₀⋉H
  goal .snd .fst = ι*-hom
  goal .snd .snd = ι*-mono

⋉-map : ∀ {ℓG₀ ℓG₁ ℓH₀ ℓH₁}
  → (G₀ : hGroup ℓG₀)
  → (H₀ : ⟨ G₀ ⟩ᵗ → hGroup ℓH₀)
  → (G₁ : hGroup ℓG₁)
  → (H₁ : ⟨ G₁ ⟩ᵗ → hGroup ℓH₁)
  → (φ : hGroupHom G₀ G₁)
  → (η : ∀ g₀ → hGroupHom (H₀ g₀) (H₁ (φ .fst g₀)))
  → hGroupHom (G₀ ⋉ H₀) (G₁ ⋉ H₁)
⋉-map G₀ H₀ G₁ H₁ φ η = goal
  {-
  where
    module φ = hGroupHom G₀ G₁ φ
    module H₀ {g₀} = hGroup (H₀ g₀)
    module H₁ {g₁} = hGroup (H₁ g₁)
    module η {g₀} = hGroupHom (H₀ g₀) (H₁ (φ.fun g₀)) (η g₀)

    goal : hGroupHom (G₀ ⋉ H₀) (G₁ ⋉ H₁)
    goal .fst (g₀ , h₀) = φ.fun g₀ , η.fun h₀
    goal .snd = funExt $ ST.elim {! !} $
      uncurry λ g₀ h₀ → ΣPathP (sym φ.pres-pt₀ , {! !})
  -}
  where
    module G₀ = hGroup G₀
    module G₁ = hGroup G₁
    module φ = hGroupHom G₀ G₁ φ
    module H₀ {g₀} = hGroup (H₀ g₀)
    module H₁ {g₁} = hGroup (H₁ g₁)
    module η {g₀} = hGroupHom (H₀ g₀) (H₁ (φ.fun g₀)) (η g₀)

    pres-pt₀' : transport (λ i → ⟨ H₁ (φ.pres-pt₀ i) ⟩ᵗ) (η.fun H₀.pt₀) ≡ H₁.pt₀
    pres-pt₀' = {! !}

    pres-pt₀ᴰ-gen : ∀ {g₁} → (p : g₁ ≡ G₁.pt₀) → PathP (λ i → ⟨ H₁ (p i) ⟩ᵗ) {! η.fun !} H₁.pt₀
    pres-pt₀ᴰ-gen = {! φ.pres-pt₀ !}

    pres-pt₀ᴰ : PathP (λ i → ⟨ H₁ (φ.pres-pt₀ i) ⟩ᵗ) (η.fun (H₀.pt₀)) H₁.pt₀
    pres-pt₀ᴰ = toPathP pres-pt₀'

    goal : hGroupHom (G₀ ⋉ H₀) (G₁ ⋉ H₁)
    goal = mkHGroupHom (G₀ ⋉ H₀) (G₁ ⋉ H₁)
      (λ { (g₀ , h₀) → φ.fun g₀ , η.fun h₀ })
      (ΣPathP (φ.pres-pt₀ , pres-pt₀ᴰ))
      -- (λ { (g₀ , h₀) → ? })

⋉-contractSnd : (G : hGroup ℓ) (H : ⟨ G ⟩ᵗ → hGroup ℓ′)
  → (∀ g → isTrivial (H g))
  → hGroupEquiv (G ⋉ H) G
⋉-contractSnd G H is-contr-H = mkHGroupEquiv (G ⋉ H) G (Σ-contractSnd is-contr-H) pres-pt₀ where
  pres-pt₀ : hGroup.pt₀ (G ⋉ H) .fst ≡ hGroup.pt₀ G
  pres-pt₀ = refl

module _ (G : hGroup ℓ) (H : ⟨ G ⟩ᵗ → hGroup ℓ′) where
  private
    module G = hGroup G

  isPropFst→⋉-contractFst : (is-prop-G : isProp ⟨ G ⟩ᵗ) → hGroupEquiv (H G.pt₀) (G ⋉ H)
  isPropFst→⋉-contractFst is-prop-G = mkHGroupEquiv (H G.pt₀) (G ⋉ H) contr-equiv refl
    where
      contr-equiv : ⟨ H G.pt₀ ⟩ᵗ ≃ ⟨ G ⋉ H ⟩ᵗ
      contr-equiv = invEquiv (Σ-contractFst (inhProp→isContr G.pt₀ is-prop-G))

  ⋉-contractFst : isTrivial G → hGroupEquiv (H G.pt₀) (G ⋉ H)
  ⋉-contractFst is-contr-G = isPropFst→⋉-contractFst (isContr→isProp is-contr-G)

module _
  (G : hGroup ℓ)
  (X : hAction ℓX G)
  (H : ⟨ G ⟩ᵗ → hGroup ℓ′)
  (Y : {g : ⟨ G ⟩ᵗ} → ⟨ X g ⟩ → hAction ℓY (H g))
  where
  ⋉Action : hAction (ℓ-max ℓX ℓY) (G ⋉ H)
  ⋉Action (g , h) = ΣSet (X g) λ x → Y x h

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


module _ (G : hGroup ℓ) (X : hAction ℓX G) (H : hGroup ℓ′) where
  private
    module G = hGroup G
    module H = hGroup H

    [X,H] : ⟨ G ⟩ᵗ → hGroup _
    [X,H] g = FunGroup ⟨ X g ⟩ H

    [X,H]-embedding : ∀ g → ⟨ [X,H] g ⟩ᵗ ↪ (⟨ X g ⟩ → ⟨ H ⟩ᵗ)
    [X,H]-embedding g = FunGroupEmbedding ⟨ X g ⟩ H

  Wr : hGroup (ℓ-max (ℓ-max ℓ ℓX) ℓ′)
  Wr = G ⋉ [X,H]

  _≀[_]_ : hGroup (ℓ-max (ℓ-max ℓ ℓX) ℓ′)
  _≀[_]_ = Wr

  module _ {ℓY} (Y : hAction ℓY H) where
    private
      Y* : {g : ⟨ G ⟩ᵗ} → ⟨ X g ⟩ → hAction _ ([X,H] g)
      Y* {g} x = uncurry λ (f : ⟨ X g ⟩ → ⟨ H ⟩ᵗ) _ → Y (f x)

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

    WrAction : hAction (ℓ-max ℓX ℓY) Wr
    WrAction = ⋉Action G X [X,H] Y*

    WrAction× : hAction (ℓ-max ℓX ℓY) Wr
    WrAction× (g , (f , _)) = ΣSet (X g) (Y ∘ f)

    _ : (g : ⟨ G ⟩ᵗ) (h : ⟨ [X,H] g ⟩ᵗ) → ⟨ WrAction (g , h) ⟩ ≡ ⟨ WrAction× (g , h) ⟩
    _ = λ g h → refl

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

  WrMonoSingle : ∀ {ℓG₀} → Mono ℓG₀ G → Mono _ Wr
  WrMonoSingle = ⋉Mono G [X,H]

  WrContractSnd : isTrivial H → hGroupEquiv Wr G
  WrContractSnd is-contr-H = ⋉-contractSnd G [X,H] is-contr-[X,H] where
    is-contr-[X,H] : ∀ g → isTrivial ([X,H] g)
    is-contr-[X,H] g = isContrFunGroup ⟨ X g ⟩ H is-contr-H

  WrContractFst : isTrivial G → hGroupEquiv Wr (FunGroup ⟨ X G.pt₀ ⟩ H)
  WrContractFst is-contr-G = invHGroupEquiv ([X,H] _) Wr (⋉-contractFst G [X,H] is-contr-G)

  isTrivialAction→WrContractFst : isTrivial G → isContr ⟨ X G.pt₀ ⟩ → hGroupEquiv Wr H
  isTrivialAction→WrContractFst is-contr-G is-contr-X = compHGroupEquiv Wr ([X,H] G.pt₀) H contr-fun contr-dom
    where
      contr-dom : hGroupEquiv ([X,H] G.pt₀) H
      contr-dom = FunGroupContractDomain ⟨ X G.pt₀ ⟩ H is-contr-X

      contr-fun : hGroupEquiv Wr ([X,H] G.pt₀)
      contr-fun = WrContractFst is-contr-G

WrMono : ∀ {ℓG₀ ℓX₀} (G : hGroup ℓ) (X : hAction ℓX G) (H : hGroup ℓ′)
  → (G₀ : hGroup ℓG₀)
  → (ι : hGroupHom G₀ G)
  → isMono G₀ G ι
  → (X₀ : hAction ℓX₀ G₀)
  → (e : ∀ g₀ → ⟨ X (ι .fst g₀) ⟩ ↪ ⟨ X₀ g₀ ⟩)
  → Mono (ℓ-max (ℓ-max ℓ′ ℓG₀) ℓX₀) (G ≀[ X ] H)
WrMono G X H G₀ (ι , ι-hom) ι-mono X₀ e = goal where
  module H = hGroup H
  module ι = hGroupHom G₀ G (ι , ι-hom)

  G₀≀H : hGroup _
  G₀≀H = G₀ ≀[ X₀ ] H

  ι* : ⟨ G₀≀H ⟩ᵗ → ⟨ G ≀[ X ] H ⟩ᵗ
  ι* (g₀ , (h , h-conn)) = ι g₀ , h′ where
    h′ : Σ[ h ∈ (⟨ X (ι g₀) ⟩ → ⟨ H ⟩ᵗ) ] ST.∣ h ∣₂ ≡ ST.∣ const H.pt₀ ∣₂
    h′ .fst = h ∘ e g₀ .fst
    h′ .snd = ST.merePath→pathSetTrunc $
      PT.map
        (λ h≡pt₀ → funExt λ x → h≡pt₀ ≡$ e g₀ .fst x)
        (ST.pathSetTrunc→merePath h-conn)

  ι*-hom : hGroupHom G₀≀H (G ≀[ X ] H)
  ι*-hom = mkHGroupHom G₀≀H (G ≀[ X ] H) ι* (ΣPathP (ι.pres-pt₀ , ΣPathP ({! !} , {! !})))

  ι*-mono : isMono G₀≀H (G ≀[ X ] H) ι*-hom
  ι*-mono = {! !}

  goal : Mono _ (G ≀[ X ] H)
  goal .fst = G₀≀H
  goal .snd .fst = ι*-hom
  goal .snd .snd = ι*-mono

WrMono' : ∀ {ℓG₀ ℓX₀} (G : hGroup ℓ) (X₀ : hAction ℓX₀ G) (H : hGroup ℓ′)
  → Subaction ℓG₀ ℓX G X₀
  → Mono (ℓ-max (ℓ-max ℓ′ ℓX) ℓG₀) (G ≀[ X₀ ] H)
WrMono' G X₀ H ((G₀ , ((ι , ι-hom) , ι-mono)) , (X , e)) = goal where
  module H = hGroup H

  G₀≀H : hGroup _
  G₀≀H = G₀ ≀[ X ] H

  ι* : ⟨ G₀≀H ⟩ᵗ → ⟨ G ≀[ X₀ ] H ⟩ᵗ
  ι* (g₀ , (h , h-conn)) = ι g₀ , h′ where
    h′ : Σ[ h ∈ (⟨ X₀ (ι g₀) ⟩ → ⟨ H ⟩ᵗ) ] ST.∣ h ∣₂ ≡ ST.∣ const H.pt₀ ∣₂
    h′ .fst = h ∘ {! e g₀ .fst !}
    h′ .snd = {! !}

  ι*-hom : hGroupHom G₀≀H (G ≀[ X₀ ] H)
  ι*-hom = {! !}

  ι*-mono : isMono G₀≀H (G ≀[ X₀ ] H) ι*-hom
  ι*-mono = {! !}

  goal : Mono _ (G ≀[ X₀ ] H)
  goal .fst = G₀≀H
  goal .snd = {! !}
