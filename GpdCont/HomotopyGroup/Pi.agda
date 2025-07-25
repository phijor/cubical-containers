module GpdCont.HomotopyGroup.Pi where

open import GpdCont.Prelude
open import GpdCont.HomotopySet
open import GpdCont.HomotopySet
open import GpdCont.HomotopyGroup.Base
open import GpdCont.HomotopyGroup.Aut
open import GpdCont.HomotopyGroup.Subgroup
open import GpdCont.HomotopyGroup.Morphism
open import GpdCont.HomotopyGroup.Equiv
open import GpdCont.HomotopyGroup.Action
open import GpdCont.HomotopyGroup.Subaction

open import GpdCont.StrictGroupoid.Base
open import GpdCont.StrictGroupoid.Morphism
import      GpdCont.SetTruncation as ST
open import GpdCont.PropositionalTruncation using (_>>=_ ; return)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (congEquiv)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.Embedding
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂ ; ∣_∣₂)
import      Cubical.HITs.PropositionalTruncation as PT

private
  variable
    ℓ ℓK ℓX : Level

private module impl {ℓK} (K : Type ℓK) (G : K → hGroup ℓ) where
  module G k = hGroup (G k)

  ⟨Π⟩ : hGroupoid _
  ⟨Π⟩ .fst = ∀ k → ⟨ G k ⟩ᵗ
  ⟨Π⟩ .snd = isGroupoidΠ G.is-groupoid
  {-# INLINE ⟨Π⟩ #-}

  Πpt : ∀ k → ⟨ G k ⟩ᵗ
  Πpt = G.pt₀
  {-# INLINE Πpt #-}

module _ {ℓK} (K : Type ℓK) (G : K → hGroup ℓ) where
  open impl K G

  ΠGroup : hGroup (ℓ-max ℓ ℓK)
  ΠGroup = Aut ⟨Π⟩ Πpt

  ΠGroupEmbedding : ⟨ ΠGroup ⟩ᵗ ↪ ((k : K) → ⟨ G k ⟩ᵗ)
  ΠGroupEmbedding = AutEmbedding ⟨Π⟩ Πpt

  isContrΠGroup : (∀ k → isContr ⟨ G k ⟩ᵗ) → isContr ⟨ ΠGroup ⟩ᵗ
  isContrΠGroup is-contr-G = isContrAut ⟨Π⟩ Πpt $ isContrΠ is-contr-G

  ΠGroupContractDomain : ((k₀ , _) : isContr K) → hGroupEquiv ΠGroup (G k₀)
  ΠGroupContractDomain is-contr-K@(k₀ , contr) = mkHGroupEquiv ΠGroup (G k₀) Π-equiv refl where
    is-conn-[K,G] : isContr ∥ (∀ k → ⟨ G k ⟩ᵗ) ∥₂
    is-conn-[K,G] = isOfHLevelRespectEquiv 0 (ST.setTruncEquiv $ invEquiv (Π-contractDom is-contr-K)) (G.is-connected k₀)

    Π-equiv : ⟨ ΠGroup ⟩ᵗ ≃ ⟨ G k₀ ⟩ᵗ
    Π-equiv =
      Σ[ γ ∈ (∀ k → ⟨ G k ⟩ᵗ) ] _ ≃⟨ invEquiv $ Σ-cong-equiv-fst $ invEquiv (Π-contractDom is-contr-K) ⟩
      Σ[ g ∈ ⟨ G k₀ ⟩ᵗ ] ∣ (λ k → transport (λ i → ⟨ G (contr k i) ⟩ᵗ) g) ∣₂ ≡ ∣ G.pt₀ ∣₂ ≃⟨ Σ-contractSnd (λ g → isOfHLevelPath 0 is-conn-[K,G] _ _) ⟩
      ⟨ G k₀ ⟩ᵗ ≃∎

  ΠPath : {γ₀ γ₁ : ⟨ ΠGroup ⟩ᵗ} → ((k : K) → γ₀ .fst k ≡ γ₁ .fst k) → γ₀ ≡ γ₁
  ΠPath p = AutPath ⟨Π⟩ Πpt (funExt p)

module _ {ℓG ℓH ℓK} {K : Type ℓK} (G : K → hGroup ℓG) (H : K → hGroup ℓH) (α : ∀ k → hGroupEquiv (G k) (H k)) where
  private
    module G k = hGroup (G k)
    module α k = hGroupEquiv (G k) (H k) (α k)

    open impl K G using () renaming (⟨Π⟩ to ΠG)
    open impl K H using () renaming (⟨Π⟩ to ΠK)

  ΠGroupEquivCodomain : hGroupEquiv (ΠGroup K G) (ΠGroup K H)
  ΠGroupEquivCodomain = AutEquiv ΠG ΠK (equivΠCod α.equiv) (funExt α.pres-pt₀)

module Curry {ℓK ℓL} {K : Type ℓK} {L : K → Type ℓL} (G : (k : K) → L k → hGroup ℓ) where
  private
    module G k l = hGroup (G k l)

  ΠGroupCurryEquiv : hGroupEquiv (ΠGroup K (λ k → ΠGroup (L k) (G k))) (ΠGroup (Σ K L) (uncurry G))
  ΠGroupCurryEquiv = mkHGroupEquiv (ΠGroup K (λ k → ΠGroup (L k) (G k))) (ΠGroup (Σ K L) (uncurry G))
    curry-equiv $
    ΠPath (Σ K L) (uncurry G) λ _ → refl
    where
      curryᴳ : ⟨ ΠGroup (Σ K L) (uncurry G) ⟩ᵗ → ⟨ ΠGroup K (λ k → ΠGroup (L k) (G k)) ⟩ᵗ
      curryᴳ (γ , γ-conn) .fst k .fst = curry γ k
      curryᴳ (γ , γ-conn) .fst k .snd = ST.merePath→pathSetTrunc do
        γ≡pt₀ ← ST.pathSetTrunc→merePath γ-conn
        return $ funExt λ l → γ≡pt₀ ≡$ (k , l)
      curryᴳ (γ , γ-conn) .snd = ST.merePath→pathSetTrunc do
        γ≡pt₀ ← ST.pathSetTrunc→merePath γ-conn
        return $ funExt λ k → ΠPath (L k) (G k) λ l → γ≡pt₀ ≡$ (k , l)

      uncurryᴳ : ⟨ ΠGroup K (λ k → ΠGroup (L k) (G k)) ⟩ᵗ → ⟨ ΠGroup (Σ K L) (uncurry G) ⟩ᵗ
      uncurryᴳ (γ , γ-conn) .fst = uncurry λ k → γ k .fst
      uncurryᴳ (γ , γ-conn) .snd = ST.merePath→pathSetTrunc do
        γ≡pt₀ ← ST.pathSetTrunc→merePath γ-conn
        return λ where
          i (k , l) → γ≡pt₀ i k .fst l

      curry-iso : Iso ⟨ ΠGroup K (λ k → ΠGroup (L k) (G k)) ⟩ᵗ ⟨ ΠGroup (Σ K L) (uncurry G) ⟩ᵗ
      curry-iso .Iso.fun = uncurryᴳ
      curry-iso .Iso.inv = curryᴳ
      curry-iso .Iso.rightInv (γ , γ-conn) = ΠPath (Σ K L) (uncurry G) λ _ → refl
      curry-iso .Iso.leftInv (γ , γ-conn) = ΠPath K (λ k → ΠGroup (L k) (G k)) λ where
        k → ΠPath (L k) (G k) λ l → refl

      curry-equiv : ⟨ ΠGroup K (λ b → ΠGroup (L b) (G b)) ⟩ᵗ ≃ ⟨ ΠGroup (Σ K L) (uncurry G) ⟩ᵗ
      curry-equiv = isoToEquiv curry-iso

open Curry using (ΠGroupCurryEquiv) public

module _ {ℓK} (K : Type ℓK) (G : hGroup ℓ) where
  FunGroup : hGroup _
  FunGroup = ΠGroup K $ const G

  FunGroupEmbedding : ⟨ FunGroup ⟩ᵗ ↪ (K → ⟨ G ⟩ᵗ)
  FunGroupEmbedding = ΠGroupEmbedding K $ const G

  FunGroupPath : {γ₀ γ₁ : ⟨ FunGroup ⟩ᵗ} → (γ₀ .fst ≡ γ₁ .fst) → γ₀ ≡ γ₁
  FunGroupPath p = ΠPath K (const G) λ k i → p i k

  isContrFunGroup : isContr ⟨ G ⟩ᵗ → isContr ⟨ FunGroup ⟩ᵗ
  isContrFunGroup is-contr-G = isContrΠGroup K (const G) (const is-contr-G)

  FunGroupContractDomain : isContr K → hGroupEquiv FunGroup G
  FunGroupContractDomain is-contr-K = ΠGroupContractDomain K (const G) is-contr-K

proj : ∀ {K : Type ℓK} (G : K → hGroup ℓ) → ∀ k → hGroupHom (ΠGroup K G) (G k)
proj _ k .fst (f , f-strict) = f k
proj {K} G k .snd = funExt (ST.elim (λ _ → G.is-groupoid k _ _) $ uncurry is-strict-π) where
  module G k = hGroup (G k)
  open import Cubical.HITs.PropositionalTruncation.Monad

  abstract
    is-strict-π' : (f : (k : K) → ⟨ G k .fst ⟩) → f ≡ G.pt₀ → ∣ f k ∣₂ ≡ G.center k
    is-strict-π' f f≡pt =
      ∣ f k ∣₂ ≡[ i ]⟨ ∣ f≡pt i k ∣₂ ⟩
      ∣ G.pt k (G.center k) ∣₂ ≡⟨ G.pt-section k (G.center k) ⟩
      G.center k ∎

  is-strict-π : (f : (k : K) → ⟨ G k .fst ⟩) → (f-strict : ∣ f ∣₂ ≡ ∣ G.pt₀ ∣₂) → G.pt k ∣ f k ∣₂ ≡ G.pt₀ k
  is-strict-π f f-strict = cong (G.pt k) $ ST.pathSetTrunc→recProp (ST.isSetSetTrunc _ _) (is-strict-π' f) f-strict

module _ {ℓ} (K : Type ℓ) (G : K → hGroup ℓ) (H : hGroup ℓ) where
  private
    module H = hGroup H
    module G k = hGroup (G k)

  Π-universal : hGroupHom H (ΠGroup K G) → (k : K) → hGroupHom H (G k)
  Π-universal φ k = compStrict (H .fst) (ΠGroup K G .fst) (G k .fst)
    φ
    (proj G k)

  Π-universal⁻ : ((k : K) → hGroupHom H (G k)) → hGroupHom H (ΠGroup K G)
  Π-universal⁻ ψ = goal where
    module ψ k = hGroupHom H (G k) (ψ k)

    fun : (h : ⟨ H ⟩ᵗ) (k : K) → ⟨ G k ⟩ᵗ
    fun h k = ψ.fun k h

    fun-conn : ∀ h → ∣ (λ k → ψ.fun k h) ∣₂ ≡ ∣ G.pt₀ ∣₂
    fun-conn = H.elimProp (λ h → ST.isSetSetTrunc _ _) $ cong ∣_∣₂ $ funExt ψ.pres-pt₀

    goal : hGroupHom H (ΠGroup K G)
    goal = mkHGroupHom H (ΠGroup K G)
      (λ h → fun h , fun-conn h)
      (Σ≡Prop (λ _ → ST.isSetSetTrunc _ _) $ funExt ψ.pres-pt₀)

  Π-universal-fiber : (ψ : ∀ k → hGroupHom H (G k)) → fiber Π-universal ψ ≃ {! !}
  Π-universal-fiber ψ =
    Σ[ φ ∈ hGroupHom H (ΠGroup K G) ] Π-universal φ ≡ ψ ≃⟨ Σ-cong-equiv-snd (λ φ → {! !}) ⟩
    Σ[ φ ∈ hGroupHom H (ΠGroup K G) ] {! !} ≃⟨ {! !} ⟩
    {! !} ≃∎

  isProductΠGroup : isEquiv Π-universal
  isProductΠGroup = isoToIsEquiv λ where
    .Iso.fun → Π-universal
    .Iso.inv → Π-universal⁻
    .Iso.leftInv φ → hGroupHom≡ H (ΠGroup K G) (funExt λ h → Σ≡Prop {! !} refl) {! !}
    .Iso.rightInv → {! !}

private
  test : (K : Type ℓ) (G : K → hGroup ℓ) → ⟨ ΠGroup K G .fst ⟩ ≡ Σ ((k : K) → fst (G k .fst)) (λ x → ∣ x ∣₂ ≡ ∣ (λ k → StrictGroupoidStr.pt (snd (G k .fst)) (G k .snd .fst)) ∣₂)
  test K G = refl

ΠActionΣ : (K : hSet ℓK) (G : ⟨ K ⟩ → hGroup ℓ) (X : (k : ⟨ K ⟩) → hAction ℓX (G k)) → hAction (ℓ-max ℓK ℓX) (ΠGroup ⟨ K ⟩ G)
ΠActionΣ K G X (f , _) = ΣSet K λ k → X k (f k)

ΠActionΠ : {K : Type ℓK} (G : K → hGroup ℓ) (X : (k : K) → hAction ℓX (G k)) → hAction (ℓ-max ℓK ℓX) (ΠGroup K G)
ΠActionΠ {K} G X (f , _) = ΠSet (λ (k : K) → X k (f k))

module _ {ℓ′} (K : Type ℓK) (H : K → hGroup ℓ) (sub : ∀ k → Mono ℓ′ (H k)) where
  private
    G : K → hGroup _
    G = λ k → sub k .fst

    ι : ∀ k → Σ[ ι ∈ hGroupHom (G k) (H k) ] isMono (G k) (H k) ι
    ι k = sub k .snd

    module G k = hGroup (G k)
    module ι k = hGroupHom (G k) (H k) (ι k .fst)

    ι* : hGroupHom (ΠGroup K G) (ΠGroup K H)
    ι* = mkHGroupHom (ΠGroup K G) (ΠGroup K H)
      (λ { (γ , γ-conn) → (λ k → ι k .fst .fst (γ k)) , ST.merePath→pathSetTrunc (PT.rec PT.isPropPropTrunc (λ p → do
          return $ funExt λ k → cong (ι.fun _) (p ≡$ k) ∙ ι.pres-pt₀ k
        )
        (ST.pathSetTrunc→merePath γ-conn)) })
      (Σ≡Prop (λ _ → ST.isSetSetTrunc _ _) $ funExt ι.pres-pt₀)

  ΠMono : Mono (ℓ-max ℓK ℓ′) (ΠGroup K H)
  ΠMono .fst = ΠGroup K G
  ΠMono .snd .fst = ι*
  ΠMono .snd .snd η = goal where
    -- The fibers of ι* can be expressed as a subtype of the (product of) fibers of ι:
    fiber-equiv : _ ≃ (fiber (ι* .fst) η)
    fiber-equiv =
      Σ[ γ* ∈ (∀ k → fiber (ι k .fst .fst) (η .fst k)) ] ∣ (λ k → γ* k .fst) ∣₂ ≡ ∣ G.pt₀ ∣₂
        ≃⟨⟩
      Σ[ γ* ∈ (∀ k → Σ[ g ∈ ⟨ G k ⟩ᵗ ] ι k .fst .fst g ≡ η .fst k) ] ∣ (λ k → γ* k .fst) ∣₂ ≡ ∣ G.pt₀ ∣₂
        ≃⟨ Σ-cong-equiv-fst Σ-Π-≃ ⟩
      Σ[ (γ , _) ∈ Σ[ γ ∈ ((k : K) → ⟨ G k ⟩ᵗ) ] (∀ k → ι k .fst .fst (γ k) ≡ η .fst k) ] ∣ γ ∣₂ ≡ ∣ G.pt₀ ∣₂
        ≃⟨ Σ-cong-equiv-fst (Σ-cong-equiv-snd λ γ → funExtEquiv) ⟩
      Σ[ (γ , _) ∈ Σ[ γ ∈ ((k : K) → ⟨ G k ⟩ᵗ) ] (λ k → ι k .fst .fst (γ k)) ≡ η .fst ] ∣ γ ∣₂ ≡ ∣ G.pt₀ ∣₂
        ≃⟨ strictEquiv (λ { ((γ , p) , c) → ((γ , c) , p) }) (λ { ((γ , c) , p) → ((γ , p) , c) }) ⟩
      Σ[ (γ , _) ∈ ⟨ ΠGroup K G ⟩ᵗ ] (λ k → ι k .fst .fst (γ k)) ≡ η .fst
        ≃⟨ Σ-cong-equiv-snd (λ { (γ , _) → Σ≡PropEquiv (λ η → ST.isSetSetTrunc _ _) }) ⟩
      Σ[ γ ∈ ⟨ ΠGroup K G ⟩ᵗ ] (ι* .fst γ) ≡ η ≃∎

    goal : isSet (fiber (ι* .fst) η)
    goal = isOfHLevelRespectEquiv 2 fiber-equiv $
      isSetΣSndProp (isSetΠ (λ k → ι k .snd (η .fst k))) λ γ → ST.isSetSetTrunc _ _


  ΠSubactionᴰ : ∀ {ℓX ℓY} (is-set-K : isSet K)
    → (Y : ∀ k → hAction ℓY (H k))
    → (∀ k → Subactionᴰ (G k) (H k) (ι k .fst) ℓX (Y k))
    → Subactionᴰ (ΠGroup K G) (ΠGroup K H) ι* (ℓ-max ℓK ℓX) (ΠActionΣ (K , is-set-K) H Y)
  ΠSubactionᴰ {ℓX} is-set-K Y X↪Y = sub-action where

    X : ∀ k → hAction _ (G k)
    X k = X↪Y k .fst
    
    sub-action : Subactionᴰ (ΠGroup K G) (ΠGroup K H) ι* _ (ΠActionΣ (K , is-set-K) H Y)
    sub-action .fst (γ , _) = {! !}
    sub-action .snd = {! !}

  ΠSubaction : ∀ {ℓX ℓY} (is-set-K : isSet K)
    → (Y : ∀ k → hAction ℓY (H k))
    -- → (∀ k → Subactionᴰ ℓX (H k) (Y k))
    → (∀ k → {! Subactionᴰ ℓX (H k) (Y k) !})
    → Subaction {! !} {! !} (ΠGroup K H) (ΠActionΣ (K , is-set-K) H Y)
  ΠSubaction is-set-K Y X* .fst = ΠMono
  ΠSubaction is-set-K Y X* .snd = ΠSubactionᴰ is-set-K Y X*
