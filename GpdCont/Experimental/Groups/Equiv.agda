module GpdCont.Experimental.Groups.Equiv where

open import GpdCont.Prelude
open import GpdCont.Experimental.Groups.Base
open import GpdCont.Univalence

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (conjugatePathEquiv)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path using (PathP≃Path)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Pointed.Base using (Pointed)
open import Cubical.Functions.Embedding
open import Cubical.Relation.Binary.Base using (module BinaryRelation)

open import Cubical.Displayed.Base using (UARel ; DUARel ; ∫)
open import Cubical.Displayed.Auto using (autoDUARel)
open import Cubical.Displayed.Universe using () renaming (𝒮-Univ to UnivalenceUARel)
open import Cubical.Displayed.Record
open import Cubical.Homotopy.Loopspace using (Ω ; isComm∙) renaming (EH to Eckmann-Hilton)

open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
import Cubical.Data.Sigma as Sigma

open Sigma using (_×_)

record GroupEquiv {ℓ} (G H : Group ℓ) : Type ℓ where
  private
    module G = GroupStr (str G)
    module H = GroupStr (str H)
  field
    hom : ⟨ G ⟩ → ⟨ H ⟩
    is-emb-hom : isEmbedding hom
    pres-pt : hom G.pt ≡ H.pt

unquoteDecl GroupEquivIsoΣ = declareRecordIsoΣ GroupEquivIsoΣ (quote GroupEquiv)

instance
  GroupEquivToΣ : ∀ {ℓ} {G H : Group ℓ} → RecordToΣ (GroupEquiv G H)
  GroupEquivToΣ = toΣ GroupEquivIsoΣ

open GroupEquiv

private
  variable
    ℓ : Level
    G H : Group ℓ

idGroupEquiv : ∀ (G : Group ℓ) → GroupEquiv G G
idGroupEquiv G .hom = id ⟨ G ⟩
idGroupEquiv G .is-emb-hom = snd (id↪ ⟨ G ⟩)
idGroupEquiv G .pres-pt = refl

isEmbeddingGroup→isEquiv : ∀ {G H : Group ℓ} → (φ : ⟨ G ⟩ → ⟨ H ⟩)
  → isEmbedding φ
  → isEquiv φ
isEmbeddingGroup→isEquiv {G} {H} φ emb-φ .equiv-proof h = inhProp→isContr (inh-fib-φ h) (has-prop-fib-φ h) where
  module G = GroupStr (str G)
  module H = GroupStr (str H)
  has-prop-fib-φ : hasPropFibers φ
  has-prop-fib-φ = isEmbedding→hasPropFibers emb-φ

  inh-fib-φ : (h : ⟨ H ⟩) → fiber φ h
  inh-fib-φ h = PT.rec {P = fiber φ h} (has-prop-fib-φ h) (G.pt ,_) mere-path where
    mere-path : ∥ φ G.pt ≡ h ∥₁
    mere-path = H.existsPath (φ G.pt) h

isEmbeddingGroup≃isEquiv : ∀ {G H : Group ℓ} → (φ : ⟨ G ⟩ → ⟨ H ⟩)
  → isEmbedding φ ≃ isEquiv φ
isEmbeddingGroup≃isEquiv {G} {H} φ = propBiimpl→Equiv
  (isPropIsEmbedding {f = φ})
  (isPropIsEquiv φ)
  (isEmbeddingGroup→isEquiv {G = G} {H = H} φ)
  (isEquiv→isEmbedding {f = φ})

private
  ⟨SIP⟩ : (G H : Group ℓ) → ⟨ G ⟩ ↪ ⟨ H ⟩ ≃ (⟨ G ⟩ ≃ ⟨ H ⟩)
  ⟨SIP⟩ G H = Sigma.Σ-cong-equiv-snd (isEmbeddingGroup≃isEquiv {G = G} {H = H})

record GroupStrEquivRaw {ℓ} {G H : Type ℓ} (G* : GroupStr G) (φ : G ≃ H) (H* : GroupStr H) : Type ℓ where
  private
    module G = GroupStr G*
    module H = GroupStr H*
  field
    point-path : equivFun φ G.pt ≡ H.pt

unquoteDecl GroupStrEquivRawIsoΣ = declareRecordIsoΣ GroupStrEquivRawIsoΣ (quote GroupStrEquivRaw)

instance
  GroupStrEquivRawToΣ : ∀ {ℓ} {G H : Type ℓ} {G* : GroupStr G} {φ : G ≃ H} {H* : GroupStr H} → RecordToΣ (GroupStrEquivRaw G* φ H*)
  GroupStrEquivRawToΣ = toΣ GroupStrEquivRawIsoΣ

𝒮ᴰ-Group : ∀ {ℓ} → DUARel (UnivalenceUARel ℓ) (GroupStr {ℓ}) ℓ
𝒮ᴰ-Group {ℓ} = 𝒮ᴰ-Record (UnivalenceUARel ℓ) GroupStrEquivRaw
  (fields:
    prop[ is-connected ∣ (λ _ _ → isPropIsContr) ]
    prop[ is-groupoid ∣ (λ _ _ → isPropIsGroupoid) ]
    data[ pt ∣ autoDUARel _ _ ∣ point-path ])
  where
    open GroupStr
    open GroupStrEquivRaw
  

open GroupStr

GroupEquivRaw : ∀ {ℓ} (G H : Group ℓ) → Type _
GroupEquivRaw G H = Σ[ φ ∈ (⟨ G ⟩ ≃ ⟨ H ⟩) ] (GroupStrEquivRaw (G .snd) φ (H .snd))

GroupEquivRaw≃Path : ∀ {ℓ} (G H : Group ℓ) → GroupEquivRaw G H ≃ (G ≡ H)
GroupEquivRaw≃Path =  ∫ 𝒮ᴰ-Group .UARel.ua

GroupEquivRawUARel : ∀ {ℓ} → UARel (Group ℓ) ℓ
GroupEquivRawUARel .UARel._≅_ = GroupEquivRaw
GroupEquivRawUARel .UARel.ua = GroupEquivRaw≃Path

GroupEquiv≃GroupEquivRaw : (G H : Group ℓ) → GroupEquiv G H ≃ GroupEquivRaw G H
GroupEquiv≃GroupEquivRaw G H =
  GroupEquiv G H ≃⟨ _ ≃Σ ⟩
  Σ[ φ ∈ (⟨ G ⟩ → ⟨ H ⟩) ] (isEmbedding φ × (φ (snd G .GroupStr.pt) ≡ snd H .GroupStr.pt))  ≃⟨ Sigma.Σ-cong-equiv-snd (λ φ → Sigma.Σ-cong-equiv-fst (isEmbeddingGroup≃isEquiv {G = G} {H = H} φ)) ⟩
  Σ[ φ ∈ (⟨ G ⟩ → ⟨ H ⟩) ] (isEquiv φ × (φ (snd G .GroupStr.pt) ≡ snd H .GroupStr.pt))      ≃⟨ invEquiv Sigma.Σ-assoc-≃ ⟩
  Σ[ φ ∈ (⟨ G ⟩ ≃ ⟨ H ⟩) ] ((equivFun φ (snd G .GroupStr.pt) ≡ snd H .GroupStr.pt))         ≃⟨ Sigma.Σ-cong-equiv-snd (λ φ → invEquiv (GroupStrEquivRaw (str G) φ (str H) ≃Σ)) ⟩
  Σ[ φ ∈ (⟨ G ⟩ ≃ ⟨ H ⟩) ] (GroupStrEquivRaw (G .snd) φ (H .snd))                           ≃∎

SIP : (G H : Group ℓ) → GroupEquiv G H ≃ (G ≡ H)
SIP G H =
  GroupEquiv G H    ≃⟨ GroupEquiv≃GroupEquivRaw G H ⟩
  GroupEquivRaw G H ≃⟨ GroupEquivRaw≃Path G H ⟩
  G ≡ H ≃∎

module _ {ℓ : Level} where
  private
    module GE = BinaryRelation (GroupEquiv {ℓ = ℓ})

  isUnivalentGroupEquiv : GE.isUnivalent
  isUnivalentGroupEquiv = SIP

GroupEquivUARel : ∀ {ℓ} → UARel (Group ℓ) ℓ
GroupEquivUARel .UARel._≅_ = GroupEquiv
GroupEquivUARel .UARel.ua = isUnivalentGroupEquiv

GroupEquiv→Path : GroupEquiv G H → ⟨ G ⟩ ≡ ⟨ H ⟩
GroupEquiv→Path φ = cong ⟨_⟩ $ (equivFun $ SIP _ _) φ

GroupEquiv→Equiv : GroupEquiv G H → ⟨ G ⟩ ≃ ⟨ H ⟩
GroupEquiv→Equiv = fst ∘ (equivFun $ GroupEquiv≃GroupEquivRaw _ _)

loopSpaceEquiv : (G : Group ℓ) → (a b : ⟨ G ⟩) → ∥ a ≡ b ∥₁ → (a ≡ a) ≃ (b ≡ b)
loopSpaceEquiv G a b = PT.rec→Set isSet≃ conjugatePathEquiv is-2-const-conj-path-equiv where
  module G = GroupStr (str G)

  Ωₐ : Pointed _
  Ωₐ = Ω (⟨ G ⟩ , a)

  ehₐ : isComm∙ Ωₐ
  ehₐ = Eckmann-Hilton {A = ⟨ G ⟩ , a} 0

  isSet≃ : isSet ((a ≡ a) ≃ (b ≡ b))
  isSet≃ = isOfHLevel≃ 2 (G.is-groupoid a a) (G.is-groupoid b b)

  lemma : ∀ (p q : a ≡ b) (r : a ≡ a) → sym p ∙ r ∙ p ≡ sym q ∙ r ∙ q
  lemma p q = {! !}

  is-2-const-conj-path-equiv : ∀ (p q : a ≡ b) → conjugatePathEquiv p ≡ conjugatePathEquiv q
  is-2-const-conj-path-equiv p q = equivEq (funExt (lemma p q))
