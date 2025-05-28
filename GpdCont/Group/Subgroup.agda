module GpdCont.Group.Subgroup where

open import GpdCont.Prelude hiding (Sub)
open import GpdCont.Equiv using (symEquiv)
open import GpdCont.Univalence

open import GpdCont.Group.DirProd

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path using (congPathEquiv)
open import Cubical.Functions.Embedding
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Pi
open import Cubical.Algebra.Group.GroupPath

import Cubical.Algebra.Group.Subgroup as Alt

private variable
  ℓ ℓG ℓH : Level
  G H : Group ℓ
  φ : GroupHom G H

isContrKer : (φ : GroupHom G H) → Type _
isContrKer φ = isContr (Ker φ)

isPropIsContrKer : (φ : GroupHom G H) → isProp (isContrKer φ)
isPropIsContrKer φ = isPropIsContr

isContrKerId : (G : Group ℓG) → isContrKer (idGroupHom {G = G})
isContrKerId G = isOfHLevelRespectEquiv 0 (Σ-cong-equiv-snd λ g → symEquiv) (isContrSingl (GroupStr.1g (str G)))

opaque
  isContrKer→isEmbedding : (φ : GroupHom G H) → isContrKer φ → isEmbedding (fst φ)
  isContrKer→isEmbedding {H} φ = injEmbedding (str H .GroupStr.is-set) ∘ isInjective→isMono φ ∘ isContrKer→isInjective φ

isEmbedding→isContrKer : (φ : GroupHom G H) → isEmbedding (fst φ) → isContrKer φ
isEmbedding→isContrKer φ is-emb = isInjective→isContrKer φ λ g φg≡1 → invEq (_ , is-emb _ _) $ φg≡1 ∙ sym (φ .snd .IsGroupHom.pres1)

isEmbedding→Injection' : ∀ {ℓA ℓB ℓC} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC}
  → (f : A → B)
  → isEmbedding f
  → (g h : C → A)
  → (f ∘ g ≡ f ∘ h)
  → g ≡ h
isEmbedding→Injection' {C} f is-emb-f g h fg≡fh = funExt $ cong fst ∘ fib-path where
  has-prop-fib-f : hasPropFibers f
  has-prop-fib-f = isEmbedding→hasPropFibers is-emb-f

  module _ (c : C) where
    fib₁ : fiber f (f (g c))
    fib₁ .fst = g c
    fib₁ .snd = refl

    fib₂ : fiber f (f (g c))
    fib₂ .fst = h c
    fib₂ .snd = sym $ fg≡fh ≡$ c

    fib-path : fib₁ ≡ fib₂
    fib-path = has-prop-fib-f (f (g c)) fib₁ fib₂

record isSubgroup (G : Group ℓG) (H : Group ℓH) : Type (ℓ-max ℓG ℓH) where
  field
    inc : GroupHom H G
    is-contr-ker-inc : isContrKer inc

  inc-fun : ⟨ H ⟩ → ⟨ G ⟩
  inc-fun = inc .fst

  is-hom : IsGroupHom (str H) inc-fun (str G)
  is-hom = inc .snd

  open IsGroupHom is-hom public

  is-embedding-inc-fun : isEmbedding inc-fun
  is-embedding-inc-fun = isContrKer→isEmbedding inc is-contr-ker-inc

unquoteDecl isSubgroupIsoΣ = declareRecordIsoΣ isSubgroupIsoΣ (quote isSubgroup)

infix 4 _≤_
_≤_ : (H : Group ℓH) (G : Group ℓG) → Type _
_≤_ H G = isSubgroup G H

instance
  isSubgroupToΣ : RecordToΣ (isSubgroup G H)
  isSubgroupToΣ = toΣ isSubgroupIsoΣ

Subgroup : ∀ (G : Group ℓG) (ℓH : Level) → Type (ℓ-max ℓG (ℓ-suc ℓH))
Subgroup G ℓH = Σ[ H ∈ Group ℓH ] isSubgroup G H

opaque
  isSetIsSubgroup : isSet (isSubgroup G H)
  isSetIsSubgroup = recordIsOfHLevel 2 $ isSetΣSndProp isSetGroupHom isPropIsContrKer

SubgroupPath : (H K : Subgroup G ℓ) → Type _
SubgroupPath (H , is-sub-H) (K , is-sub-K) = Σ[ e ∈ GroupEquiv H K ] H.inc .fst ≡ K.inc .fst ∘ groupEquivFun e where
  module H = isSubgroup is-sub-H
  module K = isSubgroup is-sub-K

isPropSubgroupPath : (H K : Subgroup G ℓ) → isProp (SubgroupPath H K)
isPropSubgroupPath {G} (H , is-sub-H) (K , is-sub-K) (((e , e-equiv) , e-group-hom) , e-comm) (((f , f-equiv) , f-group-hom) , f-comm) =
  Σ≡Prop (λ e → isOfHLevelPath' 1 (isSet→ G.is-set) _ _) (GroupEquiv≡ $ equivEq equiv-eq)
  where
  module G = GroupStr (str G)

  module K = isSubgroup is-sub-K

  comm-lemma : K.inc-fun ∘ e ≡ K.inc-fun ∘ f
  comm-lemma = sym e-comm ∙ f-comm

  equiv-eq : e ≡ f
  equiv-eq = isEmbedding→Injection' K.inc-fun K.is-embedding-inc-fun e f comm-lemma

module isSubgroupPathP
  (H K : Group ℓ)
  (H≤G : H ≤ G)
  (K≤G : K ≤ G)
  (p : H ≡ K)
  where
  private
    module H = isSubgroup H≤G
    module K = isSubgroup K≤G
  
  isSubgroupPathP :
      PathP (λ i → ⟨ p i ⟩ → ⟨ G ⟩) (isSubgroup.inc-fun H≤G) (isSubgroup.inc-fun K≤G)
    → PathP (λ i → (p i) ≤ G) H≤G K≤G
  isSubgroupPathP pᴰ = inc-path where
    hom-path : PathP (λ i → GroupHom (p i) G) H.inc K.inc
    hom-path i .fst = pᴰ i
    hom-path i .snd = isProp→PathP (λ i → isPropIsGroupHom (p i) G {f = pᴰ i}) H.is-hom K.is-hom i

    inc-path : PathP (λ i → p i ≤ G) H≤G K≤G
    inc-path i .isSubgroup.inc = hom-path i
    inc-path i .isSubgroup.is-contr-ker-inc = isProp→PathP (λ i → isPropIsContrKer (hom-path i)) H.is-contr-ker-inc K.is-contr-ker-inc i


  isSubgroupPathPEquiv :
    PathP (λ i → ⟨ p i ⟩ → ⟨ G ⟩) (isSubgroup.inc-fun H≤G) (isSubgroup.inc-fun K≤G)
      ≃
    PathP (λ i → (p i) ≤ G) H≤G K≤G
  isSubgroupPathPEquiv = propBiimpl→Equiv
    (isOfHLevelPathP' 1 (isSet→ (str G .GroupStr.is-set)) _ _)
    (isOfHLevelPathP' 1 isSetIsSubgroup _ _)
    isSubgroupPathP
    (congP (λ i → isSubgroup.inc-fun))

open isSubgroupPathP public

SubgroupPathEquiv : (H K : Subgroup G ℓ) → (SubgroupPath H K) ≃ (H ≡ K)
SubgroupPathEquiv {G} H*@(H , H≤G) K*@(K , K≤G) =
  (Σ[ e ∈ GroupEquiv H K ] H.inc .fst ≡ K.inc .fst ∘ groupEquivFun e)
    ≃⟨ Σ-cong-equiv-snd (λ (e , _) → invEquiv funExtEquiv ∙ₑ ua→Equiv {e = e} {B = λ _ → ⟨ G ⟩}) ⟩
  (Σ[ e ∈ GroupEquiv H K ] PathP (λ i → ua (e .fst) i → ⟨ G ⟩) H.inc-fun K.inc-fun)
    ≃⟨ Σ-cong-equiv-fst (GroupPath _ _) ⟩
  (Σ[ p ∈ H ≡ K ] PathP (λ i → ⟨ p i ⟩ → ⟨ G ⟩) H.inc-fun K.inc-fun)
    ≃⟨ Σ-cong-equiv-snd $ isSubgroupPathPEquiv H K H≤G K≤G ⟩
  (Σ[ p ∈ H ≡ K ] PathP (λ i → isSubgroup G (p i)) H≤G K≤G)
    ≃⟨ ΣPathP≃PathPΣ ⟩
  (H* ≡ K*) ≃∎
  where
    module H = isSubgroup H≤G
    module K = isSubgroup K≤G

isSetSubgroup : isSet (Subgroup G ℓH)
isSetSubgroup H K = isOfHLevelRespectEquiv 1 (SubgroupPathEquiv H K) (isPropSubgroupPath H K)

SubgroupDirProdRight : ∀ {ℓK} (G : Group ℓG) (K : Subgroup H ℓK) → Subgroup (DirProd G H) (ℓ-max ℓG ℓK)
SubgroupDirProdRight {H = H} G (K , K≤H) = G×K , G×K≤GH where
  module K≤H = isSubgroup K≤H

  G×K : Group _
  G×K = DirProd G K

  -×inc = DirProd.mapRight G K K≤H.inc

  ker-equiv : Ker K≤H.inc ≃ Ker -×inc
  ker-equiv =
    Ker K≤H.inc
      ≃⟨ invEquiv (Σ-contractFst (isContrKerId G)) ⟩
    Ker (idGroupHom {G = G}) × Ker K≤H.inc
      ≃⟨ shuffle ⟩
    Σ[ g ∈ ⟨ G ⟩ ] Σ[ h ∈ ⟨ K ⟩ ] isInKer (idGroupHom {G = G}) g × isInKer K≤H.inc h
      ≃⟨ Σ-cong-equiv-snd (λ g → Σ-cong-equiv-snd λ h → ΣPathP≃PathPΣ) ⟩
    Σ[ g ∈ ⟨ G ⟩ ] Σ[ h ∈ ⟨ K ⟩ ] isInKer -×inc (g , h)
      ≃⟨ invEquiv Σ-assoc-≃ ⟩
    Σ[ x ∈ ⟨ G ⟩ × ⟨ K ⟩ ] isInKer -×inc x
      ≃∎
    where
      shuffle : _ ≃ _
      shuffle = strictEquiv
        (λ { ((g , g≡1) , (k , k∈KerInc)) → (g , k , g≡1 , k∈KerInc) })
        (λ { (g , k , g≡1 , k∈KerInc) → ((g , g≡1) , (k , k∈KerInc)) })

  G×K≤GH : isSubgroup (DirProd G H) G×K
  G×K≤GH .isSubgroup.inc = -×inc
  G×K≤GH .isSubgroup.is-contr-ker-inc = isOfHLevelRespectEquiv 0 ker-equiv K≤H.is-contr-ker-inc

SubgroupΠ : ∀ {ℓX} (X : Type ℓX) (G : X → Group ℓG)
  → (H : ∀ x → Subgroup (G x) ℓH)
  → Subgroup (ΠGroup G) (ℓ-max ℓH ℓX)
SubgroupΠ X G H = ΠH , ΠH≤ΠG where
  module H≤G x = isSubgroup (H x .snd)

  ΠH : Group _
  ΠH = ΠGroup λ (x : X) → H x .fst

  ΠH≤ΠG : isSubgroup (ΠGroup G) ΠH
  ΠH≤ΠG .isSubgroup.inc .fst h x = H≤G.inc-fun x (h x)
  ΠH≤ΠG .isSubgroup.inc .snd = {! !}
  ΠH≤ΠG .isSubgroup.is-contr-ker-inc = {! !}

isClosedSubset→Subgroup : ∀ {ℓP} (G : Group ℓG) → (P : ⟨ G ⟩ → Type ℓP)
  → (∀ g → isProp (P g))
  → (let open GroupStr (str G))
  → (1* : P 1g)
  → (mul* : ∀ {g h} → P g → P h → P (g · h))
  → (inv* : ∀ {g} → P g → P (inv g))
  → Subgroup G _
isClosedSubset→Subgroup G P is-prop-P 1* mul* inv* = sub where
  open GroupStr (str G)
  GP : Group _
  GP .fst = Σ ⟨ G ⟩ P
  GP .snd .GroupStr.1g = 1g , 1*
  GP .snd .GroupStr._·_ (g , pg) (h , ph) = g · h , mul* pg ph
  GP .snd .GroupStr.inv (g , pg) = inv g , inv* pg
  GP .snd .GroupStr.isGroup = makeIsGroup (isSetΣSndProp is-set is-prop-P) {! !} {! !} {! !} {! !} {! !}

  inc : GroupHom GP G
  inc .fst = fst
  inc .snd = makeIsGroupHom λ _ _ → refl

  sub : Subgroup G _
  sub .fst = GP
  sub .snd .isSubgroup.inc .fst = fst
  sub .snd .isSubgroup.inc .snd = makeIsGroupHom λ _ _ → refl
  sub .snd .isSubgroup.is-contr-ker-inc = isEmbedding→isContrKer inc λ g h → isEmbeddingFstΣProp is-prop-P

Subgroup→ClosedSubset : ∀ {ℓ} {G H : Group ℓ} → H ≤ G → Alt.Subgroup G
Subgroup→ClosedSubset {G} {H} H≤G = IncIm where
  module G = GroupStr (str G)
  module H where
    open isSubgroup H≤G public
    open GroupStr (str H) public

  open import Cubical.Foundations.Powerset

  _∈Im : ℙ ⟨ G ⟩
  _∈Im g .fst = fiber H.inc-fun g
  _∈Im g .snd = isEmbedding→hasPropFibers H.is-embedding-inc-fun g

  IncIm : Alt.Subgroup G
  IncIm .fst = _∈Im
  IncIm .snd .Alt.isSubgroup.id-closed = H.1g , H.pres1
  IncIm .snd .Alt.isSubgroup.op-closed (h₁ , p₁) (h₂ , p₂) = h₁ H.· h₂ , H.pres· h₁ h₂ ∙ cong₂ G._·_ p₁ p₂
  IncIm .snd .Alt.isSubgroup.inv-closed (h , p) = H.inv h , H.presinv h ∙ cong G.inv p
