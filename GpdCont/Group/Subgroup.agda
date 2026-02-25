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
  G H K : Group ℓ
  φ : GroupHom G H

isContrKer : (φ : GroupHom G H) → Type _
isContrKer φ = isContr (Ker φ)

isPropIsContrKer : (φ : GroupHom G H) → isProp (isContrKer φ)
isPropIsContrKer φ = isPropIsContr

isContrKerId : (G : Group ℓG) → isContrKer (idGroupHom {G = G})
isContrKerId G = isOfHLevelRespectEquiv 0 (Σ-cong-equiv-snd λ g → symEquiv) (isContrSingl (GroupStr.1g (str G)))

isPropKer→isContrKer : (φ : GroupHom G H) → isProp (Ker φ) → isContr (Ker φ)
isPropKer→isContrKer {G} φ = inhProp→isContr (GroupStr.1g (str G) , φ .snd .IsGroupHom.pres1)

opaque
  isContrKer→isEmbedding : (φ : GroupHom G H) → isContrKer φ → isEmbedding (fst φ)
  isContrKer→isEmbedding {H} φ = injEmbedding (str H .GroupStr.is-set) ∘ isInjective→isMono φ ∘ isContrKer→isInjective φ

isEmbedding→isContrKer : (φ : GroupHom G H) → isEmbedding (fst φ) → isContrKer φ
isEmbedding→isContrKer φ is-emb = isInjective→isContrKer φ λ g φg≡1 → invEq (_ , is-emb _ _) $ φg≡1 ∙ sym (φ .snd .IsGroupHom.pres1)

isEquiv→isContrKer : (φ : GroupEquiv G H) → isContrKer (GroupEquiv→GroupHom φ)
isEquiv→isContrKer ((φ , φ-is-equiv) , φ-hom) = isEmbedding→isContrKer (φ , φ-hom) $ isEquiv→isEmbedding φ-is-equiv

opaque
  isContrKerComp : (φ : GroupHom G H) (ψ : GroupHom H K)
    → isContrKer φ
    → isContrKer ψ
    → isContrKer (compGroupHom φ ψ)
  isContrKerComp φ ψ φ-emb ψ-emb = isEmbedding→isContrKer (compGroupHom φ ψ) $
    isEmbedding-∘ {f = ψ .fst} {h = φ .fst} (isContrKer→isEmbedding ψ ψ-emb) (isContrKer→isEmbedding φ φ-emb)

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
  no-eta-equality
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

  inc-emb : ⟨ H ⟩ ↪ ⟨ G ⟩
  inc-emb .fst = inc-fun
  inc-emb .snd = is-embedding-inc-fun

unquoteDecl isSubgroupIsoΣ = declareRecordIsoΣ isSubgroupIsoΣ (quote isSubgroup)

infix 4 _≤_
_≤_ : (H : Group ℓH) (G : Group ℓG) → Type _
_≤_ H G = isSubgroup G H

Embedding→isSubgroup : (ι : ⟨ G ⟩ ↪ ⟨ H ⟩) → IsGroupHom (str G) (ι .fst) (str H) → G ≤ H
Embedding→isSubgroup (ι , ι-emb) ι-hom .isSubgroup.inc = ι , ι-hom
Embedding→isSubgroup (ι , ι-emb) ι-hom .isSubgroup.is-contr-ker-inc = isEmbedding→isContrKer (ι , ι-hom) ι-emb

instance
  isSubgroupToΣ : RecordToΣ (isSubgroup G H)
  isSubgroupToΣ = toΣ isSubgroupIsoΣ

opaque
  isSetIsSubgroup : isSet (isSubgroup G H)
  isSetIsSubgroup = recordIsOfHLevel 2 $ isSetΣSndProp isSetGroupHom isPropIsContrKer

-- Subgroup : ∀ (G : Group ℓG) (ℓH : Level) → Type (ℓ-max ℓG (ℓ-suc ℓH))
-- Subgroup G ℓH = Σ[ H ∈ Group ℓH ] isSubgroup G H
record Subgroup (G : Group ℓG) (ℓH : Level) : Type (ℓ-max ℓG (ℓ-suc ℓH)) where
  no-eta-equality
  constructor mkSubgroup
  field
    sub : Group ℓH
    is-sub : sub ≤ G

  open isSubgroup is-sub public

unquoteDecl SubgroupIsoΣ = declareRecordIsoΣ SubgroupIsoΣ (quote Subgroup)

instance
  SubgroupToΣ : RecordToΣ (Subgroup G ℓH)
  SubgroupToΣ = toΣ SubgroupIsoΣ

mkSubgroupPathP : ∀ {G₀ G₁ : Group ℓG} {G : G₀ ≡ G₁}
  → {H₀ : Subgroup G₀ ℓ}
  → {H₁ : Subgroup G₁ ℓ}
  → (p : H₀ .Subgroup.sub ≡ H₁ .Subgroup.sub)
  → (q : PathP (λ i → GroupHom (p i) (G i)) (Subgroup.inc H₀) (Subgroup.inc H₁))
  → PathP (λ i → Subgroup (G i) ℓ) H₀ H₁
mkSubgroupPathP p q i .Subgroup.sub = p i
mkSubgroupPathP p q i .Subgroup.is-sub .isSubgroup.inc = q i
mkSubgroupPathP {H₀} {H₁} p q i .Subgroup.is-sub .isSubgroup.is-contr-ker-inc = isProp→PathP (λ i → isPropIsContrKer (q i)) (Subgroup.is-contr-ker-inc H₀) (Subgroup.is-contr-ker-inc H₁) i

SubgroupPath : (H K : Subgroup G ℓ) → Type _
SubgroupPath H K = Σ[ e ∈ GroupEquiv H.sub K.sub ] H.inc-fun ≡ K.inc-fun ∘ groupEquivFun e where
  module H = Subgroup H
  module K = Subgroup K

isPropSubgroupPath : (H K : Subgroup G ℓ) → isProp (SubgroupPath H K)
isPropSubgroupPath {G} H K (((e , e-equiv) , e-group-hom) , e-comm) (((f , f-equiv) , f-group-hom) , f-comm) =
  Σ≡Prop (λ e → isOfHLevelPath' 1 (isSet→ G.is-set) _ _) (GroupEquiv≡ $ equivEq equiv-eq)
  where
  module G = GroupStr (str G)

  module K = Subgroup K

  comm-lemma : K.inc-fun ∘ e ≡ K.inc-fun ∘ f
  comm-lemma = sym e-comm ∙ f-comm

  equiv-eq : e ≡ f
  equiv-eq = isEmbedding→Injection' K.inc-fun K.is-embedding-inc-fun e f comm-lemma

module isSubgroupPathP'
  {G₀ G₁ : Group ℓG}
  (G : G₀ ≡ G₁)
  (H₀ H₁ : Group ℓH)
  (inc₀ : H₀ ≤ G₀)
  (inc₁ : H₁ ≤ G₁)
  (p : H₀ ≡ H₁)
  where
  private
    module H₀ = isSubgroup inc₀
    module H₁ = isSubgroup inc₁

  isSubgroupPathP :
      PathP (λ i → ⟨ p i ⟩ → ⟨ G i ⟩) H₀.inc-fun H₁.inc-fun
    → PathP (λ i → (p i) ≤ G i) inc₀ inc₁
  isSubgroupPathP pᴰ = inc-path where
    hom-path : PathP (λ i → GroupHom (p i) (G i)) H₀.inc H₁.inc
    hom-path i .fst = pᴰ i
    hom-path i .snd = isProp→PathP (λ i → isPropIsGroupHom (p i) (G i) {f = pᴰ i}) H₀.is-hom H₁.is-hom i

    inc-path : PathP (λ i → (p i) ≤ G i) inc₀ inc₁
    inc-path i .isSubgroup.inc = hom-path i
    inc-path i .isSubgroup.is-contr-ker-inc = isProp→PathP (λ i → isPropIsContrKer (hom-path i)) H₀.is-contr-ker-inc H₁.is-contr-ker-inc i


  isSubgroupPathPEquiv :
    PathP (λ i → ⟨ p i ⟩ → ⟨ G i ⟩) H₀.inc-fun H₁.inc-fun
      ≃
    PathP (λ i → (p i) ≤ G i) inc₀ inc₁
  isSubgroupPathPEquiv = propBiimpl→Equiv
    (isOfHLevelPathP' 1 (isSet→ (str G₁ .GroupStr.is-set)) H₀.inc-fun H₁.inc-fun)
    (isOfHLevelPathP' 1 isSetIsSubgroup _ _)
    isSubgroupPathP
    (congP (λ i → isSubgroup.inc-fun))

SubgroupPathP : {G₀ G₁ : Group ℓG} (G : G₀ ≡ G₁)
  → {H₀ : Subgroup G₀ ℓ} {H₁ : Subgroup G₁ ℓ}
  → (H : H₀ .Subgroup.sub ≡ H₁ .Subgroup.sub)
  → PathP (λ i → ⟨ H i ⟩ → ⟨ G i ⟩) (Subgroup.inc-fun H₀) (Subgroup.inc-fun H₁)
  → PathP (λ i → Subgroup (G i) ℓ) H₀ H₁
SubgroupPathP G H inc i .Subgroup.sub = H i
SubgroupPathP G {H₀} {H₁} H inc i .Subgroup.is-sub = isSubgroupPathP'.isSubgroupPathP G (Subgroup.sub H₀) (Subgroup.sub H₁) (Subgroup.is-sub H₀) (Subgroup.is-sub H₁) H inc i

module _
  {G₀ G₁ : Group ℓG}
  (γ : GroupEquiv G₀ G₁)
  {H₀ H₁ : Group ℓ}
  (η : GroupEquiv H₀ H₁)
  (inc₀ : H₀ ≤ G₀)
  (inc₁ : H₁ ≤ G₁)
  where
  private
    γ→ = equivFun (γ .fst)
    η→ = equivFun (η .fst)
    module H₀ = isSubgroup inc₀
    module H₁ = isSubgroup inc₁

  GroupEquiv→isSubgroupPathP :
    ((h₀ : ⟨ H₀ ⟩) → γ→ (H₀.inc-fun h₀) ≡ H₁.inc-fun (η→ h₀))
      →
    PathP (λ i → (uaGroup η i) ≤ (uaGroup γ i)) inc₀ inc₁
  GroupEquiv→isSubgroupPathP comm = isSubgroupPathP'.isSubgroupPathP
    (uaGroup γ)
    H₀
    H₁
    inc₀
    inc₁
    (uaGroup η)
    (ua→ua comm)

module _
  {G₀ G₁ : Group ℓG} {γ : GroupEquiv G₀ G₁}
  (H₀ : Subgroup G₀ ℓ)
  (H₁ : Subgroup G₁ ℓ)
  (η : GroupEquiv (Subgroup.sub H₀) (Subgroup.sub H₁))
  where
  private
    γ→ = equivFun (γ .fst)
    η→ = equivFun (η .fst)
    module H₀ = Subgroup H₀
    module H₁ = Subgroup H₁

  GroupEquiv→SubgroupPathP :
    ((h₀ : ⟨ H₀.sub ⟩) → γ→ (H₀.inc-fun h₀) ≡ H₁.inc-fun (η→ h₀))
    → PathP (λ i → Subgroup (uaGroup γ i) ℓ) H₀ H₁
  GroupEquiv→SubgroupPathP comm i .Subgroup.sub = uaGroup η i
  GroupEquiv→SubgroupPathP comm i .Subgroup.is-sub = GroupEquiv→isSubgroupPathP γ η (H₀.is-sub) (H₁.is-sub) comm i

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
SubgroupPathEquiv {G} H K =
  (Σ[ e ∈ GroupEquiv H.sub K.sub ] H.inc-fun ≡ K.inc-fun ∘ groupEquivFun e)
    ≃⟨ Σ-cong-equiv-snd (λ (e , _) → invEquiv funExtEquiv ∙ₑ ua→Equiv {e = e} {B = λ _ → ⟨ G ⟩}) ⟩
  (Σ[ e ∈ GroupEquiv H.sub K.sub ] PathP (λ i → ua (e .fst) i → ⟨ G ⟩) H.inc-fun K.inc-fun)
    ≃⟨ Σ-cong-equiv-fst (GroupPath _ _) ⟩
  (Σ[ p ∈ H.sub ≡ K.sub ] PathP (λ i → ⟨ p i ⟩ → ⟨ G ⟩) H.inc-fun K.inc-fun)
    ≃⟨ Σ-cong-equiv-snd $ isSubgroupPathPEquiv H.sub K.sub H.is-sub K.is-sub ⟩
  (Σ[ p ∈ H.sub ≡ K.sub ] PathP (λ i → isSubgroup G (p i)) H.is-sub K.is-sub)
    ≃⟨ ΣPathP≃PathPΣ ⟩
  {! !}
    ≃⟨ {! !} ⟩
  (H ≡ K) ≃∎
  where
    module H = Subgroup H
    module K = Subgroup K

isSetSubgroup : isSet (Subgroup G ℓH)
isSetSubgroup H K = isOfHLevelRespectEquiv 1 (SubgroupPathEquiv H K) (isPropSubgroupPath H K)

postCompEquiv→isSubgroup : ∀ {ℓK} {K : Group ℓK} → (φ : GroupEquiv G K) → H ≤ G → H ≤ K
postCompEquiv→isSubgroup {H} {K} φ ι = sub where
  module ι = isSubgroup ι

  sub : H ≤ K
  sub .isSubgroup.inc = compGroupHom ι.inc (GroupEquiv→GroupHom φ)
  sub .isSubgroup.is-contr-ker-inc = isContrKerComp ι.inc (GroupEquiv→GroupHom φ) ι.is-contr-ker-inc (isEquiv→isContrKer φ)

postCompEquiv→Subgroup : ∀ {ℓK} {K : Group ℓK} → (φ : GroupEquiv G K) → Subgroup G ℓH → Subgroup K ℓH
postCompEquiv→Subgroup φ H .Subgroup.sub = H .Subgroup.sub
postCompEquiv→Subgroup φ H .Subgroup.is-sub = postCompEquiv→isSubgroup φ (H .Subgroup.is-sub)

SubgroupDirProdRight : ∀ {ℓK} (G : Group ℓG) (K : Subgroup H ℓK) → Subgroup (DirProd G H) (ℓ-max ℓG ℓK)
SubgroupDirProdRight {H = H} G K = record { sub = G×K ; is-sub = G×K≤GH } where
  module K = Subgroup K

  G×K : Group _
  G×K = DirProd G K.sub

  -×inc = DirProd.mapRight G _ K.inc

  ker-equiv : Ker K.inc ≃ Ker -×inc
  ker-equiv =
    Ker K.inc
      ≃⟨ invEquiv (Σ-contractFst (isContrKerId G)) ⟩
    Ker (idGroupHom {G = G}) × Ker K.inc
      ≃⟨ shuffle ⟩
    Σ[ g ∈ ⟨ G ⟩ ] Σ[ h ∈ ⟨ K.sub ⟩ ] isInKer (idGroupHom {G = G}) g × isInKer K.inc h
      ≃⟨ Σ-cong-equiv-snd (λ g → Σ-cong-equiv-snd λ h → ΣPathP≃PathPΣ) ⟩
    Σ[ g ∈ ⟨ G ⟩ ] Σ[ h ∈ ⟨ K.sub ⟩ ] isInKer -×inc (g , h)
      ≃⟨ invEquiv Σ-assoc-≃ ⟩
    Σ[ x ∈ ⟨ G ⟩ × ⟨ K.sub ⟩ ] isInKer -×inc x
      ≃∎
    where
      shuffle : _ ≃ _
      shuffle = strictEquiv
        (λ { ((g , g≡1) , (k , k∈KerInc)) → (g , k , g≡1 , k∈KerInc) })
        (λ { (g , k , g≡1 , k∈KerInc) → ((g , g≡1) , (k , k∈KerInc)) })

  G×K≤GH : isSubgroup (DirProd G H) G×K
  G×K≤GH .isSubgroup.inc = -×inc
  G×K≤GH .isSubgroup.is-contr-ker-inc = isOfHLevelRespectEquiv 0 ker-equiv K.is-contr-ker-inc

-- SubgroupRestrictEquiv : (α : GroupEquiv G H) → {! !}
-- SubgroupRestrictEquiv = {! !}

SubgroupΠ : ∀ {ℓX} (X : Type ℓX) (G : X → Group ℓG)
  → (H : ∀ x → Subgroup (G x) ℓH)
  → Subgroup (ΠGroup G) (ℓ-max ℓH ℓX)
SubgroupΠ X G H = mkSubgroup ΠH ΠH≤ΠG where
  module H x = Subgroup (H x)

  ΠH : Group _
  ΠH = ΠGroup λ (x : X) → H x .Subgroup.sub

  ΠH≤ΠG : isSubgroup (ΠGroup G) ΠH
  ΠH≤ΠG .isSubgroup.inc .fst h x = H.inc-fun x (h x)
  ΠH≤ΠG .isSubgroup.inc .snd = makeIsGroupHom λ h₀ h₁ → funExt λ x → H.pres· x (h₀ x) (h₁ x)
  ΠH≤ΠG .isSubgroup.is-contr-ker-inc = isInjective→isContrKer (ΠH≤ΠG .isSubgroup.inc) λ h h∈Ker → funExt λ x → isContrKer→isInjective (H.inc x) (H.is-contr-ker-inc x) (h x) (h∈Ker ≡$ x)

isClosedSubset→Subgroup : ∀ {ℓP} (G : Group ℓG) → (P : ⟨ G ⟩ → Type ℓP)
  → (∀ g → isProp (P g))
  → (let open GroupStr (str G))
  → (1* : P 1g)
  → (mul* : ∀ {g h} → P g → P h → P (g · h))
  → (inv* : ∀ {g} → P g → P (inv g))
  → Subgroup G _
isClosedSubset→Subgroup G P is-prop-P 1* mul* inv* = sub where
  open GroupStr (str G)
  G≡ = Σ≡Prop is-prop-P

  GP : Group _
  GP .fst = Σ ⟨ G ⟩ P
  GP .snd .GroupStr.1g = 1g , 1*
  GP .snd .GroupStr._·_ (g , pg) (h , ph) = g · h , mul* pg ph
  GP .snd .GroupStr.inv (g , pg) = inv g , inv* pg
  GP .snd .GroupStr.isGroup = makeIsGroup (isSetΣSndProp is-set is-prop-P)
    (λ _ _ _ → G≡ (·Assoc _ _ _))
    (λ _ → G≡ (·IdR _))
    (λ _ → G≡ (·IdL _))
    (λ _ → G≡ (·InvR _))
    (λ _ → G≡ (·InvL _))

  inc : GroupHom GP G
  inc .fst = fst
  inc .snd = makeIsGroupHom λ _ _ → refl

  sub : Subgroup G _
  sub .Subgroup.sub = GP
  sub .Subgroup.is-sub .isSubgroup.inc .fst = fst
  sub .Subgroup.is-sub .isSubgroup.inc .snd = makeIsGroupHom λ _ _ → refl
  sub .Subgroup.is-sub .isSubgroup.is-contr-ker-inc = isEmbedding→isContrKer inc λ g h → isEmbeddingFstΣProp is-prop-P

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
