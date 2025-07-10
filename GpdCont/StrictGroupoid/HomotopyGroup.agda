module GpdCont.StrictGroupoid.HomotopyGroup where

open import GpdCont.Prelude
open import GpdCont.Connectivity
open import GpdCont.Equiv
open import GpdCont.Embedding
open import GpdCont.HomotopySet
open import GpdCont.SetTruncation as ST using (isConnected-fiber-∣-∣₂)

open import GpdCont.StrictGroupoid.Base renaming (elimProp to elimProp')
open import GpdCont.StrictGroupoid.Morphism

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed.Base as Pointed using (Pointed)
open import Cubical.Foundations.Equiv.Properties using (hasSection)
open import Cubical.Foundations.Path using (compPathrEquiv ; congPathEquiv)
open import Cubical.Foundations.Powerset
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂ ; ∣_∣₂)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
open import Cubical.HITs.Wedge as Wedge using (_⋁_)

private
  variable
    ℓ ℓ′ ℓX ℓY : Level
    X : Type

isHGroup : StrictGroupoid ℓ → Type ℓ
isHGroup G = isPathConnected ⟨ G ⟩

isPropIsHGroup : (G : StrictGroupoid ℓ) → isProp (isHGroup G)
isPropIsHGroup G = isPropIsPathConnected ⟨ G ⟩

hGroup : (ℓ : Level) → Type (ℓ-suc ℓ)
hGroup ℓ = Σ[ G ∈ StrictGroupoid ℓ ] isHGroup G

⟨_⟩ᵗ : hGroup ℓ → Type ℓ
⟨ (G , _) , _ ⟩ᵗ = G

module hGroup (G : hGroup ℓ) where
  open StrictGroupoidStr (str (G .fst)) public

  Tr : Type _
  Tr = ∥ ⟨ G .fst ⟩ ∥₂

  is-connected : isPathConnected ⟨ G .fst ⟩
  is-connected = G .snd

  center : Tr
  center = is-connected .fst

  centerElimEquiv : ∀ {ℓB} {B : Tr → Type ℓB}
    → B center ≃ (∀ x → B x)
  centerElimEquiv {B} = invEquiv (Π-contractDom is-connected)

  centerElim : ∀ {ℓB} {B : ∥ ⟨ G .fst ⟩ ∥₂ → Type ℓB}
    → B center
    → ∀ x → B x
  centerElim = equivFun centerElimEquiv

  pt₀ : ⟨ G .fst ⟩
  pt₀ = pt center

  asPointed : Pointed ℓ
  asPointed .fst = ⟨ G .fst ⟩
  asPointed .snd = pt₀

  asGroupoid : hGroupoid ℓ
  asGroupoid .fst = ⟨ G . fst ⟩
  asGroupoid .snd = is-groupoid

  mere-path : ∀ g → ∥ pt₀ ≡ g ∥₁
  mere-path g = isPathConnected→merePath is-connected pt₀ g

  elimProp : ∀ {ℓP} {P : ⟨ G ⟩ᵗ → Type ℓP}
    → (∀ g → isProp (P g))
    → (P pt₀)
    → ∀ g → P g
  elimProp {P} is-prop-P p₀ = elimProp' (G .fst) is-prop-P p* where
    -- G has a unique connected component,
    -- so the domain of this map is contractible:
    p* : (x : ∥ ⟨ G .fst ⟩ ∥₂) → P (pt x)
    p* = Π-contractDomIso is-connected .Iso.inv p₀

  elimPropᵝ : ∀ {ℓP} {P : ⟨ G ⟩ᵗ → Type ℓP}
    → (is-prop-P : ∀ g → isProp (P g))
    → (p₀ : P pt₀)
    → elimProp is-prop-P p₀ pt₀ ≡ p₀
  elimPropᵝ is-prop-P p₀ = {! !}

  module _ (is-set-X : isSet X) where
    recSetEquiv : X ≃ (⟨ G ⟩ᵗ → X)
    recSetEquiv = isPathConnected→constEquiv is-connected is-set-X

    recSet : (x₀ : X) → ⟨ G ⟩ᵗ → X
    recSet = equivFun recSetEquiv

  {-
  elimConnected : {X : ⟨ G ⟩ᵗ → Type ℓX} (is-conn-X : ∀ g → isPathConnected (X g))
    → (x₀ : X pt₀)
    → ∀ g → X g
  elimConnected is-conn-X x₀ = isConnectedPoint.elim 1 (isPathConnected→is2Connected is-connected) {! !} {! !}

  elimSet' : {X : ⟨ G ⟩ᵗ → Type ℓX} (is-set-X : ∀ g → isSet (X g))
    → (x₀ : X pt₀)
    → {! !}
    → ∀ g → X g
  elimSet' {X} is-set-X x₀ p = {! recSet  !}

  elimSet : {X : ⟨ G ⟩ᵗ → Type ℓX} (is-set-X : ∀ g → isSet (X g))
    → (x₀ : X pt₀)
    → {! !}
    → ∀ g → X g
  elimSet {X} is-set-X x₀ p g = PT.elim→Set {! !} f {! !} (mere-path g) where
    f : pt₀ ≡ g → X g
    f p = subst X p x₀

    f-filler : (p : pt₀ ≡ g) → PathP (λ i → X (p i)) x₀ (f p)
    f-filler p = subst-filler X p x₀

    link : (p q : pt₀ ≡ g) → f p ≡ f q
    link p q = {!doubleCompPathP (λ i j → X (p i)) (f-filler p) !}
  -}

hGroup≡ : ∀ {G H : hGroup ℓ} → G .fst ≡ H .fst → G ≡ H
hGroup≡ = Σ≡Prop isPropIsHGroup

hGroupHom : (G : hGroup ℓ) (H : hGroup ℓ′) → Type _
hGroupHom (G , _) (H , _) = StrictFun G H

module hGroupHom {ℓ} {ℓ′} (G : hGroup ℓ) (H : hGroup ℓ′) (φ : hGroupHom G H) where
  private
    module G = hGroup G
    module H = hGroup H

  open Σ φ public renaming (fst to fun ; snd to pres-pt)

  pres-pt₀ : fun G.pt₀ ≡ H.pt₀
  pres-pt₀ = sym (pres-pt ≡$ G.center) ∙ cong H.pt (isContr→isProp H.is-connected (ST.map fun G.center) H.center)

module _ {ℓ} {ℓ′} (G : hGroup ℓ) (H : hGroup ℓ′) where
  private
    module G = hGroup G
    module H = hGroup H

  hGroupHomStrEquiv : (φ : ⟨ G ⟩ᵗ → ⟨ H ⟩ᵗ) → (φ G.pt₀ ≡ H.pt₀) ≃ (StrictFunStr (G .fst) (H .fst) φ)
  hGroupHomStrEquiv φ =
    (φ G.pt₀ ≡ H.pt₀) ≃⟨ compPathrEquiv $ cong H.pt (isContr→isProp H.is-connected H.center (ST.map φ G.center)) ⟩
    (φ G.pt₀ ≡ H.pt (ST.map φ G.center)) ≃⟨ symEquiv ⟩
    (H.pt (ST.map φ G.center) ≡ φ G.pt₀) ≃⟨ G.centerElimEquiv ⟩
    ((x : G.Tr) → H.pt (ST.map φ x) ≡ φ (G.pt x)) ≃⟨ funExtEquiv ⟩
    (StrictFunStr (G .fst) (H .fst) φ) ≃∎

  hGroupHomEquiv : (Σ[ φ ∈ (⟨ G ⟩ᵗ → ⟨ H ⟩ᵗ) ] φ G.pt₀ ≡ H.pt₀) ≃ (hGroupHom G H)
  hGroupHomEquiv = Σ-cong-equiv-snd hGroupHomStrEquiv

  mkHGroupHom :
    ∀ (φ : ⟨ G ⟩ᵗ → ⟨ H ⟩ᵗ)
    → (pres-pt₀ : φ (hGroup.pt₀ G) ≡ hGroup.pt₀ H)
    → hGroupHom G H
  mkHGroupHom φ pres-pt₀ .fst = φ
  mkHGroupHom φ pres-pt₀ .snd = equivFun (hGroupHomStrEquiv φ) pres-pt₀

  hGroupHom≡ :
    ∀ {φ ψ : hGroupHom G H}
    → (p : φ .fst ≡ ψ .fst)
    → PathP (λ i → p i G.pt₀ ≡ H.pt₀) (hGroupHom.pres-pt₀ G H φ) (hGroupHom.pres-pt₀ G H ψ)
    → φ ≡ ψ
  hGroupHom≡ {φ} {ψ} p q = ΣPathP (p , {! !}) where
    module φ = hGroupHom G H φ
    module ψ = hGroupHom G H ψ

    -- e : PathP (λ i → StrictFunStr (fst G) (fst H) (p i)) (snd φ) (snd ψ) ≃ PathP (λ i → p i G.pt₀ ≡ H.pt₀) {! equivFun (hGroupHomStrEquiv (φ .fst)) !} {! !}
    -- e = congPathEquiv {! !}

    -- -- f : PathP (λ i → p i G.pt₀ ≡ H.pt₀) {! equivFun (hGroupHomStrEquiv (φ .fst)) !} {! !} ≃ PathP (λ i → StrictFunStr (fst G) (fst H) (p i)) (snd φ) (snd ψ)
    f : PathP (λ i → p i G.pt₀ ≡ H.pt₀) φ.pres-pt₀ ψ.pres-pt₀ ≃ PathP (λ i → StrictFunStr (fst G) (fst H) (p i)) (fst (hGroupHomStrEquiv (fst φ)) φ.pres-pt₀) (fst (hGroupHomStrEquiv (fst ψ)) ψ.pres-pt₀)
    f = congPathEquiv λ i → hGroupHomStrEquiv (p i)

    pᴰ-ext : Square (φ.pres-pt ≡$ G.center) (ψ.pres-pt ≡$ G.center) (λ i → H.pt (ST.map (p i) G.center)) (p ≡$ G.pt₀)
    pᴰ-ext = {! !}

    pᴰ : PathP (λ i → StrictFunStr (fst G) (fst H) (p i)) (snd φ) (snd ψ)
    pᴰ = funExtSquare $ G.centerElim pᴰ-ext

pointedConnectedGroupoid→hGroup : ∀ (G : Type ℓ)
  → (g₀ : G)
  → isPathConnected G
  → isGroupoid G
  → hGroup ℓ
pointedConnectedGroupoid→hGroup G g₀ is-conn-G is-groupoid-G = G* where
  G* : hGroup _
  G* .fst .fst = G
  G* .fst .snd .StrictGroupoidStr.is-groupoid = is-groupoid-G
  G* .fst .snd .StrictGroupoidStr.pt = const g₀
  G* .fst .snd .StrictGroupoidStr.pt-section = isContr→isProp is-conn-G ∣ g₀ ∣₂
  G* .snd = is-conn-G

Aut : (A : hGroupoid ℓ) (a₀ : ⟨ A ⟩) → hGroup _
Aut (A , is-groupoid-A) a₀ = pointedConnectedGroupoid→hGroup G g₀ conn-G is-groupoid-G where
  G : Type _
  G = fiber ∣_∣₂ ∣ a₀ ∣₂

  g₀ : G
  g₀ .fst = a₀
  g₀ .snd = refl′ ∣ a₀ ∣₂

  conn-G : isPathConnected G
  conn-G = isConnected-fiber-∣-∣₂ ∣ a₀ ∣₂

  is-groupoid-G : isGroupoid G
  is-groupoid-G = isGroupoidΣ is-groupoid-A λ a → isProp→isOfHLevelSuc 2 (ST.isSetSetTrunc ∣ a ∣₂ ∣ a₀ ∣₂)

module _ (A : hGroupoid ℓ) (a₀ : ⟨ A ⟩) where
  AutEmbedding : ⟨ Aut A a₀ ⟩ᵗ ↪ ⟨ A ⟩
  AutEmbedding = EmbeddingΣProp λ a → ST.isSetSetTrunc ∣ a ∣₂ ∣ a₀ ∣₂

  AutPathEquiv : ∀ (x y : ⟨ Aut A a₀ ⟩ᵗ) → (x ≡ y) ≃ Path ⟨ A ⟩ (x .fst) (y .fst)
  AutPathEquiv x y .fst = cong fst
  AutPathEquiv x y .snd = AutEmbedding .snd x y

Aut∙ : (A : Pointed ℓ) → isGroupoid ⟨ A ⟩ → hGroup _
Aut∙ (A , a₀) is-groupoid-A = Aut (A , is-groupoid-A) a₀

module _ {ℓK} (K : Type ℓK) (G : K → hGroup ℓ) where
  private
    module G k = hGroup (G k)

    ΠG : hGroupoid _
    ΠG .fst = ∀ k → ⟨ G k ⟩ᵗ
    ΠG .snd = isGroupoidΠ G.is-groupoid

    Πpt : ∀ k → ⟨ G k ⟩ᵗ
    Πpt = G.pt₀

  ΠGroup : hGroup (ℓ-max ℓ ℓK)
  ΠGroup = Aut ΠG Πpt

  ΠGroupEmbedding : ⟨ ΠGroup ⟩ᵗ ↪ ((k : K) → ⟨ G k ⟩ᵗ)
  ΠGroupEmbedding = AutEmbedding ΠG Πpt

module _ {ℓK} (K : Type ℓK) (G : hGroup ℓ) where
  FunGroup : hGroup _
  FunGroup = ΠGroup K $ const G

  FunGroupEmbedding : ⟨ FunGroup ⟩ᵗ ↪ (K → ⟨ G ⟩ᵗ)
  FunGroupEmbedding = ΠGroupEmbedding K $ const G

proj : ∀ {K : Type ℓ} (G : K → hGroup ℓ) → ∀ k → hGroupHom (ΠGroup K G) (G k)
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

Sym : (X : hSet ℓ) → hGroup (ℓ-suc ℓ)
Sym X = Aut (hSet _ , isGroupoidHSet) X

-- ∗ = \ast
_∗_ : (G H : hGroup ℓ) → hGroup ℓ
G ∗ H = Aut∙ G⋁H is-groupoid-G⋁H where
  module G = hGroup G
  module H = hGroup H

  G⋁H : Pointed _
  G⋁H = G.asPointed Wedge.⋁∙ₗ H.asPointed

  is-groupoid-G⋁H : isGroupoid ⟨ G⋁H ⟩
  is-groupoid-G⋁H = {! !}

⨁Group : (K : Type ℓ) (G : K → hGroup ℓ) → hGroup ℓ
⨁Group K G = Aut∙ (Wedge.⋁gen∙ K (hGroup.asPointed ∘ G)) is-groupoid-⨁G where
  abstract
    is-groupoid-⨁G : isGroupoid ⟨ Wedge.⋁gen∙ K (hGroup.asPointed ∘ G) ⟩
    is-groupoid-⨁G = {! !}

hAction : (ℓX : Level) → hGroup ℓ → Type _
hAction ℓX G = ⟨ G ⟩ᵗ → hSet ℓX

isFaithful : (G : hGroup ℓ) (X : hAction ℓX G) → Type _
isFaithful G X = isOfHLevelFun 2 X

isPropIsFaithful : (G : hGroup ℓ) (X : hAction ℓX G) → isProp (isFaithful G X)
isPropIsFaithful G X = isPropΠ λ _ → isPropIsSet

Pr' : (G : hGroup ℓ) → ⟨ G ⟩ᵗ → hAction ℓ G
Pr' G g₀ g .fst = g₀ ≡ g
Pr' G g₀ g .snd = hGroup.is-groupoid G g₀ g

Pr : (G : hGroup ℓ) → hAction ℓ G
Pr G = Pr' G $ hGroup.pt₀ G

Pr* : (G : hGroup ℓ) → ⟨ G ⟩ᵗ → Σ[ X ∈ hAction ℓ G ] ∥ Pr G ≡ X ∥₁
Pr* G g₀ .fst = Pr' G g₀
Pr* G g₀ .snd = PT.map (λ p → funExt λ g → hSet≡ (cong (_≡ g) p)) (hGroup.mere-path G g₀)

-- Pr⁻ : (G : hGroup ℓ) → Σ[ X ∈ hAction ℓ G ] ∥ Pr G ≡ X ∥₁ → ⟨ G ⟩ᵗ
-- Pr⁻ G = uncurry λ X → PT.rec→Gpd {! !} (λ h → {! h ≡$ hGroup.pt₀ G !}) (record { link = {! !} ; coh₁ = {! !} })

-- yonedaPr≃ : (G : hGroup ℓ) (g h : ⟨ G ⟩ᵗ) → (g ≡ h) ≃ (Pr* G g ≡ Pr* G h)
-- yonedaPr≃ G g h = {! !}
--   -- (g ≡ h) ≃⟨ {! !} ⟩
--   -- ((G.pt₀ ≡ g) ≡ (G.pt₀ ≡ h)) ≃⟨ hSet≡Equiv ⟩
--   -- (Pr G g ≡ Pr G h) ≃∎
--   -- where module G = hGroup G


-- yonedaPr : (G : hGroup ℓ) (g h : ⟨ G ⟩ᵗ) → isEquiv (λ (p : g ≡ h) → cong (Pr* G) p)
-- yonedaPr G g h = isoToIsEquiv λ where
--   .Iso.fun → _
--   .Iso.inv x → {! cong (fst) x !}
--   .Iso.leftInv → {! !}
--   .Iso.rightInv → {! !}

-- ???
isFaithfulPr : (G : hGroup ℓ) → isFaithful G (Pr G)
isFaithfulPr G = ST.isEmbeddingCong→hasSetFibers (Pr G) λ g h → injEmbedding (isOfHLevelPath' 2 isGroupoidHSet _ _) (Pr⁻ g h _ _) where
  module G = hGroup G
  Pr⁻ : (g h : ⟨ G ⟩ᵗ) → (p q : g ≡ h) → cong (Pr G) p ≡ cong (Pr G) q → p ≡ q
  Pr⁻ g h p q sq = {! !} where
    sq' : Square (λ i → G.pt₀ ≡ p i) (λ i → G.pt₀ ≡ q i) refl refl
    sq' i j = ⟨ sq i j ⟩
  -- isOfHLevelFunOfImage→isOfHLevelFun 1 _ (G.elimProp {! !} goal) where
  -- module G = hGroup G
  -- foo : (fiber (Pr G) (Pr G G.pt₀)) ≃ {! !}
  -- foo =
  --   (fiber (Pr G) (Pr G G.pt₀)) ≃⟨ {! !} ⟩
  --   Σ[ g ∈ ⟨ G ⟩ᵗ ] (Pr G g) ≡ (Pr G G.pt₀) ≃⟨ {! !} ⟩
  --   Σ[ g ∈ ⟨ G ⟩ᵗ ] (G.pt₀ ≡ g) ≡ (G.pt₀ ≡ G.pt₀) ≃⟨ {! !} {- Yoneda? -} ⟩
  --   Σ[ g ∈ ⟨ G ⟩ᵗ ] g ≡ G.pt₀ ≃⟨ {! !} ⟩
  --   singl G.pt₀ ≃∎

  -- goal : (x y : fiber (Pr G) (Pr G G.pt₀)) → isProp (x ≡ y)
  -- goal = {! !}

∫ : (G : hGroup ℓ) (X : hAction ℓX G) → hGroupoid (ℓ-max ℓ ℓX)
∫ G X .fst = Σ[ g ∈ ⟨ G ⟩ᵗ ] ⟨ X g ⟩
∫ G X .snd = isGroupoidΣ (hGroup.is-groupoid G) λ g → isSet→isGroupoid $ str $ X g

isTransitive : (G : hGroup ℓ) (X : hAction ℓX G) → Type _
isTransitive G X = isPathConnected ⟨ ∫ G X ⟩

Subgroup : (ℓX : Level) (G : hGroup ℓ) → Type _
Subgroup ℓX G = Σ[ X ∈ hAction ℓX G ] Σ[ x₀ ∈ ⟨ X (hGroup.pt₀ G) ⟩ ] isTransitive G X

isSetSubgroup : ∀ {ℓX} {G : hGroup ℓ} → isSet (Subgroup ℓX G)
isSetSubgroup = {! !}

Subgroup→hGroup : {G : hGroup ℓ} → Subgroup ℓX G → hGroup (ℓ-max ℓ ℓX)
Subgroup→hGroup {G} (X , x₀ , is-transitive-X) = pointedConnectedGroupoid→hGroup ⟨ ∫ G X ⟩ pt is-conn (str $ ∫ G X) where
  module G = hGroup G

  pt : ⟨ ∫ G X ⟩
  pt .fst = G.pt₀
  pt .snd = x₀

  is-conn : isPathConnected ⟨ ∫ G X ⟩
  is-conn = is-transitive-X

isMono : (G : hGroup ℓ) (H : hGroup ℓ′) (φ : hGroupHom G H) → Type _
isMono G H (φ , _) = isOfHLevelFun 2 φ

Mono : (ℓ : Level) (H : hGroup ℓ′) → Type _
Mono ℓ H = Σ[ G ∈ hGroup ℓ ] Σ[ ι ∈ hGroupHom G H ] isMono G H ι

isSetMono : ∀ {ℓ} {H : hGroup ℓ′} → isSet (Mono ℓ H)
isSetMono = {! !}

ΠActionΣ : (K : hSet ℓ′) (G : ⟨ K ⟩ → hGroup ℓ) (X : (k : ⟨ K ⟩) → hAction ℓX (G k)) → hAction (ℓ-max ℓ′ ℓX) (ΠGroup ⟨ K ⟩ G)
ΠActionΣ K G X (f , _) = ΣSet K λ k → X k (f k)

ΠActionΠ : {K : Type ℓ′} (G : K → hGroup ℓ) (X : (k : K) → hAction ℓX (G k)) → hAction (ℓ-max ℓ′ ℓX) (ΠGroup K G)
ΠActionΠ {K} G X (f , _) = ΠSet (λ (k : K) → X k (f k))

module _ (G : hGroup ℓ) (X : hAction ℓX G) where
  Subset : (ℓP : Level) → Type (ℓ-max (ℓ-max ℓ ℓX) (ℓ-suc ℓP))
  Subset ℓP = (g : ⟨ G ⟩ᵗ) → ⟨ X g ⟩ → hProp ℓP

  isSetSubSet : ∀ {ℓP} → isSet (Subset ℓP)
  isSetSubSet = isSetΠ2 λ g x → isSetHProp

  SubsetAction : ∀ {ℓP} → (P : Subset ℓP) → hAction (ℓ-max ℓX ℓP) G
  SubsetAction P g .fst = Σ[ x ∈ ⟨ X g ⟩ ] ⟨ P g x ⟩
  SubsetAction P g .snd = isSetΣSndProp (str (X g)) (str ∘ P g)

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

precompAction : (G : hGroup ℓ) (X : hAction ℓX G) (Y : hSet ℓ′) → hAction (ℓ-max ℓX ℓ′) G
precompAction G X Y = λ g → X g →Set Y

precompAction∫ : (G : hGroup ℓ) (X : hAction ℓX G) (Y : hSet ℓ′)
  → ⟨ ∫ G (precompAction G X Y) ⟩ ≃ {! !}
precompAction∫ G X Y =
  Σ[ g ∈ ⟨ G ⟩ᵗ ] (⟨ X g ⟩ → ⟨ Y ⟩) ≃⟨ {! !} ⟩
  {! !} ≃∎

Monoᴰ : (G : hGroup ℓ) (H : hGroup ℓ′)
  → (ι : ⟨ G ⟩ᵗ → ⟨ H ⟩ᵗ)
  → (X : hAction ℓX G)
  → (Y : hAction ℓY H)
  → Type _
Monoᴰ G H ι X Y = ∀ g → Σ[ f ∈ (⟨ X g ⟩ → ⟨ Y (ι g) ⟩) ] isOfHLevelFun 1 f

MonoAction : (ℓ ℓX : Level) (H : hGroup ℓ′) (Y : hAction ℓY H) → Type _
MonoAction ℓ ℓX H Y = Σ[ (G , ((ι , _) , _)) ∈ Mono ℓ H ] Σ[ X ∈ hAction ℓX G ] Monoᴰ G H ι X Y

private
  ℙˢ : (X : Type ℓX) → hSet _
  ℙˢ X .fst = ℙ X
  ℙˢ X .snd = isSetℙ

ℙ* : (G : hGroup ℓ) (X : hAction ℓX G) → hAction (ℓ-suc ℓX) G
ℙ* G X g = ℙˢ ⟨ X g ⟩

module _ (G : hGroup ℓ) (X : hAction ℓX G) (g₀ : ⟨ G ⟩ᵗ) (x₀ : ⟨ X g₀ ⟩) where
  Stab' : hGroup (ℓ-max ℓ ℓX)
  Stab' = Aut (∫ G X) (g₀ , x₀)

  StabEmbedding' : ⟨ Stab' ⟩ᵗ ↪ ⟨ ∫ G X ⟩
  StabEmbedding' = AutEmbedding (∫ G X) (g₀ , x₀)

  StabPathEquiv' : ∀ (x y : ⟨ Stab' ⟩ᵗ) → (x ≡ y) ≃ Path ⟨ ∫ G X ⟩ (x .fst) (y .fst)
  StabPathEquiv' = AutPathEquiv (∫ G X) (g₀ , x₀)

  StabAction' : hAction ℓ Stab'
  StabAction' x = Pr G (fst (StabEmbedding' .fst x))

  isFreeAt' : Type _
  isFreeAt' = isContr ⟨ Stab' ⟩ᵗ

  isPropIsFreeAt' : isProp isFreeAt'
  isPropIsFreeAt' = isPropIsContr

  isFreeAt'→isContrLoop-∫ : isFreeAt' → isContr (Path ⟨ ∫ G X ⟩ (_ , x₀) (_ , x₀))
  isFreeAt'→isContrLoop-∫ is-free-at = isOfHLevelRespectEquiv 0
    (StabPathEquiv' (_ , refl) (_ , refl))
    (isContr→isContrPath is-free-at _ _)

module _ (G : hGroup ℓ) (X : hAction ℓX G) (x₀ : ⟨ X (hGroup.pt₀ G) ⟩) where
  Stab : hGroup (ℓ-max ℓ ℓX)
  Stab = Stab' G X _ x₀

  StabAction : hAction ℓ Stab
  StabAction = StabAction' G X _ x₀

  private
    π-aut : ⟨ Aut (∫ G X) (_ , x₀) ⟩ᵗ → ⟨ ∫ G X ⟩
    π-aut = fst

    is-trunc-π-aut : isOfHLevelFun 2 π-aut
    is-trunc-π-aut = isOfHLevelFunSuc 1 $ isEmbedding→hasPropFibers (AutEmbedding (∫ G X) (_ , x₀) .snd)

    π-∫ : ⟨ ∫ G X ⟩ → ⟨ G ⟩ᵗ
    π-∫ = fst

    is-trunc-π-∫ : isOfHLevelFun 2 π-∫
    is-trunc-π-∫ g = goal where
      fiber-equiv : fiber π-∫ g ≃ ⟨ X g ⟩
      fiber-equiv =
        Σ[ (g' , x') ∈ ⟨ ∫ G X ⟩ ] g' ≡ g ≃⟨ strictEquiv (λ { ((g' , x') , p) → ((g' , sym p) , x') }) (λ { ((g' , p) , x') → ((g' , x') , sym p) }) ⟩
        Σ[ (g' , _) ∈ singl g ] ⟨ X g' ⟩ ≃⟨ Σ-contractFst (isContrSingl g) ⟩
        ⟨ X g ⟩ ≃∎

      goal : isSet (fiber π-∫ g)
      goal = isOfHLevelRespectEquiv 2 (invEquiv fiber-equiv) (str (X g))

  StabMono : Mono _ G
  StabMono .fst = Stab
  StabMono .snd .fst = mkHGroupHom Stab G (π-∫ ∘ π-aut) refl
  StabMono .snd .snd = isOfHLevelFunComp 2 π-∫ π-aut is-trunc-π-∫ is-trunc-π-aut

  isFreeAt : Type _
  isFreeAt = isFreeAt' G X _ x₀

  isPropIsFreeAt : isProp isFreeAt
  isPropIsFreeAt = isPropIsFreeAt' G X _ x₀

module _ (G : hGroup ℓ) (X : hAction ℓX G) where
  isFree : Type _
  isFree = ∀ x₀ → isFreeAt G X x₀

  isFree→isFreeAt' : isFree → (g : ⟨ G ⟩ᵗ) (x : ⟨ X g ⟩) → isFreeAt' G X g x
  isFree→isFreeAt' = hGroup.elimProp G (λ g → isPropΠ $ isPropIsFreeAt' G X g)

  isPropIsFree : isProp isFree
  isPropIsFree = isPropΠ $ isPropIsFreeAt G X

  isFree→isSet-∫ : isFree → isSet ⟨ ∫ G X ⟩
  isFree→isSet-∫ is-free = isContrLoops→isSet $ uncurry goal
    where module _ (g : ⟨ G ⟩ᵗ) (x : ⟨ X g ⟩) where
      goal : isContr ((g , x) ≡ (g , x))
      goal = isFreeAt'→isContrLoop-∫ G X g x $ isFree→isFreeAt' is-free g x

  isFree→isFaithful : isFree → isFaithful G X
  isFree→isFaithful is-free = {! !}

{-
module _ (G : hGroup ℓ) (X : hAction ℓX G) {g₀ : ⟨ G ⟩ᵗ} (P₀ : ℙ ⟨ X g₀ ⟩) where
  Stabℙ' : hGroup (ℓ-max ℓ (ℓ-suc ℓX))
  Stabℙ' = Stab' G (ℙ* G X) g₀ P₀

  StabℙAction' : hAction _ Stabℙ'
  StabℙAction' = StabAction' G (ℙ* G X) g₀ P₀

module _ (G : hGroup ℓ) (X : hAction ℓX G) (P₀ : ℙ ⟨ X (hGroup.pt₀ G) ⟩) where
  Stabℙ : hGroup (ℓ-max ℓ (ℓ-suc ℓX))
  Stabℙ = Stabℙ' G X P₀

  -- TODO: Is this the right way to define the canical action on the subsets of X?
  StabℙAction : hAction _ Stabℙ
  StabℙAction = StabℙAction' G X P₀

  StabℙSubgroup : Subgroup {! !} G
  StabℙSubgroup .fst = {! !}
  StabℙSubgroup .snd = {! !}

private
  Σ-cong-fiber :
    ∀ {A A′ : Type ℓ}
    → {B : A → Type ℓ′}
    → {B′ : A′ → Type ℓ′}
    → (n : HLevel)
    → isOfHLevel n A
    → isOfHLevel n A′
    → (∀ a → isOfHLevel n (B a))
    → (∀ a → isOfHLevel n (B′ a))
    → isOfHLevelFun n (λ ((p , q) : Σ[ p ∈ A ≡ A′ ] PathP (λ i → p i → Type ℓ′) B B′) → the (Σ A B ≡ Σ A′ B′) $ cong₂ Σ p q)
  Σ-cong-fiber {A} {A′} {B} {B′} n lvl-A lvl-A′ lvl-B lvl-B′ = {! !}
  -}
