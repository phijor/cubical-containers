{-# OPTIONS --lossy-unification #-}
module GpdCont.HomotopyGroup.Stabilizer where

open import GpdCont.Prelude
open import GpdCont.Embedding
open import GpdCont.HomotopySet
open import GpdCont.Connectivity
import      GpdCont.SetTruncation as ST
open import GpdCont.PropositionalTruncation as PT using (_>>=_ ; return)
open import GpdCont.HomotopyGroup.Base
open import GpdCont.HomotopyGroup.Aut
open import GpdCont.HomotopyGroup.Morphism
open import GpdCont.HomotopyGroup.Equiv
open import GpdCont.HomotopyGroup.Action
open import GpdCont.HomotopyGroup.Subgroup
open import GpdCont.HomotopyGroup.Subaction

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path using (PathP≃Path)
open import Cubical.Foundations.Powerset
open import Cubical.Functions.FunExtEquiv using (funExtNonDep⁻)
open import Cubical.Functions.Logic using (⊤)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
import      Cubical.HITs.SetTruncation as ST

private
  variable
    ℓ ℓ′ ℓX ℓY : Level

private
  ℙˢ : (X : Type ℓX) → hSet _
  ℙˢ X .fst = ℙ X
  ℙˢ X .snd = isSetℙ

ℙ* : (G : hGroup ℓ) (X : hAction ℓX G) → hAction (ℓ-suc ℓX) G
ℙ* G X g = ℙˢ ⟨ X g ⟩

module _ (G : hGroup ℓ) (X : hAction ℓX G) (g₀ : ⟨ G ⟩ᵗ) (x₀ : ⟨ X g₀ ⟩) where
  Stab' : hGroup (ℓ-max ℓ ℓX)
  Stab' = Aut (∫ G X) (g₀ , x₀)

  Stab'-fst : ⟨ Stab' ⟩ᵗ → ⟨ G ⟩ᵗ
  Stab'-fst ((g , _) , _) = g

  Stab'-fst-hom : g₀ ≡ hGroup.pt₀ G → hGroupHom Stab' G
  Stab'-fst-hom p = mkHGroupHom Stab'-fst p

  Stab'-snd : (s : ⟨ Stab' ⟩ᵗ) → ⟨ X (Stab'-fst s) ⟩
  Stab'-snd ((g , x) , _) = x

  StabEmbedding' : ⟨ Stab' ⟩ᵗ ↪ ⟨ ∫ G X ⟩
  StabEmbedding' = AutEmbedding (∫ G X) (g₀ , x₀)

  StabPathEquiv' : ∀ (x y : ⟨ Stab' ⟩ᵗ) → (x ≡ y) ≃ Path ⟨ ∫ G X ⟩ (x .fst) (y .fst)
  StabPathEquiv' = AutPathEquiv (∫ G X) (g₀ , x₀)

  -- StabAction' : hAction ℓ Stab'
  -- StabAction' x = Pr G (fst (StabEmbedding' .fst x))

  StabAction' : hAction ℓX Stab'
  StabAction' ((g , _) , _) = X g

  StabAction'-alt : hAction (ℓ-max ℓ ℓX) Stab'
  StabAction'-alt ((g , x) , _) .fst = Path ⟨ ∫ G X ⟩ (g₀ , x₀) (g , x)
  StabAction'-alt ((g , x) , _) .snd = isOfHLevelPath' 1 (str (∫ G X) _ _)

  StabMono' : Mono _ (Aut (hGroup.asGroupoid G) g₀)
  StabMono' .fst = Stab'
  StabMono' .snd .hGroupMono.hom .hGroupHom.fun (gx , gx-conn) .fst = gx .fst
  StabMono' .snd .hGroupMono.hom .hGroupHom.fun (gx , gx-conn) .snd = PT.map (cong fst) gx-conn
  StabMono' .snd .hGroupMono.hom .hGroupHom.pres-pt₀ = AutPath (hGroup.asGroupoid G) g₀ refl
  StabMono' .snd .hGroupMono.is-mono = {! !}

  isFreeAt' : Type _
  isFreeAt' = isContr ⟨ Stab' ⟩ᵗ

  isPropIsFreeAt' : isProp isFreeAt'
  isPropIsFreeAt' = isPropIsContr

  isFreeAt'→isContrLoop-∫ : isFreeAt' → isContr (Path ⟨ ∫ G X ⟩ (_ , x₀) (_ , x₀))
  isFreeAt'→isContrLoop-∫ is-free-at = isOfHLevelRespectEquiv 0
    (StabPathEquiv' _ _)
    (isContr→isContrPath is-free-at (hGroup.pt₀ Stab') (hGroup.pt₀ Stab'))

StabCongEquiv' : (G : hGroup ℓ) (X : hAction ℓX G) (g₀ : ⟨ G ⟩ᵗ) {x₀ x₁ : ⟨ X g₀ ⟩}
  → x₀ ≡ x₁
  → hGroupEquiv (Stab' G X g₀ x₀) (Stab' G X g₀ x₁)
StabCongEquiv' G X g₀ {x₀} {x₁} p = AutEquiv (∫ G X) (∫ G X) (idEquiv _) goal where
  goal : (g₀ , x₀) ≡ (g₀ , x₁)
  goal = ΣPathP (refl , p)

module _ (G : hGroup ℓ) (X : hAction ℓX G) (x₀ : ⟨ X (hGroup.pt₀ G) ⟩) where
  Stab : hGroup (ℓ-max ℓ ℓX)
  Stab = Stab' G X _ x₀

  Stab-fst : ⟨ Stab ⟩ᵗ → ⟨ G ⟩ᵗ
  Stab-fst = Stab'-fst G X _ x₀

  Stab-fst-hom : hGroupHom Stab G
  Stab-fst-hom = mkHGroupHom (λ { ((g , _) , _) → g }) refl

  Stab-snd : (s : ⟨ Stab ⟩ᵗ) → ⟨ X (Stab-fst s) ⟩
  Stab-snd = Stab'-snd G X _ x₀

  StabAction : hAction ℓX Stab
  StabAction = StabAction' G X _ x₀

  inhStabAction : ∀ g → ⟨ StabAction g ⟩
  inhStabAction = Stab-snd

  StabAction-alt : hAction (ℓ-max ℓ ℓX) Stab
  StabAction-alt = StabAction'-alt G X _ x₀

  private
    module G = hGroup G
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

  stabFstMono : hGroupMono Stab G
  stabFstMono .hGroupMono.hom = Stab-fst-hom
  stabFstMono .hGroupMono.is-mono = isOfHLevelFunComp 2 π-∫ π-aut is-trunc-π-∫ is-trunc-π-aut

  StabMono : Mono _ G
  StabMono .fst = Stab
  StabMono .snd = stabFstMono

  StabActionEmbedding : (gx : ⟨ Stab ⟩ᵗ) → ⟨ StabAction gx ⟩ ↪ ⟨ X (Stab-fst gx) ⟩
  StabActionEmbedding _ = id↪ _

  StabActionEmbedding-fun : (gx : ⟨ Stab ⟩ᵗ) → ⟨ StabAction-alt gx ⟩ → ⟨ X (Stab-fst gx) ⟩
  StabActionEmbedding-fun ((g , x) , _) p = subst (λ - → ⟨ X - ⟩) (cong fst p) x₀

  StabActionEmbedding-alt : (gx : ⟨ Stab ⟩ᵗ) → ⟨ StabAction-alt gx ⟩ ↪ ⟨ X (Stab-fst gx) ⟩
  StabActionEmbedding-alt gx .fst = StabActionEmbedding-fun gx
  StabActionEmbedding-alt gx@((g , x) , gx-conn) .snd = hasPropFibers→isEmbedding {! !} where
    fiber-equiv : ∀ (y : ⟨ X g ⟩) → fiber (StabActionEmbedding-fun gx) y ≃ {! !}
    fiber-equiv y =
      Σ[ p ∈ (_ , x₀) ≡ (g , x) ] subst (λ - → ⟨ X - ⟩) (cong fst p) x₀ ≡ y ≃⟨⟩
      Σ[ p ∈ (_ , x₀) ≡ (g , x) ] transport (λ i → ⟨ X (p i .fst) ⟩) x₀ ≡ y ≃⟨ Σ-cong-equiv-snd (λ p → invEquiv (PathP≃Path _ _ _)) ⟩
      Σ[ p ∈ (_ , x₀) ≡ (g , x) ] PathP (λ i → ⟨ X (p i .fst) ⟩) x₀ y ≃⟨ {! !}  ⟩
      Σ[ p ∈ G.pt₀ ≡ g ] PathP (λ i → ⟨ X (p i) ⟩) x₀ x × PathP (λ i → ⟨ X (p i) ⟩) x₀ y ≃⟨ {! !}  ⟩
      {! !} ≃∎

  StabSubaction : Subaction _ _ G X
  StabSubaction .fst = StabMono
  StabSubaction .snd .fst = StabAction
  StabSubaction .snd .snd = StabActionEmbedding

  isFreeAt : Type _
  isFreeAt = isFreeAt' G X _ x₀

  isPropIsFreeAt : isProp isFreeAt
  isPropIsFreeAt = isPropIsFreeAt' G X _ x₀

  isTrivialStab : isTrivial G → isTrivial Stab
  isTrivialStab is-triv-G = isTrivial→isTrivialMono G is-triv-G StabMono

StabCongEquiv : (G : hGroup ℓ) (X : hAction ℓX G) {x₀ x₁ : ⟨ X (hGroup.pt₀ G) ⟩}
  → x₀ ≡ x₁
  → hGroupEquiv (Stab G X x₀) (Stab G X x₁)
StabCongEquiv G X p = StabCongEquiv' G X _ p

module _ (G : hGroup ℓ) (X : hAction ℓX G) where
  private module G = hGroup G
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

  isFree×inhSet→isFaithful : isFree → ∥ ⟨ X G.pt₀ ⟩ ∥₁ → isFaithful G X
  isFree×inhSet→isFaithful is-free = PT.rec (isPropIsFaithful G X) λ where
    x* → isOfHLevelFunOfImage→isOfHLevelFun 1 _ λ where
      g* (g₀ , p₀) (g₁ , p₁) → {! !}

module _ (G : hGroup ℓ) (X : hAction ℓX G) {g₀ : ⟨ G ⟩ᵗ} (P₀ : ℙ ⟨ X g₀ ⟩) where
  Stabℙ' : hGroup (ℓ-max ℓ (ℓ-suc ℓX))
  Stabℙ' = Stab' G (ℙ* G X) g₀ P₀

  StabℙAction' : hAction _ Stabℙ'
  StabℙAction' = StabAction' G (ℙ* G X) g₀ P₀

  StabℙAction-alt' : hAction _ Stabℙ'
  StabℙAction-alt' ((g , P) , _) .fst = Σ[ x ∈ ⟨ X g ⟩ ] ⟨ P x ⟩
  StabℙAction-alt' ((g , P) , _) .snd = isSetΣSndProp (str (X g)) (str ∘ P)

  module _ (p : g₀ ≡ hGroup.pt₀ G) where
    StabℙMono' : Mono (ℓ-max ℓ (ℓ-suc ℓX)) G
    StabℙMono' .fst = Stabℙ'
    StabℙMono' .snd .hGroupMono.hom = Stab'-fst-hom G (ℙ* G X) g₀ P₀ p
    StabℙMono' .snd .hGroupMono.is-mono = {! !}

    StabℙSubaction-canon' : Subaction (ℓ-max ℓ (ℓ-suc ℓX)) ℓX G X
    StabℙSubaction-canon' .fst = StabℙMono'
    StabℙSubaction-canon' .snd .fst = StabℙAction-alt'
    StabℙSubaction-canon' .snd .snd ((g , p?), _)= EmbeddingΣProp λ x → str (p? x)

module _ (G : hGroup ℓ) (X : hAction ℓX G) (P₀ : ℙ ⟨ X (hGroup.pt₀ G) ⟩) where
  Stabℙ : hGroup (ℓ-max ℓ (ℓ-suc ℓX))
  Stabℙ = Stabℙ' G X P₀

  Stabℙ-fst : ⟨ Stabℙ ⟩ᵗ → ⟨ G ⟩ᵗ
  Stabℙ-fst = Stab-fst G (ℙ* G X) P₀

  Stabℙ-snd : (p : ⟨ Stabℙ ⟩ᵗ) → ℙ ⟨ X (Stabℙ-fst p) ⟩
  Stabℙ-snd = Stab-snd G (ℙ* G X) P₀

  -- TODO: Is this the right way to define the canical action on the subsets of X?
  StabℙAction : hAction _ Stabℙ
  StabℙAction = StabℙAction' G X P₀

  _ : ⟨ StabℙAction (hGroup.pt₀ Stabℙ) ⟩ ≡ ℙ ⟨ X (hGroup.pt₀ G) ⟩
  _ = refl

  inhStabℙAction : ∀ g → ⟨ StabℙAction g ⟩
  inhStabℙAction = Stabℙ-snd

  StabℙAction-alt : hAction _ Stabℙ
  StabℙAction-alt ((g , P) , _) .fst = Σ[ x ∈ ⟨ X g ⟩ ] ⟨ P x ⟩
  StabℙAction-alt ((g , P) , _) .snd = isSetΣSndProp (str (X g)) (str ∘ P)

  -- StabℙSubgroup : Subgroup {! !} G
  -- StabℙSubgroup .fst = {! !}
  -- StabℙSubgroup .snd = {! !}

  StabℙMono : Mono (ℓ-max ℓ (ℓ-suc ℓX)) G
  StabℙMono = StabMono G (ℙ* G X) P₀

  StabℙSubaction : Subaction _ _ G (ℙ* G X)
  StabℙSubaction = StabSubaction G (ℙ* G X) P₀

  StabℙSubaction-alt : Subaction (ℓ-max ℓ (ℓ-suc ℓX)) ℓX G (ℙ* G X)
  StabℙSubaction-alt .fst = StabℙMono
  StabℙSubaction-alt .snd .fst = StabℙAction-alt
  StabℙSubaction-alt .snd .snd = embedding where
    ι : (gx@((g , P) , _) : ⟨ Stabℙ ⟩ᵗ) → (Σ[ x ∈ ⟨ X g ⟩ ] ⟨ P x ⟩) → ℙ ⟨ X g ⟩
    ι ((g , P) , gP-conn) (x , p) = λ (x' : ⟨ X g ⟩) → (x ≡ x') , str (X g) _ _

    embedding : (gx@((g , P) , _) : ⟨ Stabℙ ⟩ᵗ) → (Σ[ x ∈ ⟨ X g ⟩ ] ⟨ P x ⟩) ↪ ℙ ⟨ X g ⟩
    embedding gx .fst = ι gx
    embedding gx@((g , P) , gP-conn) .snd = injEmbedding isSetℙ λ where
      {(x₀ , p₀)} {(x₁ , p₁)} htpy → Σ≡Prop (str ∘ P) $ the (x₀ ≡ x₁) $ transport (sym $ cong fst (htpy ≡$ x₁)) $ refl′ x₁

  StabℙSubaction-canon : Subaction (ℓ-max ℓ (ℓ-suc ℓX)) ℓX G X
  StabℙSubaction-canon .fst = StabℙMono
  StabℙSubaction-canon .snd .fst = StabℙAction-alt
  StabℙSubaction-canon .snd .snd ((g , P) , _) = EmbeddingΣProp {A = ⟨ X g ⟩} λ x → str (P x)

  {-
  StabℙAllEquiv' : (∀ x → ⟨ P₀ x ⟩) → hGroupEquiv Stabℙ G
  StabℙAllEquiv' all = {! !} where
    module G = hGroup G

    ⊤≡P₀ : (const ⊤) ≡ P₀
    ⊤≡P₀ = funExt λ x → TypeOfHLevel≡ 1 $ sym (Unit.isContr→≡Unit* (inhProp→isContr (all x) (str (P₀ x))))

    ty-iso : Iso ⟨ Stabℙ ⟩ᵗ ⟨ G ⟩ᵗ
    ty-iso .Iso.fun ((g , _) , _) = g
    ty-iso .Iso.inv g .fst .fst = g
    ty-iso .Iso.inv g .fst .snd = const ⊤
    ty-iso .Iso.inv g .snd = ST.merePath→pathSetTrunc (PT.map (λ p → ΣPathP (sym p , lemma p)) $ G.mere-path g)
      where
        lemma : (p : G.pt₀ ≡ g) → PathP (λ i → ⟨ ℙ* G X (p (~ i)) ⟩) (λ _ → ⊤) P₀
        lemma = J (λ g p → PathP (λ i → ⟨ ℙ* G X (p (~ i)) ⟩) (λ _ → ⊤) P₀) $ ⊤≡P₀

    ty-iso .Iso.rightInv _ = refl
    ty-iso .Iso.leftInv ((g , P) , ∣gP≡g₀⊤∣) = AutPath (∫ G (ℙ* G X)) _ $ ΣPathP (refl , {! !})
      where
        -- lemma : ∀ x → (p : Path ⟨ ∫ G (ℙ* G X) ⟩ (g , P) (G.pt₀ , P₀)) → ⊤ ≡ P x
        -- lemma x p = {! !}
        lemma : ∀ x → (p : G.pt₀ ≡ g) → PathP (λ i → ⟨ ℙ* G X (p i) ⟩) P₀ P → ⊤ ≡ P x
        lemma x = J (λ g p → PathP (λ i → ⟨ ℙ* G X (p i) ⟩) P₀ P → ⊤ ≡ P x) {! !}
        -- funExtNonDep⁻ (cong snd (sym p)) $ symP (subst-filler (λ - → ⟨ X - ⟩) (cong fst p) x)

        ⊤≡P : (const ⊤) ≡ P
        ⊤≡P = funExt λ x → ST.pathSetTrunc→recProp (isSetHProp ⊤ (P x)) {! !} ∣gP≡g₀⊤∣

      -- AutPath (∫ G (ℙ* G X)) (G.pt₀ , const ⊤) $ ? -- ΣPathP (λ where
      -- .fst → refl
      -- .snd → funExt λ x → ST.pathSetTrunc→recProp (isSetHProp ⊤ (P x)) (lemma x) ∣gP≡g₀⊤∣)
      -- where
      --   lemma : ∀ x → (p : Path ⟨ ∫ G (ℙ* G X) ⟩ (g , P) (G.pt₀ , const ⊤)) → ⊤ ≡ P x
      --   lemma x p = funExtNonDep⁻ (cong snd (sym p)) $ symP (subst-filler (λ - → ⟨ X - ⟩) (cong fst p) x)
  -}

-- The stabilizer subgroup of the subset of all elements is the entire group:
StabℙAllEquiv : (G : hGroup ℓ) (X : hAction ℓX G) → hGroupEquiv (Stabℙ G X (λ _ → ⊤)) G
StabℙAllEquiv G X = equiv where
  module G = hGroup G

  mk-stab : ⟨ G ⟩ᵗ → ⟨ Stabℙ G X (const ⊤) ⟩ᵗ
  mk-stab g .fst .fst = g
  mk-stab g .fst .snd = const ⊤
  mk-stab g .snd = do
      pt₀≡g ← G.mere-path g
      return $ ΣPathP $ sym pt₀≡g , λ i x → ⊤

  ty-iso : Iso ⟨ Stabℙ G X (const ⊤) ⟩ᵗ ⟨ G ⟩ᵗ
  ty-iso .Iso.fun ((g , _) , _) = g
  ty-iso .Iso.inv = mk-stab
  ty-iso .Iso.rightInv _ = refl
  ty-iso .Iso.leftInv ((g , P) , ∣gP≡g₀⊤∣) = AutPath (∫ G (ℙ* G X)) (G.pt₀ , const ⊤) $ ΣPathP λ where
    .fst → refl′ g
    .snd → funExt λ x → PT.rec (isSetHProp ⊤ (P x)) (lemma x) ∣gP≡g₀⊤∣
      where
        lemma : ∀ x → (p : Path ⟨ ∫ G (ℙ* G X) ⟩ (g , P) (G.pt₀ , const ⊤)) → ⊤ ≡ P x
        lemma x p = funExtNonDep⁻ (cong snd (sym p)) $ symP (subst-filler (λ - → ⟨ X - ⟩) (cong fst p) x)

  equiv : hGroupEquiv (Stabℙ G X (λ _ → ⊤)) G
  equiv = mkHGroupEquiv (Stabℙ' G X (λ _ → ⊤)) G (isoToEquiv ty-iso) refl

StabℙCongEquiv : (G : hGroup ℓ) (X : hAction ℓX G) (P₀ P₁ : ℙ ⟨ X (hGroup.pt₀ G) ⟩)
  → (∀ x → ⟨ P₀ x ⟩ ≡ ⟨ P₁ x ⟩)
  → hGroupEquiv (Stabℙ G X P₀) (Stabℙ G X P₁)
StabℙCongEquiv G X P₀ P₁ h = StabCongEquiv G (ℙ* G X) P₀≡P₁ where
  P₀≡P₁ : P₀ ≡ P₁
  P₀≡P₁ = funExt λ x → TypeOfHLevel≡ 1 {X = P₀ x} {Y = P₁ x} (h x)

module Example where
  open import GpdCont.Connectivity
  open import Cubical.Foundations.Path
  open import Cubical.Data.Int using (isSetℤ)
  open import Cubical.HITs.S1 as S1
  open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)

  _⊕_ : (G H : hGroup ℓ) → hGroup ℓ
  G ⊕ H = pointedConnectedGroupoid→hGroup
    (⟨ G ⟩ᵗ × ⟨ H ⟩ᵗ)
    (G.pt₀ , H.pt₀)
    (isPathConnectedΣ G.is-connected (const H.is-connected))
    (isGroupoid× G.is-groupoid H.is-groupoid) where
    module G = hGroup G
    module H = hGroup H
  
  G : hGroup ℓ-zero
  G = pointedConnectedGroupoid→hGroup S¹ base is-connected-S¹ isGroupoidS¹ where
    is-connected-S¹ : isPathConnected S¹
    is-connected-S¹ .fst = ST.∣ base ∣₂
    is-connected-S¹ .snd = ST.elim (λ x → ST.isSetPathImplicit) $
      S1.elim _ refl (isProp→PathP (λ i → ST.isSetSetTrunc _ _) _ _)

  H = G ⊕ G

  X : hAction _ G
  X g .fst = helix g
  X g .snd = is-set-helix g where
    is-set-helix : ∀ g → isSet (helix g)
    is-set-helix = S1.elim _ isSetℤ (isProp→PathP (λ i → isPropIsSet) _ _)

  Y : hAction _ G
  Y _ = UnitSet ℓ-zero

  Z : hAction _ H
  Z (g , _) = X g

  fiber-equiv : ∀ K → fiber Z K ≃ S¹
  fiber-equiv K =
    Σ[ (g , h) ∈ S¹ × S¹ ] X g ≡ K ≃⟨ {! !} ⟩
    Σ[ (g , h) ∈ S¹ × S¹ ] helix g ≡ ⟨ K ⟩ ≃⟨ {! !} ⟩
    S¹ × (Σ[ g ∈ S¹ ] helix g ≡ ⟨ K ⟩) ≃⟨ {! !} ⟩
    {! !} ≃∎
