module GpdCont.Suspension where

open import GpdCont.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (hasSection ; hasRetract)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (Iso ; isoToEquiv ; retract)
open import Cubical.Foundations.Univalence using (ua ; uaβ ; ~uaβ ; ua→)
open import Cubical.Foundations.Transport using (substComposite)
open import Cubical.Data.Bool
import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.List as List using (List ; [] ; _∷_ ; [_])
open import Cubical.Data.List.Properties using (isOfHLevelList)
open import Cubical.HITs.Susp as Susp using (Susp ; north ; south ; merid)
open import Cubical.HITs.Truncation as Tr using (∥_∥_)
open import Cubical.Relation.Nullary using (Dec ; yes ; no ; Discrete ; Discrete→isSet ; ¬_ ; isProp¬)

-- A family over `Susp Y` classifying edge-paths out of `north`.
--
-- An edge-path in `Susp Y` alternates between going `north → south` along some
-- `merid y` and going back along some `merid y'`.  Directions are forced by the
-- endpoints, so a path is just a list in `Y`, and it is reduced iff no two
-- neighbours agree.  Even-length paths end in `north`, odd-length ones in `south`.
-- Going around `merid y` toggles `y` at the head of the list.
module Code {ℓ} (Y : Type ℓ) (_≟_ : Discrete Y) where
  -- `HeadNot y w`: the list `w` does not start with `y`.
  HeadNot : Y → List Y → Type ℓ
  HeadNot y [] = Unit*
  HeadNot y (x ∷ _) = ¬ y ≡ x

  isPropHeadNot : ∀ y w → isProp (HeadNot y w)
  isPropHeadNot y [] = isPropUnit*
  isPropHeadNot y (x ∷ w) = isProp¬ _

  -- A list is reduced if no two neighbours agree.
  Reduced : List Y → Type ℓ
  Reduced [] = Unit*
  Reduced (x ∷ w) = HeadNot x w × Reduced w

  isPropReduced : ∀ w → isProp (Reduced w)
  isPropReduced [] = isPropUnit*
  isPropReduced (x ∷ w) = isProp× (isPropHeadNot x w) (isPropReduced w)

  parity : List Y → Bool
  parity = List.foldr (λ _ → not) false

  -- Reduced lists of a given parity.
  Code[_] : Bool → Type ℓ
  Code[ b ] = Σ[ w ∈ List Y ] Reduced w × (parity w ≡ b)

  -- Toggling `y` at the head of a list: cancel it if it's there, add it otherwise.
  toggle-cons : (y x : Y) → List Y → Dec (y ≡ x) → List Y
  toggle-cons y x w (yes _) = w
  toggle-cons y x w (no _) = y ∷ x ∷ w

  toggle : Y → List Y → List Y
  toggle y [] = [ y ]
  toggle y (x ∷ w) = toggle-cons y x w (y ≟ x)

  parity-toggle-cons : ∀ y x w (d : Dec (y ≡ x)) → parity (toggle-cons y x w d) ≡ not (parity (x ∷ w))
  parity-toggle-cons y x w (yes _) = sym (notnot _)
  parity-toggle-cons y x w (no _) = refl

  parity-toggle : ∀ y w → parity (toggle y w) ≡ not (parity w)
  parity-toggle y [] = refl
  parity-toggle y (x ∷ w) = parity-toggle-cons y x w (y ≟ x)

  toggle-reduced : ∀ y w → Reduced w → Reduced (toggle y w)
  toggle-reduced y [] _ = tt* , tt*
  toggle-reduced y (x ∷ w) red = go (y ≟ x) where
    go : (d : Dec (y ≡ x)) → Reduced (toggle-cons y x w d)
    go (yes _) = red .snd
    go (no y≢x) = y≢x , red

  -- On reduced lists, toggling is an involution.
  toggle-toggle-cons : ∀ y w → (d : Dec (y ≡ y)) → toggle-cons y y w d ≡ w
  toggle-toggle-cons y w (yes _) = refl
  toggle-toggle-cons y w (no ¬refl) = ⊥.rec (¬refl refl)

  toggle-toggle : ∀ y w → Reduced w → toggle y (toggle y w) ≡ w
  toggle-toggle y [] _ = toggle-toggle-cons y [] (y ≟ y)
  toggle-toggle y (x ∷ w) red = go (y ≟ x) where
    go-yes : y ≡ x → ∀ w → HeadNot x w → toggle y w ≡ x ∷ w
    go-yes y≡x [] _ = cong [_] y≡x
    go-yes y≡x (x' ∷ w) x≢x' = go-yes' (y ≟ x') where
      go-yes' : (d : Dec (y ≡ x')) → toggle-cons y x' w d ≡ x ∷ x' ∷ w
      go-yes' (yes y≡x') = ⊥.rec (x≢x' (sym y≡x ∙ y≡x'))
      go-yes' (no _) = cong (_∷ x' ∷ w) y≡x

    go : (d : Dec (y ≡ x)) → toggle y (toggle-cons y x w d) ≡ x ∷ w
    go (yes y≡x) = go-yes y≡x w (red .fst)
    go (no _) = toggle-toggle-cons y (x ∷ w) (y ≟ y)

  -- Toggling `y` swaps even and odd reduced lists.
  toggle-Code : ∀ {b} → Y → Code[ b ] → Code[ not b ]
  toggle-Code y (w , red , par) = toggle y w , toggle-reduced y w red , parity-toggle y w ∙ cong not par

  toggle-Code-toggle-Code : ∀ {b} y (c : Code[ b ]) → PathP (λ i → Code[ notnot b i ]) (toggle-Code y (toggle-Code y c)) c
  toggle-Code-toggle-Code y (w , red , _) = ΣPathPProp (λ w → isProp× (isPropReduced w) (isSetBool _ _)) (toggle-toggle y w red)

  toggle≃ : Y → Code[ false ] ≃ Code[ true ]
  toggle≃ y = isoToEquiv iso where
    iso : Iso Code[ false ] Code[ true ]
    iso .Iso.fun = toggle-Code y
    iso .Iso.inv = toggle-Code y
    iso .Iso.rightInv = toggle-Code-toggle-Code y
    iso .Iso.leftInv = toggle-Code-toggle-Code y

  Code : Susp Y → Type ℓ
  Code north = Code[ false ]
  Code south = Code[ true ]
  Code (merid y i) = ua (toggle≃ y) i

  isSetCode[_] : ∀ b → isSet Code[ b ]
  isSetCode[ b ] = isSetΣ (isOfHLevelList 0 (Discrete→isSet _≟_)) λ w →
    isProp→isSet (isProp× (isPropReduced w) (isSetBool _ _))

  isSetCode : ∀ x → isSet (Code x)
  isSetCode north = isSetCode[ false ]
  isSetCode south = isSetCode[ true ]
  isSetCode (merid y i) = isProp→PathP (λ i → isPropIsSet {A = Code (merid y i)}) isSetCode[ false ] isSetCode[ true ] i

  Code≡ : ∀ {b} {c c' : Code[ b ]} → c .fst ≡ c' .fst → c ≡ c'
  Code≡ = Σ≡Prop λ w → isProp× (isPropReduced w) (isSetBool _ _)

  -- Encoding a path out of `north`: transport the empty list along it.
  encode : ∀ x → north ≡ x → Code x
  encode x p = subst Code p ([] , tt* , refl)

  -- Decoding a list: walk along its letters, alternating between `merid y`
  -- and `sym (merid y)`.  The parity determines the endpoint.
  end : Bool → Susp Y
  end false = north
  end true = south

  step : Y → ∀ b → end (not b) ≡ end b
  step y false = sym (merid y)
  step y true = merid y

  parity-tail : ∀ {b} y w → parity (y ∷ w) ≡ b → parity w ≡ not b
  parity-tail y w p = sym (notnot _) ∙ cong not p

  decode-list : ∀ b (w : List Y) → parity w ≡ b → north ≡ end b
  decode-list false [] _ = refl
  decode-list true [] p = ⊥.rec (false≢true p)
  decode-list false (y ∷ w) p = decode-list true w (parity-tail y w p) ∙ step y false
  decode-list true (y ∷ w) p = decode-list false w (parity-tail y w p) ∙ step y true

  -- Decoding only depends on the list, not on the proof of its parity.
  decode-list-irr : ∀ b w p q → decode-list b w p ≡ decode-list b w q
  decode-list-irr b w p q = cong (decode-list b w) (isSetBool _ _ p q)

  decode-north : Code north → north ≡ north
  decode-north (w , _ , p) = decode-list false w p

  decode-south : Code south → north ≡ south
  decode-south (w , _ , p) = decode-list true w p

  -- Going around `merid y` toggles `y` at the head of the list,
  -- which either adds `merid y` at the end of the path, or cancels it.
  decode-merid : ∀ y (c : Code north) → PathP (λ i → north ≡ merid y i) (decode-north c) (decode-south (toggle-Code y c))
  decode-merid y ([] , _ , p) = compPath-filler refl (merid y)
  decode-merid y (x ∷ w , (hn , red) , p) = go (y ≟ x) where
    D = decode-list true w (parity-tail x w p)

    go : (d : Dec (y ≡ x))
      → PathP (λ i → north ≡ merid y i) (D ∙ sym (merid x)) (decode-list true (toggle-cons y x w d) (parity-toggle-cons y x w d ∙ cong not p))
    go (yes y≡x) =
      cong (λ z → D ∙ sym (merid z)) (sym y≡x)
        ◁ symP (compPath-filler D (sym (merid y)))
        ▷ decode-list-irr true w _ _
    go (no _) =
      decode-list-irr false (x ∷ w) _ _
        ◁ compPath-filler _ (merid y)

  decode : ∀ x → Code x → north ≡ x
  decode north = decode-north
  decode south = decode-south
  decode (merid y i) = ua→ {e = toggle≃ y} {B = λ i → north ≡ merid y i} {f₀ = decode-north} {f₁ = decode-south} (decode-merid y) i

  -- Decoding after encoding is the identity, by path induction.
  decode-encode : ∀ x (p : north ≡ x) → decode x (encode x p) ≡ p
  decode-encode x = J (λ x p → decode x (encode x p) ≡ p) (cong decode-north (transportRefl ([] , tt* , refl)))

  -- Encoding after decoding is the identity, by induction on lists.
  toggle-HeadNot : ∀ y w → HeadNot y w → toggle y w ≡ y ∷ w
  toggle-HeadNot y [] _ = refl
  toggle-HeadNot y (x ∷ w) y≢x = go (y ≟ x) where
    go : (d : Dec (y ≡ x)) → toggle-cons y x w d ≡ y ∷ x ∷ w
    go (yes y≡x) = ⊥.rec (y≢x y≡x)
    go (no _) = refl

  code-at : ∀ b → Code[ b ] → Code (end b)
  code-at false c = c
  code-at true c = c

  encode-decode-list : ∀ b w (red : Reduced w) (p : parity w ≡ b)
    → encode (end b) (decode-list b w p) ≡ code-at b (w , red , p)
  encode-decode-list false [] _ _ = transportRefl _ ∙ Code≡ refl
  encode-decode-list true [] _ p = ⊥.rec (false≢true p)
  encode-decode-list false (y ∷ w) (hn , red) p =
    substComposite Code (decode-list true w q) (sym (merid y)) _
    ∙ cong (subst Code (sym (merid y))) (encode-decode-list true w red q)
    ∙ ~uaβ (toggle≃ y) (w , red , q)
    ∙ Code≡ (toggle-HeadNot y w hn)
    where q = parity-tail y w p
  encode-decode-list true (y ∷ w) (hn , red) p =
    substComposite Code (decode-list false w q) (merid y) _
    ∙ cong (subst Code (merid y)) (encode-decode-list false w red q)
    ∙ uaβ (toggle≃ y) (w , red , q)
    ∙ Code≡ (toggle-HeadNot y w hn)
    where q = parity-tail y w p

  encode-decode-north : ∀ c → encode north (decode north c) ≡ c
  encode-decode-north (w , red , p) = encode-decode-list false w red p

  encode-decode-south : ∀ c → encode south (decode south c) ≡ c
  encode-decode-south (w , red , p) = encode-decode-list true w red p

  encode-decode : ∀ x (c : Code x) → encode x (decode x c) ≡ c
  encode-decode north = encode-decode-north
  encode-decode south = encode-decode-south
  encode-decode (merid y i) = isProp→PathP
    (λ i → isPropΠ λ (c : Code (merid y i)) → isSetCode (merid y i) (encode (merid y i) (decode (merid y i) c)) c)
    encode-decode-north encode-decode-south i

  -- Paths out of `north` are classified by `Code`.
  encodeDecodeIso : ∀ x → Iso (north ≡ x) (Code x)
  encodeDecodeIso x .Iso.fun = encode x
  encodeDecodeIso x .Iso.inv = decode x
  encodeDecodeIso x .Iso.rightInv = encode-decode x
  encodeDecodeIso x .Iso.leftInv = decode-encode x

  encodeDecode≃ : ∀ x → (north ≡ x) ≃ Code x
  encodeDecode≃ x = isoToEquiv (encodeDecodeIso x)

  isSetPathFromNorth : ∀ x → isSet (north ≡ x)
  isSetPathFromNorth x = isOfHLevelRespectEquiv 2 (invEquiv (encodeDecode≃ x)) (isSetCode x)

  -- Odd lists are non-empty, so they have a first letter.
  first-letter : (w : List Y) → parity w ≡ true → Y
  first-letter [] p = ⊥.rec (false≢true p)
  first-letter (y ∷ _) _ = y

  r : north ≡ south → Y
  r ℓ = let (w , _ , odd) = encode south ℓ in first-letter w odd

  r-merid : ∀ y → r (merid y) ≡ y
  r-merid y = transportRefl y

  hasRetractMerid : hasRetract merid
  hasRetractMerid .fst = r
  hasRetractMerid .snd = r-merid

  trunc-r : ∥ Path (Susp Y) north south ∥ 2 → Y
  trunc-r = Tr.rec (Discrete→isSet _≟_) r

  hasRetractTruncMerid : hasRetract (Tr.∣_∣ₕ {A = Path (Susp Y) north south} {n = 2} ∘ merid)
  hasRetractTruncMerid .fst = trunc-r
  hasRetractTruncMerid .snd = r-merid
