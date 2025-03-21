{-# OPTIONS --no-exact-split #-}

module GpdCont.Group.Solve where

open import GpdCont.Prelude

open import Agda.Builtin.Reflection using (Term ; TC)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Data.Empty.Base
open import Cubical.Data.Unit.Base
open import Cubical.Data.Nat.Base using (ℕ)
open import Cubical.HITs.FreeGroup as FG using (FreeGroup)
open import Cubical.Algebra.Group.Base hiding (group)
open import Cubical.Relation.Nullary.Base using (Discrete ; yes ; no ; ¬_)
open import Cubical.Tactics.MonoidSolver.MonoidExpression using (Expr)
open import Cubical.Tactics.MonoidSolver.Solver using (module Eval) renaming (solve to naiveSolveMonoid)
open import Cubical.Tactics.MonoidSolver.Reflection using (solveMonoid ; module ReflectionSolver)

module _ {ℓ} (G : Group ℓ) where
  private
    M = Group→Monoid G

  naiveSolveGroup : ∀ {n : ℕ} (e₁ e₂ : Expr ⟨ M ⟩ n) → (v : Eval.Env M n)
    → (p : Eval.eval M (Eval.normalize M e₁) v ≡ Eval.eval M (Eval.normalize M e₂) v)
    → Eval.⟦ M ⟧ e₁ v ≡ Eval.⟦ M ⟧ e₂ v
  naiveSolveGroup = naiveSolveMonoid M

macro
  solveGroup : Term → Term → TC Unit
  solveGroup = ReflectionSolver.solve-macro (quote GroupStr._·_) (quote GroupStr.1g) (quote naiveSolveGroup)

module Normalize {ℓ ℓA} (A : Type ℓA) (_≟_ : Discrete A) (G : Group ℓ) where
  open import Cubical.HITs.FreeGroup.NormalForm
  open import Cubical.Data.List using (foldr)
  open import Cubical.Algebra.Group.Free as Free using () renaming ([𝟚×_] to Word)

  open module NF = Free.NF (FG.freeGroupGroup A) FG.η using (NF)

  eval : (A → ⟨ G ⟩) → FreeGroup A → ⟨ G ⟩
  eval α = FG.rec {Group = G} α .fst

  normalize : FreeGroup A → Word A
  normalize a = (≟→normalForm _≟_ a) .NF.word

  reify : Word A → FreeGroup A
  reify = NF.fromList

  is-free : (t : FreeGroup A) → t ≡ reify (normalize t)
  is-free t = sym (≟→normalForm _≟_ t .NF.fromListWord≡)

  solve1 : (env : A → ⟨ G ⟩) (t : FreeGroup A) → eval env t ≡ eval env (reify (normalize t))
  solve1 env t = cong (eval env) (is-free t)

  solve : (env : A → ⟨ G ⟩) (s t : FreeGroup A)
    → reify (normalize s) ≡ reify (normalize t)
    → eval env s ≡ eval env t
  solve env s t p = cong (eval env) (is-free s ∙∙ p ∙∙ sym (is-free t))

module Impl {ℓ} (G : Group ℓ) {n : ℕ} where
  open import Cubical.Foundations.Function using (flip)
  open import Cubical.Data.SumFin
  open import Cubical.Data.Vec hiding (lookup)

  private
    module N = Normalize (Fin n) discreteFin G

    lookup : ∀ {n} → Vec ⟨ G ⟩ n → Fin n → ⟨ G ⟩
    lookup (x ∷ xs) fzero = x
    lookup (x ∷ xs) (fsuc i) = lookup xs i

  solve : (env : Vec ⟨ G ⟩ n) (s t : FreeGroup (Fin n))
    → N.reify (N.normalize s) ≡ N.reify (N.normalize t)
    → N.eval (lookup env) s ≡ N.eval (lookup env) t
  solve env = N.solve (lookup env)

private module Test {ℓ} (G : Group ℓ) where
  open import Cubical.HITs.FreeGroup as FG using (FreeGroup)
  open module G = GroupStr (str G) using (_·_ ; inv ; 1g)

  data Env : Type where
    ″g″ ″h″ : Env

  ″g″? : Env → Type
  ″g″? ″g″ = Unit
  ″g″? ″h″ = ⊥

  ″g″≢″h″ : ¬ ″g″ ≡ ″h″
  ″g″≢″h″ p = subst ″g″? p tt

  _=?_ : Discrete Env
  ″g″ =? ″g″ = yes refl
  ″g″ =? ″h″ = no ″g″≢″h″
  ″h″ =? ″g″ = no (λ x → ″g″≢″h″ (sym x))
  ″h″ =? ″h″ = yes refl

  test : (g h : ⟨ G ⟩) → g · (h · (inv h · inv g)) ≡ 1g
  test g h = Normalize.solve1 Env _=?_ G env (g′ * (h′ * ((h′ ⁻¹) * (g′ ⁻¹)))) where
    open FG using () renaming (_·_ to _*_ ; inv to _⁻¹)
    g′ : FreeGroup Env
    g′ = FG.η ″g″

    h′ : FreeGroup Env
    h′ = FG.η ″h″

    env : Env → ⟨ G ⟩
    env ″g″ = g
    env ″h″ = h

  -- test' : (g h : ⟨ G ⟩) → g · (h · (inv h · inv g)) ≡ 1g
  -- test' g h = solve G {2} (λ { fzero → g
  --                          ; (fsuc fzero) → h }) (g' * (h' * ((h' ⁻¹) * (g' ⁻¹)))) where
  --   open FG using () renaming (_·_ to _*_ ; inv to _⁻¹)
  --   open import Cubical.Data.SumFin
  --   -- env : Fin 2 → ⟨ G ⟩
  --   -- env zero = g
  --   -- env one = h

  --   g' = FG.η fzero
  --   h' = FG.η (fsuc fzero)

module Tactic where
  open import Agda.Builtin.Reflection hiding (Type)
  open import Agda.Builtin.String

  open import Cubical.Data.Bool.Base
  open import Cubical.Data.Bool.SwitchStatement
  open import Cubical.Data.List.Base
  open import Cubical.Data.Sigma.Base
  open import Cubical.Data.Maybe.Base
  open import Cubical.Data.SumFin as Fin using (Fin)
  import      Cubical.Data.Vec as Vec
  open import Cubical.Reflection.Base

  open import Cubical.Tactics.Reflection
  open import Cubical.Tactics.Reflection.Variables
  open import Cubical.Tactics.Reflection.Utilities

  private
    pattern v[_] a = varg a ∷ []

    record Problem : Type where
      field
        group : Term
        lhs rhs : Term
        variables : Vars

      solve : Term
      solve = def (quote Impl.solve) (group v∷ (make-env variables) ∷ lhs v∷ rhs v∷ reified-path v∷ [])
        where
        make-env : Vars → Arg Term
        make-env [] = varg $ con (quote Vec.[]) []
        make-env (x ∷ xs) = varg $ con (quote Vec._∷_) (x v∷ make-env xs ∷ [])

        reified-path : Term
        reified-path = def (quote refl) []

    quote-solver : (group env lhs rhs : Term) → Term
    quote-solver group env lhs rhs =
      def
        (quote Impl.solve)
        (group v∷ env v∷ lhs v∷ rhs v∷ reified-path v∷ [])
      where
      reified-path : Term
      reified-path = def (quote refl) []

    get-boundary' : (type : Term) → TC (Term × Term)
    get-boundary' type = do
      just bdry ← get-boundary type
        where
          nothing → typeError
            $ strErr "Failed to parse boundary of type. "
            ∷ strErr "Expected `x ≡ y`, got"
            ∷ termErr type
            ∷ []
      returnTC bdry

    fzero : ∀ {k} → Fin (suc k)
    fzero = Fin.fzero

    fsuc : ∀ {k} → Fin k → Fin (suc k)
    fsuc = Fin.fsuc

    quote-fin : ℕ → Term
    quote-fin zero = con (quote fzero) []
    quote-fin (suc n) = con (quote fsuc) v[ quote-fin n ]

    index-to-fin-term : (idx : Maybe ℕ) → Term
    index-to-fin-term (just n) = quote-fin n
    index-to-fin-term nothing = unknown

    free-group-variable : (v : Term) → (env : VarAss) → Term
    free-group-variable v env = con (quote FG.η) v[ index-to-fin-term (env v) ]

    unusable-args : ∀ {ℓ} {A : Type ℓ} → String → List (Arg Term) → TC A
    unusable-args msg args = typeError $ strErr msg ∷ map (λ { (arg _ t) → termErr t }) args

    assert-nullary : List (Arg Term) → TC Unit
    assert-nullary [] = returnTC tt
    assert-nullary (varg _ ∷ args) = assert-nullary args
    assert-nullary (harg _ ∷ args) = assert-nullary args
    assert-nullary other = unusable-args "Not a nullary expression: " other

  
    assert-unary : List (Arg Term) → TC Term
    assert-unary [] = unusable-args "Not a unary expression." []
    assert-unary (_ h∷ args) = assert-unary args
    assert-unary (v[ x ]) = returnTC x
    assert-unary (_ v∷ v[ x ]) = returnTC x
    assert-unary other = unusable-args "Not a unary expression: " other

    with-unary : ∀ {ℓ} {A : Type ℓ} → (args : List (Arg Term)) → (Term → TC A) → TC A
    with-unary (_ h∷ args) f = with-unary args f
    with-unary (x v∷ []) f = f x
    with-unary (_ v∷ x v∷ []) f = f x
    with-unary [] _ = unusable-args "Not a unary expression." []
    with-unary other _ = unusable-args "Not a unary expression: " other

    assert-binary : List (Arg Term) → TC (Term × Term)
    assert-binary [] = unusable-args "Not a binary expression." []
    assert-binary (_ h∷ args) = assert-binary args
    assert-binary (x v∷ y v∷ []) = returnTC (x , y)
    assert-binary (_ v∷ x v∷ y v∷ []) = returnTC (x , y)
    assert-binary other = unusable-args "Not a binary expression: " other

    module Quote (is-one is-mul is-inv : Name → Bool) where
      term : (tm : Term) → TC (Template × Vars)

      one : (args : List (Arg Term)) → TC (Template × Vars)
      one args = do
        assert-nullary args
        returnTC ((λ _ → con (quote FG.ε) []) , [])

      {-# NON_TERMINATING #-}
      inv : (args : List (Arg Term)) → TC (Template × Vars)
      inv args = with-unary args λ expr → do
        -- expr ← assert-unary args
        (template , vars) ← term expr
        let template' = λ assignment → con (quote FG.inv) v[ template assignment ]
        returnTC (template' , vars)

      mul : (args : List (Arg Term)) → TC (Template × Vars)
      mul args = do
        (x , y) ← assert-binary args
        (template-x , vars-x) ← term x
        (template-y , vars-y) ← term y
        returnTC λ where
          .fst assignment → con (quote FG._·_) (template-x assignment v∷ template-y assignment v∷ [])
          .snd → appendWithoutRepetition vars-x vars-y

      free-var : Term → Template × Vars
      free-var v .fst = free-group-variable v
      free-var v .snd = [ v ]

      expr : (n : Name) → (args : List (Arg Term)) → TC (Template × Vars)
      expr n args =
        switch (λ test → test n) cases
          case is-one ⇒ one args break
          case is-mul ⇒ mul args break
          case is-inv ⇒ inv args break
          default⇒ typeError (strErr "Not a group expression: " ∷ [ nameErr n ])

      term v@(var _ _) = returnTC (free-var v)
      term c@(con n args) = expr n args <|> returnTC (free-var c)
      term d@(def n args) = expr n args <|> returnTC (free-var d)
      term tm = typeError $ strErr "Cannot parse group expression " ∷ termErr tm ∷ []

      problem : (group goal-type : Term) → TC Problem
      problem group goal-type = do
        (lhs , rhs) ← get-boundary' goal-type
        (template-l , vars-l) ← term lhs
        (template-r , vars-r) ← term rhs
        let vars = appendWithoutRepetition vars-l vars-r
            instantiate : Template → Term
            instantiate tmpl = tmpl $ flip indexOf vars
        returnTC $ record
          { group = group
          ; lhs = instantiate template-l
          ; rhs = instantiate template-r
          ; variables = vars
          }


    solve-macro : (group hole : Term) → TC Unit
    solve-macro group hole = do
      goal-type ← inferType hole >>= normalise
      wait-for-type goal-type
      problem ← Quote.problem {! !} {! !} {! !} group goal-type
      let solution : Term
          solution = Problem.solve problem
      unify hole solution

  macro
    solve! : Term → Term → TC Unit
    solve! = solve-macro
