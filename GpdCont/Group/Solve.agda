module GpdCont.Group.Solve where

open import Agda.Builtin.Reflection using (Term ; TC)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Data.Nat.Base
open import Cubical.Algebra.Group.Base
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
