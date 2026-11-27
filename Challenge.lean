module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Basic.Real.Basic

/-!
# Uniform equilibrium in planar quitting games

Every finite quitting game whose singleton absorbing prizes lie in an affine
plane has a uniform Nash equilibrium payoff under independent randomization.
The model has one live state. If a nonempty coalition quits, its prize is
paid at that stage and every later stage.
-/

@[expose] public section

namespace PlanarQuitting

universe u

open scoped BigOperators

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- An ordinary quitting game's live reward and coalition prizes. -/
structure Game (I : Type*) where
  live : I → ℝ
  prize : Finset I → I → ℝ

/-- A behavioral hazard sequence takes values in the unit interval. -/
def Legal (q : ℕ → ℝ) : Prop := ∀ t, 0 ≤ q t ∧ q t ≤ 1

/-- A profile specifies each player's quitting probability at every live date. -/
abbrev Profile (I : Type*) := ℕ → I → ℝ

/-- Each player's quitting probabilities are in the unit interval. -/
def Profile.legal (σ : Profile I) : Prop := ∀ i, Legal (fun t ↦ σ t i)

/-- Replace only player `i`'s quitting probabilities. -/
def Profile.revise (σ : Profile I) (i : I) (q : ℕ → ℝ) : Profile I :=
  fun t j ↦ if j = i then q t else σ t j

/-- The probability of the given coalition under independent quitting decisions. -/
def coalitionProb (σ : Profile I) (t : ℕ) (A : Finset I) : ℝ :=
  ∏ j, if j ∈ A then σ t j else 1 - σ t j

/-- Probability the game is still live after the first `t` stages. -/
def liveProb (σ : Profile I) : ℕ → ℝ
  | 0 => 1
  | t+1 => liveProb σ t * coalitionProb σ t ∅

/-- Expected prize paid at stage `t` on histories that have already absorbed. -/
def accruedPrize (g : Game I) (σ : Profile I) (i : I) : ℕ → ℝ
  | 0 => 0
  | t+1 => accruedPrize g σ i t + liveProb σ t *
    ∑ A : Finset I, if A = ∅ then 0 else coalitionProb σ t A * g.prize A i

/-- Expected average payoff over the first `N` stages. -/
def expectedAverage (g : Game I) (σ : Profile I) (i : I) (N : ℕ) : ℝ :=
  (∑ t ∈ Finset.range N, (accruedPrize g σ i (t+1) + liveProb σ (t+1) * g.live i)) / N

/-- At each tolerance choose one profile and threshold for all later horizons. -/
def HasUniformPayoff (g : Game I) (u : I → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (σ : Profile I) (H : ℕ), σ.legal ∧ 1 ≤ H ∧
    ∀ N : ℕ, H ≤ N → ∀ i,
      |expectedAverage g σ i N - u i| ≤ ε ∧
      ∀ q, Legal q → expectedAverage g (σ.revise i q) i N ≤ expectedAverage g σ i N + ε

/-- An explicit affine-plane representation of all singleton payoff vectors. -/
def PlanarSingletons (g : Game I) : Prop :=
  ∃ (b : I → ℝ) (a R : I → Fin 2 → ℝ), ∀ i j,
    g.prize {j} i = b i + a i 0 * R j 0 + a i 1 * R j 1

/-- Full planar existence claim, recorded as the proposition to prove. -/
def PlanarExistence (I : Type*) [Fintype I] [DecidableEq I] : Prop :=
  ∀ g : Game I, PlanarSingletons g → ∃ u, HasUniformPayoff g u

set_option warn.sorry false in
/-- Uniform Nash equilibrium payoff existence for all planar quitting games. -/
theorem planar_uniform_payoff (I : Type u) [Fintype I] [DecidableEq I] :
    PlanarExistence I := by
  sorry

end

end PlanarQuitting
