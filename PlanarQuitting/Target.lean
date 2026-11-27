module

public import PlanarQuitting.Volunteer
public import Mathlib.Data.Fintype.Powerset

/-!
# Target statement for ordinary planar quitting games

Every behavioral profile determines independent probabilities of quitting on the
unique live history at each date. The empty coalition continues the game. Every
nonempty coalition absorbs immediately and pays its prize forever. An absorbing
initial state gives its constant payoff for every positive horizon.
-/

@[expose] public section

namespace PlanarQuitting

open scoped BigOperators

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev Profile (I : Type*) := ℕ → I → ℝ

def Profile.legal (σ : Profile I) : Prop := ∀ i, Legal (fun t ↦ σ t i)

def Profile.revise (σ : Profile I) (i : I) (q : ℕ → ℝ) : Profile I :=
  fun t j ↦ if j = i then q t else σ t j

/-- The probability of the given coalition under independent quitting decisions. -/
def coalitionProb (σ : Profile I) (t : ℕ) (A : Finset I) : ℝ :=
  ∏ j, if j ∈ A then σ t j else 1 - σ t j

def liveProb (σ : Profile I) : ℕ → ℝ
  | 0 => 1
  | t+1 => liveProb σ t * coalitionProb σ t ∅

def accruedPrize (g : Game I) (σ : Profile I) (i : I) : ℕ → ℝ
  | 0 => 0
  | t+1 => accruedPrize g σ i t + liveProb σ t *
    ∑ A : Finset I, if A = ∅ then 0 else coalitionProb σ t A * g.prize A i

def expectedAverage (g : Game I) (σ : Profile I) (i : I) (N : ℕ) : ℝ :=
  (∑ t ∈ Finset.range N, (accruedPrize g σ i (t+1) + liveProb σ (t+1) * g.live i)) / N

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

end

end PlanarQuitting
