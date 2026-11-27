module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Real.Basic

/-!
# Uniform equilibrium from a periodic quitting calendar

Each live date designates one player who may quit. The continuation promises
are individually rational relative to quitting alone and satisfy the waiting
recurrence. Each player faces a positive rival quitting opportunity somewhere
in the period. The theorem gives the common initial promised payoff as a
uniform Nash payoff in the independent quitting game. The solution uses
arbitrarily small hazards obtained by subdividing the calendar.
-/

@[expose] public section

namespace PlanarQuitting

open scoped BigOperators

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- An ordinary quitting game's live reward and coalition prizes. -/
structure Game (I : Type*) where
  live : I → ℝ
  prize : Finset I → I → ℝ

/-- The only player allowed to mix between quitting and continuing on each live date. -/
structure Calendar (I : Type*) where
  actor : ℕ → I
  prob : ℕ → ℝ

def Legal (q : ℕ → ℝ) : Prop := ∀ t, 0 ≤ q t ∧ q t ≤ 1

variable (p : Calendar I) (g : Game I)

/-- The player's prescribed probability of quitting. -/
def own (i : I) (t : ℕ) : ℝ := if p.actor t = i then p.prob t else 0

/-- The total rival hazard, which comes from at most one rival. -/
def rival (i : I) (t : ℕ) : ℝ := if p.actor t = i then 0 else p.prob t

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

set_option warn.sorry false in
theorem periodic_calendar_uniform_payoff (g : Game I) (p : Calendar I) (v : ℕ → I → ℝ)
    {L : ℕ} {β M C : ℝ} (hβ₀ : 0 ≤ β) (hβ₁ : β < 1) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (prob : ∀ t, 0 ≤ p.prob t ∧ p.prob t ≤ β)
    (actorPeriod : ∀ t, p.actor (t+L) = p.actor t)
    (probPeriod : ∀ t, p.prob (t+L) = p.prob t)
    (opportunity : ∀ i, ∃ t < L, 0 < rival p i t)
    (recurrence : ∀ t i,
      (1-p.prob t)*v (t+1) i + p.prob t*g.prize {p.actor t} i = v t i)
    (tie : ∀ t, v (t+1) (p.actor t) = g.prize {p.actor t} (p.actor t))
    (ir : ∀ t i, g.prize {i} i ≤ v t i)
    (liveBound : ∀ t i, |g.live i - v t i| ≤ M)
    (collision : ∀ i j, g.prize {i,j} i - g.prize {i} i ≤ C) :
    HasUniformPayoff g (v 0) := by
  sorry

end

end PlanarQuitting
