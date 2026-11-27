module

public import PlanarQuitting.Target
public import PlanarQuitting.Period
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
# Calendar implementation in the full independent-hazard model

At a live date after a unilateral deviation, only the actor and the deviating
player can quit. Summing the product distribution over these coalitions gives
the calendar formulas used in the incentive proof.
-/

@[expose] public section

namespace PlanarQuitting

open scoped BigOperators

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

def Calendar.profile (p : Calendar I) : Profile I := fun t i ↦ own p i t

private theorem support_prob {σ : Profile I} {t : ℕ} {B A : Finset I}
    (hA : A ⊆ B) (hσ : ∀ j ∉ B, σ t j = 0) :
    coalitionProb σ t A = ∏ j ∈ B, if j ∈ A then σ t j else 1 - σ t j := by
  unfold coalitionProb
  symm
  apply Finset.prod_subset (Finset.subset_univ B)
  intro j _ hj
  simp [show j ∉ A from fun h ↦ hj (hA h), hσ j hj]

private theorem unsupported_prob {σ : Profile I} {t : ℕ} {B A : Finset I}
    (hA : ¬ A ⊆ B) (hσ : ∀ j ∉ B, σ t j = 0) : coalitionProb σ t A = 0 := by
  have ⟨j, hj, hb⟩ := Finset.not_subset.mp hA
  unfold coalitionProb
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj, hσ j hb])

private theorem support_sum (g : Game I) {σ : Profile I} {t : ℕ} (i : I)
    {B : Finset I} (hσ : ∀ j ∉ B, σ t j = 0) :
    (∑ A : Finset I, if A = ∅ then 0 else coalitionProb σ t A * g.prize A i) =
      ∑ A ∈ B.powerset, if A = ∅ then 0 else
        (∏ j ∈ B, if j ∈ A then σ t j else 1 - σ t j) * g.prize A i := by
  rw [← Finset.sum_subset (Finset.subset_univ B.powerset)]
  · apply Finset.sum_congr rfl
    intro A hA
    rw [support_prob (Finset.mem_powerset.mp hA) hσ]
  · intro A _ hA
    rw [Finset.mem_powerset] at hA
    simp [unsupported_prob hA hσ]

private theorem profile_row (g : Game I) (p : Calendar I) (i : I) (q : ℕ → ℝ) (t : ℕ) :
    let σ := p.profile.revise i q
    coalitionProb σ t ∅ = remaining p i q t ∧
    (∑ A : Finset I, if A = ∅ then 0 else coalitionProb σ t A * g.prize A i) =
      newPrize p g i q t := by
  dsimp only
  by_cases hi : p.actor t = i
  · have hσ : ∀ j ∉ ({i} : Finset I), p.profile.revise i q t j = 0 := by
      intro j hj
      have hji : j ≠ i := by simpa using hj
      simp [Profile.revise, Calendar.profile, own, hi, hji, Ne.symm hji]
    constructor
    · rw [support_prob (Finset.empty_subset {i}) hσ]
      simp [Profile.revise, remaining, rival, hi]
    · rw [support_sum g i hσ]
      rw [← insert_empty_eq, Finset.sum_powerset_insert (by simp)]
      simp [Profile.revise, newPrize, quitReward, rival, hi]
  · let j := p.actor t
    have hji : j ≠ i := hi
    have hij : i ≠ j := Ne.symm hji
    have hσ : ∀ k ∉ ({i,j} : Finset I), p.profile.revise i q t k = 0 := by
      intro k hk
      have hki : k ≠ i := fun H ↦ hk (by simp [H])
      have hkj : k ≠ j := fun H ↦ hk (by simp [H])
      simp [Profile.revise, Calendar.profile, own, hki, show p.actor t ≠ k from Ne.symm hkj]
    have hai : p.profile.revise i q t i = q t := by simp [Profile.revise]
    have haj : p.profile.revise i q t j = p.prob t := by
      simp [Profile.revise, Calendar.profile, own, hji, j]
    constructor
    · rw [support_prob (Finset.empty_subset {i,j}) hσ]
      simp [Finset.prod_pair hij, hai, haj, remaining, rival, hi]
    · rw [support_sum g i hσ, Finset.sum_powerset_insert (by simpa using hij)]
      have hpair : ∀ (f : Finset I → ℝ),
          (∑ A ∈ ({j} : Finset I).powerset, f A) = f ∅ + f {j} := by
        intro f
        rw [← insert_empty_eq, Finset.sum_powerset_insert (by simp)]
        simp
      rw [hpair, hpair]
      simp [Finset.prod_pair hij, hai, haj, hji, hij, newPrize, quitReward, rival, j]
      ring

/-- The exact finite-horizon payoff under every behavioral deviation. -/
theorem revised_average (g : Game I) (p : Calendar I) (i : I) (q : ℕ → ℝ) (N : ℕ) :
    expectedAverage g (p.profile.revise i q) i N = average p g i q N := by
  have halive (t : ℕ) : liveProb (p.profile.revise i q) t = alive p i q t := by
    induction t with
    | zero => rfl
    | succ t ih => simp only [liveProb, alive, ih, (profile_row g p i q t).1]
  have hcash (t : ℕ) : accruedPrize g (p.profile.revise i q) i t = accrued p g i q t := by
    induction t with
    | zero => rfl
    | succ t ih => simp only [accruedPrize, accrued, halive, ih, (profile_row g p i q t).2]
  simp only [expectedAverage, average, stage, halive, hcash]

omit [Fintype I] in
private theorem revise_own (p : Calendar I) (i : I) : p.profile.revise i (own p i) = p.profile := by
  funext t j
  by_cases h : j = i
  · subst j
    simp [Profile.revise, Calendar.profile]
  · simp [Profile.revise, h]

/-- A periodic volunteer certificate gives a uniform equilibrium payoff for the
ordinary quitting game. Each tolerance selects one independent profile for all
later horizons, and arbitrary behavioral deviations are admissible. -/
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
  intro ε hε
  obtain ⟨p', H, hp', hH, h⟩ :=
    uniform_of_periodic_calendar g p v hβ₀ hβ₁ hM hC prob actorPeriod probPeriod
      opportunity recurrence tie ir liveBound collision ε hε
  refine ⟨p'.profile, H, fun i ↦ own_legal hp' i, hH, ?_⟩
  intro N hN i
  have honest : expectedAverage g p'.profile i N = average p' g i (own p' i) N := by
    rw [← revise_own p' i, revised_average]
  rw [honest]
  exact ⟨(h N hN i _ (own_legal hp' i)).1, fun q hq ↦
    (revised_average g p' i q N).le.trans (h N hN i q hq).2⟩

#print axioms periodic_calendar_uniform_payoff

end

end PlanarQuitting
