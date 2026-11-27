module

public import PlanarQuitting.Refinement

/-!
# Periodic calendars with rival quitting opportunities

If each player faces at least one rival who can quit in each period, the expected
duration is bounded even when the deviator never quits. This discharges the
summed-survival premise of the calendar refinement theorem.
-/

@[expose] public section

namespace PlanarQuitting

open scoped BigOperators

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

private theorem period_survival_sum {p : Calendar I} (hp : Legal p.prob)
    {L : ℕ} (actorPeriod : ∀ t, p.actor (t+L) = p.actor t)
    (probPeriod : ∀ t, p.prob (t+L) = p.prob t)
    (opportunity : ∀ i, ∃ t < L, 0 < rival p i t) :
    ∃ K : ℝ, ∀ N i, (∑ t ∈ Finset.range N, alive p i (fun _ ↦ 0) (t+1)) ≤ K := by
  let S (i : I) (t : ℕ) := alive p i (fun _ ↦ 0) t
  have hpos (i : I) (t : ℕ) : 0 ≤ S i t :=
    alive_nonneg hp i (q := fun _ ↦ 0) (by intro t; norm_num) t
  have hstep (i : I) (t : ℕ) : S i (t+1) = S i t * (1-rival p i t) := by
    simp [S, alive, remaining]
  have hanti (i : I) : Antitone (S i) := by
    apply antitone_nat_of_succ_le
    intro t
    rw [hstep]
    exact mul_le_of_le_one_right (hpos i t) (sub_le_self _ (rival_legal hp i t).1)
  have hone (i : I) (t : ℕ) : S i t ≤ 1 := hanti i (Nat.zero_le t)
  have hcontract (i : I) : S i L < 1 := by
    obtain ⟨t, ht, ht'⟩ := opportunity i
    refine (hanti i ht).trans_lt ?_
    rw [hstep]
    have hnon := sub_nonneg.mpr (rival_legal hp i t).2
    have hmul := mul_le_mul_of_nonneg_right (hone i t) hnon
    linarith
  have hperiod (i : I) (t : ℕ) : S i (L+t) = S i L * S i t := by
    induction t with
    | zero => simp [S, alive]
    | succ t ih =>
      rw [Nat.add_succ, hstep, hstep, ih]
      have hr : rival p i (L+t) = rival p i t := by
        rw [Nat.add_comm L t]
        simp [rival, actorPeriod, probPeriod]
      rw [hr, mul_assoc]
  let cap (i : I) := (L : ℝ) / (1 - S i L)
  refine ⟨∑ j, cap j, ?_⟩
  intro N i
  refine le_trans ?_ (Finset.single_le_sum
    (f := cap) (fun j _ ↦ div_nonneg (Nat.cast_nonneg L) (sub_nonneg.mpr (hone j L)))
    (Finset.mem_univ i))
  change (∑ t ∈ Finset.range N, S i (t+1)) ≤ (L : ℝ) / (1 - S i L)
  let sumS (N : ℕ) := ∑ t ∈ Finset.range N, S i (t+1)
  have hsmall (n : ℕ) : sumS n ≤ n := by
    calc
      _ ≤ ∑ t ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum (fun t _ ↦ hone i (t+1))
      _ = n := by simp
  have hgoal : sumS N ≤ (L : ℝ) + S i L * sumS N := by
    by_cases hLN : L ≤ N
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hLN
      have hsplit : sumS (L+k) = sumS L + S i L * sumS k := by
        simp only [sumS, Finset.sum_range_add, Nat.add_assoc, hperiod, Finset.mul_sum]
      have hle : sumS k ≤ sumS (L+k) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_add_left k L))
          (fun t _ _ ↦ hpos i (t+1))
      linarith only [hsplit, hsmall L, mul_le_mul_of_nonneg_left hle (hpos i L)]
    · exact ((hsmall N).trans (Nat.cast_le.mpr (Nat.le_of_not_ge hLN))).trans
        (le_add_of_nonneg_right (mul_nonneg (hpos i L)
          (Finset.sum_nonneg fun t _ ↦ hpos i (t+1))))
  exact (le_div_iff₀ (sub_pos.mpr (hcontract i))).mpr (by linarith only [hgoal])

/-- A periodic calendar along individually rational promises gives a uniform payoff
if every player faces a rival quitting opportunity in one period. -/
theorem uniform_of_periodic_calendar (g : Game I) (p : Calendar I) (v : ℕ → I → ℝ)
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
    ∀ ε : ℝ, 0 < ε → ∃ (p' : Calendar I) (H : ℕ), Legal p'.prob ∧ 1 ≤ H ∧
      ∀ N : ℕ, H ≤ N → ∀ i q, Legal q →
        |average p' g i (own p' i) N - v 0 i| ≤ ε ∧
        average p' g i q N ≤ average p' g i (own p' i) N + ε := by
  have hp : Legal p.prob := fun t ↦ ⟨(prob t).1, (prob t).2.trans hβ₁.le⟩
  obtain ⟨K, hK⟩ := period_survival_sum hp actorPeriod probPeriod opportunity
  exact uniform_of_refinable
    (⟨prob, recurrence, tie, ir, hM, liveBound, hK⟩ :
      Refinable g p v β M K) hβ₀ hβ₁ hC collision

#print axioms uniform_of_periodic_calendar

end

end PlanarQuitting
