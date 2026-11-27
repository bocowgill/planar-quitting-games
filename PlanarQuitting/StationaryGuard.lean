module

public import PlanarQuitting.StationaryDerivative
public import PlanarQuitting.PlanarComparison
public import PlanarQuitting.CycleImplementation
import Mathlib.Tactic.Linarith

/-!
# Guarding the positive rows of the stationary comparisons

A player who strictly prefers every rival singleton to their own cannot
be the only positive quitter in the modified comparisons. The modification
preserves all original cube comparisons at each of its solutions.
-/

@[expose] public section

namespace PlanarQuitting

open Set Filter
open scoped BigOperators Topology

noncomputable section

variable {n : ℕ}

def withoutOwn (i : Fin n) (x : Coordinates n) : Coordinates n :=
  fun j ↦ if j = i then 0 else x j

theorem withoutOwn_continuous (i : Fin n) : Continuous (withoutOwn i) := by
  apply continuous_pi
  intro j
  by_cases hj : j = i
  · simpa only [withoutOwn, if_pos hj] using continuous_const
  · simpa only [withoutOwn, if_neg hj] using continuous_apply j

@[simp] theorem withoutOwn_zero (i : Fin n) : withoutOwn i 0 = 0 := by
  funext j
  simp [withoutOwn]

theorem stationaryDifference_ignores_own (g : Game (Fin n)) (i : Fin n)
    (x : Coordinates n) : stationaryDifference g (withoutOwn i x) i = stationaryDifference g x i := by
  have hm (A : Finset (Fin n)) : opponentMass (withoutOwn i x) i A = opponentMass x i A := by
    apply Finset.prod_congr rfl
    intro j hj
    simp [withoutOwn, (Finset.mem_erase.mp hj).1]
  simp only [stationaryDifference, stationaryQuit, stationaryCash, opponentWait, hm]

private theorem positive_row_near (g : Game (Fin n)) (i : Fin n)
    (h : ∀ j, j ≠ i → 0 < prizeGapMatrix g i j) :
    ∃ δ > 0, ∀ x : Coordinates n, (∀ j, 0 ≤ x j) → x i = 0 → ‖x‖ < δ →
      0 ≤ stationaryDifference g x i := by
  let S := Finset.univ.erase i
  have slope : ∃ c : ℝ, 0 < c ∧ ∀ j ∈ S, c ≤ prizeGapMatrix g i j := by
    by_cases hn : S.Nonempty
    · obtain ⟨j,hj,hmin⟩ := Finset.exists_min_image S (prizeGapMatrix g i) hn
      exact ⟨prizeGapMatrix g i j, h j (Finset.mem_erase.mp hj).1,hmin⟩
    · exact ⟨1,one_pos,fun j hj ↦ (hn ⟨j,hj⟩).elim⟩
  obtain ⟨c,hc,hmin⟩ := slope
  have hdiff := hasFDerivAt_pi'.mp (stationaryDifference_derivative g) i
  obtain ⟨δ,hδ,hbound⟩ := Metric.mem_nhds_iff.mp (hdiff.isLittleO.bound (half_pos hc))
  refine ⟨δ,hδ,fun x hx hxi hn ↦ ?_⟩
  have hball : x ∈ Metric.ball (0 : Coordinates n) δ := by
    simpa only [Metric.mem_ball, dist_zero_right] using hn
  have he := hbound hball
  change ‖stationaryDifference g x i - stationaryDifference g 0 i -
      matrixMap (prizeGapMatrix g) (x - 0) i‖ ≤ c/2 * ‖x - 0‖ at he
  simp only [stationaryDifference_zero, Pi.zero_apply, sub_zero] at he
  have hS : ‖x‖ ≤ ∑ j ∈ S, x j := by
    rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ ↦ hx j)]
    intro j
    rw [Real.norm_of_nonneg (hx j)]
    by_cases hj : j = i
    · rw [hj,hxi]
      exact Finset.sum_nonneg (fun k _ ↦ hx k)
    · exact Finset.single_le_sum (fun j _ ↦ hx j)
        (show j ∈ S from Finset.mem_erase.mpr ⟨hj,Finset.mem_univ _⟩)
  have hD : c * ‖x‖ ≤ matrixMap (prizeGapMatrix g) x i := by
    rw [matrixMap_apply, ← Finset.sum_erase_add _ _ (Finset.mem_univ i),
      prizeGapMatrix_diag, zero_mul, add_zero]
    refine (mul_le_mul_of_nonneg_left hS hc.le).trans ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j hj ↦ mul_le_mul_of_nonneg_right (hmin j hj) (hx j)
  have hb := (Real.le_norm_self
    (-(stationaryDifference g x i - matrixMap (prizeGapMatrix g) x i))).trans
      (by simpa only [norm_neg] using he)
  linarith [mul_nonneg hc.le (norm_nonneg x)]

/-- A continuous cutoff for an entrywise positive rival row. Its support
uses only rival probabilities, and its contribution vanishes when the
original row would permit a positive own hazard. -/
private theorem positive_cutoff (g : Game (Fin n)) (i : Fin n)
    (h : ∀ j, j ≠ i → 0 < prizeGapMatrix g i j) :
    ∃ χ : Coordinates n → ℝ, Continuous χ ∧
      (∀ x, 0 ≤ χ x) ∧ (∀ᶠ x in 𝓝 0, χ x = 1) ∧
      (∀ x, withoutOwn i x = 0 → χ x = 1) ∧
      (∀ x, (∀ j, 0 ≤ x j) → 0 < χ x → 0 ≤ stationaryDifference g x i) := by
  obtain ⟨δ,hδ,hbound⟩ := positive_row_near g i h
  let χ (x : Coordinates n) := min 1 (max 0 (2 - 2*‖withoutOwn i x‖/δ))
  have hcont : Continuous χ :=
    continuous_const.min (continuous_const.max
      (continuous_const.sub ((continuous_const.mul (withoutOwn_continuous i).norm).div_const δ)))
  have hχ (x : Coordinates n) (hx : ‖withoutOwn i x‖ < δ/2) : χ x = 1 := by
    apply min_eq_left
    apply le_trans _ (le_max_right ..)
    have he : 2*‖withoutOwn i x‖/δ < 1 := (div_lt_iff₀ hδ).2 (by linarith)
    linarith
  refine ⟨χ,hcont,fun x ↦ le_min zero_le_one (le_max_left ..),?_,?_,?_⟩
  · have h0 : ‖withoutOwn i (0 : Coordinates n)‖ < δ/2 := by
      simpa using half_pos hδ
    have hn := (isOpen_lt (withoutOwn_continuous i).norm continuous_const).mem_nhds h0
    filter_upwards [hn] with x hx
    exact hχ x hx
  · intro x hx
    exact hχ x (by simpa [hx] using half_pos hδ)
  · intro x hx hpos
    rw [← stationaryDifference_ignores_own]
    apply hbound
    · intro j
      by_cases hj : j = i <;> simp [withoutOwn,hj,hx]
    · simp [withoutOwn]
    · have he : 0 < 2 - 2*‖withoutOwn i x‖/δ := by
        have hm : 0 < max 0 (2 - 2*‖withoutOwn i x‖/δ) :=
          hpos.trans_le (min_le_right ..)
        exact (lt_max_iff.mp hm).resolve_left (lt_irrefl 0)
      have hn : 2*‖withoutOwn i x‖/δ < 2 := by linarith
      have hb := (div_lt_iff₀ hδ).1 hn
      linarith

def guardedMatrix (g : Game (Fin n)) (K : Finset (Fin n)) : PayoffMatrix n :=
  fun i j ↦ prizeGapMatrix g i j + if i = j ∧ i ∉ K then 1 else 0

private def guardLinear (K : Finset (Fin n)) : Coordinates n →L[ℝ] Coordinates n :=
  ContinuousLinearMap.pi fun i ↦ if i ∈ K then 0 else ContinuousLinearMap.proj i

private theorem matrix_guard (g : Game (Fin n)) (K : Finset (Fin n)) :
    matrixMap (guardedMatrix g K) = matrixMap (prizeGapMatrix g) + guardLinear K := by
  ext x i
  change matrixMap (guardedMatrix g K) x i =
    matrixMap (prizeGapMatrix g) x i + guardLinear K x i
  rw [matrixMap_apply, matrixMap_apply]
  simp only [guardedMatrix, add_mul, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
  · by_cases hi : i ∈ K <;> simp [guardLinear,hi]
  · intro j _ hne
    simp [hne.symm]

structure GuardedComparison (g : Game (Fin n)) (K : Finset (Fin n)) where
  fieldMap : Coordinates n → Coordinates n
  continuous : Continuous fieldMap
  zero : fieldMap 0 = 0
  derivative : HasFDerivAt fieldMap (matrixMap (guardedMatrix g K)) 0
  original : ∀ p, CubeComparison fieldMap p → StationaryComparisons g p
  sole : ∀ p, CubeComparison fieldMap p → ∀ i, 0 < p i → withoutOwn i p = 0 → i ∈ K

theorem exists_guarded_comparison (g : Game (Fin n)) (K : Finset (Fin n))
    (h : ∀ i ∉ K, ∀ j, j ≠ i → 0 < prizeGapMatrix g i j) :
    Nonempty (GuardedComparison g K) := by
  classical
  have pick (i : Fin n) : ∃ χ : Coordinates n → ℝ, Continuous χ ∧
      (∀ x, 0 ≤ χ x) ∧
      (∀ᶠ x in 𝓝 0, χ x = if i ∈ K then 0 else 1) ∧
      (∀ x, withoutOwn i x = 0 → i ∉ K → χ x = 1) ∧
      (∀ x, (∀ j, 0 ≤ x j) → 0 < χ x → 0 ≤ stationaryDifference g x i) := by
    by_cases hi : i ∈ K
    · exact ⟨fun _ ↦ 0,continuous_const,fun _ ↦ le_rfl,
        Eventually.of_forall (by simp [hi]),fun _ _ h ↦ (h hi).elim,
        fun _ _ hp ↦ ((lt_irrefl 0) hp).elim⟩
    · obtain ⟨χ,hc,hn,ha,hb,hp⟩ := positive_cutoff g i (h i hi)
      exact ⟨χ,hc,hn,by simpa [hi] using ha,fun x hx _ ↦ hb x hx,hp⟩
  choose χ hcont hnon hnear hown hpos using pick
  let field (x : Coordinates n) (i : Fin n) := stationaryDifference g x i + χ i x * x i
  refine ⟨⟨field,?_,?_,?_,?_,?_⟩⟩
  · apply continuous_pi
    exact fun i ↦ ((continuous_apply i).comp (stationaryDifference_continuous g)).add
      ((hcont i).mul (continuous_apply i))
  · funext i
    simp [field, stationaryDifference_zero]
  · rw [matrix_guard]
    apply ((stationaryDifference_derivative g).add (guardLinear K).hasFDerivAt).congr_of_eventuallyEq
    filter_upwards [eventually_all.mpr hnear] with x hx
    funext i
    show field x i = stationaryDifference g x i + guardLinear K x i
    dsimp only [field]
    rw [hx i]
    by_cases hi : i ∈ K <;> simp [guardLinear,hi]
  · intro p hp
    have vanish (i : Fin n) : χ i p * p i = 0 := by
      by_contra hne
      have hc : 0 < χ i p := lt_of_le_of_ne (hnon i p)
        (fun he ↦ hne (by rw [← he,zero_mul]))
      have hp₀ : 0 < p i := lt_of_le_of_ne (hp.1.1 i)
        (fun he ↦ hne (by rw [← he,mul_zero]))
      have hh := hpos i p hp.1.1 hc
      have hnd := (hp.2 i).2 hp₀
      exact (not_lt_of_ge hnd) (add_pos_of_nonneg_of_pos hh (mul_pos hc hp₀))
    intro i
    have he : field p i = stationaryDifference g p i := by simp [field,vanish]
    simpa only [← he] using hp.2 i
  · intro p hp i hpi hzero
    by_contra hi
    have hχ := hown i p hzero hi
    have hh := hpos i p hp.1.1 (by rw [hχ]; exact one_pos)
    have hnd := (hp.2 i).2 hpi
    rw [show field p i = stationaryDifference g p i + p i by simp [field,hχ]] at hnd
    linarith

/-- The geometry forces a nonzero stationary comparison solution with
any sole quitter in the core, or a directed cycle. -/
theorem stationary_comparisons_or_cycle {E : Type*} [AddCommGroup E] [Module ℝ E]
    (g : Game (Fin n)) (K : Finset (Fin n)) [Nonempty K] (F : Faces K E)
    (hreg : RegularFaces F) (sites : ∀ i, ¬ F.Feasible (F.site i))
    (core : ∀ i j : K, prizeGapMatrix g i j = F.cross i j)
    (out : ∀ i ∉ K, ∀ j, j ≠ i → 0 < prizeGapMatrix g i j) :
    (∃ p : Coordinates n, p ≠ 0 ∧ p ∈ Icc 0 1 ∧ StationaryComparisons g p ∧
      (∀ i, 0 < p i → withoutOwn i p = 0 → i ∈ K)) ∨ Nonempty (DirectedCycle F) := by
  obtain ⟨guard⟩ := exists_guarded_comparison g K out
  have rep : ComparisonFaces (guardedMatrix g K) K F := by
    constructor
    · intro i j
      simpa [guardedMatrix,i.property] using core i j
    · intro i hi j
      by_cases h : i = j
      · subst j
        simp [guardedMatrix,hi]
      · simpa [guardedMatrix,h] using out i hi j (Ne.symm h)
  rcases rep.cube_or_cycle hreg sites guard.continuous guard.zero guard.derivative with h | h
  · obtain ⟨p,hp,hs⟩ := h
    exact Or.inl ⟨p,hp,hs.1,guard.original p hs,guard.sole p hs⟩
  · exact Or.inr h

#print axioms exists_guarded_comparison
#print axioms stationary_comparisons_or_cycle

end

end PlanarQuitting
