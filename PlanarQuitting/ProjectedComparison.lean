module

public import PlanarQuitting.IndexTransfer
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Projected payoff comparisons

A fixed point of the projected comparison map encodes the sign at each of
the two ends of a player's probability interval. The first-order map uses
only the positive part, since the upper faces do not meet zero.
-/

@[expose] public section

namespace PlanarQuitting

open Filter Set
open scoped BigOperators Topology

noncomputable section

variable {n : ℕ}

def positivePart (x : Coordinates n) : Coordinates n := fun i ↦ max 0 (x i)

def cubeClip (x : Coordinates n) : Coordinates n := fun i ↦ min 1 (max 0 (x i))

theorem continuous_positivePart : Continuous (positivePart (n := n)) :=
  continuous_pi fun i ↦ continuous_const.max (continuous_apply i)

theorem continuous_cubeClip : Continuous (cubeClip (n := n)) :=
  continuous_pi fun i ↦ continuous_const.min (continuous_const.max (continuous_apply i))

theorem cubeClip_mem (x : Coordinates n) : cubeClip x ∈ Icc 0 1 :=
  ⟨fun _ ↦ le_min zero_le_one (le_max_left ..), fun _ ↦ min_le_left ..⟩

def CubeComparison (f : Coordinates n → Coordinates n) (p : Coordinates n) : Prop :=
  p ∈ Icc 0 1 ∧ ∀ i, (p i < 1 → 0 ≤ f p i) ∧ (0 < p i → f p i ≤ 0)

def projectedMap (f : Coordinates n → Coordinates n) (x : Coordinates n) : Coordinates n :=
  x - cubeClip x + f (cubeClip x)

def normalMap (D : Coordinates n →L[ℝ] Coordinates n) (x : Coordinates n) : Coordinates n :=
  x - positivePart x + D (positivePart x)

theorem projectedMap_continuous {f : Coordinates n → Coordinates n} (hf : Continuous f) :
    Continuous (projectedMap f) :=
  (continuous_id.sub continuous_cubeClip).add (hf.comp continuous_cubeClip)

theorem normalMap_continuous (D : Coordinates n →L[ℝ] Coordinates n) :
    Continuous (normalMap D) :=
  (continuous_id.sub continuous_positivePart).add (D.continuous.comp continuous_positivePart)

/-- Projected zeros and the cube endpoint inequalities are equivalent. -/
theorem projected_zero_iff (f : Coordinates n → Coordinates n) (x : Coordinates n) :
    projectedMap f x = 0 ↔
      CubeComparison f (cubeClip x) ∧ x = cubeClip x - f (cubeClip x) := by
  let p := cubeClip x
  have hp : p ∈ Icc 0 1 := cubeClip_mem x
  constructor
  · intro hz
    have balance : x = p - f p := by
      have h : x - p + f p = 0 := hz
      rw [← sub_eq_zero] at *
      abel_nf at h ⊢
      exact h
    refine ⟨⟨hp, fun i ↦ ⟨?_, ?_⟩⟩, balance⟩
    · intro hlt
      have hi : p i = max 0 (x i) := by
        change min 1 (max 0 (x i)) < 1 at hlt
        rw [min_lt_iff] at hlt
        exact min_eq_right ((hlt.resolve_left (lt_irrefl 1)).le)
      have hb := congrFun balance i
      change x i = p i - f p i at hb
      linarith [hi, le_max_right 0 (x i)]
    · intro hpos
      have hx : 0 < x i := by
        by_contra! h
        change 0 < min 1 (max 0 (x i)) at hpos
        rw [max_eq_left h, min_eq_right zero_le_one] at hpos
        exact (lt_irrefl _) hpos
      have hi : p i ≤ x i := by
        change min 1 (max 0 (x i)) ≤ x i
        rw [max_eq_right hx.le]
        exact min_le_right ..
      have hb := congrFun balance i
      change x i = p i - f p i at hb
      linarith
  · rintro ⟨_, balance⟩
    change x - p + f p = 0
    calc
      _ = (p - f p) - p + f p := by rw [← balance]
      _ = 0 := by abel

theorem posPart_norm_le (x : Coordinates n) : ‖positivePart x‖ ≤ ‖x‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  rw [positivePart, Real.norm_of_nonneg (le_max_left ..)]
  exact max_le (norm_nonneg _) ((Real.le_norm_self _).trans (norm_le_pi_norm x i))

theorem clip_eq_positivePart {x : Coordinates n} (hx : ‖x‖ ≤ 1) :
    cubeClip x = positivePart x := by
  funext i
  exact min_eq_right (max_le zero_le_one
    ((Real.le_norm_self _).trans ((norm_le_pi_norm x i).trans hx)))

theorem normalMap_scale (D : Coordinates n →L[ℝ] Coordinates n)
    (x : Coordinates n) {a : ℝ} (ha : 0 ≤ a) :
    normalMap D (a • x) = a • normalMap D x := by
  have hpos : positivePart (a • x) = a • positivePart x := by
    funext i
    change max 0 (a * x i) = a * max 0 (x i)
    rw [mul_max_of_nonneg _ _ ha, mul_zero]
  simp only [normalMap, hpos, map_smul, smul_add, smul_sub]

private theorem affine_scale {m : Coordinates n → Coordinates n}
    (hom : ∀ a : ℝ, 0 ≤ a → ∀ x, m (a • x) = a • m x)
    {q z k : Coordinates n} {a : ℝ} (ha : 0 < a)
    (L : Coordinates n ≃L[ℝ] Coordinates n)
    (h : (fun x ↦ m x + q) =ᶠ[𝓝 z] fun x ↦ L x + k) :
    (fun x ↦ m x + a • q) =ᶠ[𝓝 (a • z)] fun x ↦ L x + a • k := by
  have hz : a⁻¹ • (a • z) = z := by rw [smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
  have hcont : Continuous (fun x : Coordinates n ↦ a⁻¹ • x) := continuous_id.const_smul a⁻¹
  have hlim := hcont.continuousAt (x := a • z)
  change Tendsto _ _ (𝓝 (a⁻¹ • (a • z))) at hlim
  rw [hz] at hlim
  filter_upwards [hlim.eventually h] with x hx
  have h' := congrArg (fun v : Coordinates n ↦ a • v) hx
  change a • (m (a⁻¹ • x) + q) = a • (L (a⁻¹ • x) + k) at h'
  simpa only [smul_add, hom _ (inv_nonneg.mpr ha.le), L.map_smul, smul_smul,
    mul_inv_cancel₀ ha.ne', one_smul] using h'

/-- A homogeneous continuous map bounded away from zero on nonzero vectors
has a uniform linear lower bound on its norm. -/
theorem normalMap_coercive (D : Coordinates n →L[ℝ] Coordinates n)
    (nonzero : ∀ x, x ≠ 0 → normalMap D x ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ≤ ‖normalMap D x‖ := by
  let S := Metric.sphere (0 : Coordinates n) 1
  have unit (x : Coordinates n) (hx : x ≠ 0) : ‖x‖⁻¹ • x ∈ S := by
    have hp := norm_pos_iff.mpr hx
    change dist (‖x‖⁻¹ • x) 0 = 1
    rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hp.le),
      inv_mul_cancel₀ hp.ne']
  by_cases hS : S.Nonempty
  · obtain ⟨z, hz, hmin⟩ := (isCompact_sphere (0 : Coordinates n) 1).exists_isMinOn
      hS (normalMap_continuous D).norm.continuousOn
    have hne : z ≠ 0 := by
      intro h
      change dist z 0 = 1 at hz
      simp [h] at hz
    refine ⟨‖normalMap D z‖, norm_pos_iff.mpr (nonzero z hne), fun x ↦ ?_⟩
    by_cases hx : x = 0
    · simp [hx]
    have hp := norm_pos_iff.mpr hx
    have h := hmin (unit x hx)
    change ‖normalMap D z‖ ≤ ‖normalMap D (‖x‖⁻¹ • x)‖ at h
    rw [normalMap_scale _ _ (inv_nonneg.mpr hp.le), norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hp.le), ← div_eq_inv_mul] at h
    exact (le_div_iff₀ hp).1 h
  · exact ⟨1, one_pos, fun x ↦ by
      have hx : x = 0 := by
        by_contra h
        exact hS ⟨_, unit x h⟩
      simp [hx]⟩

/-- If the signed count of a translated homogeneous model is different from
one, the original payoff comparison has a solution with a nonzero hazard.
This theorem includes the approximation at zero and compactness at infinity. -/
theorem nonzero_cube_of_signed_count {J : Type*} [Fintype J]
    {f : Coordinates n → Coordinates n} (hf : Continuous f) (fzero : f 0 = 0)
    (D : Coordinates n →L[ℝ] Coordinates n) (diff : HasFDerivAt f D 0)
    (normal_nonzero : ∀ x, x ≠ 0 → normalMap D x ≠ 0)
    (q : Coordinates n) (z : J → Coordinates n) (injective : Function.Injective z)
    (exactRoots : ∀ x, normalMap D x + q = 0 ↔ ∃ j, x = z j)
    (L : J → Coordinates n ≃L[ℝ] Coordinates n) (offset : J → Coordinates n)
    (affine : ∀ j, (fun x ↦ normalMap D x + q) =ᶠ[𝓝 (z j)] fun x ↦ L j x + offset j)
    (count : (∑ j, (L j).toContinuousLinearMap.det / |(L j).toContinuousLinearMap.det|) ≠ 1) :
    ∃ p, p ≠ 0 ∧ CubeComparison f p := by
  by_contra! no
  have nonzero (x : Coordinates n) (hx : x ≠ 0) : projectedMap f x ≠ 0 := by
    intro hz
    obtain ⟨hc, he⟩ := (projected_zero_iff f x).1 hz
    have h : cubeClip x = 0 := by
      by_contra hneg
      exact no (cubeClip x) hneg hc
    exact hx (by simpa [h, fzero] using he)
  obtain ⟨c, hc, lower⟩ := normalMap_coercive D normal_nonzero
  have hdiff := diff.isLittleO.bound (half_pos hc)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hdiff
  let r := min δ 1 / 4
  have hr : 0 < r := div_pos (lt_min hδ zero_lt_one) (by norm_num)
  have closer (x : Coordinates n) (hx : ‖x‖ ≤ 2*r) :
      ‖projectedMap f x - normalMap D x‖ ≤ c * ‖x‖ / 2 := by
    have hmδ : min δ 1 ≤ δ := min_le_left ..
    have hm₁ : min δ 1 ≤ 1 := min_le_right ..
    have hp := posPart_norm_le x
    have hsmall : positivePart x ∈ Metric.ball (0 : Coordinates n) δ := by
      rw [Metric.mem_ball, dist_zero_right]
      dsimp [r] at hx
      linarith
    have h := hball hsmall
    change ‖f (positivePart x) - f 0 - D (positivePart x - 0)‖ ≤
      c/2 * ‖positivePart x - 0‖ at h
    simp only [fzero, sub_zero] at h
    rw [projectedMap, normalMap, clip_eq_positivePart (by dsimp [r] at hx; linarith)]
    rw [show x - positivePart x + f (positivePart x) -
        (x - positivePart x + D (positivePart x)) =
        f (positivePart x) - D (positivePart x) by abel]
    linarith [mul_le_mul_of_nonneg_left hp (half_pos hc).le]
  have compact : IsCompact (Icc (0 : Coordinates n) 1) := isCompact_Icc
  obtain ⟨B, hB⟩ := compact.exists_bound_of_continuousOn
    (hf.sub continuous_id).continuousOn
  have far (x : Coordinates n) : ‖projectedMap f x - x‖ ≤ B := by
    unfold projectedMap
    rw [show x - cubeClip x + f (cubeClip x) - x = f (cubeClip x) - cubeClip x by abel]
    exact hB _ (cubeClip_mem x)
  let R := max B (2*r) + 1
  have hR : 2*r < R := (le_max_right ..).trans_lt (lt_add_one _)
  have hBR : B < R := (le_max_left ..).trans_lt (lt_add_one _)
  let a := c*r/(4*(1+‖q‖))
  have hden : 0 < 4*(1+‖q‖) := by positivity
  have ha : 0 < a := div_pos (mul_pos hc hr) hden
  have small : ‖a • q‖ < c*r/2 := by
    rw [norm_smul, Real.norm_of_nonneg ha.le]
    change (c*r/(4*(1+‖q‖))) * ‖q‖ < c*r/2
    rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
    have hp := mul_pos hc hr
    nlinarith [mul_nonneg hp.le (norm_nonneg q)]
  have scaled (x : Coordinates n) : normalMap D x + a • q = 0 ↔
      ∃ j, x = a • z j := by
    have hx : a • (a⁻¹ • x) = x := by rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
    have he : a • (normalMap D (a⁻¹ • x) + q) = normalMap D x + a • q := by
      rw [smul_add, ← normalMap_scale _ _ ha.le, hx]
    rw [← he, smul_eq_zero, or_iff_right ha.ne', exactRoots]
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, hx.symm.trans (congrArg (a • ·) hj)⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j, by rw [smul_smul, inv_mul_cancel₀ ha.ne', one_smul]⟩
  apply count
  exact signed_count_transfer (projectedMap_continuous hf) (normalMap_continuous D)
    hc hr hR hBR lower closer far nonzero (a • q) small (fun j ↦ a • z j)
    (fun j k h ↦ injective ((smul_right_injective _ ha.ne') h)) scaled L (fun j ↦ a • offset j)
    (fun j ↦ affine_scale (fun a ha x ↦ normalMap_scale D x ha) ha (L j) (affine j))

#print axioms projected_zero_iff
#print axioms normalMap_coercive
#print axioms nonzero_cube_of_signed_count

end

end PlanarQuitting
