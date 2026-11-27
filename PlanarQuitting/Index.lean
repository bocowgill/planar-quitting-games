import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Barycentric complementarity and the four-player square

The geometric identity works for every real vector space and linear payoff
functional. The explicit four-player system uses the singleton payoff rows
of the square with points (0,-2), (1,3), (-1,0), and (2,1).
-/

namespace PlanarQuitIndex

open scoped BigOperators Matrix

variable {I E : Type*} [Fintype I] [AddCommGroup E] [Module ℝ E]

/-- Evaluating a row at the barycenter gives exactly its complementarity slack,
scaled by the total barycentric mass. -/
theorem barycentric_row (row : E →ₗ[ℝ] ℝ) (R : I → E) (i : I) (z₀ Z : E) (t : I → ℝ)
    (balance : (1 + ∑ j, t j) • Z = z₀ + ∑ j, t j • R j) :
    row (z₀ - R i) + ∑ j, t j * row (R j - R i) =
      (1 + ∑ j, t j) * row (Z - R i) := by
  have hz := congrArg row balance
  simp only [map_add, map_sum, map_smul, smul_eq_mul] at hz
  simp only [map_sub, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  linarith only [hz]

/-- At an intersection of two binding faces, outward directions give negative
cross entries and a negative determinant for their active minor. -/
theorem sink_minor (u v : E →ₗ[ℝ] ℝ) (ri rj z : E)
    (hu : u (z - ri) = 0) (hv : v (z - rj) = 0)
    (hout₁ : u (rj - z) < 0) (hout₂ : v (ri - z) < 0) :
    u (rj - ri) < 0 ∧ v (ri - rj) < 0 ∧
      (!![0, u (rj - ri); v (ri - rj), 0] : Matrix (Fin 2) (Fin 2) ℝ).det < 0 := by
  simp only [map_sub] at *
  have h₁ : u rj - u ri < 0 := by linarith only [hu, hout₁]
  have h₂ : v ri - v rj < 0 := by linarith only [hv, hout₂]
  exact ⟨h₁, h₂, by simpa [Matrix.det_fin_two] using neg_neg_of_pos (mul_pos_of_neg_of_neg h₁ h₂)⟩

/-- Two negative cross entries give a unique positive active-pair solution
exactly for two positive offsets. -/
theorem active_pair_iff {a b h₁ h₂ x y : ℝ} (ha : a < 0) (hb : b < 0) :
    (0 < x ∧ 0 < y ∧ h₁ + a * y = 0 ∧ h₂ + b * x = 0) ↔
      (0 < h₁ ∧ 0 < h₂ ∧ x = -h₂ / b ∧ y = -h₁ / a) := by
  constructor
  · rintro ⟨hx, hy, hxy, hyx⟩
    exact ⟨by linarith only [hxy, mul_neg_of_neg_of_pos ha hy],
      by linarith only [hyx, mul_neg_of_neg_of_pos hb hx],
      (eq_div_iff hb.ne).2 (by linarith only [hyx, mul_comm b x]),
      (eq_div_iff ha.ne).2 (by linarith only [hxy, mul_comm a y])⟩
  · rintro ⟨hh₁, hh₂, hx, hy⟩
    exact ⟨hx ▸ div_pos_of_neg_of_neg (neg_neg_of_pos hh₂) hb,
      hy ▸ div_pos_of_neg_of_neg (neg_neg_of_pos hh₁) ha,
      by linarith only [(eq_div_iff ha.ne).1 hy, mul_comm a y],
      by linarith only [(eq_div_iff hb.ne).1 hx, mul_comm b x]⟩

/-- The square's normalized complementary system at offset (-q,0,0,0). -/
def SquareLCP (q x y z w : ℝ) : Prop :=
  let s₁ := -q + y - z + 2*w
  let s₂ := x + 2*z - w
  let s₃ := -2*x + 3*y + w
  let s₄ := 3*x - 2*y + z
  0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ 0 ≤ w ∧ 0 ≤ s₁ ∧ 0 ≤ s₂ ∧ 0 ≤ s₃ ∧ 0 ≤ s₄ ∧
    x*s₁ = 0 ∧ y*s₂ = 0 ∧ z*s₃ = 0 ∧ w*s₄ = 0

/-- This includes uniqueness of the homogeneous zero and the unique strictly
complementary positive-offset preimage on the ray. All sixteen supports are allowed. -/
theorem square_lcp_iff {q x y z w : ℝ} (hq : 0 ≤ q) :
    SquareLCP q x y z w ↔ x = 2*q/7 ∧ y = 3*q/7 ∧ z = 0 ∧ w = 2*q/7 := by
  constructor
  · rintro ⟨hx, hy, hz, hw, s₁, s₂, s₃, s₄, c₁, c₂, c₃, c₄⟩
    rcases mul_eq_zero.mp c₁ with a | a <;>
      rcases mul_eq_zero.mp c₂ with b | b <;>
      rcases mul_eq_zero.mp c₃ with c | c <;>
      rcases mul_eq_zero.mp c₄ with d | d
    all_goals (repeat' constructor) <;> linarith only [hq, hx, hy, hz, hw, s₁, s₂, s₃, s₄, a, b, c, d]
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    dsimp [SquareLCP]
    repeat' constructor
    all_goals nlinarith only [hq]

private def pos (x : ℝ) := max x 0

private theorem parts (x : ℝ) : pos x * pos (-x) = 0 ∧ pos x - pos (-x) = x := by
  rcases le_total 0 x with h | h
  · simp [pos, max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
  · simp [pos, max_eq_right h, max_eq_left (neg_nonneg.mpr h)]

/-- The square normal map at a signed vector equals (q,0,0,0). -/
def SquarePreimage (q x y z w : ℝ) : Prop :=
  -q + pos y - pos z + 2*pos w = pos (-x) ∧
    pos x + 2*pos z - pos w = pos (-y) ∧
    -2*pos x + 3*pos y + pos w = pos (-z) ∧
    3*pos x - 2*pos y + pos z = pos (-w)

/-- The signed normal map has a unique inverse image along the nonnegative first axis. -/
theorem square_preimage_iff {q x y z w : ℝ} (hq : 0 ≤ q) :
    SquarePreimage q x y z w ↔ x = 2*q/7 ∧ y = 3*q/7 ∧ z = -q ∧ w = 2*q/7 := by
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    have hp (a : ℝ) : 0 ≤ pos a := le_max_right ..
    have hc : SquareLCP q (pos x) (pos y) (pos z) (pos w) :=
      ⟨hp _, hp _, hp _, hp _, h₁ ▸ hp _, h₂ ▸ hp _, h₃ ▸ hp _, h₄ ▸ hp _,
        h₁ ▸ (parts x).1, h₂ ▸ (parts y).1, h₃ ▸ (parts z).1, h₄ ▸ (parts w).1⟩
    obtain ⟨a, b, c, d⟩ := (square_lcp_iff hq).mp hc
    exact ⟨by linarith only [a,b,c,d,h₁,(parts x).2],
      by linarith only [a,b,c,d,h₂,(parts y).2],
      by linarith only [a,b,c,d,h₃,(parts z).2],
      by linarith only [a,b,c,d,h₄,(parts w).2]⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    have h₂ : 0 ≤ 2*q/7 := by linarith
    have h₃ : 0 ≤ 3*q/7 := by linarith
    simp only [SquarePreimage, pos, neg_neg, max_eq_left hq, max_eq_right (neg_nonpos.mpr hq),
      max_eq_left h₂, max_eq_left h₃, max_eq_right (neg_nonpos.mpr h₂),
      max_eq_right (neg_nonpos.mpr h₃)]
    exact ⟨by ring, by ring, by ring, by ring⟩

/-- The active minor at the nonzero preimage uses rows and columns 1,2,4. -/
theorem square_active_det :
    (!![0,1,2; 1,0,-1; 3,-2,0] : Matrix (Fin 3) (Fin 3) ℝ).det = -7 := by
  rw [Matrix.det_fin_three]
  change 0*0*0 - 0*(-1)*(-2) - 1*1*0 + 1*(-1)*3 + 2*1*(-2) - 2*0*3 = (-7 : ℝ)
  norm_num

#print axioms barycentric_row
#print axioms sink_minor
#print axioms active_pair_iff
#print axioms square_lcp_iff
#print axioms square_preimage_iff
#print axioms square_active_det

end PlanarQuitIndex
