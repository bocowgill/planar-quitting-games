module

public import PlanarQuitting.ContinuousCount
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Comparing a finite local signed count with the identity

An inner interpolation replaces a continuous map by a translated linearization
without introducing annular zeros. An outer interpolation makes that map the
identity outside a bounded set. The affine zero formulas survive both
interpolations.
-/

@[expose] public section

namespace PlanarQuitting

open Filter Set
open scoped BigOperators Topology

noncomputable section

private def radialWeight {n : ℕ} (a b : ℝ) (x : Coordinates n) : ℝ :=
  min 1 (max 0 ((‖x‖ - a) / (b-a)))

private def radialBlend {n : ℕ} (a b : ℝ)
    (f g : Coordinates n → Coordinates n) (x : Coordinates n) : Coordinates n :=
  (1 - radialWeight a b x) • f x + radialWeight a b x • g x

private theorem weight_bounds {n : ℕ} (a b : ℝ) (x : Coordinates n) :
    0 ≤ radialWeight a b x ∧ radialWeight a b x ≤ 1 :=
  ⟨le_min zero_le_one (le_max_left ..), min_le_left ..⟩

private theorem continuous_blend {n : ℕ} (a b : ℝ)
    {f g : Coordinates n → Coordinates n} (hf : Continuous f) (hg : Continuous g) :
    Continuous (radialBlend a b f g) := by
  have hw : Continuous (radialWeight (n := n) a b) :=
    continuous_const.min (continuous_const.max
      ((continuous_norm.sub continuous_const).div_const _))
  exact ((continuous_const.sub hw).smul hf).add (hw.smul hg)

private theorem blend_inner {n : ℕ} {a b : ℝ} (hab : a < b)
    (f g : Coordinates n → Coordinates n) (x : Coordinates n) (hx : ‖x‖ ≤ a) :
    radialBlend a b f g x = f x := by
  have hw : radialWeight a b x = 0 := by
    unfold radialWeight
    rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) (sub_nonneg.mpr hab.le)),
      min_eq_right zero_le_one]
  simp [radialBlend, hw]

private theorem blend_outer {n : ℕ} {a b : ℝ} (hab : a < b)
    (f g : Coordinates n → Coordinates n) (x : Coordinates n) (hx : b ≤ ‖x‖) :
    radialBlend a b f g x = g x := by
  have hv : 1 ≤ (‖x‖ - a) / (b - a) := by
    rw [le_div_iff₀ (sub_pos.mpr hab), one_mul]
    linarith
  have hw : radialWeight a b x = 1 := min_eq_left (hv.trans (le_max_right ..))
  simp [radialBlend, hw]

private theorem blend_within {n : ℕ} (a b : ℝ) (f g : Coordinates n → Coordinates n)
    (x y : Coordinates n) {e : ℝ} (hf : ‖f x - y‖ ≤ e) (hg : ‖g x - y‖ ≤ e) :
    ‖radialBlend a b f g x - y‖ ≤ e := by
  let w := radialWeight a b x
  obtain ⟨h₀, h₁⟩ := weight_bounds a b x
  have h₂ : 0 ≤ 1 - w := sub_nonneg.mpr h₁
  have hsplit : radialBlend a b f g x - y = (1-w) • (f x-y) + w • (g x-y) := by
    have hy : (1-w) • y + w • y = y := by rw [← add_smul, sub_add_cancel, one_smul]
    symm
    calc
      _ = radialBlend a b f g x - ((1-w) • y + w • y) := by
        change (1-w) • (f x-y) + w • (g x-y) =
          (1-w) • f x + w • g x - ((1-w) • y + w • y)
        simp only [smul_sub]
        abel
      _ = _ := by rw [hy]
  calc
    _ = ‖(1-w) • (f x-y) + w • (g x-y)‖ := congrArg norm hsplit
    _ ≤ ‖(1-w) • (f x-y)‖ + ‖w • (g x-y)‖ := norm_add_le _ _
    _ = (1-w) * ‖f x-y‖ + w * ‖g x-y‖ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg h₂, Real.norm_of_nonneg h₀]
    _ ≤ (1-w) * e + w * e :=
      add_le_add (mul_le_mul_of_nonneg_left hf h₂) (mul_le_mul_of_nonneg_left hg h₀)
    _ = e := by ring

/-- If the original map has no nonzero root, any sufficiently small translated
local model with finitely many locally invertible affine roots has signed count
one. The constants give explicit no-zero bounds on both interpolation annuli. -/
theorem signed_count_transfer {n : ℕ} {J : Type*} [Fintype J]
    {f m : Coordinates n → Coordinates n} (hf : Continuous f) (hm : Continuous m)
    {c r R B : ℝ} (hc : 0 < c) (hr : 0 < r) (hR : 2*r < R)
    (hBR : B < R) (lower : ∀ x, c * ‖x‖ ≤ ‖m x‖)
    (closer : ∀ x, ‖x‖ ≤ 2*r → ‖f x - m x‖ ≤ c * ‖x‖ / 2)
    (far : ∀ x, ‖f x - x‖ ≤ B) (nonzero : ∀ x, x ≠ 0 → f x ≠ 0)
    (q : Coordinates n) (hsmall : ‖q‖ < c*r/2)
    (z : J → Coordinates n) (injective : Function.Injective z)
    (exactRoots : ∀ x, m x + q = 0 ↔ ∃ j, x = z j)
    (L : J → Coordinates n ≃L[ℝ] Coordinates n) (offset : J → Coordinates n)
    (affine : ∀ j, (fun x ↦ m x + q) =ᶠ[𝓝 (z j)] fun x ↦ L j x + offset j) :
    (∑ j, (L j).toContinuousLinearMap.det / |(L j).toContinuousLinearMap.det|) = 1 := by
  let m' := fun x ↦ m x + q
  let inner := radialBlend r (2*r) m' f
  let outer := radialBlend R (R+1) inner id
  have hr₂ : r < 2*r := by linarith
  have hR₁ : R < R+1 := by linarith
  have hb : 0 ≤ B := (norm_nonneg _).trans (far 0)
  have fixed (x : Coordinates n) (hx : R+1 ≤ ‖x‖) : outer x = x :=
    blend_outer hR₁ _ _ x hx
  have inner_eq (x : Coordinates n) (hx : ‖x‖ ≤ r) : outer x = m' x := by
    rw [show outer x = inner x from blend_inner hR₁ _ _ x (by linarith)]
    exact blend_inner hr₂ _ _ x hx
  have smallRoot {x : Coordinates n} (hx : m' x = 0) : ‖x‖ < r := by
    have hneg : m x = -q := eq_neg_of_add_eq_zero_left hx
    have h := lower x
    rw [hneg, norm_neg] at h
    by_contra! hnr
    have hh := mul_le_mul_of_nonneg_left hnr hc.le
    linarith [mul_pos hc hr]
  have outerNonzero (x : Coordinates n) (hx : r < ‖x‖) : outer x ≠ 0 := by
    by_cases hi : ‖x‖ ≤ 2*r
    · rw [show outer x = inner x from blend_inner hR₁ _ _ x (hi.trans hR.le)]
      have hmBound : ‖m' x - m x‖ ≤ c * ‖x‖ / 2 := by
        change ‖m x + q - m x‖ ≤ _
        rw [add_sub_cancel_left]
        have hh := mul_le_mul_of_nonneg_left hx.le hc.le
        linarith
      have h := blend_within r (2*r) m' f x (m x) hmBound (closer x hi)
      intro hz
      rw [show radialBlend r (2*r) m' f x = 0 from hz, zero_sub, norm_neg] at h
      nlinarith [lower x, mul_pos hc (hr.trans hx)]
    · have hie : inner x = f x := blend_outer hr₂ _ _ x (le_of_not_ge hi)
      by_cases ho : ‖x‖ ≤ R
      · rw [show outer x = inner x from blend_inner hR₁ _ _ x ho, hie]
        exact nonzero x (norm_pos_iff.mp (hr.trans hx))
      · have hh : ‖outer x - x‖ ≤ B :=
          blend_within R (R+1) inner id x x (hie ▸ far x)
            (by simpa using hb)
        intro hz
        rw [hz, zero_sub, norm_neg] at hh
        exact (not_le_of_gt (hBR.trans (lt_of_not_ge ho))) hh
  have exactOuter (x : Coordinates n) : outer x = 0 ↔ ∃ j, x = z j := by
    constructor
    · intro hx
      have hrx : ‖x‖ ≤ r := le_of_not_gt (fun h ↦ outerNonzero x h hx)
      exact (exactRoots x).1 ((inner_eq x hrx).symm.trans hx)
    · rintro ⟨j, rfl⟩
      have hj := (exactRoots (z j)).2 ⟨j, rfl⟩
      exact (inner_eq _ (smallRoot hj).le).trans hj
  apply locally_affine_signed_count
    (continuous_blend _ _ (continuous_blend _ _ (hm.add continuous_const) hf) continuous_id)
    (by linarith : 0 < R+1) fixed z injective exactOuter L offset
  intro j
  have hz := smallRoot ((exactRoots (z j)).2 ⟨j, rfl⟩)
  filter_upwards [affine j, (isOpen_lt continuous_norm continuous_const).mem_nhds hz]
    with x h hx
  exact (inner_eq x (show ‖x‖ < r from hx).le).trans h

#print axioms signed_count_transfer

end

end PlanarQuitting
