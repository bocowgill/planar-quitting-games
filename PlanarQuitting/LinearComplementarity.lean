module

public import PlanarQuitting.ProjectedComparison
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Tactic.Linarith

/-!
# Local affine roots of the linear comparison problem

The complementarity roots can be represented by their nonnegative weights.
At a strictly complementary root, the sign pattern is constant on an open
neighborhood. The active columns are then the columns of the comparison
matrix. All other columns are those of the identity.
-/

@[expose] public section

namespace PlanarQuitting

open Filter Set
open scoped BigOperators Topology Matrix

noncomputable section

variable {n : ℕ}

abbrev PayoffMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def matrixMap (M : PayoffMatrix n) : Coordinates n →L[ℝ] Coordinates n :=
  (Matrix.toLin' M).toContinuousLinearMap

def AffineComplementary (M : PayoffMatrix n) (q t : Coordinates n) : Prop :=
  ∀ i, 0 ≤ t i ∧ 0 ≤ (q + matrixMap M t) i ∧
    t i * (q + matrixMap M t) i = 0

def signedRoot (M : PayoffMatrix n) (q t : Coordinates n) : Coordinates n :=
  t - (q + matrixMap M t)

theorem matrixMap_apply (M : PayoffMatrix n) (t : Coordinates n) (i : Fin n) :
    matrixMap M t i = ∑ j, M i j * t j := rfl

/-- The zero equation recovers exactly a nonnegative complementary split. -/
theorem complementary_of_normal_zero (M : PayoffMatrix n) (q x : Coordinates n)
    (h : normalMap (matrixMap M) x + q = 0) :
    AffineComplementary M q (positivePart x) ∧
      signedRoot M q (positivePart x) = x := by
  have he : x = positivePart x - (q + matrixMap M (positivePart x)) := by
    rw [← sub_eq_zero]
    change x - positivePart x + matrixMap M (positivePart x) + q = 0 at h
    convert h using 1
    abel
  refine ⟨fun i ↦ ⟨le_max_left .., ?_, ?_⟩, he.symm⟩
  all_goals
    have hi := congrFun he i
    change x i = max 0 (x i) - (q + matrixMap M (positivePart x)) i at hi
    by_cases hp : 0 ≤ x i
    · rw [max_eq_right hp] at hi
      have hz : (q + matrixMap M (positivePart x)) i = 0 := by linarith
      simp [hz]
    · have hp' := (le_of_not_ge hp)
      rw [max_eq_left hp'] at hi
      first
      | linarith
      | change max 0 (x i) * (q + matrixMap M (positivePart x)) i = 0
        rw [max_eq_left hp', zero_mul]

theorem normal_zero_of_complementary (M : PayoffMatrix n) (q t : Coordinates n)
    (h : AffineComplementary M q t) :
    positivePart (signedRoot M q t) = t ∧ normalMap (matrixMap M) (signedRoot M q t) + q = 0 := by
  have hp : positivePart (signedRoot M q t) = t := by
    funext i
    change max 0 (t i - (q + matrixMap M t) i) = t i
    rcases mul_eq_zero.mp (h i).2.2 with ht | hs
    · rw [ht, zero_sub, max_eq_left (neg_nonpos.mpr (h i).2.1)]
    · rw [hs, sub_zero, max_eq_right (h i).1]
  refine ⟨hp, ?_⟩
  rw [normalMap, hp, signedRoot]
  abel

def activeMatrix (M : PayoffMatrix n) (A : Finset (Fin n)) : PayoffMatrix n :=
  fun i j ↦ if j ∈ A then M i j else if i = j then 1 else 0

@[simp] theorem activeMatrix_empty (M : PayoffMatrix n) : activeMatrix M ∅ = 1 := by
  ext i j
  simp [activeMatrix, Matrix.one_apply]

theorem det_active_pair (M : PayoffMatrix n) {i j : Fin n} (hne : i ≠ j)
    (hi : M i i = 0) (hj : M j j = 0) :
    (activeMatrix M {i,j}).det = -(M j i * M i j) := by
  classical
  let A := activeMatrix M {i,j}
  rw [show activeMatrix M {i,j} = A from rfl, Matrix.det_apply', Finset.sum_eq_single (Equiv.swap i j)]
  · have factors (k : Fin n) :
        A (Equiv.swap i j k) k = (if k = i then M j i else if k = j then M i j else 1) := by
      by_cases hki : k = i
      · simp [hki, A, activeMatrix]
      by_cases hkj : k = j
      · simp [hkj, A, activeMatrix, hne.symm]
      simp [A, activeMatrix, hki, hkj, Equiv.swap_apply_of_ne_of_ne hki hkj]
    let f (k : Fin n) := if k = i then M j i else if k = j then M i j else 1
    have prod' : (∏ k, A (Equiv.swap i j k) k) = ∏ k, f k :=
      Finset.prod_congr rfl (fun k _ ↦ factors k)
    have h : (∏ k ∈ (Finset.univ.erase i).erase j,
        f k) = 1 := by
      apply Finset.prod_eq_one
      intro k hk
      simp [f, (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1, (Finset.mem_erase.mp hk).1]
    have prod_f : (∏ k, f k) = M j i * M i j := by
      rw [← Finset.prod_erase_mul Finset.univ f (Finset.mem_univ i)]
      rw [← Finset.prod_erase_mul (Finset.univ.erase i) f
        (by simp [hne.symm] : j ∈ Finset.univ.erase i), h]
      simp [f, hne.symm, mul_comm]
    rw [prod', prod_f, Equiv.Perm.sign_swap hne]
    simp
  · intro σ _ hσ
    have hzero : ∃ k, A (σ k) k = 0 := by
      by_contra! hnonzero
      have fixed (k : Fin n) (hki : k ≠ i) (hkj : k ≠ j) : σ k = k := by
        by_contra hk
        exact hnonzero k (by simp [A, activeMatrix, hki, hkj, hk])
      have hsi : σ i = j := by
        have nei : σ i ≠ i := by
          intro h
          exact hnonzero i (by simp [h, A, activeMatrix, hi])
        by_contra nej
        exact nei (σ.injective (fixed (σ i) nei nej))
      have hsj : σ j = i := by
        have nej : σ j ≠ j := by
          intro h
          exact hnonzero j (by simp [h, A, activeMatrix, hj])
        by_contra nei
        exact nej (σ.injective (fixed (σ j) nei nej))
      apply hσ
      apply Equiv.ext
      intro k
      by_cases hki : k = i
      · simpa [hki] using hsi
      by_cases hkj : k = j
      · simpa [hkj] using hsj
      rw [fixed k hki hkj, Equiv.swap_apply_of_ne_of_ne hki hkj]
    obtain ⟨k, hk⟩ := hzero
    have he : (∏ l, A (σ l) l) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ k) hk
    rw [he, mul_zero]
  · simp

def matrixEquiv (M : PayoffMatrix n) (hM : M.det ≠ 0) : Coordinates n ≃L[ℝ] Coordinates n :=
  (LinearEquiv.ofInjectiveEndo (Matrix.toLin' M)
    (by
      intro x y h
      exact M.mulVec_injective_of_det_ne_zero hM h)).toContinuousLinearEquiv

theorem matrixEquiv_apply (M : PayoffMatrix n) (hM : M.det ≠ 0) (x : Coordinates n) :
    matrixEquiv M hM x = matrixMap M x := rfl

theorem matrixEquiv_det (M : PayoffMatrix n) (hM : M.det ≠ 0) :
    (matrixEquiv M hM).toContinuousLinearMap.det = M.det := LinearMap.det_toLin' M

/-- The normal map agrees near a strict root with the affine formula whose
linear part consists of active comparison columns and inactive identity columns. -/
theorem normal_affine_near (M : PayoffMatrix n) (q z : Coordinates n)
    (A : Finset (Fin n)) (pos : ∀ j ∈ A, 0 < z j) (neg : ∀ j ∉ A, z j < 0) :
    (fun x ↦ normalMap (matrixMap M) x + q) =ᶠ[𝓝 z]
      fun x ↦ matrixMap (activeMatrix M A) x + q := by
  have hsign (j : Fin n) : ∀ᶠ x in 𝓝 z, if j ∈ A then 0 < x j else x j < 0 := by
    by_cases hj : j ∈ A
    · have h : {x : Coordinates n | 0 < x j} ∈ 𝓝 z :=
        (isOpen_lt continuous_const (continuous_apply j)).mem_nhds (pos j hj)
      filter_upwards [h] with x hx
      exact if_pos hj ▸ hx
    · have h : {x : Coordinates n | x j < 0} ∈ 𝓝 z :=
        (isOpen_lt (continuous_apply j) continuous_const).mem_nhds (neg j hj)
      filter_upwards [h] with x hx
      exact if_neg hj ▸ hx
  filter_upwards [eventually_all.mpr hsign] with x hx
  have hp (j : Fin n) : positivePart x j = if j ∈ A then x j else 0 := by
    have h := hx j
    by_cases hj : j ∈ A
    · simp only [if_pos hj] at h ⊢
      exact max_eq_right h.le
    · simp only [if_neg hj] at h ⊢
      exact max_eq_left h.le
  funext i
  change x i - positivePart x i + matrixMap M (positivePart x) i + q i =
    matrixMap (activeMatrix M A) x i + q i
  rw [matrixMap_apply, matrixMap_apply]
  congr 1
  have split (j : Fin n) : activeMatrix M A i j * x j =
      M i j * positivePart x j + (if i = j then x i - positivePart x i else 0) := by
    by_cases hj : j ∈ A
    · by_cases hij : i = j
      · subst j
        simp [activeMatrix, hj, hp]
      · simp [activeMatrix, hj, hp, hij]
    · by_cases hij : i = j
      · subst j
        simp [activeMatrix, hj, hp]
      · simp [activeMatrix, hj, hp, hij]
  simp_rw [split]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos (Finset.mem_univ i)]
  abel

#print axioms complementary_of_normal_zero
#print axioms normal_zero_of_complementary
#print axioms det_active_pair
#print axioms normal_affine_near

end

end PlanarQuitting
