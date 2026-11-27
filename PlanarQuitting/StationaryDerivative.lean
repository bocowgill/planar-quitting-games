module

public import PlanarQuitting.LinearComplementarity
public import PlanarQuitting.Stationary
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.FunProp

/-!
# First derivative of the exact stationary payoff comparisons

At zero hazards any coalition containing at least two rival quitters has
zero mass and zero derivative. The derivative of a singleton mass is the
coordinate of that quitter. The derivative of the waiting probability is
minus the sum of the rival coordinates.
-/

@[expose] public section

namespace PlanarQuitting

open scoped BigOperators

noncomputable section

variable {n : ℕ}

private abbrev Row (n : ℕ) := Coordinates n →L[ℝ] ℝ

private def coord (j : Fin n) : Row n := ContinuousLinearMap.proj j

def prizeGapMatrix (g : Game (Fin n)) : PayoffMatrix n :=
  fun i j ↦ g.prize {j} i - g.prize {i} i

@[simp] theorem prizeGapMatrix_diag (g : Game (Fin n)) (i : Fin n) :
    prizeGapMatrix g i i = 0 := sub_self _

private theorem opponentMass_zero (i : Fin n) (A : Finset (Fin n))
    (hA : A ⊆ Finset.univ.erase i) :
    opponentMass (0 : Coordinates n) i A = if A = ∅ then 1 else 0 := by
  by_cases h : A = ∅
  · subst A
    simp [opponentMass]
  · obtain ⟨j,hj⟩ := Finset.nonempty_iff_ne_empty.mpr h
    have he : opponentMass (0 : Coordinates n) i A = 0 :=
      Finset.prod_eq_zero (hA hj) (by simp [hj])
    simp [h,he]

private def massDerivative (i : Fin n) (A : Finset (Fin n)) : Row n :=
  ∑ j ∈ Finset.univ.erase i,
    (∏ k ∈ (Finset.univ.erase i).erase j, if k ∈ A then (0 : ℝ) else 1) •
      (if j ∈ A then coord j else -(coord j))

private theorem mass_hasDeriv (i : Fin n) (A : Finset (Fin n)) :
    HasFDerivAt (fun x ↦ opponentMass x i A) (massDerivative i A) 0 := by
  have h (j : Fin n) :
      HasFDerivAt (fun x : Coordinates n ↦ if j ∈ A then x j else 1-x j)
        (if j ∈ A then coord j else -(coord j)) 0 := by
    have he := (coord j).hasFDerivAt (x := (0 : Coordinates n))
    by_cases hj : j ∈ A
    · simp only [ite_eq_left hj]
      exact he
    · simp only [ite_eq_right hj]
      exact he.const_sub (1 : ℝ)
  have hh := HasFDerivAt.finsetProd (u := Finset.univ.erase i) (fun j _ ↦ h j)
  simpa only [opponentMass, Finset.prod_apply, Pi.zero_apply, sub_zero, massDerivative] using hh

private theorem massDerivative_empty (i : Fin n) :
    massDerivative i ∅ = -(∑ j ∈ Finset.univ.erase i, coord j) := by
  simp [massDerivative, Finset.sum_neg_distrib]

private theorem massDerivative_single (i j : Fin n) (hij : j ≠ i) :
    massDerivative i {j} = coord j := by
  classical
  unfold massDerivative
  rw [Finset.sum_eq_single_of_mem j (by simp [hij])]
  · have h : (∏ k ∈ (Finset.univ.erase i).erase j,
        if k ∈ ({j} : Finset (Fin n)) then (0 : ℝ) else 1) = 1 := by
      apply Finset.prod_eq_one
      intro k hk
      simp [(Finset.mem_erase.mp hk).1]
    rw [h]
    simp
  · intro k _ hk
    have h : (∏ t ∈ (Finset.univ.erase i).erase k,
        if t ∈ ({j} : Finset (Fin n)) then (0 : ℝ) else 1) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hk.symm, by simp [hij]⟩) (by simp)
    rw [h, zero_smul]

private theorem massDerivative_multiple (i : Fin n) (A : Finset (Fin n))
    (hA : A ⊆ Finset.univ.erase i)
    (hm : ∀ j, ∃ k ∈ A, k ≠ j) :
    massDerivative i A = 0 := by
  unfold massDerivative
  apply Finset.sum_eq_zero
  intro j _
  obtain ⟨k,hk,hne⟩ := hm j
  have hz : (∏ k ∈ (Finset.univ.erase i).erase j, if k ∈ A then (0 : ℝ) else 1) = 0 :=
    Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hne,hA hk⟩) (by simp [hk])
  simp [hz]

private theorem cash_hasDeriv (g : Game (Fin n)) (i : Fin n) :
    HasFDerivAt (fun x ↦ stationaryCash g x i)
      (∑ j ∈ Finset.univ.erase i, g.prize {j} i • coord j) 0 := by
  let rival := Finset.univ.erase i
  let d (A : Finset (Fin n)) := if A = ∅ then (0 : Row n) else
    g.prize A i • massDerivative i A
  have h (A : Finset (Fin n)) :
      HasFDerivAt (fun x : Coordinates n ↦ if A = ∅ then 0 else opponentMass x i A * g.prize A i)
        (d A) 0 := by
    by_cases hA : A = ∅
    · simpa [d,hA] using hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) (0 : Coordinates n)
    · simpa [d,hA, mul_comm] using (mass_hasDeriv i A).const_mul (g.prize A i)
  have hd : (∑ A ∈ rival.powerset, d A) = ∑ j ∈ rival, g.prize {j} i • coord j := by
    let one (j : Fin n) : Finset (Fin n) := {j}
    calc
      _ = ∑ A ∈ rival.image one, d A := by
        symm
        apply Finset.sum_subset
        · intro A hA
          obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hA
          exact Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hj)
        · intro A hA ho
          by_cases he : A = ∅
          · simp [d,he]
          have hm (j : Fin n) : ∃ k ∈ A, k ≠ j := by
            by_contra! h
            obtain ⟨k,hk⟩ := Finset.nonempty_iff_ne_empty.mpr he
            have hs : A = {j} := Finset.eq_singleton_iff_unique_mem.mpr ⟨h k hk ▸ hk, h⟩
            have hj : j ∈ rival := (Finset.mem_powerset.mp hA) (by simp [hs])
            exact ho (Finset.mem_image.mpr ⟨j,hj,hs.symm⟩)
          simp [d,he,massDerivative_multiple i A (Finset.mem_powerset.mp hA) hm]
      _ = ∑ j ∈ rival, d (one j) :=
        Finset.sum_image (fun a _ b _ h ↦ Finset.singleton_inj.mp h)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        simp [d,one,massDerivative_single i j (Finset.mem_erase.mp hj).1]
  have hh := HasFDerivAt.fun_sum (u := rival.powerset) (fun A _ ↦ h A)
  rw [hd] at hh
  exact hh

private theorem stationaryQuit_at_zero (g : Game (Fin n)) (i : Fin n) :
    stationaryQuit g 0 i = g.prize {i} i := by
  unfold stationaryQuit
  rw [Finset.sum_eq_single_of_mem ∅ (Finset.empty_mem_powerset _)]
  · simp [opponentMass_zero i ∅ (Finset.empty_subset _)]
  · intro A hA hne
    simp [opponentMass_zero i A (Finset.mem_powerset.mp hA), hne]

private theorem stationaryQuit_differentiable_zero (g : Game (Fin n)) (i : Fin n) :
    DifferentiableAt ℝ (fun x ↦ stationaryQuit g x i) 0 :=
  (HasFDerivAt.fun_sum (u := (Finset.univ.erase i).powerset)
    (fun A _ ↦ (mass_hasDeriv i A).mul_const (g.prize (insert i A) i))).differentiableAt

theorem stationaryDifference_zero (g : Game (Fin n)) :
    stationaryDifference g 0 = 0 := by
  funext i
  have hcash : stationaryCash g 0 i = 0 := by
    apply Finset.sum_eq_zero
    intro A hA
    by_cases he : A = ∅ <;>
      simp [he, opponentMass_zero i A (Finset.mem_powerset.mp hA)]
  simp [stationaryDifference, hcash, opponentWait, opponentMass_zero i ∅ (Finset.empty_subset _)]

/-- The exact stationary comparison field has the singleton payoff
differences as its first derivative at unanimous continuation. -/
theorem stationaryDifference_derivative (g : Game (Fin n)) :
    HasFDerivAt (stationaryDifference g) (matrixMap (prizeGapMatrix g)) 0 := by
  apply hasFDerivAt_pi''
  intro i
  let S := ∑ j ∈ Finset.univ.erase i, coord j
  have hw : HasFDerivAt (fun x ↦ 1 - opponentWait x i) S 0 := by
    have hh := (mass_hasDeriv i ∅).const_sub 1
    simpa [opponentWait, massDerivative_empty, S] using hh
  have hD := (stationaryQuit_differentiable_zero g i).hasFDerivAt
  have hp := hw.fun_mul hD
  have hl : 1 - opponentWait (0 : Coordinates n) i = 0 := by
    simp [opponentWait, opponentMass_zero i ∅ (Finset.empty_subset _)]
  rw [stationaryQuit_at_zero g i, hl] at hp
  simp only [zero_smul, zero_add] at hp
  have h := (cash_hasDeriv g i).sub hp
  convert h using 1 <;> try rfl
  ext x
  change matrixMap (prizeGapMatrix g) x i =
    ((∑ j ∈ Finset.univ.erase i, g.prize {j} i • coord j) - g.prize {i} i • S) x
  rw [matrixMap_apply, ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  simp only [prizeGapMatrix_diag, zero_mul, add_zero, sub_apply,
    sum_apply, smul_apply, smul_eq_mul,
    S, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  change (g.prize {j} i - g.prize {i} i) * x j =
    g.prize {j} i * x j - g.prize {i} i * x j
  exact sub_mul _ _ _

theorem stationaryDifference_continuous (g : Game (Fin n)) :
    Continuous (stationaryDifference g) := by
  have mass (i : Fin n) (A : Finset (Fin n)) :
      Continuous (fun x : Coordinates n ↦ opponentMass x i A) := by
    unfold opponentMass
    apply continuous_finsetProd
    intro j _
    by_cases hj : j ∈ A
    · simp only [ite_eq_left hj]
      exact continuous_apply j
    · simp only [ite_eq_right hj]
      exact continuous_const.sub (continuous_apply j)
  apply continuous_pi
  intro i
  have hq : Continuous fun x : Coordinates n ↦ stationaryQuit g x i := by
    apply continuous_finsetSum
    exact fun A _ ↦ (mass i A).mul continuous_const
  have hh : Continuous fun x : Coordinates n ↦ 1 - opponentWait x i :=
    continuous_const.sub (mass i ∅)
  have hc : Continuous fun x : Coordinates n ↦ stationaryCash g x i := by
    apply continuous_finsetSum
    intro A _
    by_cases he : A = ∅
    · simp only [ite_eq_left he]
      exact continuous_const
    · simp only [ite_eq_right he]
      exact (mass i A).mul continuous_const
  exact hc.sub (hh.mul hq)

#print axioms stationaryDifference_zero
#print axioms stationaryDifference_derivative
#print axioms stationaryDifference_continuous

end

end PlanarQuitting
