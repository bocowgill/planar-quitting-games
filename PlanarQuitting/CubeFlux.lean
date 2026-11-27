module

public import Mathlib.Analysis.Calculus.DifferentialForm.VectorField
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Smooth homotopies and signed boundary integrals

Pull back a top-dimensional form under a smooth map from one additional
dimension. Its exterior derivative is zero. The divergence theorem then
equates the two time-face integrals if the form vanishes on every space face.
This is a step towards the signed zero count for the complementarity map.
-/

@[expose] public section

namespace PlanarQuitting

open MeasureTheory Set VectorField
open scoped BigOperators

noncomputable section

abbrev Coordinates (n : ℕ) := Fin n → ℝ

abbrev ScalarForm (k n : ℕ) := Coordinates n [⋀^Fin k]→L[ℝ] ℝ

def formPullback {k m n : ℕ} (f : Coordinates m → Coordinates n)
    (ω : Coordinates n → ScalarForm k n) (x : Coordinates m) : ScalarForm k m :=
  (ω (f x)).compContinuousLinearMap (fderiv ℝ f x)

def faceBasis {n : ℕ} (i : Fin (n+1)) (j : Fin n) : Coordinates (n+1) :=
  Pi.single (i.succAbove j) 1

def fluxCoefficient {n : ℕ} (η : Coordinates (n+1) → ScalarForm n (n+1))
    (i : Fin (n+1)) (x : Coordinates (n+1)) : ℝ :=
  (-1 : ℝ)^i.val * η x (faceBasis i)

private theorem closed_top_form {n : ℕ} (ω : Coordinates n → ScalarForm n n)
    (x : Coordinates n) : extDeriv ω x = 0 := by
  ext w
  change (extDeriv ω x).toAlternatingMap w = 0
  apply AlternatingMap.map_linearDependent
  intro h
  have hc := h.fintype_card_le_finrank
  simp at hc

private theorem pullback_differentiable {n : ℕ} {f : Coordinates (n+1) → Coordinates n}
    {ω : Coordinates n → ScalarForm n n} (hf : ContDiff ℝ 2 f)
    (hω : Differentiable ℝ ω) : Differentiable ℝ (formPullback f ω) := by
  intro x
  unfold formPullback
  refine DifferentiableAt.continuousAlternatingMapCompContinuousLinearMap ?_ ?_
  · exact (hω.differentiableAt.comp x (hf.differentiable (by norm_num)).differentiableAt)
  · have hfd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
    exact (hfd.differentiable (by simp)).differentiableAt

private theorem pullback_closed {n : ℕ} {f : Coordinates (n+1) → Coordinates n}
    {ω : Coordinates n → ScalarForm n n} (hf : ContDiff ℝ 2 f)
    (hω : Differentiable ℝ ω) (x : Coordinates (n+1)) : extDeriv (formPullback f ω) x = 0 := by
  unfold formPullback
  rw [extDeriv_pullback hω.differentiableAt hf.contDiffAt (by simp), closed_top_form]
  rfl

private theorem coordinateDifferentiable {n : ℕ} {η : Coordinates (n+1) → ScalarForm n (n+1)}
    (hη : Differentiable ℝ η) (i : Fin (n+1)) :
    Differentiable ℝ (fun x ↦ η x (faceBasis i)) := by
  exact (ContinuousAlternatingMap.apply ℝ (Coordinates (n+1)) ℝ
    (faceBasis i)).differentiable.comp hη

private theorem fluxDivergence {n : ℕ} {η : Coordinates (n+1) → ScalarForm n (n+1)}
    (hη : Differentiable ℝ η) (x : Coordinates (n+1)) :
    (∑ i, fderiv ℝ (fluxCoefficient η i) x (Pi.single i 1)) =
      extDeriv η x (fun i ↦ Pi.single i 1) := by
  let field (i : Fin (n+1)) : Coordinates (n+1) → Coordinates (n+1) := fun _ ↦ Pi.single i 1
  have hcomm : Pairwise fun i j : Fin (n+1) ↦ lieBracket ℝ (field i) (field j) x = 0 := by
    intro i j _
    simp [field, lieBracket]
  have hder := extDeriv_apply_vectorField_of_pairwise_commute
    (ω := η) (V := field) hη.differentiableAt (fun _ ↦ differentiableAt_const _) hcomm
  change extDeriv η x (fun i ↦ Pi.single i 1) = _ at hder
  rw [hder]
  apply Finset.sum_congr rfl
  intro i _
  have hdiff := (coordinateDifferentiable hη i).differentiableAt (x := x)
  have hfd := (hdiff.hasFDerivAt.const_smul ((-1 : ℝ)^i.val)).fderiv
  change fderiv ℝ (((-1 : ℝ)^i.val) • (fun y ↦ η y (faceBasis i))) x
      (Pi.single i 1) = _
  rw [hfd]
  simp [field, zsmul_eq_mul]
  rfl

def faceIntegral {n : ℕ} (η : Coordinates (n+1) → ScalarForm n (n+1))
    (a b : Coordinates (n+1)) (i : Fin (n+1)) (s : ℝ) : ℝ :=
  ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), fluxCoefficient η i (i.insertNth s y)

/-- The time-face fluxes of a pullback agree when the pushed-forward side
faces lie outside the form's support. -/
theorem pullback_time_faces {n : ℕ} {f : Coordinates (n+1) → Coordinates n}
    {ω : Coordinates n → ScalarForm n n} (hf : ContDiff ℝ 2 f)
    (hω : Differentiable ℝ ω) {a b : Coordinates (n+1)} (hab : a ≤ b)
    (sides : ∀ (i : Fin (n+1)), i ≠ 0 →
      ∀ y ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
        ω (f (i.insertNth (a i) y)) = 0 ∧ ω (f (i.insertNth (b i) y)) = 0) :
    faceIntegral (formPullback f ω) a b 0 (b 0) =
      faceIntegral (formPullback f ω) a b 0 (a 0) := by
  let η := formPullback f ω
  have hη : Differentiable ℝ η := pullback_differentiable hf hω
  have hzero (x : Coordinates (n+1)) :
      (∑ i, fderiv ℝ (fluxCoefficient η i) x (Pi.single i 1)) = 0 := by
    rw [fluxDivergence hη, pullback_closed hf hω]
    rfl
  have hcoeff (i : Fin (n+1)) : Differentiable ℝ (fluxCoefficient η i) := by
    unfold fluxCoefficient
    exact (coordinateDifferentiable hη i).const_mul _
  have hInt :
      IntegrableOn (fun x ↦ ∑ i, fderiv ℝ (fluxCoefficient η i) x (Pi.single i 1))
        (Icc a b) := by
    simp only [hzero]
    exact integrable_zero _ _ _
  have hDiv := integral_divergence_of_hasFDerivAt_off_countable' a b hab (fluxCoefficient η)
    (fun i x ↦ fderiv ℝ (fluxCoefficient η i) x) ∅ countable_empty
    (fun i ↦ (hcoeff i).continuous.continuousOn)
    (fun x _ i ↦ ((hcoeff i).differentiableAt (x := x)).hasFDerivAt) hInt
  change (∫ x in Icc a b, ∑ i, fderiv ℝ (fluxCoefficient η i) x (Pi.single i 1)) =
      ∑ i, (faceIntegral η a b i (b i) - faceIntegral η a b i (a i)) at hDiv
  simp only [hzero, integral_zero] at hDiv
  have hside (i : Fin (n+1)) (hi : i ≠ 0) :
      faceIntegral η a b i (b i) - faceIntegral η a b i (a i) = 0 := by
    have oneSide (s : ℝ) (hs : ∀ y ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
        ω (f (i.insertNth s y)) = 0) : faceIntegral η a b i s = 0 := by
      unfold faceIntegral
      calc
        _ = ∫ _y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), (0 : ℝ) := by
          apply setIntegral_congr_fun measurableSet_Icc
          intro y hy
          simp [fluxCoefficient, η, formPullback, hs y hy]
        _ = 0 := by simp
    rw [oneSide _ (fun y hy ↦ (sides i hi y hy).2),
      oneSide _ (fun y hy ↦ (sides i hi y hy).1), sub_self]
  rw [Finset.sum_eq_single 0 (fun i _ h ↦ hside i h) (by simp)] at hDiv
  exact sub_eq_zero.mp hDiv.symm

#print axioms pullback_time_faces

end

end PlanarQuitting
