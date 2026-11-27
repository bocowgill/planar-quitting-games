module

public import PlanarQuitting.CubeDegree
public import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.FieldSimp

/-!
# Signed contributions from affine pieces

The integral of a pulled-back top form can be computed locally if the map
is affine on disjoint open sets covering the preimage of its support. A fixed
outer boundary normalizes the sum of the signs of the local determinants to one.
-/

@[expose] public section

namespace PlanarQuitting

open MeasureTheory Set Filter
open scoped BigOperators Topology

noncomputable section

def volumeForm (n : ℕ) : ScalarForm n n :=
  { (Pi.basisFun ℝ (Fin n)).det with
    cont := (Pi.basisFun ℝ (Fin n)).continuous_toMatrix.matrix_det }

theorem volumeForm_apply_comp {n : ℕ} (L : Coordinates n →L[ℝ] Coordinates n) :
    volumeForm n (fun j ↦ L (Pi.single j 1)) = L.det := by
  have h (j : Fin n) : Pi.single j (1:ℝ) = Pi.basisFun ℝ (Fin n) j := by
    rw [Pi.basisFun_apply]
  change (Pi.basisFun ℝ (Fin n)).det (fun j ↦ L (Pi.single j 1)) = L.det
  simp only [h]
  change (Pi.basisFun ℝ (Fin n)).det (L.toLinearMap ∘ Pi.basisFun ℝ (Fin n)) = L.det
  rw [Module.Basis.det_comp, Module.Basis.det_self, mul_one]

private def weightedForm {n : ℕ} (ρ : Coordinates n → ℝ) (x : Coordinates n) :
    ScalarForm n n := ρ x • volumeForm n

private theorem topIntegral_density {n : ℕ} (f : Coordinates n → Coordinates n)
    (ρ : Coordinates n → ℝ) (a b : Coordinates n) :
    topIntegral f (weightedForm ρ) a b =
      ∫ x in Icc a b, (fderiv ℝ f x).det * ρ (f x) := by
  unfold topIntegral
  apply setIntegral_congr_fun measurableSet_Icc
  intro x _
  simp only [formPullback, weightedForm, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  rw [mul_comm]
  congr 1
  exact volumeForm_apply_comp (fderiv ℝ f x)

private theorem affine_derivative {n : ℕ} {f : Coordinates n → Coordinates n}
    {L : Coordinates n →L[ℝ] Coordinates n} {c : Coordinates n} {U : Set (Coordinates n)}
    (hU : IsOpen U) (he : EqOn f (fun x ↦ L x + c) U) {x : Coordinates n} (hx : x ∈ U) :
    HasFDerivAt f L x := by
  have hh : HasFDerivAt (fun y ↦ L y + c) L x := L.hasFDerivAt.add_const c
  have hEq : f =ᶠ[𝓝 x] (fun y ↦ L y + c) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact he hy
  exact hh.congr_of_eventuallyEq hEq

/-- For a smooth map, each affine part of the inverse image of a bump
contributes the sign of its determinant. The outer boundary fixes their sum. -/
theorem signed_count_eq_one {n : ℕ} {J : Type*} [Fintype J]
    {a b : Coordinates n} (hab : a ≤ b) {f : Coordinates n → Coordinates n}
    (hf : ContDiff ℝ 2 f) (fixed : ∀ x, boxBoundary a b x → f x = x)
    (ρ : Coordinates n → ℝ) (smoothρ : Differentiable ℝ ρ)
    (mass : (∫ x, ρ x) ≠ 0) (vanishBoundary : ∀ x, boxBoundary a b x → ρ x = 0)
    (vanishOutside : ∀ x ∉ Icc a b, ρ x = 0)
    (U : J → Set (Coordinates n)) (openU : ∀ j, IsOpen (U j))
    (disjointU : Pairwise fun j k ↦ Disjoint (U j) (U k))
    (insideU : ∀ j, U j ⊆ Icc a b)
    (L : J → Coordinates n →L[ℝ] Coordinates n) (offset : J → Coordinates n)
    (injectiveL : ∀ j, Function.Injective (L j)) (detL : ∀ j, (L j).det ≠ 0)
    (affineU : ∀ j, EqOn f (fun x ↦ L j x + offset j) (U j))
    (covers : ∀ x ∈ Icc a b, x ∉ ⋃ j, U j → ρ (f x) = 0)
    (rangeCovers : ∀ j y, y ∉ f '' (U j) → ρ y = 0) :
    (∑ j, (L j).det / |(L j).det|) = 1 := by
  classical
  have hdiff : Differentiable ℝ (weightedForm ρ) := smoothρ.smul_const _
  have hzero (x : Coordinates n) (hx : boxBoundary a b x) : weightedForm ρ x = 0 := by
    simp [weightedForm, vanishBoundary x hx]
  have hmain := topIntegral_eq_id hab hf fixed hdiff hzero
  rw [topIntegral_density, topIntegral_density] at hmain
  have hid : (∫ x in Icc a b, (fderiv ℝ (id : Coordinates n → Coordinates n) x).det *
      ρ (id x)) = ∫ x, ρ x := by
    have hdet : (ContinuousLinearMap.id ℝ (Coordinates n)).det = 1 := LinearMap.det_id
    simp only [fderiv_id, hdet, one_mul, id_eq]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero vanishOutside
  rw [hid] at hmain
  let h x := (fderiv ℝ f x).det * ρ (f x)
  have hder : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hc : Continuous h := by
    exact (ContinuousLinearMap.continuous_det.comp hder.continuous).mul
      (smoothρ.continuous.comp hf.continuous)
  have hint : IntegrableOn h (Icc a b) := hc.continuousOn.integrableOn_compact isCompact_Icc
  have hu : (⋃ j, U j) ⊆ Icc a b := iUnion_subset insideU
  have hrestrict : (∫ x in ⋃ j, U j, h x) = ∫ x in Icc a b, h x := by
    symm
    apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Icc.nullMeasurableSet hu
    filter_upwards with x hx
    exact mul_eq_zero_of_right _ (covers x hx.1 hx.2)
  have hunion : (∫ x in ⋃ j, U j, h x) = ∑ j, ∫ x in U j, h x := by
    apply integral_iUnion_fintype (fun j ↦ (openU j).measurableSet) disjointU
    exact fun j ↦ hint.mono_set (insideU j)
  have piece (j : J) : (∫ x in U j, h x) =
      ((L j).det / |(L j).det|) * ∫ x, ρ x := by
    have hd (x : Coordinates n) (hx : x ∈ U j) : HasFDerivAt f (L j) x :=
      affine_derivative (openU j) (affineU j) hx
    have hinj : InjOn f (U j) := by
      intro x hx y hy hh
      apply injectiveL j
      rw [affineU j hx, affineU j hy] at hh
      exact add_right_cancel hh
    have hjac := integral_image_eq_integral_abs_det_fderiv_smul volume
      (openU j).measurableSet (fun x hx ↦ (hd x hx).hasFDerivWithinAt) hinj ρ
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (rangeCovers j)] at hjac
    have hjac' : (∫ x, ρ x) = |(L j).det| * ∫ x in U j, ρ (f x) := by
      simpa only [smul_eq_mul, integral_const_mul] using hjac
    calc
      _ = ∫ x in U j, (L j).det * ρ (f x) := by
        apply setIntegral_congr_fun (openU j).measurableSet
        intro x hx
        unfold h
        rw [(hd x hx).fderiv]
      _ = _ := by
        rw [integral_const_mul, hjac']
        field_simp [abs_ne_zero.mpr (detL j)]
  have hmul : (∑ j, (L j).det / |(L j).det|) * (∫ x, ρ x) = 1 * (∫ x, ρ x) := by
    calc
      _ = ∑ j, ((L j).det / |(L j).det|) * ∫ x, ρ x := by rw [Finset.sum_mul]
      _ = ∑ j, ∫ x in U j, h x := Finset.sum_congr rfl (fun j _ ↦ (piece j).symm)
      _ = ∫ x in ⋃ j, U j, h x := hunion.symm
      _ = ∫ x in Icc a b, h x := hrestrict
      _ = _ := by simpa only [h, one_mul] using hmain
  exact mul_right_cancel₀ mass hmul

#print axioms signed_count_eq_one

end

end PlanarQuitting
