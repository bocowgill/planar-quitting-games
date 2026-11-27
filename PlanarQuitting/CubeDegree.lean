module

public import PlanarQuitting.CubeFlux
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Invariance of the integral defining smooth degree

A smooth self-map of coordinate space agreeing with the identity on the
boundary of a box has the same integral of any top form vanishing on that
boundary as the identity. This avoids a regular-value hypothesis on the
intermediate maps of the linear homotopy.
-/

@[expose] public section

namespace PlanarQuitting

open MeasureTheory Set Function

noncomputable section

def boxBoundary {n : ℕ} (a b x : Coordinates n) : Prop :=
  x ∈ Icc a b ∧ ∃ j, x j = a j ∨ x j = b j

def topIntegral {n : ℕ} (f : Coordinates n → Coordinates n)
    (ω : Coordinates n → ScalarForm n n) (a b : Coordinates n) : ℝ :=
  ∫ x in Icc a b, formPullback f ω x (fun j ↦ Pi.single j 1)

private def spatial {n : ℕ} (x : Coordinates (n+1)) : Coordinates n :=
  fun j ↦ x j.succ

@[simp] private theorem spatial_cons {n : ℕ} (s : ℝ) (x : Coordinates n) :
    spatial (Fin.cons s x) = x := by
  funext j
  rfl

private def timeLine {n : ℕ} (g : Coordinates n → Coordinates n)
    (x : Coordinates (n+1)) : Coordinates n :=
  (1 - x 0) • spatial x + x 0 • g (spatial x)

private def liftSpatial (n : ℕ) : Coordinates n →L[ℝ] Coordinates (n+1) :=
  ContinuousLinearMap.pi (Fin.cases 0 fun j ↦ ContinuousLinearMap.proj j)

private abbrev insertCoord {n : ℕ} (i : Fin (n+1)) (s : ℝ) (x : Coordinates n) :
    Coordinates (n+1) := @Fin.insertNth n (fun _ ↦ ℝ) i s x

private theorem timeInset_deriv {n : ℕ} (s : ℝ) (x : Coordinates n) :
    HasFDerivAt (insertCoord (0 : Fin (n+1)) s) (liftSpatial n) x := by
  apply hasFDerivAt_pi'.mpr
  intro j
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · simpa [liftSpatial, Fin.insertNth_zero'] using (hasFDerivAt_const s x)
  · simpa [liftSpatial, Fin.insertNth_zero'] using
      (hasFDerivAt_apply (𝕜 := ℝ) k x)

private theorem liftBasis {n : ℕ} (j : Fin n) :
    liftSpatial n (Pi.single j 1) = faceBasis 0 j := by
  ext i
  refine Fin.cases ?_ (fun k ↦ ?_) i
  · simp [liftSpatial, faceBasis]
  · simp [liftSpatial, faceBasis, Pi.single_apply]

private theorem eval_time_face {n : ℕ} {h : Coordinates (n+1) → Coordinates n}
    (hh : Differentiable ℝ h) (ω : Coordinates n → ScalarForm n n) (s : ℝ)
    (a b : Coordinates n) (lo hi : ℝ) :
    faceIntegral (formPullback h ω) (Fin.cons lo a) (Fin.cons hi b) 0 s =
      topIntegral (h ∘ insertCoord (0 : Fin (n+1)) s) ω a b := by
  unfold faceIntegral topIntegral
  have ha : Fin.cons lo a ∘ (0 : Fin (n+1)).succAbove = a := by
    funext j
    simp
  have hb : Fin.cons hi b ∘ (0 : Fin (n+1)).succAbove = b := by
    funext j
    simp
  rw [ha, hb]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x _
  simp only [fluxCoefficient, Fin.val_zero, pow_zero, one_mul, formPullback,
    Function.comp_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  have hcomp := (hh.differentiableAt.hasFDerivAt.comp x (timeInset_deriv s x)).fderiv
  rw [hcomp]
  congr 1
  funext j
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, liftBasis]

private theorem insert_mem_box {n : ℕ} {A B : Coordinates (n+1)} (i : Fin (n+1))
    {h : ℝ} (hl : A i ≤ h) (hu : h ≤ B i) {y : Coordinates n}
    (hy : y ∈ Icc (A ∘ i.succAbove) (B ∘ i.succAbove)) : insertCoord i h y ∈ Icc A B := by
  have bounds (k : Fin (n+1)) :
      A k ≤ insertCoord i h y k ∧ insertCoord i h y k ≤ B k := by
    by_cases hk : k = i
    · simpa [hk] using And.intro hl hu
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk
      simpa using And.intro (hy.1 j) (hy.2 j)
  exact ⟨fun k ↦ (bounds k).1, fun k ↦ (bounds k).2⟩

/-- For any differential top form vanishing on the spatial boundary, a smooth
map fixing the boundary has the same integral as the identity. -/
theorem topIntegral_eq_id {n : ℕ} {a b : Coordinates n} (hab : a ≤ b)
    {f : Coordinates n → Coordinates n} (hf : ContDiff ℝ 2 f)
    (fixed : ∀ x, boxBoundary a b x → f x = x)
    {ω : Coordinates n → ScalarForm n n} (hω : Differentiable ℝ ω)
    (vanish : ∀ x, boxBoundary a b x → ω x = 0) :
    topIntegral f ω a b = topIntegral id ω a b := by
  let A : Coordinates (n+1) := Fin.cons 0 a
  let B : Coordinates (n+1) := Fin.cons 1 b
  have hAB : A ≤ B := by
    intro j
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · simp [A, B]
    · simpa [A, B] using hab k
  have hspace : ContDiff ℝ 2 (spatial : Coordinates (n+1) → Coordinates n) := by
    exact contDiff_pi.mpr (fun j ↦ contDiff_apply ℝ ℝ j.succ)
  have htime : ContDiff ℝ 2 (fun x : Coordinates (n+1) ↦ x 0) :=
    contDiff_apply ℝ ℝ 0
  have hH : ContDiff ℝ 2 (timeLine f) :=
    ((contDiff_const.sub htime).smul hspace).add (htime.smul (hf.comp hspace))
  have hfaces (i : Fin (n+1)) (hi : i ≠ 0) (y : Coordinates n)
      (hy : y ∈ Icc (A ∘ i.succAbove) (B ∘ i.succAbove)) (s : ℝ)
      (hs : s = A i ∨ s = B i) :
      ω (timeLine f (insertCoord i s y)) = 0 := by
    have hl : A i ≤ s := hs.elim (fun e ↦ e.symm.le) (fun e ↦ e ▸ hAB i)
    have hu : s ≤ B i := hs.elim (fun e ↦ e ▸ hAB i) (fun e ↦ e.le)
    have hm := insert_mem_box i hl hu hy
    have hz : boxBoundary a b (spatial (insertCoord i s y)) := by
      refine ⟨⟨fun j ↦ hm.1 j.succ, fun j ↦ hm.2 j.succ⟩, ?_⟩
      obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi
      refine ⟨j, ?_⟩
      simpa [spatial, A, B] using hs
    unfold timeLine
    rw [fixed _ hz, ← add_smul, sub_add_cancel, one_smul]
    exact vanish _ hz
  have heq := pullback_time_faces hH hω hAB
    (fun i hi y hy ↦ ⟨hfaces i hi y hy (A i) (Or.inl rfl),
      hfaces i hi y hy (B i) (Or.inr rfl)⟩)
  change faceIntegral (formPullback (timeLine f) ω) (Fin.cons 0 a) (Fin.cons 1 b) 0 1 =
    faceIntegral (formPullback (timeLine f) ω) (Fin.cons 0 a) (Fin.cons 1 b) 0 0 at heq
  rw [eval_time_face (hH.differentiable (by norm_num)),
    eval_time_face (hH.differentiable (by norm_num))] at heq
  have h1 : timeLine f ∘ insertCoord (0 : Fin (n+1)) 1 = f := by
    funext y
    simp [timeLine, Fin.insertNth_zero']
  have h0 : timeLine f ∘ insertCoord (0 : Fin (n+1)) 0 = id := by
    funext y
    simp [timeLine, Fin.insertNth_zero']
  simpa only [h1, h0] using heq

#print axioms topIntegral_eq_id

end

end PlanarQuitting
