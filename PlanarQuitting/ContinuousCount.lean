module

public import PlanarQuitting.SignedCount
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Topology.Order.Compact

/-!
# Signed counts for continuous maps with affine zero neighborhoods

Keep the map fixed on the local affine pieces and on the boundary while
smoothing it elsewhere. Compactness bounds its norm away from zero off the
affine pieces. A normalized bump supported in a small ball detects precisely
those pieces.
-/

@[expose] public section

namespace PlanarQuitting

open MeasureTheory Set Filter
open scoped BigOperators Topology

noncomputable section

private theorem norm_gap {n : ℕ} {S : Set (Coordinates n)}
    (compact : IsCompact S) {f : Coordinates n → Coordinates n}
    (hf : Continuous f) (nonzero : ∀ x ∈ S, f x ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ S, δ ≤ ‖f x‖ := by
  by_cases h : S.Nonempty
  · obtain ⟨x, hx, hmin⟩ := compact.exists_isMinOn h hf.norm.continuousOn
    exact ⟨‖f x‖, norm_pos_iff.mpr (nonzero x hx), fun y hy ↦ hmin hy⟩
  · exact ⟨1, one_pos, fun x hx ↦ (h ⟨x, hx⟩).elim⟩

/-- The signed count for a continuous map equal to the identity on the boundary.
The closed set of points to be preserved by smoothing contains the boundary
and every local affine patch, and the original map is smooth on a neighborhood
of that closed set. -/
theorem continuous_signed_count_eq_one {n : ℕ} {J : Type*} [Fintype J]
    {a b : Coordinates n} (center : ∀ j, a j < 0 ∧ 0 < b j)
    {f : Coordinates n → Coordinates n} (hf : Continuous f)
    (fixed : ∀ x, boxBoundary a b x → f x = x)
    (U : J → Set (Coordinates n)) (openU : ∀ j, IsOpen (U j))
    (disjointU : Pairwise fun j k ↦ Disjoint (U j) (U k))
    (insideU : ∀ j, U j ⊆ Icc a b)
    (L : J → Coordinates n ≃L[ℝ] Coordinates n) (offset : J → Coordinates n)
    (affineU : ∀ j, EqOn f (fun x ↦ L j x + offset j) (U j))
    (roots : ∀ j, (0 : Coordinates n) ∈ f '' (U j))
    (no_other_roots : ∀ x ∈ Icc a b, x ∉ ⋃ j, U j → f x ≠ 0)
    {S V : Set (Coordinates n)} (closedS : IsClosed S)
    (S_nhds : V ∈ 𝓝ˢ S) (fSmooth : ContDiffOn ℝ 2 f V)
    (containsBoundary : ∀ x, boxBoundary a b x → x ∈ S)
    (containsAffine : ∀ j, U j ⊆ S) :
    (∑ j, (L j).toContinuousLinearMap.det / |(L j).toContinuousLinearMap.det|) = 1 := by
  classical
  have hb : a ≤ b := fun j ↦ (center j).1.le.trans (center j).2.le
  obtain ⟨δ, hδ, hgap⟩ := norm_gap
    (isCompact_Icc.diff (isOpen_iUnion openU)) hf
    (fun x hx ↦ no_other_roots x hx.1 hx.2)
  obtain ⟨g, hg, hdist, hkeep, _⟩ :=
    hf.exists_contDiff_approx_and_eqOn 2 continuous_const
      (fun _ ↦ half_pos hδ) closedS S_nhds fSmooth
  have ha (j : J) : EqOn g (fun x ↦ L j x + offset j) (U j) := by
    intro x hx
    exact (hkeep (containsAffine j hx)).trans (affineU j hx)
  have hg_image (j : J) : g '' U j = f '' U j := by
    apply Set.EqOn.image_eq
    exact fun x hx ↦ hkeep (containsAffine j hx)
  have hOpenImage (j : J) : IsOpen (g '' U j) := by
    rw [(ha j).image_eq]
    let hom := (L j).toHomeomorph.trans (Homeomorph.addRight (offset j))
    change IsOpen ((⇑hom) '' U j)
    exact hom.isOpenMap _ (openU j)
  let interiorBox := Set.pi Set.univ (fun j ↦ Ioo (a j) (b j))
  let target := (interiorBox ∩ ⋂ j, g '' U j) ∩ Metric.ball 0 (δ/2)
  have ho : IsOpen target := by
    apply IsOpen.inter _ Metric.isOpen_ball
    apply IsOpen.inter
    · exact isOpen_set_pi finite_univ (fun j _ ↦ isOpen_Ioo)
    · exact isOpen_iInter_of_finite hOpenImage
  have hz : (0 : Coordinates n) ∈ target := by
    refine ⟨⟨fun j _ ↦ center j, ?_⟩, Metric.mem_ball_self (half_pos hδ)⟩
    exact mem_iInter.mpr fun j ↦ (hg_image j).symm ▸ roots j
  obtain ⟨r, hr, htarget⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds hz)
  let bump : ContDiffBump (0 : Coordinates n) := ⟨r/2, r, half_pos hr, half_lt_self hr⟩
  let ρ := bump.normed volume
  have hm : (∫ x, ρ x) ≠ 0 := by
    change (∫ x, bump.normed volume x) ≠ 0
    rw [bump.integral_normed]
    exact one_ne_zero
  have hρ : Differentiable ℝ ρ := (bump.contDiff_normed (n := 1)).differentiable (by simp)
  have loc (x : Coordinates n) (hx : ρ x ≠ 0) : x ∈ target := by
    apply htarget
    change x ∈ Function.support ρ at hx
    rw [show Function.support ρ = Metric.ball 0 r from bump.support_normed_eq] at hx
    exact hx
  have hzBoundary (x : Coordinates n) (hx : boxBoundary a b x) : ρ x = 0 := by
    by_contra h
    have ht := (loc x h).1.1
    obtain ⟨j, e | e⟩ := hx.2
    · exact (lt_irrefl _) (e ▸ (ht j (mem_univ j)).1)
    · exact (lt_irrefl _) (e ▸ (ht j (mem_univ j)).2)
  have hzOutside (x : Coordinates n) (hx : x ∉ Icc a b) : ρ x = 0 := by
    by_contra h
    have hh := (loc x h).1.1
    exact hx ⟨fun j ↦ (hh j (mem_univ j)).1.le, fun j ↦ (hh j (mem_univ j)).2.le⟩
  have hzComplement (x : Coordinates n) (hx : x ∈ Icc a b) (hn : x ∉ ⋃ j, U j) :
      ρ (g x) = 0 := by
    by_contra h
    have hl : ‖g x‖ < δ/2 := by
      simpa only [Metric.mem_ball, dist_zero_right] using (loc (g x) h).2
    have hd : ‖f x‖ ≤ dist (g x) (f x) + ‖g x‖ := by
      rw [← dist_zero_right, ← dist_zero_right (g x), dist_comm (g x) (f x)]
      exact dist_triangle _ _ _
    have hh := hgap x ⟨hx, hn⟩
    linarith only [hd, hh, hdist x, hl]
  have rangez (j : J) (x : Coordinates n) (hx : x ∉ g '' U j) : ρ x = 0 := by
    by_contra h
    exact hx (mem_iInter.mp (loc x h).1.2 j)
  exact signed_count_eq_one hb hg (fun x hx ↦
    (hkeep (containsBoundary x hx)).trans (fixed x hx)) ρ hρ hm
    hzBoundary hzOutside U openU disjointU insideU (fun j ↦ (L j).toContinuousLinearMap)
    offset (fun j ↦ (L j).injective) (fun j ↦ (L j).toLinearEquiv.isUnit_det'.ne_zero)
    ha hzComplement rangez

#print axioms continuous_signed_count_eq_one

/-- It suffices that the finite roots have locally invertible affine formulas
and that the map equals the identity outside a bounded set. -/
theorem locally_affine_signed_count {n : ℕ} {J : Type*} [Fintype J]
    {f : Coordinates n → Coordinates n} (hf : Continuous f)
    {R : ℝ} (hR : 0 < R) (exterior : ∀ x, R ≤ ‖x‖ → f x = x)
    (z : J → Coordinates n) (injective : Function.Injective z)
    (exactRoots : ∀ x, f x = 0 ↔ ∃ j, x = z j)
    (L : J → Coordinates n ≃L[ℝ] Coordinates n) (offset : J → Coordinates n)
    (affine : ∀ j, f =ᶠ[𝓝 (z j)] fun x ↦ L j x + offset j) :
    (∑ j, (L j).toContinuousLinearMap.det / |(L j).toContinuousLinearMap.det|) = 1 := by
  classical
  let a : Coordinates n := fun _ ↦ -(R + 2)
  let b : Coordinates n := fun _ ↦ R + 2
  have rootNorm (j : J) : ‖z j‖ < R := by
    by_contra! h
    have e := (exterior _ h).symm.trans ((exactRoots _).2 ⟨j, rfl⟩)
    simp [e, hR.not_ge] at h
  obtain ⟨W, hW, hdis⟩ := (Set.finite_range z).t2_separation
  have mainNhds (j : J) :
      (W (z j) ∩ {x | ‖x‖ < R + 1}) ∩ {x | f x = L j x + offset j} ∈ 𝓝 (z j) :=
    inter_mem (inter_mem ((hW _).2.mem_nhds (hW _).1)
      ((isOpen_lt continuous_norm continuous_const).mem_nhds (by
        change ‖z j‖ < R + 1
        linarith [rootNorm j]))) (affine j)
  choose radius hpos hball using fun j ↦ Metric.mem_nhds_iff.mp (mainNhds j)
  let U (j : J) := Metric.ball (z j) (radius j / 2)
  let C (j : J) := Metric.closedBall (z j) (radius j / 2)
  let S := {x : Coordinates n | R + 2 ≤ ‖x‖} ∪ ⋃ j, C j
  let V := {x : Coordinates n | R < ‖x‖} ∪ ⋃ j, Metric.ball (z j) (radius j)
  have hU (j : J) : U j ⊆ Metric.ball (z j) (radius j) :=
    Metric.ball_subset_ball (by linarith [hpos j])
  have hcV (j : J) : C j ⊆ Metric.ball (z j) (radius j) :=
    Metric.closedBall_subset_ball (half_lt_self (hpos j))
  have hS : IsClosed S :=
    (isClosed_le continuous_const continuous_norm).union
      (isClosed_iUnion_of_finite fun _ ↦ Metric.isClosed_closedBall)
  have hV : IsOpen V :=
    (isOpen_lt continuous_const continuous_norm).union
      (isOpen_iUnion fun _ ↦ Metric.isOpen_ball)
  have hSV : S ⊆ V := by
    rintro x (hx | hx)
    · exact Or.inl (by change R + 2 ≤ ‖x‖ at hx; show R < ‖x‖; linarith)
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      exact Or.inr (mem_iUnion.mpr ⟨j, hcV j hj⟩)
  have smoothV : ContDiffOn ℝ 2 f V := by
    intro x hx
    apply ContDiffAt.contDiffWithinAt
    rcases hx with hx | hx
    · apply (contDiff_id.contDiffAt (x := x)).congr_of_eventuallyEq
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
      exact exterior y (show R < ‖y‖ from hy).le
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      apply (((L j).toContinuousLinearMap.contDiff.add contDiff_const).contDiffAt
        (x := x)).congr_of_eventuallyEq
      filter_upwards [Metric.isOpen_ball.mem_nhds hj] with y hy
      exact (hball j hy).2
  have boundaryNorm (x : Coordinates n) (hx : boxBoundary a b x) : R + 2 ≤ ‖x‖ := by
    obtain ⟨i, hi | hi⟩ := hx.2
    · have e : x i = -(R + 2) := hi
      exact le_trans (by rw [e, norm_neg, Real.norm_eq_abs, abs_of_pos (by linarith)])
        (norm_le_pi_norm x i)
    · have e : x i = R + 2 := hi
      exact le_trans (by rw [e, Real.norm_eq_abs, abs_of_pos (by linarith)])
        (norm_le_pi_norm x i)
  refine continuous_signed_count_eq_one (a := a) (b := b)
    (fun j ↦ ⟨by change -(R + 2) < 0; linarith, by change 0 < R + 2; linarith⟩)
    hf (fun x hx ↦ exterior x (by linarith [boundaryNorm x hx]))
    U (fun _ ↦ Metric.isOpen_ball) ?_ ?_ L offset
    (fun j x hx ↦ (hball j (hU j hx)).2) ?_ ?_ hS (hV.mem_nhdsSet.mpr hSV)
    smoothV (fun x hx ↦ Or.inl (boundaryNorm x hx)) ?_
  · intro j k h
    exact (hdis (mem_range_self j) (mem_range_self k) (injective.ne h)).mono
      (fun _ hx ↦ (hball j (hU j hx)).1.1)
      (fun _ hx ↦ (hball k (hU k hx)).1.1)
  · intro j x hx
    have hn : ‖x‖ < R + 1 := (hball j (hU j hx)).1.2
    have hi (i : Fin n) : |x i| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm x i
    refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩
    · change -(R + 2) ≤ x i
      linarith [hi i, neg_abs_le (x i)]
    · change x i ≤ R + 2
      linarith [hi i, le_abs_self (x i)]
  · exact fun j ↦ ⟨z j, Metric.mem_ball_self (half_pos (hpos j)),
      (exactRoots _).2 ⟨j, rfl⟩⟩
  · intro x _ hn hz
    obtain ⟨j, rfl⟩ := (exactRoots x).1 hz
    exact hn (mem_iUnion.mpr ⟨j, Metric.mem_ball_self (half_pos (hpos j))⟩)
  · exact fun j x hx ↦ Or.inr (mem_iUnion.mpr ⟨j, Metric.ball_subset_closedBall hx⟩)

#print axioms locally_affine_signed_count

end

end PlanarQuitting
