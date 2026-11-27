module

public import PlanarQuitting.Geometry
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Complementarity solutions on planar payoff faces

The homogeneous problem has no nonzero solution if none of the sites is
feasible. At an offset represented by a strictly feasible point, each nonzero
solution has exactly two positive coordinates, and these two faces form a sink.
Conversely each sink supplies such a solution.
-/

@[expose] public section

namespace PlanarQuitting

open scoped BigOperators

noncomputable section

variable {I E : Type*} [Fintype I] [AddCommGroup E] [Module ℝ E]

variable (F : Faces I E)

def Faces.cross (i j : I) : ℝ := F.slack i (F.site j)

omit [Fintype I] in
@[simp] theorem Faces.cross_self (i : I) : F.cross i i = 0 := F.slack_site i

def Faces.slackVector (q t : I → ℝ) (i : I) : ℝ :=
  q i + ∑ j, t j * F.cross i j

def Faces.Complementary (q t : I → ℝ) : Prop :=
  ∀ i, 0 ≤ t i ∧ 0 ≤ F.slackVector q t i ∧ t i * F.slackVector q t i = 0

def Faces.SinkPair (i j : I) : Prop :=
  i ≠ j ∧ ∃ z, F.Feasible z ∧ F.slack i z = 0 ∧ F.slack j z = 0 ∧
    F.cross j i < 0 ∧ F.cross i j < 0

theorem Faces.affine_sum (m : ℝ) (z x : E) (t : I → ℝ)
    (h : (m + ∑ j, t j) • z = m • x + ∑ j, t j • F.site j) (i : I) :
    (m + ∑ j, t j) * F.slack i z =
      m * F.slack i x + ∑ j, t j * F.cross i j := by
  have hs := congrArg (F.row i) h
  simp only [map_smul, map_add, map_sum, smul_eq_mul] at hs
  simp only [Faces.slack, Faces.cross, map_sub, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul]
  linarith only [hs]

private def center (m : ℝ) (x : E) (t : I → ℝ) : E :=
  (m + ∑ j, t j)⁻¹ • (m • x + ∑ j, t j • F.site j)

private theorem center_slack {m : ℝ} (x : E) (t : I → ℝ) (hm : m + ∑ j, t j ≠ 0)
    (i : I) :
    (m + ∑ j, t j) * F.slack i (center F m x t) =
      m * F.slack i x + ∑ j, t j * F.cross i j := by
  apply F.affine_sum
  rw [center, smul_smul, mul_inv_cancel₀ hm, one_smul]

private theorem weighted_support (t : I → ℝ) (hn : ∀ j, 0 ≤ t j) (h : ¬ t = 0) :
    ∃ i, 0 < t i := by
  by_contra! h0
  apply h
  funext i
  exact le_antisymm (h0 i) (hn i)

private theorem binding_of_positive {q t : I → ℝ} (hc : F.Complementary q t)
    {z : E} {m : ℝ} (hm : 0 < m) (hb : ∀ i, m * F.slack i z = F.slackVector q t i)
    (i : I) (hi : 0 < t i) : F.slack i z = 0 := by
  have hv := (mul_eq_zero.mp (hc i).2.2).resolve_left hi.ne'
  have he := (hb i).trans hv
  exact (mul_eq_zero.mp he).resolve_left hm.ne'

private theorem feasible_of_barycentric {q t : I → ℝ} (hc : F.Complementary q t)
    {z : E} {m : ℝ} (hm : 0 < m) (hb : ∀ i, m * F.slack i z = F.slackVector q t i) :
    F.Feasible z := by
  intro i
  by_contra! h
  have hm' := mul_neg_of_pos_of_neg hm h
  rw [hb i] at hm'
  exact (not_lt_of_ge (hc i).2.1) hm'

private theorem support_pair {q t : I → ℝ} (hc : F.Complementary q t)
    (hreg : RegularFaces F) {z : E} {m : ℝ} (hm : 0 < m)
    (hb : ∀ i, m * F.slack i z = F.slackVector q t i)
    (i j : I) (hn : i ≠ j) (hi : 0 < t i) (hj : 0 < t j) :
    ∀ k, k ≠ i → k ≠ j → t k = 0 := by
  intro k hki hkj
  by_contra ht
  have hpos := lt_of_le_of_ne (hc k).1 (Ne.symm ht)
  rcases hreg.no_third z i j k hn (binding_of_positive F hc hm hb i hi)
      (binding_of_positive F hc hm hb j hj) (binding_of_positive F hc hm hb k hpos) with H | H
  · exact hki H
  · exact hkj H

private theorem row_sum_pair (t : I → ℝ) (i j : I)
    (hz : ∀ k, k ≠ i → k ≠ j → t k = 0) :
    (∑ k, t k * F.cross i k) = t j * F.cross i j := by
  classical
  apply Finset.sum_eq_single j
  · intro k _ hk
    by_cases hi : k = i
    · simp [hi]
    · rw [hz k hi hk, zero_mul]
  · simp

/-- A strictly positive homogeneous solution would put a solo prize inside the
feasible region or require a site on another player's line. -/
theorem Faces.homogeneous_zero (hreg : RegularFaces F)
    (infeasible : ∀ i, ¬ F.Feasible (F.site i)) {t : I → ℝ}
    (hc : F.Complementary (fun _ ↦ 0) t) : t = 0 := by
  classical
  by_contra hne
  have hn (j : I) := (hc j).1
  obtain ⟨i, hi⟩ := weighted_support t hn hne
  let m : ℝ := ∑ j, t j
  have hm : 0 < m := Finset.sum_pos' (fun j _ ↦ hn j) ⟨i, Finset.mem_univ i, hi⟩
  let z := center F 0 (F.site i) t
  have hb (k : I) : m * F.slack k z = F.slackVector (fun _ ↦ 0) t k := by
    simpa [m, z, Faces.slackVector] using
      (center_slack F (m := 0) (F.site i) t (by simpa using hm.ne') k)
  by_cases htwo : ∃ j, j ≠ i ∧ 0 < t j
  · obtain ⟨j, hji, hj⟩ := htwo
    have hz := support_pair F hc hreg hm hb i j hji.symm hi hj
    have bind := binding_of_positive F hc hm hb i hi
    have hs := hb i
    rw [bind, mul_zero, Faces.slackVector, zero_add, row_sum_pair F t i j hz] at hs
    exact (mul_ne_zero hj.ne' (hreg.site_off i j hji.symm)) hs.symm
  · have hz (j : I) (hj : j ≠ i) : t j = 0 :=
      le_antisymm (le_of_not_gt fun hp ↦ htwo ⟨j, hj, hp⟩) (hn j)
    have hmass : m = t i := by
      apply Finset.sum_eq_single i
      · intro j _ hj
        exact hz j hj
      · simp
    have hvec : (∑ j, t j • F.site j) = t i • F.site i := by
      apply Finset.sum_eq_single i
      · intro j _ hj
        rw [hz j hj, zero_smul]
      · simp
    have he : z = F.site i := by
      simp only [z, center, zero_add, zero_smul, hvec, smul_smul]
      change (m⁻¹ * t i) • F.site i = F.site i
      rw [hmass, inv_mul_cancel₀ hi.ne', one_smul]
    exact infeasible i (he ▸ feasible_of_barycentric F hc hm hb)

/-- A nonzero solution at a strictly feasible offset determines a sink.
Any coordinate outside that pair has zero activity and strict dual slack. -/
theorem Faces.offset_support (hreg : RegularFaces F) (x : E)
    (hstrict : ∀ i, 0 < F.slack i x) {t : I → ℝ}
    (hc : F.Complementary (fun i ↦ F.slack i x) t) (hne : t ≠ 0) :
    ∃ i j, F.SinkPair i j ∧ 0 < t i ∧ 0 < t j ∧
      (∀ k, k ≠ i → k ≠ j → t k = 0 ∧ 0 < F.slackVector (fun i ↦ F.slack i x) t k) := by
  classical
  have hn (j : I) := (hc j).1
  obtain ⟨i, hi⟩ := weighted_support t hn hne
  let m : ℝ := 1 + ∑ j, t j
  have hm : 0 < m := by
    dsimp [m]
    exact add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg (fun j _ ↦ hn j))
  let z := center F 1 x t
  have hb (k : I) : m * F.slack k z = F.slackVector (fun i ↦ F.slack i x) t k := by
    simpa [m, z, Faces.slackVector] using
      (center_slack F (m := 1) x t hm.ne' k)
  have hbind := binding_of_positive F hc hm hb i hi
  have hex : ∃ j, j ≠ i ∧ 0 < t j := by
    by_contra! ha
    have hsum : ∑ j, t j * F.cross i j = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      by_cases hj : j = i
      · simp [hj]
      · have hz := le_antisymm (ha j hj) (hn j)
        rw [hz, zero_mul]
    have hs := hb i
    rw [hbind, mul_zero, Faces.slackVector, hsum, add_zero] at hs
    exact (hstrict i).ne' hs.symm
  obtain ⟨j, hji, hj⟩ := hex
  have hbind' := binding_of_positive F hc hm hb j hj
  have hz := support_pair F hc hreg hm hb i j hji.symm hi hj
  have hirow := hb i
  have hjrow := hb j
  rw [hbind, mul_zero, Faces.slackVector, row_sum_pair F t i j hz] at hirow
  rw [hbind', mul_zero, Faces.slackVector, row_sum_pair F t j i
    (fun k h₁ h₂ ↦ hz k h₂ h₁)] at hjrow
  have neg {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (he : 0 = a + b*c) :
      c < 0 := by
    by_contra! h
    linarith only [he, ha, mul_nonneg hb.le h]
  refine ⟨i, j, ⟨hji.symm, z, feasible_of_barycentric F hc hm hb, hbind, hbind',
    neg (hstrict j) hi hjrow, neg (hstrict i) hj hirow⟩, hi, hj, ?_⟩
  intro k hki hkj
  refine ⟨hz k hki hkj, ?_⟩
  rw [← hb]
  have hf := feasible_of_barycentric F hc hm hb k
  apply mul_pos hm
  by_contra! he
  exact (hreg.no_third z i j k hji.symm hbind hbind' (le_antisymm he hf)).elim hki hkj

#print axioms Faces.homogeneous_zero
#print axioms Faces.offset_support

/-- The affine offset cannot have a complementary solution when the
individually rational region is empty. -/
theorem Faces.no_offset_solution (x : E) (empty : ¬ ∃ z, F.Feasible z)
    (t : I → ℝ) : ¬ F.Complementary (fun i ↦ F.slack i x) t := by
  intro hc
  let m : ℝ := 1 + ∑ j, t j
  have hm : 0 < m :=
    add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun j _ ↦ (hc j).1)
  let z := center F 1 x t
  have hb (k : I) : m * F.slack k z = F.slackVector (fun i ↦ F.slack i x) t k := by
    simpa [m, z, Faces.slackVector] using
      (center_slack F (m := 1) x t hm.ne' k)
  exact empty ⟨z, feasible_of_barycentric F hc hm hb⟩

/-- Each sink supplies exactly one strictly complementary solution on its
two-face support, with the two weights given by the binding comparisons. -/
theorem Faces.sink_solution (hreg : RegularFaces F) (x : E)
    (hstrict : ∀ i, 0 < F.slack i x) {i j : I} (sink : F.SinkPair i j) :
    ∃! t : I → ℝ, F.Complementary (fun k ↦ F.slack k x) t ∧
      0 < t i ∧ 0 < t j ∧
      (∀ k, k ≠ i → k ≠ j → t k = 0 ∧ 0 < F.slackVector (fun k ↦ F.slack k x) t k) := by
  classical
  obtain ⟨hij, z, hf, hi, hj, hji, hij'⟩ := sink
  let a := -(F.slack j x) / F.cross j i
  let b := -(F.slack i x) / F.cross i j
  have ha : 0 < a := div_pos_of_neg_of_neg (neg_neg_of_pos (hstrict j)) hji
  have hb : 0 < b := div_pos_of_neg_of_neg (neg_neg_of_pos (hstrict i)) hij'
  let t (k : I) := if k = i then a else if k = j then b else 0
  have ti : t i = a := by simp [t]
  have tj : t j = b := by simp [t, hij.symm]
  have rest (k : I) (hki : k ≠ i) (hkj : k ≠ j) : t k = 0 := by simp [t, hki, hkj]
  have hn (k : I) : 0 ≤ t k := by
    by_cases hk : k = i
    · simpa [hk, ti] using ha.le
    by_cases hj' : k = j
    · simpa [hj', tj] using hb.le
    rw [rest k hk hj']
  have ai : a * F.cross j i = -F.slack j x := div_mul_cancel₀ _ hji.ne
  have bj : b * F.cross i j = -F.slack i x := div_mul_cancel₀ _ hij'.ne
  have zi : F.slackVector (fun k ↦ F.slack k x) t i = 0 := by
    rw [Faces.slackVector, row_sum_pair F t i j rest, tj, bj, add_neg_cancel]
  have zj : F.slackVector (fun k ↦ F.slack k x) t j = 0 := by
    rw [Faces.slackVector, row_sum_pair F t j i (fun k u v ↦ rest k v u),
      ti, ai, add_neg_cancel]
  let m : ℝ := 1 + ∑ k, t k
  have hm : 0 < m :=
    add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun k _ ↦ hn k)
  let y := center F 1 x t
  have bal (k : I) : m * F.slack k y = F.slackVector (fun k ↦ F.slack k x) t k := by
    simpa [m, y, Faces.slackVector] using
      (center_slack F (m := 1) x t hm.ne' k)
  have hz : y = z := hreg.unique_corner y z i j hij
    ((mul_eq_zero.mp ((bal i).trans zi)).resolve_left hm.ne')
    ((mul_eq_zero.mp ((bal j).trans zj)).resolve_left hm.ne') hi hj
  have eqSlack (k : I) : F.slackVector (fun k ↦ F.slack k x) t k = m * F.slack k z := by
    rw [← hz, bal]
  refine ⟨t, ⟨?_, ti ▸ ha, tj ▸ hb, ?_⟩, ?_⟩
  · intro k
    refine ⟨hn k, by rw [eqSlack]; exact mul_nonneg hm.le (hf k), ?_⟩
    by_cases hk : k = i
    · simp [hk, zi]
    by_cases hj' : k = j
    · simp [hj', zj]
    rw [rest k hk hj', zero_mul]
  · intro k hki hkj
    refine ⟨rest k hki hkj, ?_⟩
    rw [eqSlack]
    apply mul_pos hm
    exact lt_of_le_of_ne (hf k) (fun h ↦ (hreg.no_third z i j k hij hi hj h.symm).elim hki hkj)
  · intro u ⟨hu, hui, huj, hrest⟩
    have e₁ := (mul_eq_zero.mp (hu i).2.2).resolve_left hui.ne'
    have e₂ := (mul_eq_zero.mp (hu j).2.2).resolve_left huj.ne'
    rw [Faces.slackVector, row_sum_pair F u i j (fun k hi hj ↦ (hrest k hi hj).1)] at e₁
    rw [Faces.slackVector, row_sum_pair F u j i (fun k hj hi ↦ (hrest k hi hj).1)] at e₂
    funext k
    by_cases hk : k = i
    · subst k
      rw [ti]
      exact (eq_div_iff hji.ne).2 (by linarith only [e₂])
    by_cases hj' : k = j
    · subst k
      rw [tj]
      exact (eq_div_iff hij'.ne).2 (by linarith only [e₁])
    rw [(hrest k hk hj').1, rest k hk hj']

#print axioms Faces.no_offset_solution
#print axioms Faces.sink_solution

end

end PlanarQuitting
