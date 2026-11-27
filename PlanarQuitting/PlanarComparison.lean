module

public import PlanarQuitting.LinearComplementarity
public import PlanarQuitting.NormalMap
import Mathlib.Tactic.Linarith

/-!
# The signed-count alternative for regular planar comparison systems

The core contains the players whose rows need not be positive. The other
rows have strictly positive entries. In the linear complementarity problem
they are inactive at the two offsets used here. An empty feasible region
gives count zero. A feasible sink produces a negative contribution, and
only the zero weight vector gives a positive contribution.
-/

@[expose] public section

namespace PlanarQuitting

open Filter Set
open scoped BigOperators Topology

noncomputable section

variable {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The geometric representation of the first derivative on the core, with
entrywise positive rows for players outside the core. -/
structure ComparisonFaces (M : PayoffMatrix n) (K : Finset (Fin n))
    (F : Faces K E) : Prop where
  core : ∀ i j : K, M i j = F.cross i j
  outside : ∀ i ∉ K, ∀ j, 0 < M i j

variable {M : PayoffMatrix n} {K : Finset (Fin n)} {F : Faces K E}

def restrictCore (t : Coordinates n) : K → ℝ := fun i ↦ t i

def extendCore (default : ℝ) (t : K → ℝ) : Coordinates n :=
  fun i ↦ if h : i ∈ K then t ⟨i, h⟩ else default

@[simp] theorem extendCore_in (d : ℝ) (t : K → ℝ) (i : K) :
    extendCore d t i = t i := dite_eq_left i.property

@[simp] theorem extendCore_out (d : ℝ) (t : K → ℝ) {i : Fin n} (hi : i ∉ K) :
    extendCore d t i = d := dite_eq_right hi

variable (rep : ComparisonFaces M K F)

include rep

private theorem outside_zero {q t : Coordinates n}
    (hq : ∀ i ∉ K, 0 ≤ q i) (ht : AffineComplementary M q t) :
    ∀ i ∉ K, t i = 0 := by
  intro i hi
  by_contra h
  have hp : 0 < t i := lt_of_le_of_ne (ht i).1 (Ne.symm h)
  have hsum : 0 < matrixMap M t i := by
    rw [matrixMap_apply]
    exact Finset.sum_pos' (fun j _ ↦ mul_nonneg (rep.outside i hi j).le (ht j).1)
      ⟨i, Finset.mem_univ _, mul_pos (rep.outside i hi i) hp⟩
  have hs : 0 < (q + matrixMap M t) i := add_pos_of_nonneg_of_pos (hq i hi) hsum
  exact (mul_pos hp hs).ne' (ht i).2.2

private theorem coreSlack (q t : Coordinates n) (ht : ∀ i ∉ K, t i = 0) (i : K) :
    (q + matrixMap M t) i = F.slackVector (restrictCore (K := K) q) (restrictCore (K := K) t) i := by
  change q i + matrixMap M t i = _
  rw [matrixMap_apply, Faces.slackVector]
  congr 1
  calc
    (∑ j, M i j * t j) = ∑ j ∈ K, M i j * t j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      simp [ht j hj]
    _ = ∑ j : K, M i j * t j :=
      (Finset.sum_coe_sort K (fun j ↦ M i j * t j)).symm
    _ = _ := Finset.sum_congr rfl fun j _ ↦ by
      rw [rep.core]
      exact mul_comm ..

private theorem restrict_complementary {q t : Coordinates n}
    (hq : ∀ i ∉ K, 0 ≤ q i) (ht : AffineComplementary M q t) :
    F.Complementary (restrictCore (K := K) q) (restrictCore (K := K) t) := by
  intro i
  rw [← coreSlack rep q t (outside_zero rep hq ht) i]
  exact ht i

private theorem extend_complementary {q : Coordinates n}
    (hq : ∀ i ∉ K, 0 ≤ q i) {t : K → ℝ}
    (ht : F.Complementary (restrictCore (K := K) q) t) :
    AffineComplementary M q (extendCore 0 t) := by
  have hnon (j : Fin n) : 0 ≤ extendCore 0 t j := by
    by_cases hj : j ∈ K
    · simpa [extendCore, hj] using (ht ⟨j,hj⟩).1
    · simp [extendCore, hj]
  intro i
  by_cases hi : i ∈ K
  · have hh := coreSlack rep q (extendCore 0 t) (fun j hj ↦ extendCore_out 0 t hj) ⟨i,hi⟩
    have he : restrictCore (extendCore 0 t) = t := by
      funext j
      exact extendCore_in 0 t j
    rw [he] at hh
    change (q + matrixMap M (extendCore 0 t)) i = _ at hh
    rw [hh]
    simpa [extendCore, hi] using ht ⟨i,hi⟩
  · have hsum : 0 ≤ matrixMap M (extendCore 0 t) i := by
      rw [matrixMap_apply]
      exact Finset.sum_nonneg (fun j _ ↦ mul_nonneg (rep.outside i hi j).le (hnon j))
    rw [extendCore_out 0 t hi]
    exact ⟨le_rfl, add_nonneg (hq i hi) hsum, zero_mul _⟩

private theorem outside_slack {q t : Coordinates n} (hq : ∀ i ∉ K, 0 < q i)
    (ht : AffineComplementary M q t) (i : Fin n) (hi : i ∉ K) :
    0 < (q + matrixMap M t) i := by
  change 0 < q i + matrixMap M t i
  rw [matrixMap_apply]
  exact add_pos_of_pos_of_nonneg (hq i hi)
    (Finset.sum_nonneg fun j _ ↦ mul_nonneg (rep.outside i hi j).le (ht j).1)

/-- The homogeneous normal map has no nonzero roots. -/
theorem ComparisonFaces.normal_nonzero (hreg : RegularFaces F)
    (sites : ∀ i, ¬ F.Feasible (F.site i)) (x : Coordinates n) (hx : x ≠ 0) :
    normalMap (matrixMap M) x ≠ 0 := by
  intro hz
  obtain ⟨ht, he⟩ := complementary_of_normal_zero M 0 x (by simpa using hz)
  have hr := F.homogeneous_zero hreg sites
    (restrict_complementary rep (fun _ _ ↦ le_rfl) ht)
  have hzero : positivePart x = 0 := by
    funext i
    by_cases hi : i ∈ K
    · exact congrFun hr ⟨i,hi⟩
    · exact outside_zero rep (fun _ _ ↦ le_rfl) ht i hi
  apply hx
  rw [hzero, signedRoot, map_zero, add_zero, sub_zero] at he
  exact he.symm

/-- With an empty core region the translated normal map has no roots, so
the signed-count transfer forces a nonzero solution of the cube comparison. -/
theorem ComparisonFaces.cube_of_empty (hreg : RegularFaces F)
    (empty : ¬ ∃ x, F.Feasible x) (x : E)
    {f : Coordinates n → Coordinates n} (hf : Continuous f) (fzero : f 0 = 0)
    (diff : HasFDerivAt f (matrixMap M) 0) :
    ∃ p, p ≠ 0 ∧ CubeComparison f p := by
  let q := extendCore (K := K) 1 fun i ↦ F.slack i x
  have hq (i : Fin n) (hi : i ∉ K) : 0 ≤ q i := by simp [q, hi]
  have no (y : Coordinates n) : normalMap (matrixMap M) y + q ≠ 0 := by
    intro hz
    obtain ⟨ht, _⟩ := complementary_of_normal_zero M q y hz
    have hc := restrict_complementary rep hq ht
    have hq' : restrictCore q = fun i ↦ F.slack i x := by
      funext i
      simp [q, restrictCore]
    rw [hq'] at hc
    exact F.no_offset_solution x empty _ hc
  exact nonzero_cube_of_signed_count hf fzero (matrixMap M) diff
    (rep.normal_nonzero hreg fun i hi ↦ empty ⟨F.site i,hi⟩)
    q (fun j : Fin 0 ↦ j.elim0) (fun j ↦ j.elim0)
    (fun y ↦ ⟨fun h ↦ (no y h).elim, fun ⟨j,_⟩ ↦ j.elim0⟩)
    (fun j ↦ j.elim0) (fun j ↦ j.elim0) (fun j ↦ j.elim0) (by simp)

/-- At a strictly feasible core offset, any nonzero complementary weight
vector has a two-face sink support. -/
private theorem core_support (hreg : RegularFaces F) (x : E) (hstrict : ∀ i, 0 < F.slack i x)
    {t : Coordinates n}
    (ht : AffineComplementary M (extendCore 1 fun i ↦ F.slack i x) t) (hne : t ≠ 0) :
    ∃ i j : K, F.SinkPair i j ∧ 0 < t i ∧ 0 < t j ∧
      (∀ k : Fin n, k ≠ i → k ≠ j → t k = 0 ∧
        0 < (extendCore (K := K) 1 (fun i ↦ F.slack i x) + matrixMap M t) k) := by
  let q := extendCore (K := K) 1 fun i ↦ F.slack i x
  have hq (i : Fin n) (hi : i ∉ K) : 0 < q i := by simp [q, hi]
  have ret := restrict_complementary rep (fun i hi ↦ (hq i hi).le) ht
  have he : restrictCore (K := K) q = fun i ↦ F.slack i x := by
    funext i
    simp [q, restrictCore]
  rw [he] at ret
  have hz := outside_zero rep (fun i hi ↦ (hq i hi).le) ht
  have hn : restrictCore (K := K) t ≠ 0 := by
    intro h
    apply hne
    funext k
    by_cases hk : k ∈ K
    · exact congrFun h ⟨k,hk⟩
    · exact hz k hk
  obtain ⟨i,j,hs,hi,hj,hrest⟩ := F.offset_support hreg x hstrict ret hn
  refine ⟨i,j,hs,hi,hj,fun k hki hkj ↦ ?_⟩
  by_cases hk : k ∈ K
  · have h := hrest ⟨k,hk⟩ (fun e ↦ hki (congrArg Subtype.val e))
      (fun e ↦ hkj (congrArg Subtype.val e))
    have hsl := coreSlack rep q t hz ⟨k,hk⟩
    rw [he] at hsl
    exact ⟨h.1, hsl.symm ▸ h.2⟩
  · exact ⟨hz k hk, outside_slack rep hq ht k hk⟩

private theorem active_unique (hreg : RegularFaces F) (x : E) (hstrict : ∀ i, 0 < F.slack i x)
    {t u : Coordinates n}
    (ht : AffineComplementary M (extendCore 1 (fun i ↦ F.slack i x)) t)
    (hu : AffineComplementary M (extendCore 1 (fun i ↦ F.slack i x)) u)
    (same : ∀ i, 0 < t i ↔ 0 < u i) : t = u := by
  by_cases htz : t = 0
  · subst t
    funext i
    exact (le_antisymm (le_of_not_gt fun h ↦ (lt_irrefl 0) ((same i).2 h)) (hu i).1).symm
  · let q := extendCore (K := K) 1 fun i ↦ F.slack i x
    have hq (i : Fin n) (hi : i ∉ K) : 0 ≤ q i := by simp [q, hi]
    have he : restrictCore (K := K) q = fun i ↦ F.slack i x := by
      funext i
      simp [q, restrictCore]
    have restrict {c : Coordinates n} (hc : AffineComplementary M q c) :=
      he ▸ restrict_complementary rep hq hc
    obtain ⟨i,j,sink,hpi,hpj,hrest⟩ := core_support rep hreg x hstrict ht htz
    obtain ⟨y, _, huniq⟩ := F.sink_solution hreg x hstrict sink
    have ht0 := outside_zero rep hq ht
    have hu0 := outside_zero rep hq hu
    have eq_t : restrictCore t = y :=
      huniq _ ⟨restrict ht, hpi, hpj, fun k hki hkj ↦ by
        have hk := hrest k (fun e ↦ hki (Subtype.ext e)) (fun e ↦ hkj (Subtype.ext e))
        have hsl := coreSlack rep q t ht0 k
        rw [he] at hsl
        exact ⟨hk.1, hsl ▸ hk.2⟩⟩
    have huv : u ≠ 0 := by
      intro h
      have hj := (same i).1 hpi
      rw [h] at hj
      exact (lt_irrefl 0) hj
    obtain ⟨a,b,sink',ha,hb,hrest'⟩ := core_support rep hreg x hstrict hu huv
    have hia : (i : Fin n) = a ∨ (i : Fin n) = b := by
      by_contra! h
      have h0 := (same i).1 hpi
      rw [(hrest' i h.1 h.2).1] at h0
      exact (lt_irrefl 0) h0
    have hja : (j : Fin n) = a ∨ (j : Fin n) = b := by
      by_contra! h
      have h0 := (same j).1 hpj
      rw [(hrest' j h.1 h.2).1] at h0
      exact (lt_irrefl 0) h0
    have hne : (i : Fin n) ≠ j := fun e ↦ sink.1 (Subtype.ext e)
    have swap : ((i : Fin n) = a ∧ (j : Fin n) = b) ∨
        ((i : Fin n) = b ∧ (j : Fin n) = a) := by
      rcases hia with hia | hia <;> rcases hja with hja | hja
      · exact (hne (hia.trans hja.symm)).elim
      · exact Or.inl ⟨hia,hja⟩
      · exact Or.inr ⟨hia,hja⟩
      · exact (hne (hia.trans hja.symm)).elim
    have eq_u : restrictCore u = y :=
      huniq _ ⟨restrict hu, (same i).1 hpi, (same j).1 hpj, fun k hki hkj ↦ by
        have hk : u k = 0 ∧ 0 < (q + matrixMap M u) k := by
          rcases swap with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
          · exact hrest' k (fun e ↦ hki (Subtype.ext (e.trans h₁.symm)))
              (fun e ↦ hkj (Subtype.ext (e.trans h₂.symm)))
          · exact hrest' k (fun e ↦ hkj (Subtype.ext (e.trans h₂.symm)))
              (fun e ↦ hki (Subtype.ext (e.trans h₁.symm)))
        have hsl := coreSlack rep q u hu0 k
        rw [he] at hsl
        exact ⟨hk.1, hsl ▸ hk.2⟩⟩
    funext k
    by_cases hk : k ∈ K
    · exact congrFun (eq_t.trans eq_u.symm) ⟨k,hk⟩
    · exact (ht0 k hk).trans (hu0 k hk).symm

#print axioms ComparisonFaces.normal_nonzero
#print axioms ComparisonFaces.cube_of_empty
#print axioms core_support
#print axioms active_unique

/-- A feasible sink changes the signed count from one, forcing a nonzero
solution of the exact cube comparisons. All complementary roots at the
chosen strictly feasible offset are covered. -/
theorem ComparisonFaces.cube_of_sink (hreg : RegularFaces F)
    (sites : ∀ i, ¬ F.Feasible (F.site i)) (x : E)
    (hstrict : ∀ i, 0 < F.slack i x) (sink : F.HasSink)
    {f : Coordinates n → Coordinates n} (hf : Continuous f) (fzero : f 0 = 0)
    (diff : HasFDerivAt f (matrixMap M) 0) :
    ∃ p, p ≠ 0 ∧ CubeComparison f p := by
  classical
  let q := extendCore (K := K) 1 fun i ↦ F.slack i x
  let J := {t : Coordinates n // AffineComplementary M q t}
  let active (j : J) := Finset.univ.filter (fun i ↦ 0 < j.val i)
  have inj : Function.Injective active := by
    intro a b he
    apply Subtype.ext
    apply active_unique rep hreg x hstrict a.property b.property
    intro i
    have hh : i ∈ active a ↔ i ∈ active b := by rw [he]
    simpa [active] using hh
  let : Finite J := Finite.of_injective active inj
  let : Fintype J := Fintype.ofFinite J
  have hpos (i : Fin n) : 0 < q i := by
    by_cases hi : i ∈ K
    · simpa [q, extendCore, hi] using hstrict ⟨i,hi⟩
    · simp [q, hi]
  let j₀ : J := ⟨0, fun i ↦ by simpa using (hpos i).le⟩
  let z (j : J) := signedRoot M q j.val
  have hz (j : J) := normal_zero_of_complementary M q j.val j.property
  have hiz : Function.Injective z := by
    intro j k h
    exact Subtype.ext ((hz j).1.symm.trans ((congrArg positivePart h).trans (hz k).1))
  have exactRoots (y : Coordinates n) :
      normalMap (matrixMap M) y + q = 0 ↔ ∃ j : J, y = z j := by
    constructor
    · intro hy
      obtain ⟨h, he⟩ := complementary_of_normal_zero M q y hy
      exact ⟨⟨positivePart y, h⟩, he.symm⟩
    · rintro ⟨j, rfl⟩
      exact (hz j).2
  have actPair {t : J} {i j : K} (hi : 0 < t.val i) (hj : 0 < t.val j)
      (hr : ∀ k : Fin n, k ≠ i → k ≠ j → t.val k = 0 ∧
        0 < (q + matrixMap M t.val) k) :
      active t = {(i : Fin n), (j : Fin n)} := by
    ext k
    by_cases hki : k = i
    · subst k
      simp [active, hi]
    by_cases hkj : k = j
    · subst k
      simp [active, hj]
    simp [active, hki, hkj, (hr k hki hkj).1]
  have det_one : (activeMatrix M (active j₀)).det = 1 := by
    have he : active j₀ = ∅ := by ext i; simp [active, j₀]
    rw [he, activeMatrix_empty, Matrix.det_one]
  have det_neg (t : J) (hne : t ≠ j₀) : (activeMatrix M (active t)).det < 0 := by
    have hn : t.val ≠ 0 := fun he ↦ hne (Subtype.ext he)
    obtain ⟨i,j,hs,hi,hj,hr⟩ := core_support rep hreg x hstrict t.property hn
    rw [actPair hi hj hr, det_active_pair M (fun h ↦ hs.1 (Subtype.ext h))
      ((rep.core i i).trans (F.cross_self i)) ((rep.core j j).trans (F.cross_self j))]
    rw [rep.core j i, rep.core i j]
    obtain ⟨_,_,_,_,_,hji,hij⟩ := hs
    exact neg_lt_zero.mpr (mul_pos_of_neg_of_neg hji hij)
  have det_nonzero (t : J) : (activeMatrix M (active t)).det ≠ 0 := by
    by_cases ht : t = j₀
    · rw [ht, det_one]
      exact one_ne_zero
    · exact (det_neg t ht).ne
  let L (t : J) := matrixEquiv (activeMatrix M (active t)) (det_nonzero t)
  have pos (t : J) (i : Fin n) (hi : i ∈ active t) : 0 < z t i := by
    have ht : 0 < t.val i := (Finset.mem_filter.mp hi).2
    have hs := (mul_eq_zero.mp (t.property i).2.2).resolve_left ht.ne'
    change 0 < t.val i - (q + matrixMap M t.val) i
    simpa [hs] using ht
  have neg (t : J) (i : Fin n) (hi : i ∉ active t) : z t i < 0 := by
    by_cases ht : t = j₀
    · subst t
      change 0 - (q + matrixMap M 0) i < 0
      simpa using hpos i
    · have hn : t.val ≠ 0 := fun he ↦ ht (Subtype.ext he)
      obtain ⟨a,b,_,ha,hb,hr⟩ := core_support rep hreg x hstrict t.property hn
      have hia : i ≠ a := fun e ↦ hi (Finset.mem_filter.mpr
        ⟨Finset.mem_univ i, e.symm ▸ ha⟩)
      have hib : i ≠ b := fun e ↦ hi (Finset.mem_filter.mpr
        ⟨Finset.mem_univ i, e.symm ▸ hb⟩)
      change t.val i - (q + matrixMap M t.val) i < 0
      rw [(hr i hia hib).1]
      exact sub_neg.mpr (hr i hia hib).2
  have hne : ∃ t : J, t ≠ j₀ := by
    obtain ⟨y,i,j,hij,hy,hi,hj,hji,hij'⟩ := sink
    obtain ⟨t,⟨ht,hpt,_,_⟩,_⟩ :=
      F.sink_solution hreg x hstrict ⟨hij,y,hy,hi,hj,hji,hij'⟩
    have hs : restrictCore (K := K) q = fun i ↦ F.slack i x := by
      funext i
      simp [restrictCore, q]
    have hqt (i : Fin n) (hi : i ∉ K) : 0 ≤ q i := (hpos i).le
    refine ⟨⟨extendCore 0 t, extend_complementary rep hqt (hs.symm ▸ ht)⟩, ?_⟩
    intro he
    have hz : extendCore 0 t i = 0 :=
      congrFun (congrArg Subtype.val he) i
    exact hpt.ne' ((extendCore_in 0 t i).symm.trans hz)
  apply nonzero_cube_of_signed_count hf fzero (matrixMap M) diff
    (rep.normal_nonzero hreg sites) q z hiz exactRoots L (fun _ ↦ q)
  · intro t
    simpa only [L, matrixEquiv_apply] using normal_affine_near M q (z t)
      (active t) (pos t) (neg t)
  · let sign (t : J) := (L t).toContinuousLinearMap.det / |(L t).toContinuousLinearMap.det|
    change (∑ t, sign t) ≠ 1
    have s₀ : sign j₀ = 1 := by simp [sign, L, matrixEquiv_det, det_one]
    have sneg (t : J) (ht : t ≠ j₀) : sign t = -1 := by
      unfold sign L
      rw [matrixEquiv_det, abs_of_neg (det_neg t ht), div_neg,
        div_self (det_nonzero t)]
    have hsum : (∑ t ∈ Finset.univ.erase j₀, sign t) < 0 := by
      obtain ⟨t, ht⟩ := hne
      apply Finset.sum_neg'
      · intro a ha
        rw [sneg a (Finset.mem_erase.mp ha).1]
        norm_num
      · exact ⟨t, Finset.mem_erase.mpr ⟨ht,Finset.mem_univ _⟩, by rw [sneg t ht]; norm_num⟩
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j₀), s₀]
    linarith

#print axioms ComparisonFaces.cube_of_sink

omit rep in
/-- Any nonempty feasible region under the regular incidence hypotheses with
infeasible sites contains a strictly feasible point. At a pair of binding
lines the two directions along the lines increase opposite slacks. -/
theorem Faces.strict_feasible {I : Type*} [Fintype I] {F : Faces I E}
    (hreg : RegularFaces F) (sites : ∀ i, ¬ F.Feasible (F.site i))
    {x : E} (hx : F.Feasible x) : ∃ y, ∀ i, 0 < F.slack i y := by
  classical
  by_cases some_zero : ∃ i, F.slack i x = 0
  · obtain ⟨i, hi⟩ := some_zero
    have nonparallel (i j : I) (hne : i ≠ j) (hz : F.slack i x = 0) :
        F.row i (F.site j - x) ≠ 0 := by
      have he : F.row i (F.site j - x) = F.slack i (F.site j) := by
        simp only [Faces.slack, map_sub] at hz ⊢
        linarith
      rw [he]
      exact hreg.site_off i j hne
    have direction : ∃ d : E, ∀ k, F.slack k x = 0 → 0 < F.row k d := by
      by_cases hex : ∃ j, j ≠ i ∧ F.slack j x = 0
      · obtain ⟨j,hji,hj⟩ := hex
        let a := F.site j - x
        let b := F.site i - x
        have y₁ : F.row i a ≠ 0 := nonparallel i j hji.symm hi
        have y₂ : F.row j b ≠ 0 := nonparallel j i hji hj
        have zero₁ : F.row i b = 0 := by
          change F.row i (F.site i - x) = 0
          rw [← neg_sub, map_neg, show F.row i (x-F.site i) = 0 from hi, neg_zero]
        have zero₂ : F.row j a = 0 := by
          change F.row j (F.site j - x) = 0
          rw [← neg_sub, map_neg, show F.row j (x-F.site j) = 0 from hj, neg_zero]
        refine ⟨(F.row i a)⁻¹ • a + (F.row j b)⁻¹ • b, fun k hk ↦ ?_⟩
        rcases hreg.no_third x i j k hji.symm hi hj hk with h | h
        · rw [h, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
            zero₁, mul_zero, add_zero, inv_mul_cancel₀ y₁]
          exact one_pos
        · rw [h, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
            zero₂, mul_zero, zero_add, inv_mul_cancel₀ y₂]
          exact one_pos
      · have exj : ∃ j, j ≠ i := by
          by_contra! h
          apply sites i
          intro j
          simp [h j]
        obtain ⟨j,hji⟩ := exj
        let a := F.site j - x
        have ya : F.row i a ≠ 0 := nonparallel i j hji.symm hi
        refine ⟨(F.row i a)⁻¹ • a, fun k hk ↦ ?_⟩
        have he : k = i := by
          by_contra hn
          exact hex ⟨k,hn,hk⟩
        rw [he, map_smul, smul_eq_mul, inv_mul_cancel₀ ya]
        exact one_pos
    obtain ⟨d,hd⟩ := direction
    let okay (t : ℝ) (k : I) := F.slack k x = 0 ∨ 0 < F.slack k x + t * F.row k d
    have close (k : I) : ∀ᶠ t : ℝ in 𝓝 0, okay t k := by
      by_cases hk : F.slack k x = 0
      · exact Filter.Eventually.of_forall (fun _ ↦ Or.inl hk)
      · have hcont : Continuous (fun t : ℝ ↦ F.slack k x + t * F.row k d) :=
          continuous_const.add (continuous_id.mul continuous_const)
        have hs : 0 < F.slack k x + 0 * F.row k d := by
          simpa using lt_of_le_of_ne (hx k) (Ne.symm hk)
        have hnhds := (isOpen_lt continuous_const hcont).mem_nhds hs
        filter_upwards [hnhds] with t ht using Or.inr ht
    obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (eventually_all.mpr close)
    have en : δ/2 ∈ Metric.ball (0 : ℝ) δ := by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_of_nonneg (half_pos hδ).le]
      exact half_lt_self hδ
    refine ⟨x + (δ/2) • d, fun k ↦ ?_⟩
    have sl : F.slack k (x + (δ/2) • d) = F.slack k x + δ/2 * F.row k d := by
      simp only [Faces.slack, map_sub, map_add, map_smul, smul_eq_mul]
      ring
    rw [sl]
    rcases hball en k with hk | hk
    · rw [hk, zero_add]
      exact mul_pos (half_pos hδ) (hd k hk)
    · exact hk
  · refine ⟨x, fun i ↦ lt_of_le_of_ne (hx i) ?_⟩
    exact fun h ↦ some_zero ⟨i,h.symm⟩

/-- The regular planar alternative at the level of the exact cube
comparisons. A nonzero hazard solves the comparisons, or the feasible
region gives a directed quitting cycle. -/
theorem ComparisonFaces.cube_or_cycle [Nonempty K] (hreg : RegularFaces F)
    (sites : ∀ i, ¬ F.Feasible (F.site i))
    {f : Coordinates n → Coordinates n} (hf : Continuous f) (fzero : f 0 = 0)
    (diff : HasFDerivAt f (matrixMap M) 0) :
    (∃ p, p ≠ 0 ∧ CubeComparison f p) ∨ Nonempty (DirectedCycle F) := by
  by_cases feasible : ∃ x, F.Feasible x
  · by_cases sink : F.HasSink
    · obtain ⟨x,hx⟩ := feasible
      obtain ⟨y,hy⟩ := F.strict_feasible hreg sites hx
      exact Or.inl (rep.cube_of_sink hreg sites y hy sink hf fzero diff)
    · refine Or.inr (F.directed_cycle hreg feasible (fun i ↦ ?_) sink)
      simpa [Faces.Feasible, not_le] using sites i
  · exact Or.inl (rep.cube_of_empty hreg feasible 0 hf fzero diff)

#print axioms Faces.strict_feasible
#print axioms ComparisonFaces.cube_or_cycle

end

end PlanarQuitting
