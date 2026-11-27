module

public import PlanarQuitting.SoloVerification
import Mathlib.Tactic.Linarith

/-!
# Existence for a regular affine representation of singleton prizes

The core comprises players with a rival solo prize weakly below their own.
A feasible singleton gives an immediate solo construction. In the remaining
case the verified geometric alternative either gives a directed cycle or a
stationary solution. A stationary solution with only one positive hazard is
implemented by the finite-cutoff argument.
-/

@[expose] public section

namespace PlanarQuitting

open Set
open scoped BigOperators

noncomputable section

variable {n : ℕ}

private theorem hazard_exists {p : Coordinates n} (hp : 0 ≤ p) (hne : p ≠ 0) :
    ∃ i, 0 < p i := by
  by_contra! h
  apply hne
  funext i
  exact le_antisymm (h i) (hp i)

private theorem solo_stationary_inequality (g : Game (Fin n))
    (p : Coordinates n) (k : Fin n) (hk : 0 < p k) (only : withoutOwn k p = 0)
    (comparisons : StationaryComparisons g p) (i : Fin n) (hi : i ≠ k) :
    (1-p k)*g.prize {i} i + p k*g.prize {i,k} i ≤ g.prize {k} i := by
  have off (a : Fin n) (ha : a ≠ k) : p a = 0 := by
    have h := congrFun only a
    simpa only [withoutOwn, if_neg ha, Pi.zero_apply] using h
  let cal : Calendar (Fin n) := ⟨fun _ ↦ k, fun _ ↦ p k⟩
  have eqP : cal.profile = Profile.stationary p := by
    funext t a
    by_cases ha : a = k
    · simp [ha, Calendar.profile, own, cal, Profile.stationary]
    · simp [Calendar.profile, own, cal, Profile.stationary, Ne.symm ha, off a ha]
  have exact (q : ℕ → ℝ) :
      (1-q 0)*stationaryCash g p i + q 0*stationaryQuit g p i =
      newPrize cal g i q 0 := by
    rw [← stationarity_row, ← eqP]
    exact (profile_row g cal i q 0).2
  have hCash := exact (fun _ ↦ 0)
  have hQuit := exact (fun _ ↦ 1)
  have hw : opponentWait p i = 1-p k := by
    simp only [opponentWait, opponentMass,Finset.notMem_empty,if_false]
    rw [Finset.prod_eq_single_of_mem k (Finset.mem_erase.mpr ⟨Ne.symm hi,Finset.mem_univ _⟩)]
    intro a _ ha
    simp [off a ha]
  have hne : p i < 1 := by simp [off i hi]
  have hc := (comparisons i).1 hne
  simp only [stationaryDifference,hw,sub_sub_cancel] at hc
  simp [newPrize,rival,cal,Ne.symm hi] at hCash
  simp [newPrize,quitReward,rival,cal,Ne.symm hi] at hQuit
  rw [hCash,hQuit,← mul_sub] at hc
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hc hk)

private theorem rival_positive_exit (p : Coordinates n) (hp : p ∈ Icc 0 1)
    (positive : ∀ i, ∃ j, j ≠ i ∧ 0 < p j) :
    StationaryExit p := by
  refine ⟨fun i ↦ ⟨hp.1 i,hp.2 i⟩,fun i ↦ ?_⟩
  obtain ⟨j,hji,hj⟩ := positive i
  let s := Finset.univ.erase i
  have hmem : j ∈ s := Finset.mem_erase.mpr ⟨hji,Finset.mem_univ _⟩
  have hrest : (∏ k ∈ s.erase j, (1-p k)) ≤ 1 :=
    Finset.prod_le_one (fun k _ ↦ sub_nonneg.mpr (hp.2 k))
      (fun k _ ↦ sub_le_self 1 (hp.1 k))
  have he : opponentWait p i = ∏ k ∈ s, (1-p k) := by simp [opponentWait,opponentMass,s]
  rw [he, ← Finset.prod_erase_mul s (fun k ↦ 1-p k) hmem]
  have hj₁ : (1 : ℝ) - p j < 1 := sub_lt_self 1 hj
  exact (mul_le_of_le_one_left (sub_nonneg.mpr (hp.2 j)) hrest).trans_lt hj₁

/-- The stationary alternatives are uniform-payoff constructions provided
each permitted sole quitter has a rival who can cap its payoff. -/
theorem uniform_of_stationary_comparisons (g : Game (Fin n))
    (p : Coordinates n) (hne : p ≠ 0) (hp : p ∈ Icc 0 1)
    (hc : StationaryComparisons g p)
    (punish : ∀ i, 0 < p i → withoutOwn i p = 0 →
      ∃ j, j ≠ i ∧ g.prize {j} i ≤ g.prize {i} i) :
    ∃ u, HasUniformPayoff g u := by
  by_cases h : ∃ i, 0 < p i ∧ withoutOwn i p = 0
  · obtain ⟨i,hi,hs⟩ := h
    obtain ⟨j,hji,hjp⟩ := punish i hi hs
    refine ⟨g.prize {i},uniform_of_solo_cutoff g i j (Or.inl hji) hjp ?_⟩
    intro e he
    refine ⟨p i,hi,hp.2 i,fun k hk ↦ ?_⟩
    exact (solo_stationary_inequality g p i hi hs hc k hk).trans (le_add_of_nonneg_right he.le)
  · refine uniform_of_stationary_exit g p (rival_positive_exit p hp ?_) hc
    intro i
    by_contra! not_pos
    have hzero : withoutOwn i p = 0 := by
      funext j
      by_cases hj : j = i
      · simp [withoutOwn,hj]
      · exact (if_neg hj).trans (le_antisymm (not_pos j hj) (hp.1 j))
    obtain ⟨j,hj⟩ := hazard_exists hp.1 hne
    have hji : j = i := by
      by_contra hj'
      exact (not_lt_of_ge (not_pos j hj')) hj
    exact h ⟨i,hji ▸ hj,hzero⟩

def quittingCore (g : Game (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ ∃ j, j ≠ i ∧ g.prize {j} i ≤ g.prize {i} i

theorem mem_quittingCore (g : Game (Fin n)) (i : Fin n) :
    i ∈ quittingCore g ↔ ∃ j, j ≠ i ∧ g.prize {j} i ≤ g.prize {i} i := by simp [quittingCore]

def Faces.restrict {E : Type*} [AddCommGroup E] [Module ℝ E]
    (F : Faces (Fin n) E) (K : Finset (Fin n)) : Faces K E :=
  ⟨fun i ↦ F.row i, fun i ↦ F.site i⟩

theorem RegularFaces.restrict {E : Type*} [AddCommGroup E] [Module ℝ E]
    {F : Faces (Fin n) E} (h : RegularFaces F) (K : Finset (Fin n)) :
    RegularFaces (F.restrict K) := by
  constructor
  · exact fun i j hij ↦ h.site_off i j (fun h ↦ hij (Subtype.ext h))
  · intro x i j k hij hi hj hk
    exact (h.no_third x i j k (fun e ↦ hij (Subtype.ext e)) hi hj hk).imp Subtype.ext Subtype.ext
  · exact fun x y i j hij hx₁ hx₂ hy₁ hy₂ ↦
      h.unique_corner x y i j (fun e ↦ hij (Subtype.ext e)) hx₁ hx₂ hy₁ hy₂

/-- The full uniform-payoff conclusion for any regular affine representation
of the singleton prizes. Live and collision prizes are arbitrary. -/
theorem uniform_of_regular_faces {E : Type*} [AddCommGroup E] [Module ℝ E]
    (g : Game (Fin n)) (F : Faces (Fin n) E) (b : Coordinates n)
    (rep : ∀ i j, g.prize {j} i = b i + F.row i (F.site j))
    (reg : RegularFaces F) :
    ∃ u, HasUniformPayoff g u := by
  classical
  let K := quittingCore g
  have out (i : Fin n) (hi : i ∉ K) (j : Fin n) (hj : j ≠ i) :
      g.prize {i} i < g.prize {j} i :=
    lt_of_not_ge (fun hn ↦ hi ((mem_quittingCore g i).2 ⟨j,hj,hn⟩))
  by_cases hn : Nonempty K
  · let : Nonempty K := hn
    let FK := F.restrict K
    have core (i j : K) : prizeGapMatrix g i j = FK.cross i j := by
      simp only [prizeGapMatrix, rep i j, rep i i, Faces.cross, Faces.slack,
        Faces.restrict, FK, map_sub]
      ring
    by_cases some : ∃ i, FK.Feasible (FK.site i)
    · obtain ⟨k,hk⟩ := some
      obtain ⟨j,hj,hjr⟩ := (mem_quittingCore g k).1 k.property
      refine ⟨g.prize {(k : Fin n)},uniform_of_solo_dominance g k j (Or.inl hj) hjr ?_⟩
      intro i hi
      by_cases hh : i ∈ K
      · have h := hk ⟨i,hh⟩
        rw [← Faces.cross, ← core] at h
        exact sub_nonneg.mp h
      · exact (out i hh k (Ne.symm hi)).le
    · have sites : ∀ i, ¬ FK.Feasible (FK.site i) := fun i hi ↦ some ⟨i,hi⟩
      have hOut (i : Fin n) (hi : i ∉ K) (j : Fin n) (hj : j ≠ i) :
          0 < prizeGapMatrix g i j := sub_pos.mpr (out i hi j hj)
      rcases stationary_comparisons_or_cycle g K FK (reg.restrict K) sites core hOut with h | h
      · obtain ⟨p,hp,hp',hc,hs⟩ := h
        exact uniform_of_stationary_comparisons g p hp hp' hc
          (fun i hi hsole ↦ (mem_quittingCore g i).1 (hs i hi hsole))
      · obtain ⟨d⟩ := h
        let owner : K ↪ Fin n := ⟨Subtype.val,Subtype.val_injective⟩
        exact d.hasUniformPayoff g owner b F.row (fun _ ↦ rfl)
          (fun i j ↦ (rep i j).symm) (fun i ha j ↦
            (out i (fun h ↦ ha ⟨i,h⟩ rfl) j (ha j)).le)
  · have empty (i : Fin n) : i ∉ K := fun h ↦ hn ⟨⟨i,h⟩⟩
    by_cases hwait : ∀ i, g.prize {i} i ≤ g.live i
    · exact ⟨g.live,uniform_of_wait g hwait⟩
    · push Not at hwait
      obtain ⟨i,hi⟩ := hwait
      exact ⟨g.prize {i},uniform_of_solo_dominance g i i (Or.inr hi.le) le_rfl
        (fun j hj ↦ (out j (empty j) i (Ne.symm hj)).le)⟩

#print axioms uniform_of_stationary_comparisons
#print axioms uniform_of_regular_faces

end

end PlanarQuitting
