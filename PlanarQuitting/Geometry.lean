module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Directed cycles of individually rational continuation values

The continuation value region is the intersection of finitely many affine
half-spaces. The distinguished point for each half-space is the payoff vector
when its owner quits alone. Under the generic incidence assumptions, following
each binding line toward its distinguished point reaches another binding line.
Either two lines point into their intersection, or one can keep walking and
find a cycle among the finitely many intersections.
-/

@[expose] public section

namespace PlanarQuitting

open Function

noncomputable section

variable {I E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A finite collection of linear payoff rows and the corresponding solo prizes. -/
structure Faces (I E : Type*) [AddCommGroup E] [Module ℝ E] where
  row : I → (E →ₗ[ℝ] ℝ)
  site : I → E

def Faces.slack (F : Faces I E) (i : I) (x : E) : ℝ := F.row i (x - F.site i)

def Faces.Feasible (F : Faces I E) (x : E) : Prop := ∀ i, 0 ≤ F.slack i x

def Faces.mix (_F : Faces I E) (x y : E) (a : ℝ) : E := (1-a) • x + a • y

@[simp] theorem Faces.slack_site (F : Faces I E) (i : I) : F.slack i (F.site i) = 0 := by
  simp [Faces.slack]

theorem Faces.slack_mix (F : Faces I E) (i : I) (x y : E) (a : ℝ) :
    F.slack i (F.mix x y a) = (1-a) * F.slack i x + a * F.slack i y := by
  simp only [Faces.slack, Faces.mix, map_sub, map_add, map_smul, smul_eq_mul]
  ring

variable (F : Faces I E)

/-- Generic incidence conditions used in the walk along the boundary. -/
structure RegularFaces : Prop where
  site_off : ∀ i j, i ≠ j → F.slack i (F.site j) ≠ 0
  no_third : ∀ x i j k, i ≠ j → F.slack i x = 0 → F.slack j x = 0 →
    F.slack k x = 0 → k = i ∨ k = j
  unique_corner : ∀ x y i j, i ≠ j → F.slack i x = 0 → F.slack j x = 0 →
    F.slack i y = 0 → F.slack j y = 0 → x = y

/-- A sink is a feasible intersection towards which both owners' lines point. -/
def Faces.HasSink : Prop :=
  ∃ x i j, i ≠ j ∧ F.Feasible x ∧ F.slack i x = 0 ∧ F.slack j x = 0 ∧
    F.slack j (F.site i) < 0 ∧ F.slack i (F.site j) < 0

/-- Move towards an infeasible point and stop when the first constraint binds.
The stopping time is positive if the constraint that binds was strictly slack. -/
theorem Faces.first_hit [Fintype I] {x y : E} (hx : F.Feasible x)
    (hy : ∃ j, F.slack j y < 0) :
    ∃ (j : I) (a : ℝ), 0 ≤ a ∧ a < 1 ∧ F.slack j y < 0 ∧
      F.Feasible (F.mix x y a) ∧ F.slack j (F.mix x y a) = 0 ∧
      (0 < F.slack j x → 0 < a) := by
  classical
  let negative := Finset.univ.filter (fun i ↦ F.slack i y < 0)
  let ratio (i : I) := F.slack i x / (F.slack i x - F.slack i y)
  have hnegative : negative.Nonempty := by
    obtain ⟨j, hj⟩ := hy
    exact ⟨j, by simp [negative, hj]⟩
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image negative ratio hnegative
  have hj' : F.slack j y < 0 := (Finset.mem_filter.mp hj).2
  have hden : 0 < F.slack j x - F.slack j y := sub_pos.mpr (hj'.trans_le (hx j))
  have hjlt : ratio j < 1 := (div_lt_iff₀ hden).mpr (by linarith only [hj'])
  refine ⟨j, ratio j, div_nonneg (hx j) hden.le, hjlt, hj', ?_, ?_,
    fun h ↦ div_pos h hden⟩
  · intro k
    rw [F.slack_mix]
    by_cases hk : F.slack k y < 0
    · have hdk : 0 < F.slack k x - F.slack k y := sub_pos.mpr (hk.trans_le (hx k))
      have hcmp : ratio j ≤ ratio k := hmin k (by simp [negative, hk])
      have hmul := (le_div_iff₀ hdk).mp hcmp
      linarith only [hmul]
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr hjlt.le) (hx k))
        (mul_nonneg (div_nonneg (hx j) hden.le) (not_lt.mp hk))
  · rw [F.slack_mix]
    have hmul : ratio j * (F.slack j x - F.slack j y) = F.slack j x :=
      div_mul_cancel₀ _ hden.ne'
    linarith only [hmul]

/-- A corner reached along its incoming line. The outgoing constraint is the
first one that obstructs continuing towards the incoming owner's solo prize. -/
structure Corner where
  incoming : I
  outgoing : I
  point : E
  distinct : incoming ≠ outgoing
  feasible : F.Feasible point
  on_incoming : F.slack incoming point = 0
  on_outgoing : F.slack outgoing point = 0
  blocked : F.slack outgoing (F.site incoming) < 0

private theorem corner_key_injective (hreg : RegularFaces F) :
    Injective (fun c : Corner F ↦ (c.incoming, c.outgoing)) := by
  intro a b h
  have hi : a.incoming = b.incoming := congrArg Prod.fst h
  have hj : a.outgoing = b.outgoing := congrArg Prod.snd h
  have hb₁ : F.slack a.incoming b.point = 0 := by rw [hi]; exact b.on_incoming
  have hb₂ : F.slack a.outgoing b.point = 0 := by rw [hj]; exact b.on_outgoing
  have hp := hreg.unique_corner a.point b.point a.incoming a.outgoing a.distinct
    a.on_incoming a.on_outgoing hb₁ hb₂
  cases a
  cases b
  simp_all

/-- The outgoing owner is the incoming owner of the next corner. -/
structure CornerStep (c d : Corner F) (a : ℝ) : Prop where
  owner : d.incoming = c.outgoing
  pos : 0 < a
  lt_one : a < 1
  point : d.point = F.mix c.point (F.site c.outgoing) a

theorem Faces.initial_corner [Fintype I] [Nonempty I] (feasible : ∃ x, F.Feasible x)
    (sites : ∀ i, ∃ j, F.slack j (F.site i) < 0) : Nonempty (Corner F) := by
  let i : I := Classical.choice inferInstance
  obtain ⟨x, hx⟩ := feasible
  obtain ⟨j, a, _, _, _, hz, hj, _⟩ := F.first_hit hx (sites i)
  obtain ⟨k, b, _, _, hk, hw, hbind, _⟩ := F.first_hit hz (sites j)
  have hjk : j ≠ k := by
    intro h
    subst k
    simp at hk
  have hon : F.slack j (F.mix (F.mix x (F.site i) a) (F.site j) b) = 0 := by
    rw [F.slack_mix, hj, F.slack_site]
    ring
  exact ⟨⟨j, k, _, hjk, hw, hon, hbind, hk⟩⟩

theorem Faces.next_corner [Fintype I] (hreg : RegularFaces F)
    (sites : ∀ i, ∃ j, F.slack j (F.site i) < 0)
    (noSink : ¬F.HasSink) (c : Corner F) :
    ∃ (d : Corner F) (a : ℝ), CornerStep F c d a := by
  have hr : 0 < F.slack c.incoming (F.site c.outgoing) := by
    by_contra! h
    have hneg := lt_of_le_of_ne h (hreg.site_off _ _ c.distinct)
    exact noSink ⟨c.point, c.incoming, c.outgoing, c.distinct, c.feasible,
      c.on_incoming, c.on_outgoing, c.blocked, hneg⟩
  obtain ⟨j, a, _, ha, hj, hx, hbind, hpositive⟩ := F.first_hit c.feasible (sites c.outgoing)
  have hn : c.outgoing ≠ j := by
    intro e
    rw [← e, F.slack_site] at hj
    exact (lt_irrefl 0 hj)
  have hpos : 0 < F.slack j c.point := by
    by_contra! h
    rcases hreg.no_third _ _ _ _ c.distinct c.on_incoming c.on_outgoing
        (le_antisymm h (c.feasible j)) with he | he
    · rw [he] at hj
      exact (not_lt_of_ge hr.le) hj
    · exact hn he.symm
  have hon : F.slack c.outgoing (F.mix c.point (F.site c.outgoing) a) = 0 := by
    rw [F.slack_mix, c.on_outgoing, F.slack_site]
    ring
  exact ⟨⟨c.outgoing, j, _, hn, hx, hon, hbind, hj⟩, a, rfl, hpositive hpos, ha, rfl⟩

/-- A directed periodic walk, traversed in the backwards order of the game. -/
structure DirectedCycle where
  length : ℕ
  length_pos : 0 < length
  corner : ℕ → Corner F
  stepSize : ℕ → ℝ
  period : ∀ t, corner (t + length) = corner t
  period_size : ∀ t, stepSize (t + length) = stepSize t
  step : ∀ t, CornerStep F (corner t) (corner (t+1)) (stepSize t)

/-- The feasible, no-sink case yields an actual directed cycle. -/
theorem Faces.directed_cycle [Fintype I] [Nonempty I] (hreg : RegularFaces F)
    (feasible : ∃ x, F.Feasible x)
    (sites : ∀ i, ∃ j, F.slack j (F.site i) < 0) (noSink : ¬F.HasSink) :
    Nonempty (DirectedCycle F) := by
  let _ : Finite (Corner F) := Finite.of_injective _ (corner_key_injective F hreg)
  let start := Classical.choice (F.initial_corner feasible sites)
  let next (c : Corner F) := Classical.choose (F.next_corner hreg sites noSink c)
  let size (c : Corner F) := Classical.choose (Classical.choose_spec (F.next_corner hreg sites noSink c))
  have hstep (c : Corner F) : CornerStep F c (next c) (size c) :=
    Classical.choose_spec (Classical.choose_spec (F.next_corner hreg sites noSink c))
  let walk t := (next^[t]) start
  obtain ⟨a, b, hne, he⟩ := Finite.exists_ne_map_eq_of_infinite walk
  have build (a b : ℕ) (hlt : a < b) (he : walk a = walk b) : Nonempty (DirectedCycle F) := by
    let L := b - a
    let c t := walk (t + a)
    have hp : ∀ t, c (t+L) = c t := by
      intro t
      have hL : L + a = b := by dsimp [L]; omega
      change walk (t + L + a) = walk (t + a)
      rw [Nat.add_assoc, hL]
      simp only [walk, iterate_add_apply, he]
    refine ⟨⟨L, by dsimp [L]; omega, c, fun t ↦ size (c t), hp,
      fun t ↦ congrArg size (hp t), ?_⟩⟩
    intro t
    have hnext : c (t+1) = next (c t) := by
      change walk (t + 1 + a) = next (walk (t+a))
      rw [show t + 1 + a = 1 + (t+a) by omega]
      simp [walk, iterate_add_apply]
    rw [hnext]
    exact hstep (c t)
  rcases lt_or_gt_of_ne hne with hab | hba
  · exact build a b hab he
  · exact build b a hba he.symm

#print axioms Faces.directed_cycle

end

end PlanarQuitting
