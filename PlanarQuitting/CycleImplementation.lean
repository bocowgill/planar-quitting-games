module

public import PlanarQuitting.Geometry
public import PlanarQuitting.Independent
import Lean.Elab.Tactic.Omega

/-!
# From the planar boundary cycle to a uniform payoff

Reverse the geometric walk to obtain the chronology of the quitting game.
Each edge gives the probability with which its owner quits. The continuation
promises are feasible at every corner, including for players outside the face
system whose payoffs from the marked solo quits cover their own solo prize.
-/

@[expose] public section

namespace PlanarQuitting

open scoped BigOperators

noncomputable section

variable {J E : Type*} [AddCommGroup E] [Module ℝ E] {F : Faces J E}

private theorem DirectedCycle.length_gt_one (d : DirectedCycle F) : 1 < d.length := by
  by_contra! h
  have hL : d.length = 1 := by have := d.length_pos; omega
  have hp := d.period 0
  rw [zero_add, hL] at hp
  have he := (d.step 0).owner
  rw [zero_add, hp] at he
  exact (d.corner 0).distinct he

def DirectedCycle.revIndex (d : DirectedCycle F) (t : ℕ) : ℕ := d.length - t % d.length

def DirectedCycle.reverse (d : DirectedCycle F) (t : ℕ) : Corner F := d.corner (d.revIndex t)

theorem DirectedCycle.reverse_step (d : DirectedCycle F) (t : ℕ) :
    CornerStep F (d.reverse (t+1)) (d.reverse t) (d.stepSize (d.revIndex (t+1))) := by
  have hm := Nat.mod_lt t d.length_pos
  have h1 : 1 % d.length = 1 := Nat.mod_eq_of_lt d.length_gt_one
  by_cases ht : t % d.length + 1 < d.length
  · have hs : (t+1) % d.length = t % d.length + 1 := by
      rw [Nat.add_mod, h1, Nat.mod_eq_of_lt ht]
    have hr : d.revIndex (t+1) + 1 = d.revIndex t := by
      unfold DirectedCycle.revIndex
      omega
    simpa only [DirectedCycle.reverse, hr] using d.step (d.revIndex (t+1))
  · have he : t % d.length + 1 = d.length := by omega
    have hs : (t+1) % d.length = 0 := by rw [Nat.add_mod, h1, he, Nat.mod_self]
    have hr₀ : d.revIndex t = 1 := by unfold DirectedCycle.revIndex; omega
    have hr₁ : d.revIndex (t+1) = d.length := by simp [DirectedCycle.revIndex, hs]
    unfold DirectedCycle.reverse
    rw [hr₀, hr₁]
    simpa only [zero_add] using
      (show CornerStep F (d.corner (0+d.length)) (d.corner (0+1))
        (d.stepSize (0+d.length)) by rw [d.period, d.period_size]; exact d.step 0)

variable {I : Type*}

def DirectedCycle.calendar (d : DirectedCycle F) (owner : J ↪ I) : Calendar I where
  actor t := owner (d.reverse (t+1)).outgoing
  prob t := d.stepSize (d.revIndex (t+1))

private theorem calendar_period_actor (d : DirectedCycle F) (owner : J ↪ I) (t : ℕ) :
    (d.calendar owner).actor (t+d.length) = (d.calendar owner).actor t := by
  simp [DirectedCycle.calendar, DirectedCycle.reverse, DirectedCycle.revIndex,
    show t+d.length+1 = (t+1)+d.length by omega]

private theorem calendar_period_prob (d : DirectedCycle F) (owner : J ↪ I) (t : ℕ) :
    (d.calendar owner).prob (t+d.length) = (d.calendar owner).prob t := by
  simp [DirectedCycle.calendar, DirectedCycle.revIndex,
    show t+d.length+1 = (t+1)+d.length by omega]

private theorem calendar_prob_mod (d : DirectedCycle F) (owner : J ↪ I) (t : ℕ) :
    (d.calendar owner).prob (t % d.length) = (d.calendar owner).prob t := by
  simp only [DirectedCycle.calendar, DirectedCycle.revIndex]
  congr 2
  rw [Nat.add_mod (t % d.length), Nat.mod_mod, ← Nat.add_mod]

private theorem reverse_mod (d : DirectedCycle F) (t : ℕ) :
    d.reverse (t % d.length) = d.reverse t := by simp [DirectedCycle.reverse, DirectedCycle.revIndex]

private theorem rival_opportunity [DecidableEq I] (d : DirectedCycle F) (owner : J ↪ I) (i : I) :
    ∃ t < d.length, 0 < rival (d.calendar owner) i t := by
  have hd : (d.calendar owner).actor 0 ≠ (d.calendar owner).actor 1 := by
    change owner (d.reverse (0+1)).outgoing ≠ owner (d.reverse (1+1)).outgoing
    have he := (d.reverse_step 1).owner
    rw [← he]
    exact fun h ↦ (d.reverse 1).distinct (owner.injective h).symm
  by_cases h : (d.calendar owner).actor 0 = i
  · have h' : (d.calendar owner).actor 1 ≠ i := fun he ↦ hd (h.trans he.symm)
    exact ⟨1, d.length_gt_one, by rw [rival, ite_eq_right h']; exact (d.reverse_step 1).pos⟩
  · exact ⟨0, d.length_pos, by rw [rival, ite_eq_right h]; exact (d.reverse_step 0).pos⟩

private theorem finite_upper_bound {A : Type*} [Fintype A] (f : A → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a, f a ≤ C := by
  refine ⟨∑ a, |f a|, Finset.sum_nonneg (fun a _ ↦ abs_nonneg _), ?_⟩
  exact fun a ↦ (le_abs_self _).trans
    (Finset.single_le_sum (fun a _ ↦ abs_nonneg (f a)) (Finset.mem_univ a))

/-- A directed boundary cycle implements a uniform payoff. The marked players
own the faces. Other players only need their solo prize to be bounded by their
payoff at every marked site. -/
theorem DirectedCycle.hasUniformPayoff [Fintype I] [DecidableEq I]
    (d : DirectedCycle F) (g : Game I)
    (owner : J ↪ I) (b : I → ℝ) (a : I → E →ₗ[ℝ] ℝ)
    (rows : ∀ j, a (owner j) = F.row j)
    (prize : ∀ i j, b i + a i (F.site j) = g.prize {owner j} i)
    (absent : ∀ i, (∀ j, owner j ≠ i) → ∀ j, g.prize {i} i ≤ g.prize {owner j} i) :
    ∃ u, HasUniformPayoff g u := by
  classical
  let p := d.calendar owner
  let v t i := b i + a i (d.reverse t).point
  have recurrence (t : ℕ) (i : I) :
      (1-p.prob t)*v (t+1) i + p.prob t*g.prize {p.actor t} i = v t i := by
    have hs := (d.reverse_step t).point
    change (1-p.prob t)*(b i+a i (d.reverse (t+1)).point) +
      p.prob t*g.prize {owner (d.reverse (t+1)).outgoing} i =
        b i+a i (d.reverse t).point
    rw [hs, ← prize]
    simp only [Faces.mix, map_add, map_smul, smul_eq_mul]
    change (1-p.prob t)*(b i+a i (d.reverse (t+1)).point) +
      p.prob t*(b i+a i (F.site (d.reverse (t+1)).outgoing)) =
        b i+((1-p.prob t)*a i (d.reverse (t+1)).point +
          p.prob t*a i (F.site (d.reverse (t+1)).outgoing))
    ring
  have marked (t : ℕ) (j : J) : v t (owner j) - g.prize {owner j} (owner j) =
      F.slack j (d.reverse t).point := by
    dsimp [v, Faces.slack]
    rw [← prize, rows, map_sub]
    ring
  have htie (t : ℕ) : v (t+1) (p.actor t) = g.prize {p.actor t} (p.actor t) := by
    exact sub_eq_zero.mp ((marked (t+1) (d.reverse (t+1)).outgoing).trans
      (d.reverse (t+1)).on_outgoing)
  have hmod (t : ℕ) (i : I) : v (t % d.length) i = v t i := by
    dsimp [v]
    rw [reverse_mod]
  have hir (t : ℕ) (i : I) : g.prize {i} i ≤ v t i := by
    by_cases hi : ∃ j, owner j = i
    · obtain ⟨j, rfl⟩ := hi
      exact sub_nonneg.mp ((marked t j).symm ▸ (d.reverse t).feasible j)
    · have hno : ∀ j, owner j ≠ i := fun j h ↦ hi ⟨j, h⟩
      obtain ⟨k, hk, hmin⟩ := Finset.exists_min_image (Finset.range d.length)
        (fun s ↦ v s i) ⟨0, Finset.mem_range.mpr d.length_pos⟩
      have hnext : v k i ≤ v (k+1) i := by
        rw [← hmod (k+1) i]
        exact hmin _ (Finset.mem_range.mpr (Nat.mod_lt _ d.length_pos))
      have hq := d.reverse_step k
      have hl : (1-p.prob k)*v k i ≤ (1-p.prob k)*v (k+1) i :=
        mul_le_mul_of_nonneg_left hnext (sub_nonneg.mpr hq.lt_one.le)
      have hpos : 0 < p.prob k := hq.pos
      have hmul : p.prob k * (g.prize {p.actor k} i - v k i) ≤ 0 := by
        linarith only [recurrence k i, hl]
      have hn : g.prize {p.actor k} i ≤ v k i := by
        by_contra! H
        exact (not_lt_of_ge hmul) (mul_pos hpos (sub_pos.mpr H))
      have hpr := absent i hno (d.reverse (k+1)).outgoing
      have hmin' := hmin (t % d.length) (Finset.mem_range.mpr (Nat.mod_lt _ d.length_pos))
      rw [hmod] at hmin'
      exact hpr.trans (hn.trans hmin')
  obtain ⟨k, _, hmax⟩ := Finset.exists_max_image (Finset.range d.length) p.prob
    ⟨0, Finset.mem_range.mpr d.length_pos⟩
  let β := p.prob k
  have hβ : ∀ t, 0 ≤ p.prob t ∧ p.prob t ≤ β := by
    intro t
    refine ⟨(d.reverse_step t).pos.le, ?_⟩
    rw [← calendar_prob_mod d owner t]
    exact hmax _ (Finset.mem_range.mpr (Nat.mod_lt _ d.length_pos))
  obtain ⟨M, hM, hbound⟩ := finite_upper_bound
    (fun z : Fin d.length × I ↦ |g.live z.2 - v z.1.val z.2|)
  obtain ⟨C, hC, hcollision⟩ := finite_upper_bound
    (fun z : I × I ↦ g.prize {z.1,z.2} z.1 - g.prize {z.1} z.1)
  refine ⟨v 0, periodic_calendar_uniform_payoff g p v (hβ k).1 (d.reverse_step k).lt_one
    hM hC hβ (calendar_period_actor d owner) (calendar_period_prob d owner)
    (rival_opportunity d owner) recurrence htie hir ?_ (fun i j ↦ hcollision (i,j))⟩
  intro t i
  rw [← hmod t i]
  exact hbound (⟨t % d.length, Nat.mod_lt _ d.length_pos⟩, i)

#print axioms DirectedCycle.hasUniformPayoff

/-- A feasible regular face system with infeasible sites and no sink yields
a uniform payoff in the quitting game that it represents. -/
theorem uniform_of_feasible_no_sink [Fintype J] [Nonempty J] [Fintype I] [DecidableEq I]
    (hreg : RegularFaces F) (feasible : ∃ x, F.Feasible x)
    (sites : ∀ j, ∃ k, F.slack k (F.site j) < 0) (noSink : ¬ F.HasSink)
    (g : Game I) (owner : J ↪ I) (b : I → ℝ) (a : I → E →ₗ[ℝ] ℝ)
    (rows : ∀ j, a (owner j) = F.row j)
    (prize : ∀ i j, b i + a i (F.site j) = g.prize {owner j} i)
    (absent : ∀ i, (∀ j, owner j ≠ i) → ∀ j, g.prize {i} i ≤ g.prize {owner j} i) :
    ∃ u, HasUniformPayoff g u := by
  obtain ⟨d⟩ := F.directed_cycle hreg feasible sites noSink
  exact d.hasUniformPayoff g owner b a rows prize absent

#print axioms uniform_of_feasible_no_sink

end

end PlanarQuitting
