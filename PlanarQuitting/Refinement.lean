module

public import PlanarQuitting.Volunteer
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecificLimits.Basic
import Lean.Elab.Tactic.Omega

/-!
# Dividing the edges of a quitting calendar

Bisect each step into two steps by the same player. The product of the two new
survival probabilities is the original survival probability. Bisection fixes
the initial promise and uniformly shrinks the hazards. A complete payoff and
deviation bound then follows from the calendar certificate.
-/

@[expose] public section

namespace PlanarQuitting

open scoped BigOperators
open Filter

noncomputable section

variable {I : Type*}

/-- A calendar whose promised continuations satisfy the waiting and solo-quitting
comparisons, before any errors from simultaneous quitting are charged. -/
structure Refinable [DecidableEq I] (g : Game I) (p : Calendar I) (v : ℕ → I → ℝ)
    (β M K : ℝ) : Prop where
  prob : ∀ t, 0 ≤ p.prob t ∧ p.prob t ≤ β
  recurrence : ∀ t i,
    (1 - p.prob t) * v (t + 1) i + p.prob t * g.prize {p.actor t} i = v t i
  tie : ∀ t, v (t + 1) (p.actor t) = g.prize {p.actor t} (p.actor t)
  ir : ∀ t i, g.prize {i} i ≤ v t i
  bound_nonneg : 0 ≤ M
  live_bound : ∀ t i, |g.live i - v t i| ≤ M
  survival_sum : ∀ N i, (∑ t ∈ Finset.range N, alive p i (fun _ ↦ 0) (t + 1)) ≤ K

def halfHazard (x : ℝ) : ℝ := 1 - Real.sqrt (1 - x)

theorem halfHazard_sq {x : ℝ} (hx : x ≤ 1) :
    (1 - halfHazard x)^2 = 1 - x := by
  have hs : 1 - halfHazard x = Real.sqrt (1 - x) := by unfold halfHazard; ring
  rw [hs, Real.sq_sqrt (sub_nonneg.mpr hx)]

theorem halfHazard_nonneg {x : ℝ} (hx : 0 ≤ x) (hx₁ : x ≤ 1) : 0 ≤ halfHazard x := by
  have hsq := Real.sq_sqrt (sub_nonneg.mpr hx₁)
  have hs := Real.sqrt_nonneg (1 - x)
  unfold halfHazard
  nlinarith

theorem halfHazard_le {x β : ℝ} (hx : 0 ≤ x) (hxβ : x ≤ β) (hβ : β < 1) :
    halfHazard x ≤ x / (2 - β) := by
  let y := halfHazard x
  have hy0 : 0 ≤ y := halfHazard_nonneg hx (hxβ.trans hβ.le)
  have hy1 : y ≤ 1 := by
    dsimp [y, halfHazard]
    linarith [Real.sqrt_nonneg (1 - x)]
  have hx' : x = y * (2 - y) := by
    have hsq : (1 - y)^2 = 1 - x := halfHazard_sq (hxβ.trans hβ.le)
    nlinarith
  have hyx : y ≤ x := by
    nlinarith [mul_nonneg hy0 (sub_nonneg.mpr hy1)]
  apply (le_div_iff₀ (show 0 < 2 - β by linarith)).mpr
  exact (mul_le_mul_of_nonneg_left (sub_le_sub_left (hyx.trans hxβ) 2) hy0).trans hx'.symm.le

def bisect (p : Calendar I) : Calendar I where
  actor t := p.actor (t / 2)
  prob t := halfHazard (p.prob (t / 2))

def bisectPromise (g : Game I) (p : Calendar I) (v : ℕ → I → ℝ) (t : ℕ) (i : I) : ℝ :=
  if t % 2 = 0 then v (t / 2) i
  else (1 - halfHazard (p.prob (t / 2))) * v (t / 2 + 1) i +
    halfHazard (p.prob (t / 2)) * g.prize {p.actor (t / 2)} i

@[simp] theorem bisect_actor_even (p : Calendar I) (t : ℕ) :
    (bisect p).actor (2*t) = p.actor t := by simp [bisect, show (2*t)/2 = t by omega]

@[simp] theorem bisect_actor_odd (p : Calendar I) (t : ℕ) :
    (bisect p).actor (2*t+1) = p.actor t := by simp [bisect, show (2*t+1)/2 = t by omega]

@[simp] theorem bisect_prob_even (p : Calendar I) (t : ℕ) :
    (bisect p).prob (2*t) = halfHazard (p.prob t) := by
  simp [bisect, show (2*t)/2 = t by omega]

@[simp] theorem bisect_prob_odd (p : Calendar I) (t : ℕ) :
    (bisect p).prob (2*t+1) = halfHazard (p.prob t) := by
  simp [bisect, show (2*t+1)/2 = t by omega]

@[simp] theorem bisectPromise_even (g : Game I) (p : Calendar I) (v : ℕ → I → ℝ)
    (t : ℕ) (i : I) : bisectPromise g p v (2*t) i = v t i := by
  simp [bisectPromise, show (2*t)/2 = t by omega, show (2*t)%2 = 0 by omega]

@[simp] theorem bisectPromise_odd (g : Game I) (p : Calendar I) (v : ℕ → I → ℝ)
    (t : ℕ) (i : I) : bisectPromise g p v (2*t+1) i =
      (1 - halfHazard (p.prob t)) * v (t+1) i + halfHazard (p.prob t) * g.prize {p.actor t} i := by
  simp [bisectPromise, show (2*t+1)/2 = t by omega, show (2*t+1)%2 = 1 by omega]

private theorem nat_even_or_odd (t : ℕ) : ∃ k, t = 2*k ∨ t = 2*k+1 := by
  exact ⟨t/2, by omega⟩

private theorem abs_mix_sub_le {z x y a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hx : |z - x| ≤ M) (hy : |z - y| ≤ M) : |z - ((1-a)*x+a*y)| ≤ M := by
  have he : z - ((1-a)*x+a*y) = (1-a)*(z-x)+a*(z-y) := by ring
  rw [he]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr ha1), abs_of_nonneg ha0]
  nlinarith only [mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr ha1),
    mul_le_mul_of_nonneg_left hy ha0]

variable [DecidableEq I] {g : Game I} {p : Calendar I} {v : ℕ → I → ℝ} {β M K : ℝ}

omit [DecidableEq I] in
private theorem bisect_prob_unit (hp : ∀ t, 0 ≤ p.prob t ∧ p.prob t ≤ 1) :
    Legal (bisect p).prob := by
  intro t
  obtain ⟨k, hk | hk⟩ := nat_even_or_odd t
  all_goals
    rw [hk]
    simp only [bisect_prob_even, bisect_prob_odd]
    refine ⟨halfHazard_nonneg (hp k).1 (hp k).2, ?_⟩
    unfold halfHazard
    linarith [Real.sqrt_nonneg (1 - p.prob k)]

/-- Splitting each live date into two keeps cumulative survival at the original boundaries. -/
theorem bisect_alive (hp : Legal p.prob) (i : I) (t : ℕ) :
    alive (bisect p) i (fun _ ↦ 0) (2*t) = alive p i (fun _ ↦ 0) t := by
  induction t with
  | zero => simp [alive]
  | succ t ih =>
    rw [show 2*(t+1) = (2*t+1)+1 by omega, alive, alive, ih, alive]
    by_cases h : p.actor t = i
    · simp [remaining, rival, h]
    · simp only [remaining, rival, bisect_actor_even, bisect_actor_odd, bisect_prob_even,
        bisect_prob_odd, h, ite_false, sub_zero, one_mul]
      rw [mul_assoc, ← pow_two, halfHazard_sq (hp t).2]

private theorem bisect_alive_between (hp : Legal p.prob) (i : I) (t : ℕ) :
    alive (bisect p) i (fun _ ↦ 0) (2*t+1) ≤ alive p i (fun _ ↦ 0) t := by
  rw [alive, bisect_alive hp]
  have hnon := alive_nonneg hp i (q := fun _ ↦ 0) (by intro k; norm_num) t
  have hremain : remaining (bisect p) i (fun _ ↦ 0) (2*t) ≤ 1 := by
    simp only [remaining, sub_zero, one_mul]
    exact sub_le_self _ (rival_legal (bisect_prob_unit hp) i _).1
  simpa using mul_le_mul_of_nonneg_left hremain hnon

private theorem bisect_sum (h : Refinable g p v β M K) (hβ : β ≤ 1) (i : I) (N : ℕ) :
    (∑ t ∈ Finset.range N, alive (bisect p) i (fun _ ↦ 0) (t+1)) ≤ 2*K + 1 := by
  have hp : Legal p.prob := fun t ↦ ⟨(h.prob t).1, (h.prob t).2.trans hβ⟩
  have hn := fun t ↦ alive_nonneg (bisect_prob_unit hp) i (q := fun _ ↦ 0)
    (by intro k; norm_num) t
  let S := fun t ↦ alive p i (fun _ ↦ 0) t
  let T := fun t ↦ alive (bisect p) i (fun _ ↦ 0) (t+1)
  have hpair (k : ℕ) :
      (∑ t ∈ Finset.range (2*k), T t) ≤ ∑ t ∈ Finset.range k, (S t + S (t+1)) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show 2*(k+1) = (2*k+1)+1 by omega, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ]
      have hodd : T (2*k) ≤ S k := bisect_alive_between hp i k
      have heven : T (2*k+1) = S (k+1) := by
        dsimp [T, S]
        rw [show 2*k+1+1 = 2*(k+1) by omega, bisect_alive hp]
      linarith only [ih, hodd, heven]
  have hstart : (∑ t ∈ Finset.range N, S t) ≤ K+1 := by
    have heq : (∑ t ∈ Finset.range N, S t) + S N =
        S 0 + ∑ t ∈ Finset.range N, S (t+1) := by
      rw [← Finset.sum_range_succ, Finset.sum_range_succ']
      ring
    have hs0 : S 0 = 1 := rfl
    linarith only [heq, hs0, alive_nonneg hp i (q := fun _ ↦ 0) (by intro t; norm_num) N,
      h.survival_sum N i]
  have hsub : (∑ t ∈ Finset.range N, T t) ≤ ∑ t ∈ Finset.range (2*N), T t :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun t _ _ ↦ hn (t+1))
  refine hsub.trans ((hpair N).trans ?_)
  rw [Finset.sum_add_distrib]
  linarith only [hstart, h.survival_sum N i]

/-- Each bisection preserves the promise equations and keeps the total survival bounded. -/
theorem refinable_bisect (h : Refinable g p v β M K) {B : ℝ} (hβB : β ≤ B) (hB : B < 1) :
    Refinable g (bisect p) (bisectPromise g p v) (β/(2-B)) M (2*K+1) := by
  have hp : Legal p.prob := fun t ↦ ⟨(h.prob t).1, (h.prob t).2.trans (hβB.trans hB.le)⟩
  have hh (t : ℕ) : 0 ≤ halfHazard (p.prob t) := halfHazard_nonneg (hp t).1 (hp t).2
  have hh1 (t : ℕ) : halfHazard (p.prob t) ≤ 1 := by
    unfold halfHazard
    linarith [Real.sqrt_nonneg (1-p.prob t)]
  refine ⟨?_, ?_, ?_, ?_, h.bound_nonneg, ?_, ?_⟩
  · intro t
    exact ⟨hh _, (halfHazard_le (hp _).1 ((h.prob _).2.trans hβB) hB).trans
      (div_le_div_of_nonneg_right (h.prob _).2 (by linarith))⟩
  · intro t i
    obtain ⟨k, hk | hk⟩ := nat_even_or_odd t
    · rw [hk]
      simp only [bisect_prob_even, bisect_actor_even, bisectPromise_even, bisectPromise_odd]
      let q := halfHazard (p.prob k)
      change (1-q)*((1-q)*v (k+1) i+q*g.prize {p.actor k} i)+q*g.prize {p.actor k} i = v k i
      calc
        _ = (1-q)^2*v (k+1) i+(1-(1-q)^2)*g.prize {p.actor k} i := by ring
        _ = _ := by
          rw [show (1-q)^2 = 1-p.prob k from halfHazard_sq (hp k).2]
          simpa using h.recurrence k i
    · rw [hk, show 2*k+1+1=2*(k+1) by omega]
      simp only [bisect_prob_odd, bisect_actor_odd, bisectPromise_even, bisectPromise_odd]
  · intro t
    obtain ⟨k, hk | hk⟩ := nat_even_or_odd t
    · rw [hk, bisect_actor_even, bisectPromise_odd, h.tie k]
      ring
    · rw [hk, show 2*k+1+1=2*(k+1) by omega]
      simpa using h.tie k
  · intro t i
    obtain ⟨k, hk | hk⟩ := nat_even_or_odd t
    · rw [hk, bisectPromise_even]
      exact h.ir k i
    · rw [hk, bisectPromise_odd]
      -- The midpoint lies between the two original promises.
      have hn : 0 < 2 - halfHazard (p.prob k) := by linarith [hh1 k]
      let q := halfHazard (p.prob k)
      have hq : 0 ≤ q := hh k
      have hq1 : q ≤ 1 := hh1 k
      have hsq : (1-q)^2 = 1-p.prob k := halfHazard_sq (hp k).2
      have hmix :
          (2-q)*((1-q)*v (k+1) i+q*g.prize {p.actor k} i) =
            (1-q)*v (k+1) i + v k i := by
        have hr := h.recurrence k i
        nlinarith only [hr, congrArg (v (k+1) i * ·) hsq,
          congrArg (g.prize {p.actor k} i * ·) hsq]
      apply le_of_mul_le_mul_left (a := 2-q) _ hn
      rw [hmix]
      nlinarith only [h.ir k i,
        mul_le_mul_of_nonneg_left (h.ir (k+1) i) (sub_nonneg.mpr hq1)]
  · intro t i
    obtain ⟨k, hk | hk⟩ := nat_even_or_odd t
    · rw [hk, bisectPromise_even]
      exact h.live_bound k i
    · rw [hk, bisectPromise_odd]
      let q := halfHazard (p.prob k)
      have hn : 0 < 2 - q := by linarith [hh1 k]
      have hsq : (1-q)^2 = 1-p.prob k := halfHazard_sq (hp k).2
      have hmix : (1-q)*v (k+1) i+q*g.prize {p.actor k} i =
          (1-(2-q)⁻¹)*v (k+1) i + (2-q)⁻¹*v k i := by
        field_simp
        nlinarith only [h.recurrence k i, congrArg (v (k+1) i * ·) hsq,
          congrArg (g.prize {p.actor k} i * ·) hsq]
      rw [hmix]
      have hq1 : q ≤ 1 := hh1 k
      exact abs_mix_sub_le (inv_nonneg.mpr hn.le) ((inv_le_one₀ hn).mpr (by linarith))
        (h.live_bound (k+1) i) (h.live_bound k i)
  · exact fun N i ↦ bisect_sum h (hβB.trans hB.le) i N

private theorem toCertificate (h : Refinable g p v β M K) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    {C e : ℝ} (hC : 0 ≤ C) (he : 0 ≤ e) (hsmall : β * C ≤ e)
    (collision : ∀ i j, g.prize {i, j} i - g.prize {i} i ≤ C) :
    Certificate g p v e M K := by
  refine ⟨fun t ↦ ⟨(h.prob t).1, (h.prob t).2.trans hβ₁⟩, he, h.bound_nonneg,
    h.recurrence, h.tie, ?_, h.live_bound, h.survival_sum⟩
  intro t i
  have hr : 0 ≤ rival p i t ∧ rival p i t ≤ β := by
    by_cases hi : p.actor t = i
    · simp [rival, hi, hβ₀]
    · simpa [rival, hi] using h.prob t
  have hmul := mul_le_mul_of_nonneg_left (collision i (p.actor t)) hr.1
  have hcap := mul_le_mul_of_nonneg_right hr.2 hC
  unfold quitReward
  linarith only [hmul, hcap, hsmall, h.ir t i]

private theorem refine_n (h : Refinable g p v β M K) (hβ₀ : 0 ≤ β) (hβ₁ : β < 1)
    (j : ℕ) :
    ∃ (p' : Calendar I) (v' : ℕ → I → ℝ) (K' : ℝ),
      v' 0 = v 0 ∧ Refinable g p' v' (β * ((2-β)⁻¹)^j) M K' := by
  have hc : 0 ≤ (2-β)⁻¹ := inv_nonneg.mpr (by linarith)
  have hc₁ : (2-β)⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).mpr (by linarith)
  induction j with
  | zero => exact ⟨p, v, K, rfl, by simpa using h⟩
  | succ j ih =>
    obtain ⟨p', v', K', hv', hh⟩ := ih
    have hcap : β * ((2-β)⁻¹)^j ≤ β := by
      simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ hc hc₁) hβ₀
    refine ⟨bisect p', bisectPromise g p' v', 2*K'+1, ?_, ?_⟩
    · funext i
      simpa [bisectPromise] using congrFun hv' i
    · simpa [pow_succ, mul_assoc, div_eq_mul_inv] using refinable_bisect hh hcap hβ₁

/-- A refinable calendar gives a single payoff vector supported at arbitrarily
small tolerances. The horizon threshold is simultaneous over all deviations. -/
theorem uniform_of_refinable (h : Refinable g p v β M K)
    (hβ₀ : 0 ≤ β) (hβ₁ : β < 1) {C : ℝ} (hC : 0 ≤ C)
    (collision : ∀ i j, g.prize {i, j} i - g.prize {i} i ≤ C) :
    ∀ ε : ℝ, 0 < ε → ∃ (p' : Calendar I) (H : ℕ), Legal p'.prob ∧ 1 ≤ H ∧
      ∀ N : ℕ, H ≤ N → ∀ i q, Legal q →
        |average p' g i (own p' i) N - v 0 i| ≤ ε ∧
        average p' g i q N ≤ average p' g i (own p' i) N + ε := by
  apply uniform_of_certificates g (v 0)
  intro e he
  have hc : 0 ≤ (2-β)⁻¹ := inv_nonneg.mpr (by linarith)
  have hc₁ : (2-β)⁻¹ < 1 := (inv_lt_one₀ (by linarith)).mpr (by linarith)
  have ht : Tendsto (fun j : ℕ ↦ (β*C) * ((2-β)⁻¹)^j) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc hc₁).const_mul (β*C)
  obtain ⟨j, hj⟩ := (ht.eventually_lt_const he).exists
  obtain ⟨p', v', K', hv', hh⟩ := refine_n h hβ₀ hβ₁ j
  have hj' : (β * ((2-β)⁻¹)^j) * C ≤ e := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hj.le
  have hcap : β * ((2-β)⁻¹)^j ≤ β := by
    simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ hc hc₁.le) hβ₀
  exact ⟨p', v', M, K', hv', toCertificate hh
    (mul_nonneg hβ₀ (pow_nonneg hc j)) (hcap.trans hβ₁.le) hC he.le hj' collision⟩

#print axioms calendar_bounds
#print axioms uniform_of_refinable

end

end PlanarQuitting
