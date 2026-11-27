module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Uniform incentives for an independent quitting calendar

On each live date a deterministic calendar names one player who may quit. A unilateral
deviator may choose any time-dependent probability of quitting. Before absorption there
is exactly one public history at each date, so these sequences cover all behavioral
deviations. The terminal reward begins at the first quitting date.
-/

@[expose] public section

namespace PlanarQuitting

noncomputable section

open scoped BigOperators

variable {I : Type*} [DecidableEq I]

/-- An ordinary quitting game's live reward and coalition prizes. -/
structure Game (I : Type*) where
  live : I → ℝ
  prize : Finset I → I → ℝ

/-- The only player allowed to mix between quitting and continuing on each live date. -/
structure Calendar (I : Type*) where
  actor : ℕ → I
  prob : ℕ → ℝ

def Legal (q : ℕ → ℝ) : Prop := ∀ t, 0 ≤ q t ∧ q t ≤ 1

variable (p : Calendar I) (g : Game I)

/-- The player's prescribed probability of quitting. -/
def own (i : I) (t : ℕ) : ℝ := if p.actor t = i then p.prob t else 0

/-- The total rival hazard, which comes from at most one rival. -/
def rival (i : I) (t : ℕ) : ℝ := if p.actor t = i then 0 else p.prob t

/-- The expected payoff of quitting now, with independent own and rival choices. -/
def quitReward (i : I) (t : ℕ) : ℝ :=
  (1 - rival p i t) * g.prize {i} i + rival p i t * g.prize {i, p.actor t} i

def remaining (i : I) (q : ℕ → ℝ) (t : ℕ) : ℝ :=
  (1 - q t) * (1 - rival p i t)

/-- Unconditional contribution to the payoff given that the stage is reached live. -/
def newPrize (i : I) (q : ℕ → ℝ) (t : ℕ) : ℝ :=
  q t * quitReward p g i t + (1 - q t) * rival p i t * g.prize {p.actor t} i

def alive (i : I) (q : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | t + 1 => alive i q t * remaining p i q t

def accrued (i : I) (q : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => accrued i q t + alive p i q t * newPrize p g i q t

/-- Expected stage payoff at date `t`, starting at date zero. -/
def stage (i : I) (q : ℕ → ℝ) (t : ℕ) : ℝ :=
  accrued p g i q (t + 1) + alive p i q (t + 1) * g.live i

/-- The expected average payoff over the first `N` stages. -/
def average (i : I) (q : ℕ → ℝ) (N : ℕ) : ℝ :=
  (∑ t ∈ Finset.range N, stage p g i q t) / N

variable {p g}

theorem own_legal (hp : Legal p.prob) (i : I) : Legal (own p i) := by
  intro t
  by_cases h : p.actor t = i
  · simpa [own, h] using hp t
  · simp [own, h]

theorem rival_legal (hp : Legal p.prob) (i : I) : Legal (rival p i) := by
  intro t
  by_cases h : p.actor t = i
  · simp [rival, h]
  · simpa [rival, h] using hp t

theorem alive_nonneg (hp : Legal p.prob) (i : I) {q : ℕ → ℝ} (hq : Legal q) (t : ℕ) :
    0 ≤ alive p i q t := by
  induction t with
  | zero => norm_num [alive]
  | succ t ih =>
    exact mul_nonneg ih (mul_nonneg (sub_nonneg.mpr (hq t).2)
      (sub_nonneg.mpr (rival_legal hp i t).2))

/-- Survival is largest when the deviating player never quits. -/
theorem alive_le_wait (hp : Legal p.prob) (i : I) {q : ℕ → ℝ} (hq : Legal q) (t : ℕ) :
    alive p i q t ≤ alive p i (fun _ ↦ 0) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hw := sub_nonneg.mpr (rival_legal hp i t).2
    have hremain : remaining p i q t ≤ remaining p i (fun _ ↦ 0) t := by
      simpa [remaining] using (mul_le_mul_of_nonneg_right
        (show 1 - q t ≤ 1 by linarith [(hq t).1]) hw)
    exact mul_le_mul ih hremain
      (mul_nonneg (sub_nonneg.mpr (hq t).2) hw)
      (alive_nonneg hp i (by intro t; norm_num) t)

/-- Promise equations and bounded summed survival for a volunteer calendar. -/
structure Certificate (g : Game I) (p : Calendar I) (v : ℕ → I → ℝ)
    (error M K : ℝ) : Prop where
  legal : Legal p.prob
  error_nonneg : 0 ≤ error
  bound_nonneg : 0 ≤ M
  recurrence : ∀ t i,
    (1 - p.prob t) * v (t + 1) i + p.prob t * g.prize {p.actor t} i = v t i
  actor_tie : ∀ t, v (t + 1) (p.actor t) = g.prize {p.actor t} (p.actor t)
  quit_le : ∀ t i, quitReward p g i t ≤ v t i + error
  live_bound : ∀ t i, |g.live i - v t i| ≤ M
  survival_sum : ∀ N i, (∑ t ∈ Finset.range N, alive p i (fun _ ↦ 0) (t + 1)) ≤ K

variable {v : ℕ → I → ℝ} {e M K : ℝ}

theorem wait_eq (h : Certificate g p v e M K) (t : ℕ) (i : I) :
    (1 - rival p i t) * v (t + 1) i + rival p i t * g.prize {p.actor t} i = v t i := by
  by_cases hi : p.actor t = i
  · have ht := h.actor_tie t
    have hr := h.recurrence t i
    rw [hi] at ht hr
    simp only [rival, hi, ite_true, sub_zero, one_mul, zero_mul, add_zero]
    rw [← ht] at hr
    linarith
  · simpa [rival, hi] using h.recurrence t i

theorem honest_step (h : Certificate g p v e M K) (t : ℕ) (i : I) :
    newPrize p g i (own p i) t + remaining p i (own p i) t * v (t + 1) i = v t i := by
  by_cases hi : p.actor t = i
  · have ht := h.actor_tie t
    rw [hi] at ht
    simp only [newPrize, quitReward, remaining, own, rival, hi, ite_true, sub_zero, one_mul,
      zero_mul, add_zero, mul_zero, mul_one]
    rw [← ht]
    have hv := wait_eq h t i
    simp [rival, hi] at hv
    linarith
  · have hv := wait_eq h t i
    simp only [own, hi, ite_false, newPrize, remaining, sub_zero, one_mul, zero_mul, zero_add]
    linarith

theorem honest_account (h : Certificate g p v e M K) (i : I) (t : ℕ) :
    accrued p g i (own p i) t + alive p i (own p i) t * v t i = v 0 i := by
  induction t with
  | zero => simp [accrued, alive]
  | succ t ih =>
    simp only [accrued, alive]
    calc
      _ = accrued p g i (own p i) t + alive p i (own p i) t *
          (newPrize p g i (own p i) t + remaining p i (own p i) t * v (t + 1) i) := by ring
      _ = v 0 i := by rw [honest_step h]; exact ih

/-- The error from excessive value of quitting can be charged only once. -/
theorem deviation_account (h : Certificate g p v e M K) (i : I)
    (q : ℕ → ℝ) (hq : Legal q) (t : ℕ) :
    accrued p g i q t + alive p i q t * v t i ≤ v 0 i + e * (1 - alive p i q t) := by
  induction t with
  | zero => simp [alive, accrued]
  | succ t ih =>
    have halive := alive_nonneg h.legal i hq t
    have hq0 := (hq t).1
    have hq1 := (hq t).2
    have hr0 := (rival_legal h.legal i t).1
    have hquit := mul_le_mul_of_nonneg_left (h.quit_le t i) hq0
    have hstep : newPrize p g i q t + remaining p i q t * v (t + 1) i ≤
        v t i + e * (1 - remaining p i q t) := by
      have heq := congrArg ((1 - q t) * ·) (wait_eq h t i)
      have herr := mul_nonneg h.error_nonneg (mul_nonneg (sub_nonneg.mpr hq1) hr0)
      unfold newPrize remaining
      linarith only [hquit, heq, herr]
    have hs := mul_le_mul_of_nonneg_left hstep halive
    simp only [accrued, alive]
    linarith only [ih, hs]

theorem stage_honest (h : Certificate g p v e M K) (i : I) (t : ℕ) :
    |stage p g i (own p i) t - v 0 i| ≤ M * alive p i (fun _ ↦ 0) (t + 1) := by
  have hq := own_legal h.legal i
  have hs := alive_nonneg h.legal i hq (t + 1)
  have heq : stage p g i (own p i) t - v 0 i =
      alive p i (own p i) (t + 1) * (g.live i - v (t + 1) i) := by
    unfold stage
    linarith only [honest_account h i (t + 1)]
  rw [heq, abs_mul, abs_of_nonneg hs]
  calc
    _ ≤ alive p i (own p i) (t + 1) * M :=
      mul_le_mul_of_nonneg_left (h.live_bound (t + 1) i) hs
    _ ≤ _ := by
      rw [mul_comm M]
      exact mul_le_mul_of_nonneg_right (alive_le_wait h.legal i hq _) h.bound_nonneg

theorem stage_deviation (h : Certificate g p v e M K) (i : I) (q : ℕ → ℝ) (hq : Legal q)
    (t : ℕ) : stage p g i q t ≤ v 0 i + e + M * alive p i (fun _ ↦ 0) (t + 1) := by
  have hs := alive_nonneg h.legal i hq (t + 1)
  have hg := mul_le_mul_of_nonneg_left (le_abs_self (g.live i - v (t + 1) i) |>.trans
    (h.live_bound (t + 1) i)) hs
  have hw := mul_le_mul_of_nonneg_left (alive_le_wait h.legal i hq (t + 1)) h.bound_nonneg
  unfold stage
  linarith only [deviation_account h i q hq (t + 1), hg, hw, mul_nonneg h.error_nonneg hs]

private theorem sum_error_le (h : Certificate g p v e M K) (i : I) (N : ℕ) :
    (∑ t ∈ Finset.range N, M * alive p i (fun _ ↦ 0) (t + 1)) ≤ M * K := by
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (h.survival_sum N i) h.bound_nonneg

/-- Common bounds over every horizon and every unilateral behavioral deviation. -/
theorem calendar_bounds (h : Certificate g p v e M K) (i : I) (q : ℕ → ℝ) (hq : Legal q)
    {N : ℕ} (hN : 0 < N) :
    |average p g i (own p i) N - v 0 i| ≤ M * K / N ∧
      average p g i q N ≤ average p g i (own p i) N + e + 2 * (M * K / N) := by
  have hpos : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hsum : (∑ t ∈ Finset.range N, |stage p g i (own p i) t - v 0 i|) ≤ M * K :=
    (Finset.sum_le_sum (fun t _ ↦ stage_honest h i t)).trans (sum_error_le h i N)
  have hon : |average p g i (own p i) N - v 0 i| ≤ M * K / N := by
    have heq : average p g i (own p i) N - v 0 i =
        ((∑ t ∈ Finset.range N, stage p g i (own p i) t) - (N : ℝ) * v 0 i) / N := by
      unfold average
      field_simp
    rw [heq, abs_div, abs_of_pos hpos]
    apply div_le_div_of_nonneg_right _ hpos.le
    have ht := Finset.abs_sum_le_sum_abs (s := Finset.range N)
      (fun t ↦ stage p g i (own p i) t - v 0 i)
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at ht
    exact ht.trans hsum
  have hdev := Finset.sum_le_sum (s := Finset.range N)
    (fun t _ ↦ stage_deviation h i q hq t)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hdev
  have hdev' : average p g i q N ≤ v 0 i + e + M * K / N := by
    rw [average, div_le_iff₀ hpos]
    calc
      _ ≤ (N : ℝ) * v 0 i + (N : ℝ) * e + M * K :=
        by linarith only [hdev, sum_error_le h i N]
      _ = _ := by field_simp
  exact ⟨hon, by linarith only [hdev', (abs_le.mp hon).1]⟩

/-- A family of certificates with common initial promises and arbitrarily small quitting
errors produces a uniform Nash payoff. Each constructed calendar serves all later horizons. -/
theorem uniform_of_certificates (g : Game I) (u : I → ℝ)
    (build : ∀ e : ℝ, 0 < e → ∃ (p : Calendar I) (v : ℕ → I → ℝ) (M K : ℝ),
      v 0 = u ∧ Certificate g p v e M K) :
    ∀ ε : ℝ, 0 < ε → ∃ (p : Calendar I) (H : ℕ), Legal p.prob ∧ 1 ≤ H ∧
      ∀ N : ℕ, H ≤ N → ∀ i q, Legal q →
        |average p g i (own p i) N - u i| ≤ ε ∧
        average p g i q N ≤ average p g i (own p i) N + ε := by
  intro ε hε
  obtain ⟨p, v, M, K, hv, h⟩ := build (ε / 3) (by linarith)
  obtain ⟨H, hH⟩ := exists_nat_gt (3 * (M * K) / ε)
  refine ⟨p, H + 1, h.legal, Nat.succ_le_succ (Nat.zero_le H), ?_⟩
  intro N hN i q hq
  have hn : 0 < N := (Nat.zero_lt_succ H).trans_le hN
  have hcast : (H : ℝ) ≤ N := Nat.cast_le.mpr ((Nat.le_succ H).trans hN)
  have hsmall : M * K / N ≤ ε / 3 := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr hn)).mpr
    have ht := (div_lt_iff₀ hε).mp (hH.trans_le hcast)
    linarith
  obtain ⟨hpay, hregret⟩ := calendar_bounds h i q hq hn
  rw [hv] at hpay
  exact ⟨by linarith, by linarith⟩

end

end PlanarQuitting
