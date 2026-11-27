module

public import PlanarQuitting.Independent
public import PlanarQuitting.StationaryGuard
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Verifying a sole quitter with a finite cutoff

A solo quitter normally uses a fixed positive hazard. After a fixed cutoff
on the live history, the profile switches to a rival whose singleton caps
the original quitter's reward. The cutoff and the punishment hazard are
chosen before the horizon threshold.
-/

@[expose] public section

namespace PlanarQuitting

open Filter Set
open scoped BigOperators Topology

noncomputable section

variable {I : Type*} [DecidableEq I]

private def capital (g : Game I) (p : Calendar I) (i : I)
    (q : ℕ → ℝ) (u : ℝ) (t : ℕ) : ℝ :=
  accrued p g i q t + alive p i q t * u

private theorem capital_step (g : Game I) (p : Calendar I) (i : I)
    (q : ℕ → ℝ) (u : ℝ) (t : ℕ) :
    capital g p i q u (t+1) - capital g p i q u t =
      alive p i q t * (q t * (quitReward p g i t - u) +
        (1-q t)*rival p i t*(g.prize {p.actor t} i - u)) := by
  simp only [capital, accrued, alive, remaining, newPrize]
  ring

private theorem alive_drop {p : Calendar I} (hp : Legal p.prob) (i : I)
    {q : ℕ → ℝ} (hq : Legal q) (t : ℕ) :
    alive p i q (t+1) ≤ alive p i q t := by
  have hr := rival_legal hp i t
  have hw : remaining p i q t ≤ 1 := by
    unfold remaining
    exact (mul_le_of_le_one_left (sub_nonneg.mpr hr.2)
      (sub_le_self 1 (hq t).1)).trans (sub_le_self 1 hr.1)
  exact mul_le_of_le_one_right (alive_nonneg hp i hq t) hw

private theorem alive_antitone {p : Calendar I} (hp : Legal p.prob) (i : I)
    {q : ℕ → ℝ} (hq : Legal q) : Antitone (alive p i q) :=
  antitone_nat_of_succ_le (alive_drop hp i hq)

private theorem alive_le_one {p : Calendar I} (hp : Legal p.prob) (i : I)
    {q : ℕ → ℝ} (hq : Legal q) (t : ℕ) : alive p i q t ≤ 1 :=
  alive_antitone hp i hq (Nat.zero_le t)

private theorem capital_between {g : Game I} {p : Calendar I} (hp : Legal p.prob)
    (i : I) {q : ℕ → ℝ} (hq : Legal q) (u lo hi : ℝ) {a b : ℕ} (hab : a ≤ b)
    (bound : ∀ t, a ≤ t → t < b →
      (lo ≤ quitReward p g i t - u ∧ quitReward p g i t - u ≤ hi) ∧
      (lo ≤ g.prize {p.actor t} i - u ∧ g.prize {p.actor t} i - u ≤ hi)) :
    lo * (alive p i q a - alive p i q b) ≤ capital g p i q u b - capital g p i q u a ∧
      capital g p i q u b - capital g p i q u a ≤ hi * (alive p i q a - alive p i q b) := by
  have step (t : ℕ) (ha : a ≤ t) (hb : t < b) :
      lo * (alive p i q t - alive p i q (t+1)) ≤
        capital g p i q u (t+1) - capital g p i q u t ∧
      capital g p i q u (t+1) - capital g p i q u t ≤
        hi * (alive p i q t - alive p i q (t+1)) := by
    obtain ⟨⟨hl,hU⟩,⟨hl',hU'⟩⟩ := bound t ha hb
    have hw : 0 ≤ (1-q t)*rival p i t :=
      mul_nonneg (sub_nonneg.mpr (hq t).2) (rival_legal hp i t).1
    have h₀ := mul_le_mul_of_nonneg_left hl (hq t).1
    have h₁ := mul_le_mul_of_nonneg_left hl' hw
    have h₂ := mul_le_mul_of_nonneg_left hU (hq t).1
    have h₃ := mul_le_mul_of_nonneg_left hU' hw
    have hA := alive_nonneg hp i hq t
    rw [capital_step]
    have he : alive p i q t - alive p i q (t+1) =
        alive p i q t * (q t + (1-q t)*rival p i t) := by
      simp only [alive, remaining]
      ring
    rw [he]
    constructor
    · have h := mul_le_mul_of_nonneg_left (add_le_add h₀ h₁) hA
      linarith only [h]
    · have h := mul_le_mul_of_nonneg_left (add_le_add h₂ h₃) hA
      linarith only [h]
  have all (t : ℕ) (hat : a ≤ t) (htb : t ≤ b) :
      lo * (alive p i q a - alive p i q t) ≤ capital g p i q u t - capital g p i q u a ∧
      capital g p i q u t - capital g p i q u a ≤ hi * (alive p i q a - alive p i q t) := by
    induction t, hat using Nat.le_induction with
    | base => simp
    | succ t ha ih =>
      obtain ⟨h₁,h₂⟩ := step t ha (lt_of_lt_of_le (Nat.lt_succ_self t) htb)
      obtain ⟨h₃,h₄⟩ := ih (Nat.le_of_succ_le htb)
      constructor <;> linarith only [h₁,h₂,h₃,h₄]
  exact all b hab le_rfl

private theorem survival_window {p : Calendar I} (hp : Legal p.prob)
    (i : I) {q : ℕ → ℝ} (hq : Legal q) {r : ℝ} (hr : 0 ≤ r)
    {a b : ℕ} (hab : a ≤ b) (step : ∀ t, a ≤ t → t < b → remaining p i q t ≤ r) :
    alive p i q b ≤ r^(b-a) := by
  have grow (t : ℕ) (ht : a ≤ t) (hb : t ≤ b) : alive p i q t ≤ r^(t-a) := by
    induction t, ht using Nat.le_induction with
    | base => simpa using alive_le_one hp i hq a
    | succ t ha ih =>
      rw [alive, show t+1-a = (t-a)+1 by omega, pow_succ]
      exact mul_le_mul (ih (Nat.le_of_succ_le hb))
        (step t ha (lt_of_lt_of_le (Nat.lt_succ_self t) hb))
        (mul_nonneg (sub_nonneg.mpr (hq t).2) (sub_nonneg.mpr (rival_legal hp i t).2))
        (pow_nonneg hr _)
  exact grow b hab le_rfl

private theorem mean_upper (f : ℕ → ℝ) (u e B : ℝ) (T : ℕ) (he : 0 ≤ e)
    (hB : 0 ≤ B) (early : ∀ t, f t ≤ u+B) (late : ∀ t, T ≤ t → f t ≤ u+e)
    {N : ℕ} (hN : 0 < N) :
    (∑ t ∈ Finset.range N, f t) / N ≤ u + e + B*(T : ℝ)/N := by
  have ht (t : ℕ) : f t ≤ u+e + if t < T then B else 0 := by
    split
    · linarith [early t]
    · linarith [late t (by omega)]
  have hs := Finset.sum_le_sum (s := Finset.range N) fun t _ ↦ ht t
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← Finset.sum_filter] at hs
  have card : ((Finset.range N).filter (· < T)).card ≤ T := by
    calc
      _ ≤ (Finset.range T).card :=
        Finset.card_le_card (fun t h ↦ Finset.mem_range.mpr (Finset.mem_filter.mp h).2)
      _ = T := Finset.card_range T
  have hcast := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr card) hB
  rw [div_le_iff₀ (Nat.cast_pos.mpr hN)]
  have hi : (u + e + B * (T : ℝ) / ↑N) * ↑N = ↑N * u + ↑N * e + ↑T * B := by
    field_simp
  rw [hi]
  linarith only [hs,hcast]

omit [DecidableEq I] in
private theorem game_bound [Fintype I] (g : Game I) (u : I → ℝ) :
    ∃ B : ℝ, 0 < B ∧ (∀ i, |g.live i-u i| ≤ B) ∧ ∀ i A, |g.prize A i-u i| ≤ B := by
  let live := ∑ i, |g.live i-u i|
  let prize := ∑ a : I × Finset I, |g.prize a.2 a.1-u a.1|
  have hl : 0 ≤ live := Finset.sum_nonneg fun i _ ↦ abs_nonneg _
  have hp : 0 ≤ prize := Finset.sum_nonneg fun a _ ↦ abs_nonneg _
  refine ⟨1+live+prize, by linarith, fun i ↦ ?_, fun i A ↦ ?_⟩
  · have h : |g.live i-u i| ≤ live :=
      Finset.single_le_sum (fun j _ ↦ abs_nonneg (g.live j-u j)) (Finset.mem_univ i)
    linarith
  · have h : |g.prize A i-u i| ≤ prize :=
      Finset.single_le_sum (fun a : I × Finset I ↦ fun _ ↦ abs_nonneg (g.prize a.2 a.1-u a.1))
        (Finset.mem_univ (i,A))
    linarith

private theorem all_rewards_bound {g : Game I} {p : Calendar I} (hp : Legal p.prob)
    (u : I → ℝ) {B : ℝ} (hB : ∀ i A, |g.prize A i-u i| ≤ B) (i : I) (t : ℕ) :
    |quitReward p g i t-u i| ≤ B := by
  have h : quitReward p g i t-u i =
      (1-rival p i t)*(g.prize {i} i-u i) +
        rival p i t*(g.prize {i,p.actor t} i-u i) := by
    unfold quitReward
    ring
  rw [h]
  have hr := rival_legal hp i t
  refine (abs_add_le ..).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hr.2), abs_of_nonneg hr.1]
  have ha := mul_le_mul_of_nonneg_left (hB i {i}) (sub_nonneg.mpr hr.2)
  have hb := mul_le_mul_of_nonneg_left (hB i {i,p.actor t}) hr.1
  linarith only [ha,hb]

private theorem honest_capital_step (g : Game I) (p : Calendar I) (i : I)
    (u : ℝ) (t : ℕ) :
    capital g p i (own p i) u (t+1) - capital g p i (own p i) u t =
      alive p i (own p i) t * p.prob t * (g.prize {p.actor t} i-u) := by
  rw [capital_step]
  by_cases h : p.actor t = i <;> simp [own,rival,quitReward,h] <;> ring

private theorem expected_from_capital (g : Game I) (p : Calendar I) (i : I)
    (q : ℕ → ℝ) (u : ℝ) (t : ℕ) :
    stage p g i q t = capital g p i q u (t+1) +
      alive p i q (t+1)*(g.live i-u) := by
  unfold stage capital
  ring

#print axioms capital_between
#print axioms survival_window
#print axioms mean_upper

/-- A sole quitter's prize is a uniform payoff if rival quit incentives
can be made arbitrarily small at the prefix hazard and some rival can
punish the quitter by quitting alone. The prefix hazard need not vanish. -/
theorem uniform_of_solo_cutoff [Fintype I] (g : Game I) (k j : I)
    (safe : j ≠ k ∨ g.live k ≤ g.prize {k} k)
    (punish : g.prize {j} k ≤ g.prize {k} k)
    (prefixHazard : ∀ e : ℝ, 0 < e → ∃ h : ℝ, 0 < h ∧ h ≤ 1 ∧
      ∀ i, i ≠ k →
      (1-h)*g.prize {i} i + h*g.prize {i,k} i ≤ g.prize {k} i + e) :
    HasUniformPayoff g (g.prize {k}) := by
  intro ε hε
  let u := g.prize {k}
  let e := ε/6
  have he : 0 < e := by dsimp [e]; positivity
  obtain ⟨B,hB,hLive,hPrize⟩ := game_bound g u
  let δ := e/(1+2*B)
  have hδ : 0 < δ := div_pos he (by linarith)
  have δsmall : 2*B*δ ≤ e := by
    dsimp [δ]
    rw [← mul_div_assoc, div_le_iff₀ (by linarith : 0 < 1+2*B)]
    linarith only [he]
  obtain ⟨h,hh₀,hh₁,hcomp⟩ := prefixHazard e he
  let η := min (1/2) δ
  have ηpos : 0 < η := lt_min (by norm_num) hδ
  have ηle : η ≤ 1 := (min_le_left ..).trans (by norm_num)
  have ηsmall : B*η ≤ e := by
    have hen := mul_le_mul_of_nonneg_left (min_le_right (1/2 : ℝ) δ) hB.le
    nlinarith only [δsmall,hen,mul_nonneg hB.le hδ.le]
  obtain ⟨H,hH⟩ := eventually_atTop.mp
    ((tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.mpr hh₁)
      (by linarith : 1-h < 1)).eventually_lt_const hδ)
  obtain ⟨D,hD⟩ := eventually_atTop.mp
    ((tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.mpr ηle)
      (by linarith : 1-η < 1)).eventually_lt_const hδ)
  let p : Calendar I := ⟨fun t ↦ if t < H then k else j, fun t ↦ if t < H then h else η⟩
  have hp : Legal p.prob := by
    intro t
    by_cases ht : t < H
    · simpa [p,ht] using And.intro hh₀.le hh₁
    · simpa [p,ht] using And.intro ηpos.le ηle
  have prefUpper (t : ℕ) (ht : t < H) (i : I) : quitReward p g i t - u i ≤ e := by
    by_cases hi : i = k
    · subst i
      simp [quitReward,rival,p,ht,u,he.le]
    · have h := hcomp i hi
      simp [quitReward,rival,p,ht,Ne.symm hi]
      linarith
  have tailUpper (t : ℕ) (ht : H ≤ t) : quitReward p g k t - u k ≤ e := by
    by_cases hjk : j = k
    · simp [quitReward,rival,p,not_lt.mpr ht,hjk,u,he.le]
    have hlep : g.prize {k,j} k - u k ≤ B := (abs_le.mp (hPrize k {k,j})).2
    have heq : quitReward p g k t-u k = η*(g.prize {k,j} k-u k) := by
      simp [quitReward,rival,p,not_lt.mpr ht,hjk,u]
      ring
    rw [heq]
    exact (mul_le_mul_of_nonneg_left hlep ηpos.le).trans (mul_comm η B ▸ ηsmall)
  let A (i : I) (q : ℕ → ℝ) := alive p i q
  let C (i : I) (q : ℕ → ℝ) := capital g p i q (u i)
  have diff_bound (i : I) (q : ℕ → ℝ) (hq : Legal q) {a b : ℕ} (hab : a ≤ b) :
      |C i q b-C i q a| ≤ B*(A i q a-A i q b) := by
    apply abs_le.mpr
    have h := capital_between hp i hq (u i) (-B) B hab
      (fun t _ _ ↦ ⟨abs_le.mp (all_rewards_bound hp u hPrize i t),
        abs_le.mp (hPrize i {p.actor t})⟩)
    exact ⟨by linarith only [h.1], h.2⟩
  have default0 (i : I) (q : ℕ → ℝ) : C i q 0 = u i := by simp [C,capital,alive,accrued]
  have early (i : I) (q : ℕ → ℝ) (hq : Legal q) (t : ℕ) :
      |stage p g i q t - u i| ≤ 2*B := by
    have hh := diff_bound i q hq (Nat.zero_le (t+1))
    rw [default0] at hh
    have hb' : |C i q (t+1)-u i| ≤ B :=
      hh.trans (by
        change B * (1 - A i q (t+1)) ≤ B
        nlinarith only [mul_nonneg hB.le (alive_nonneg hp i hq (t+1))])
    have hl : |A i q (t+1) * (g.live i - u i)| ≤ B := by
      rw [abs_mul, abs_of_nonneg (alive_nonneg hp i hq (t+1))]
      exact (mul_le_of_le_one_left (abs_nonneg _) (alive_le_one hp i hq (t+1))).trans (hLive i)
    rw [expected_from_capital g p i q (u i)]
    change |C i q (t+1) + A i q (t+1) * (g.live i-u i) - u i| ≤ _
    rw [show C i q (t+1) + A i q (t+1) * (g.live i-u i)-u i =
      (C i q (t+1)-u i) + A i q (t+1) * (g.live i-u i) by ring]
    exact (abs_add_le ..).trans (by linarith only [hb',hl])
  have preCap (i : I) (q : ℕ → ℝ) (hq : Legal q) :
      C i q H ≤ u i + e := by
    have h := (capital_between hp i hq (u i) (-B) e (Nat.zero_le H) (fun t _ ht ↦
      ⟨⟨(abs_le.mp (all_rewards_bound hp u hPrize i t)).1, prefUpper t ht i⟩,
        by simp [p,ht,u,hB.le,he.le]⟩)).2
    change C i q H - C i q 0 ≤ e*(1-A i q H) at h
    rw [default0] at h
    linarith only [h,mul_nonneg he.le (alive_nonneg hp i hq H)]
  have ownCap (i : I) (t : ℕ) (ht : t ≤ H) : C i (own p i) t = u i := by
    induction t with
    | zero => exact default0 i (own p i)
    | succ t ih =>
      have ht' : t < H := by omega
      have h := honest_capital_step g p i (u i) t
      change C i (own p i) (t+1) - C i (own p i) t = _ at h
      simp only [p,ht',ite_true,u,sub_self,mul_zero] at h
      rw [ih (by omega)] at h
      linarith
  have ownSurv (i : I) : A i (own p i) H ≤ δ := by
    have h' := survival_window hp i (own_legal hp i) (sub_nonneg.mpr hh₁)
      (Nat.zero_le H) (fun t _ ht ↦ show remaining p i (own p i) t ≤ 1-h from by
        by_cases hi : k = i <;> simp [remaining,own,rival,p,ht,hi])
    simpa using h'.trans (by simpa using (hH H le_rfl).le)
  have otherSurv (i : I) (hi : i ≠ k) (q : ℕ → ℝ) (hq : Legal q) : A i q H ≤ δ := by
    have h' := survival_window hp i hq (sub_nonneg.mpr hh₁) (Nat.zero_le H)
      (fun t _ ht ↦ by
        simp only [remaining,rival,p,ht,ite_true,ite_eq_right (Ne.symm hi)]
        exact mul_le_of_le_one_left (sub_nonneg.mpr hh₁) (sub_le_self _ (hq t).1))
    simpa using h'.trans (by simpa using (hH H le_rfl).le)
  let T := H+D
  have late_hon (i : I) (t : ℕ) (ht : T ≤ t) :
      |stage p g i (own p i) t-u i| ≤ e := by
    have hq := own_legal hp i
    have hb' := diff_bound i (own p i) hq (show H ≤ t+1 by dsimp [T] at ht; omega)
    rw [ownCap i H le_rfl] at hb'
    have hc : |C i (own p i) (t+1)-u i| ≤ B*δ :=
      hb'.trans (mul_le_mul_of_nonneg_left (by
        have ha := alive_nonneg hp i hq (t+1)
        linarith only [ha,ownSurv i]) hB.le)
    have hs : A i (own p i) (t+1) ≤ δ :=
      (alive_antitone hp i hq (show H ≤ t+1 by dsimp [T] at ht; omega)).trans (ownSurv i)
    have hl : |A i (own p i) (t+1)*(g.live i-u i)| ≤ B*δ := by
      rw [abs_mul,abs_of_nonneg (alive_nonneg hp i hq (t+1)),mul_comm B δ]
      exact mul_le_mul hs (hLive i) (abs_nonneg _) hδ.le
    rw [expected_from_capital g p i (own p i) (u i)]
    change |C i (own p i) (t+1) + A i (own p i) (t+1)*(g.live i-u i)-u i| ≤ _
    rw [show C i (own p i) (t+1)+A i (own p i) (t+1)*(g.live i-u i)-u i =
      (C i (own p i) (t+1)-u i)+A i (own p i) (t+1)*(g.live i-u i) by ring]
    exact (abs_add_le ..).trans (by linarith only [hc,hl,δsmall])
  have late_dev (i : I) (q : ℕ → ℝ) (hq : Legal q) (t : ℕ) (ht : T ≤ t) :
      stage p g i q t ≤ u i + 2*e := by
    have Hle : H ≤ t+1 := by dsimp [T] at ht; omega
    have liveSmall (i : I) (hs : A i q (t+1) ≤ δ) :
        A i q (t+1)*(g.live i-u i) ≤ B*δ :=
      (mul_le_mul_of_nonneg_left ((abs_le.mp (hLive i)).2) (alive_nonneg hp i hq (t+1))).trans
        (by simpa only [mul_comm] using mul_le_mul_of_nonneg_right hs hB.le)
    have both : C i q (t+1) ≤ u i + e + B*δ ∧
        A i q (t+1)*(g.live i-u i) ≤ B*δ := by
      by_cases hi : i = k
      · subst i
        have h' := (capital_between hp k hq (u k) (-B) e (Nat.zero_le (t+1)) (fun s _ _ ↦ by
          refine ⟨⟨(abs_le.mp (all_rewards_bound hp u hPrize k s)).1, ?_⟩,
            ⟨(abs_le.mp (hPrize k {p.actor s})).1, ?_⟩⟩
          · by_cases hs : s < H
            · exact prefUpper s hs k
            · exact tailUpper s (le_of_not_gt hs)
          · by_cases hs : s < H
            · simp [p,hs,u,he.le]
            · simp only [p,hs,ite_false,u]
              linarith only [punish,he])).2
        change C k q (t+1)-C k q 0 ≤ e*(1-A k q (t+1)) at h'
        rw [default0] at h'
        refine ⟨by linarith only [h',mul_nonneg he.le (alive_nonneg hp k hq (t+1)),
          mul_nonneg hB.le hδ.le], ?_⟩
        rcases safe with hjk | hs
        · have hstay := survival_window hp k hq (sub_nonneg.mpr ηle) Hle (fun s hs _ ↦ by
            simp only [remaining,rival,p,not_lt.mpr hs,ite_false,ite_eq_right hjk]
            exact mul_le_of_le_one_left (sub_nonneg.mpr ηle) (sub_le_self _ (hq s).1))
          exact liveSmall k (hstay.trans (hD _ (by dsimp [T] at ht; omega)).le)
        · exact (mul_nonpos_of_nonneg_of_nonpos (alive_nonneg hp k hq (t+1))
            (sub_nonpos.mpr hs)).trans (mul_nonneg hB.le hδ.le)
      · have hs := otherSurv i hi q hq
        have hc := (abs_le.mp (diff_bound i q hq Hle)).2
        have ha := alive_nonneg hp i hq (t+1)
        exact ⟨by
          have hh : B*(A i q H-A i q (t+1)) ≤ B*δ :=
            mul_le_mul_of_nonneg_left (by linarith only [hs,ha]) hB.le
          linarith only [hc,hh,preCap i q hq],
          liveSmall i ((alive_antitone hp i hq Hle).trans hs)⟩
    rw [expected_from_capital g p i q (u i)]
    change C i q (t+1)+A i q (t+1)*(g.live i-u i) ≤ _
    linarith only [both.1,both.2,δsmall]
  obtain ⟨L,hL⟩ := exists_nat_gt (2*B*(T : ℝ)/e)
  refine ⟨p.profile,L+1,fun i ↦ own_legal hp i,by omega,?_⟩
  intro N hN i
  have hN₀ : 0 < N := by omega
  have hsmall : 2*B*(T : ℝ)/N ≤ e := by
    have hcast : (L : ℝ) ≤ N := Nat.cast_le.mpr (by omega)
    have hh := (div_lt_iff₀ he).1 (hL.trans_le hcast)
    exact (div_le_iff₀ (Nat.cast_pos.mpr hN₀)).2 (by linarith)
  have honest : expectedAverage g p.profile i N = average p g i (own p i) N := by
    have rev : p.profile.revise i (own p i) = p.profile := by
      funext t j
      by_cases hj : j = i
      · subst j; simp [Profile.revise,Calendar.profile]
      · simp [Profile.revise,hj]
    rw [← rev,revised_average]
  have high := mean_upper (stage p g i (own p i)) (u i) e (2*B) T he.le (by positivity)
    (fun t ↦ by linarith only [(abs_le.mp (early i _ (own_legal hp i) t)).2])
    (fun t ht ↦ by linarith only [(abs_le.mp (late_hon i t ht)).2]) hN₀
  have low := mean_upper (fun t ↦ -stage p g i (own p i) t) (-u i) e (2*B) T he.le
    (by positivity)
    (fun t ↦ by linarith only [(abs_le.mp (early i _ (own_legal hp i) t)).1])
    (fun t ht ↦ by linarith only [(abs_le.mp (late_hon i t ht)).1]) hN₀
  simp only [Finset.sum_neg_distrib,neg_div] at low
  change -average p g i (own p i) N ≤ -u i+e+2*B*(T : ℝ)/N at low
  change average p g i (own p i) N ≤ u i+e+2*B*(T : ℝ)/N at high
  rw [honest]
  change |average p g i (own p i) N-u i| ≤ ε ∧ _
  refine ⟨abs_le.mpr ⟨?_,?_⟩,fun q hq ↦ ?_⟩
  · dsimp [e] at *
    linarith only [low,hsmall,hε]
  · dsimp [e] at *
    linarith only [high,hsmall,hε]
  · rw [revised_average]
    have hd := mean_upper (stage p g i q) (u i) (2*e) (2*B) T (by positivity) (by positivity)
      (fun t ↦ by linarith only [(abs_le.mp (early i q hq t)).2]) (late_dev i q hq) hN₀
    change average p g i q N ≤ _ at hd
    dsimp [e] at *
    linarith only [low,hsmall,hd,hε]

#print axioms uniform_of_solo_cutoff

/-- A solo prize that covers all rival solo payoffs can be implemented with
arbitrarily small prefix hazards. A safe live payoff also suffices for the
solo actor, since even a deviation suppressing absorption is bounded. -/
theorem uniform_of_solo_dominance [Fintype I] (g : Game I) (k j : I)
    (safe : j ≠ k ∨ g.live k ≤ g.prize {k} k)
    (punish : g.prize {j} k ≤ g.prize {k} k)
    (rivals : ∀ i, i ≠ k → g.prize {i} i ≤ g.prize {k} i) :
    HasUniformPayoff g (g.prize {k}) := by
  apply uniform_of_solo_cutoff g k j safe punish
  intro e he
  obtain ⟨B,hB,_,hpr⟩ := game_bound g (g.prize {k})
  let h := min (1/2) (e/(1+B))
  have hp : 0 < h := lt_min (by norm_num) (div_pos he (by linarith))
  have hu : h ≤ 1 := (min_le_left ..).trans (by norm_num)
  have small : h*B ≤ e := by
    have hh := mul_le_mul_of_nonneg_right (min_le_right (1/2 : ℝ) (e/(1+B))) hB.le
    rw [div_mul_eq_mul_div] at hh
    exact hh.trans ((div_le_iff₀ (by linarith : 0 < 1+B)).2 (by linarith only [he]))
  refine ⟨h,hp,hu,fun i hi ↦ ?_⟩
  have h₁ := mul_le_mul_of_nonneg_left (rivals i hi) (sub_nonneg.mpr hu)
  have h₂ := mul_le_mul_of_nonneg_left ((abs_le.mp (hpr i {i,k})).2) hp.le
  linarith only [h₁,h₂,small]

/-- If the live payoff covers the player's own solo prize for every player,
permanent continuation is a uniform payoff. -/
theorem uniform_of_wait [Fintype I] (g : Game I)
    (no_gain : ∀ i, g.prize {i} i ≤ g.live i) : HasUniformPayoff g g.live := by
  intro ε hε
  let profile : Profile I := fun _ _ ↦ 0
  refine ⟨profile,1,fun _ _ ↦ by norm_num,le_rfl,?_⟩
  intro N hN i
  let p : Calendar I := ⟨fun _ ↦ i,fun _ ↦ 0⟩
  have legal : Legal p.prob := fun _ ↦ by simp [p]
  have hprofile : p.profile = profile := by funext t j; by_cases h : i = j <;> simp [Calendar.profile,own,p,profile,h]
  have hquit (t : ℕ) : quitReward p g i t = g.prize {i} i := by simp [p,rival,quitReward]
  have hone (t : ℕ) : alive p i (own p i) t = 1 := by
    induction t with
    | zero => rfl
    | succ t ih => simp [alive,ih,remaining,own,rival,p]
  have ha (t : ℕ) : accrued p g i (own p i) t = 0 := by
    induction t with
    | zero => rfl
    | succ t ih => simp [accrued,ih,newPrize,own,rival,p]
  have honest : expectedAverage g profile i N = g.live i := by
    have hrev : p.profile.revise i (own p i) = profile := by
      funext t j
      by_cases hj : j = i <;> simp [Profile.revise,Calendar.profile,own,p,profile,hj]
    rw [← hrev,revised_average]
    have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simp [average,stage,ha,hone,hn]
  rw [honest]
  refine ⟨by simpa using hε.le,fun q hq ↦ ?_⟩
  rw [← hprofile,revised_average]
  have hcap (t : ℕ) : capital g p i q (g.live i) t ≤ g.live i := by
    induction t with
    | zero => simp [capital,accrued,alive]
    | succ t ih =>
      have he := capital_step g p i q (g.live i) t
      simp only [hquit,rival,p,ite_true,mul_zero,zero_mul,add_zero] at he
      have hn := mul_nonpos_of_nonneg_of_nonpos (alive_nonneg legal i hq t)
        (mul_nonpos_of_nonneg_of_nonpos (hq t).1 (sub_nonpos.mpr (no_gain i)))
      linarith only [ih,he,hn]
  have hstage (t : ℕ) : stage p g i q t ≤ g.live i := by
    rw [expected_from_capital g p i q (g.live i),sub_self,mul_zero,add_zero]
    exact hcap _
  have hh := Finset.sum_le_sum (s := Finset.range N) fun t _ ↦ hstage t
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hh
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  exact ((div_le_iff₀ hn).2 (by linarith only [hh])).trans (le_add_of_nonneg_right hε.le)

#print axioms uniform_of_solo_dominance
#print axioms uniform_of_wait

end

end PlanarQuitting
