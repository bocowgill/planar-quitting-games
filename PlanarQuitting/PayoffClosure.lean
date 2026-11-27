module

public import PlanarQuitting.RegularApproximation
import Mathlib.Topology.Sequences
import Mathlib.Tactic.Linarith

/-!
# Stability of uniform payoffs under reward perturbations

The distribution of absorbed and live histories has total probability
one at every date. Thus changing all rewards by at most a fixed amount
changes each finite-horizon average by at most that amount, including
for revised behavioral profiles.
-/

@[expose] public section

namespace PlanarQuitting

open Filter Set
open scoped BigOperators Topology

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] in
theorem Profile.legal_revise {σ : Profile I} (hσ : σ.legal) (i : I)
    {q : ℕ → ℝ} (hq : Legal q) : (σ.revise i q).legal := by
  intro j t
  by_cases h : j = i
  · simpa [Profile.revise,h] using hq t
  · simpa [Profile.revise,h] using hσ j t

private theorem mass_nonneg {σ : Profile I} (hσ : σ.legal) (t : ℕ) (A : Finset I) :
    0 ≤ coalitionProb σ t A := by
  apply Finset.prod_nonneg
  intro i _
  by_cases hi : i ∈ A
  · simp [hi,(hσ i t).1]
  · simp [hi,(hσ i t).2]

private theorem coalition_mass_one (σ : Profile I) (t : ℕ) :
    (∑ A : Finset I, coalitionProb σ t A) = 1 := by
  let w (S A : Finset I) := ∏ i ∈ S, if i ∈ A then σ t i else 1-σ t i
  have h (S : Finset I) : (∑ A ∈ S.powerset, w S A) = 1 := by
    induction S using Finset.induction_on with
    | empty => simp [w]
    | insert i S hnot ih =>
      rw [Finset.sum_powerset_insert hnot]
      have h₁ : (∑ A ∈ S.powerset, w (insert i S) A) =
          (1-σ t i) * ∑ A ∈ S.powerset, w S A := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro A hA
        have hi : i ∉ A := fun h ↦ hnot (Finset.mem_powerset.mp hA h)
        simp [w,Finset.prod_insert,hnot,hi]
      have h₂ : (∑ A ∈ S.powerset, w (insert i S) (insert i A)) =
          σ t i * ∑ A ∈ S.powerset, w S A := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro A _
        simp only [w,Finset.prod_insert hnot,Finset.mem_insert_self,ite_true]
        congr 1
        apply Finset.prod_congr rfl
        intro j hj
        have hj' : j ≠ i := fun e ↦ hnot (e ▸ hj)
        simp [Finset.mem_insert,hj']
      rw [h₁,h₂,ih]
      ring
  have full : (Finset.univ : Finset I).powerset = (Finset.univ : Finset (Finset I)) := by
    ext A
    simp
  simpa only [full,w,coalitionProb] using h (Finset.univ : Finset I)

private theorem cash_mass (σ : Profile I) (t : ℕ) :
    (∑ A : Finset I, if A = ∅ then 0 else coalitionProb σ t A) =
      1 - coalitionProb σ t ∅ := by
  have h := coalition_mass_one σ t
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (∅ : Finset I))] at h
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (∅ : Finset I))]
  simp only [ite_true,add_zero]
  have he : (∑ A ∈ Finset.univ.erase (∅ : Finset I),
      if A = ∅ then 0 else coalitionProb σ t A) =
      ∑ A ∈ Finset.univ.erase (∅ : Finset I), coalitionProb σ t A := by
    apply Finset.sum_congr rfl
    intro A hA
    simp [(Finset.mem_erase.mp hA).1]
  rw [he]
  linarith only [h]

private theorem liveProb_nonneg {σ : Profile I} (hσ : σ.legal) (t : ℕ) :
    0 ≤ liveProb σ t := by
  induction t with
  | zero => exact zero_le_one
  | succ t ih => exact mul_nonneg ih (mass_nonneg hσ t ∅)

/-- For legal profiles the average payoff lies in the same interval
`[-B,B]` as the rewards. The estimate is independent of the horizon. -/
theorem expected_abs_bound (g : Game I) {σ : Profile I} (hσ : σ.legal)
    (i : I) {B : ℝ} (hB : 0 ≤ B) (live : |g.live i| ≤ B)
    (absorbed : ∀ A, |g.prize A i| ≤ B) (N : ℕ) :
    |expectedAverage g σ i N| ≤ B := by
  have hAcc (t : ℕ) : |accruedPrize g σ i t| ≤ B * (1 - liveProb σ t) := by
    induction t with
    | zero => simp [accruedPrize,liveProb]
    | succ t ih =>
      simp only [accruedPrize,liveProb]
      have hmass := cash_mass σ t
      have hcash :
          |∑ A : Finset I, if A = ∅ then 0 else coalitionProb σ t A * g.prize A i| ≤
            B * (1 - coalitionProb σ t ∅) := by
        refine (Finset.abs_sum_le_sum_abs ..).trans ?_
        rw [← hmass,Finset.mul_sum]
        apply Finset.sum_le_sum
        intro A _
        by_cases h : A = ∅
        · simp [h]
        · rw [ite_eq_right h,ite_eq_right h,abs_mul,abs_of_nonneg (mass_nonneg hσ t A),mul_comm B]
          exact mul_le_mul_of_nonneg_left (absorbed A) (mass_nonneg hσ t A)
      refine (abs_add_le ..).trans ?_
      rw [abs_mul,abs_of_nonneg (liveProb_nonneg hσ t)]
      have h := mul_le_mul_of_nonneg_left hcash (liveProb_nonneg hσ t)
      linarith only [ih,h]
  have hStage (t : ℕ) :
      |accruedPrize g σ i (t+1)+liveProb σ (t+1)*g.live i| ≤ B := by
    refine (abs_add_le ..).trans ?_
    rw [abs_mul,abs_of_nonneg (liveProb_nonneg hσ (t+1))]
    have h := mul_le_mul_of_nonneg_left live (liveProb_nonneg hσ (t+1))
    linarith only [hAcc (t+1),h]
  by_cases hN : N = 0
  · simpa [hN,expectedAverage] using hB
  have hpos : 0 < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  rw [expectedAverage,abs_div,abs_of_pos hpos,div_le_iff₀ hpos]
  refine (Finset.abs_sum_le_sum_abs ..).trans ?_
  have hs := Finset.sum_le_sum (s := Finset.range N) fun t _ ↦ hStage t
  simpa [mul_comm B] using hs

/-- The reward sup bound is stable under all signed differences of two
games, since the same independent strategy profile induces the same law. -/
theorem expected_difference_bound (g h : Game I) {σ : Profile I} (hσ : σ.legal)
    (i : I) {d : ℝ} (hd : 0 ≤ d) (live : |g.live i-h.live i| ≤ d)
    (absorbed : ∀ A, |g.prize A i-h.prize A i| ≤ d) (N : ℕ) :
    |expectedAverage g σ i N - expectedAverage h σ i N| ≤ d := by
  let diff : Game I := ⟨fun i ↦ g.live i - h.live i, fun A i ↦ g.prize A i-h.prize A i⟩
  have hAcc (t : ℕ) : accruedPrize diff σ i t = accruedPrize g σ i t-accruedPrize h σ i t := by
    induction t with
    | zero => simp [accruedPrize]
    | succ t ih =>
      have hSum : (∑ A : Finset I, if A = ∅ then 0 else coalitionProb σ t A * diff.prize A i) =
          (∑ A : Finset I, if A = ∅ then 0 else coalitionProb σ t A * g.prize A i) -
          (∑ A : Finset I, if A = ∅ then 0 else coalitionProb σ t A * h.prize A i) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro A _
        by_cases hA : A = ∅ <;> simp [hA,diff,mul_sub]
      simp only [accruedPrize,ih,hSum]
      ring
  have hAvg : expectedAverage diff σ i N = expectedAverage g σ i N-expectedAverage h σ i N := by
    unfold expectedAverage
    rw [← sub_div, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    rw [hAcc]
    dsimp [diff]
    ring
  rw [← hAvg]
  exact expected_abs_bound diff hσ i hd live absorbed N

omit [DecidableEq I] in
private theorem rewards_bounded (g : Game I) :
    ∃ B : ℝ, 0 ≤ B ∧ (∀ i, |g.live i| ≤ B) ∧ ∀ A i, |g.prize A i| ≤ B := by
  let l := ∑ i, |g.live i|
  let a := ∑ p : Finset I × I, |g.prize p.1 p.2|
  have hl : 0 ≤ l := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have ha : 0 ≤ a := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  refine ⟨l+a,add_nonneg hl ha,fun i ↦ ?_,fun A i ↦ ?_⟩
  · have h : |g.live i| ≤ l :=
      Finset.single_le_sum (fun j _ ↦ abs_nonneg (g.live j)) (Finset.mem_univ i)
    linarith
  · have h : |g.prize A i| ≤ a :=
      Finset.single_le_sum
        (fun p : Finset I × I ↦ fun _ ↦ abs_nonneg (g.prize p.1 p.2)) (Finset.mem_univ (A,i))
    linarith

/-- The existence property is closed under uniform approximation of
finite-game rewards. Each final strategy still works at all large horizons. -/
theorem uniform_payoff_of_reward_approximation (g : Game I)
    (approx : ∀ e : ℝ, 0 < e → ∃ (h : Game I) (u : I → ℝ), HasUniformPayoff h u ∧
      (∀ i, |h.live i-g.live i| ≤ e) ∧ ∀ A i, |h.prize A i-g.prize A i| ≤ e) :
    ∃ u, HasUniformPayoff g u := by
  let d (m : ℕ) : ℝ := 1 / ((m : ℝ)+1)
  have dpos (m : ℕ) : 0 < d m := by dsimp [d]; positivity
  have dle (m : ℕ) : d m ≤ 1 := by
    dsimp [d]
    rw [div_le_iff₀ (by positivity : 0 < (m : ℝ)+1),one_mul]
    linarith only [Nat.cast_nonneg (α := ℝ) m]
  choose h u exists_h hLive hAbs using fun m ↦ approx (d m) (dpos m)
  obtain ⟨B,hB,live,absorb⟩ := rewards_bounded g
  have mem (m : ℕ) : u m ∈ Icc (fun _ ↦ -(B+2)) (fun _ ↦ B+2) := by
    obtain ⟨σ,H,hσ,_,check⟩ := exists_h m 1 zero_lt_one
    have hbound (i : I) : |u m i| ≤ B+2 := by
      have h₁ := (check H le_rfl i).1
      have h₂ := expected_difference_bound (h := g) (h m) hσ i (dpos m).le
        (hLive m i) (fun A ↦ hAbs m A i) H
      have h₃ := expected_abs_bound g hσ i hB (live i) (fun A ↦ absorb A i) H
      apply abs_le.mpr
      have hh₁ := abs_le.mp h₁
      have hh₂ := abs_le.mp h₂
      have hh₃ := abs_le.mp h₃
      constructor <;> linarith only [hh₁.1,hh₁.2,hh₂.1,hh₂.2,hh₃.1,hh₃.2,dle m]
    exact ⟨fun i ↦ (abs_le.mp (hbound i)).1,fun i ↦ (abs_le.mp (hbound i)).2⟩
  obtain ⟨v,_,φ,hφ,conv⟩ := isCompact_Icc.isSeqCompact mem
  refine ⟨v,fun ε hε ↦ ?_⟩
  let e := ε/4
  have he : 0 < e := by dsimp [e]; positivity
  have convd : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have eventuallyD : ∀ᶠ k in atTop, d (φ k) < e :=
    (convd.comp hφ.tendsto_atTop).eventually_lt_const he
  have eventuallyU : ∀ᶠ k in atTop, dist (u (φ k)) v < e :=
    (tendsto_iff_dist_tendsto_zero.mp conv).eventually_lt_const he
  obtain ⟨k,hk⟩ := (eventuallyD.and eventuallyU).exists
  let m := φ k
  have hclose (i : I) : |u m i-v i| ≤ e := by
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm (u m-v) i).trans
      (by simpa only [dist_eq_norm] using hk.2.le)
  obtain ⟨σ,H,hσ,hH,valid⟩ := exists_h m e he
  refine ⟨σ,H,hσ,hH,fun N hN i ↦ ?_⟩
  have Hnear := expected_difference_bound (h m) g hσ i (dpos m).le
    (hLive m i) (fun A ↦ hAbs m A i) N
  constructor
  · have b₁ := abs_le.mp (valid N hN i).1
    have b₂ := abs_le.mp Hnear
    have b₃ := abs_le.mp (hclose i)
    apply abs_le.mpr
    dsimp [e] at *
    constructor <;> linarith only [b₁.1,b₁.2,b₂.1,b₂.2,b₃.1,b₃.2,hk.1,hε]
  · intro q hq
    have b₁ := (valid N hN i).2 q hq
    have b₂ := (abs_le.mp Hnear).2
    have b₃ := (abs_le.mp (expected_difference_bound (h m) g (Profile.legal_revise hσ i hq)
      i (dpos m).le (hLive m i) (fun A ↦ hAbs m A i) N)).1
    dsimp [e] at *
    linarith only [b₁,b₂,b₃,hk.1,hε]

/-- The planar theorem on the finite coordinate type. -/
theorem planar_uniform_payoff_fin (n : ℕ) : PlanarExistence (Fin n) := by
  intro g hplanar
  apply uniform_payoff_of_reward_approximation g
  intro e he
  obtain ⟨h,F,b,regular,rep,live,prize⟩ := regular_approximation g hplanar e he
  obtain ⟨u,valid⟩ := uniform_of_regular_faces h F b rep regular
  exact ⟨h,u,valid,live,prize⟩

#print axioms expected_difference_bound
#print axioms uniform_payoff_of_reward_approximation
#print axioms planar_uniform_payoff_fin

end

end PlanarQuitting
