module

public import PlanarQuitting.Target
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Stationary exit certificates

Fix a stationary product of quitting probabilities. A unilateral deviator
can change its probability on every live date. If every player faces a
positive rival hazard, the two pure-action Bellman bounds yield a uniform
payoff for the stationary profile.
-/

@[expose] public section

namespace PlanarQuitting

open scoped BigOperators

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

def Profile.stationary (x : I → ℝ) : Profile I := fun _ ↦ x

def opponentMass (x : I → ℝ) (i : I) (A : Finset I) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, if j ∈ A then x j else 1 - x j

def opponentWait (x : I → ℝ) (i : I) : ℝ := opponentMass x i ∅

def stationaryQuit (g : Game I) (x : I → ℝ) (i : I) : ℝ :=
  ∑ A ∈ (Finset.univ.erase i).powerset, opponentMass x i A * g.prize (insert i A) i

def stationaryCash (g : Game I) (x : I → ℝ) (i : I) : ℝ :=
  ∑ A ∈ (Finset.univ.erase i).powerset, if A = ∅ then 0 else opponentMass x i A * g.prize A i

private theorem opponentMass_insert (x : I → ℝ) (i : I) (A : Finset I) :
    opponentMass x i (insert i A) = opponentMass x i A := by
  unfold opponentMass
  apply Finset.prod_congr rfl
  intro j hj
  simp [(Finset.mem_erase.mp hj).1]

private theorem stationary_product (x : I → ℝ) (i : I) (q : ℕ → ℝ) (t : ℕ)
    (A : Finset I) :
    coalitionProb ((Profile.stationary x).revise i q) t A =
      (if i ∈ A then q t else 1 - q t) * opponentMass x i A := by
  unfold coalitionProb opponentMass
  conv_lhs =>
    rw [← Finset.insert_erase (Finset.mem_univ i), Finset.prod_insert (Finset.notMem_erase _ _)]
  simp only [Profile.revise]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp [Profile.stationary, (Finset.mem_erase.mp hj).1]

theorem stationarity_row (g : Game I) (x : I → ℝ) (i : I) (q : ℕ → ℝ) (t : ℕ) :
    let σ := (Profile.stationary x).revise i q
    (∑ A : Finset I, if A = ∅ then 0 else coalitionProb σ t A * g.prize A i) =
      (1-q t) * stationaryCash g x i + q t * stationaryQuit g x i := by
  dsimp only
  have huniv : (Finset.univ : Finset (Finset I)) =
      (insert i (Finset.univ.erase i)).powerset := by
    rw [Finset.insert_erase (Finset.mem_univ i)]
    ext A
    simp
  rw [huniv, Finset.sum_powerset_insert (Finset.notMem_erase _ _)]
  unfold stationaryCash stationaryQuit
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro A hA
    have hi : i ∉ A := fun hi ↦ Finset.notMem_erase i _ (Finset.mem_powerset.mp hA hi)
    by_cases h : A = ∅
    · simp [h]
    · simp [h, stationary_product, hi, mul_assoc]
  · apply Finset.sum_congr rfl
    intro A _
    simp [stationary_product, opponentMass_insert, mul_assoc]

private theorem opponentWait_unit {x : I → ℝ}
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (i : I) : 0 ≤ opponentWait x i ∧ opponentWait x i ≤ 1 := by
  simp only [opponentWait, opponentMass, Finset.notMem_empty, if_false]
  exact ⟨Finset.prod_nonneg (fun j _ ↦ sub_nonneg.mpr (hx j).2),
    Finset.prod_le_one (fun j _ ↦ sub_nonneg.mpr (hx j).2) (fun j _ ↦ sub_le_self 1 (hx j).1)⟩

/-- The stationary product has at least two effective quitting actors in the
sense that every player faces a positive probability of a rival quitting. -/
def StationaryExit (x : I → ℝ) : Prop :=
  (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ ∀ i, opponentWait x i < 1

/-- The sign convention comes from comparing the value of waiting for a rival
to quit with the value of quitting immediately. -/
def stationaryDifference (g : Game I) (x : I → ℝ) (i : I) : ℝ :=
  stationaryCash g x i - (1 - opponentWait x i) * stationaryQuit g x i

def StationaryComparisons (g : Game I) (x : I → ℝ) : Prop :=
  ∀ i, (x i < 1 → 0 ≤ stationaryDifference g x i) ∧
    (0 < x i → stationaryDifference g x i ≤ 0)

private theorem stage_account (g : Game I) (x u : I → ℝ) (i : I)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (hq : stationaryQuit g x i ≤ u i)
    (hw : stationaryCash g x i + opponentWait x i * u i ≤ u i)
    (q : ℕ → ℝ) (legal : Legal q) (t : ℕ) :
    let σ := (Profile.stationary x).revise i q
    0 ≤ liveProb σ t ∧ liveProb σ t ≤ (opponentWait x i)^t ∧
      accruedPrize g σ i t + liveProb σ t * u i ≤ u i := by
  dsimp only
  induction t with
  | zero => simp [liveProb, accruedPrize]
  | succ t ih =>
    have hσ : coalitionProb ((Profile.stationary x).revise i q) t ∅ =
        (1-q t)*opponentWait x i := by simp [stationary_product, opponentWait]
    have hs : 0 ≤ 1 - q t := sub_nonneg.mpr (legal t).2
    have hn := (opponentWait_unit hx i).1
    have hr : (1-q t)*opponentWait x i ≤ opponentWait x i :=
      mul_le_of_le_one_left hn (sub_le_self _ (legal t).1)
    simp only [liveProb, accruedPrize, hσ, stationarity_row]
    refine ⟨mul_nonneg ih.1 (mul_nonneg hs hn), ?_, ?_⟩
    · rw [pow_succ]
      exact mul_le_mul ih.2.1 hr (mul_nonneg hs hn) (pow_nonneg hn _)
    · have hW := mul_le_mul_of_nonneg_left hw hs
      have hQ := mul_le_mul_of_nonneg_left hq (legal t).1
      have hstep : (1-q t)*stationaryCash g x i+q t*stationaryQuit g x i +
          (1-q t)*opponentWait x i*u i ≤ u i := by linarith only [hW, hQ]
      have hh := mul_le_mul_of_nonneg_left hstep ih.1
      linarith only [hh, ih.2.2]

private theorem stage_account_eq (g : Game I) (x u : I → ℝ) (i : I)
    (h : (1-x i)*(stationaryCash g x i + opponentWait x i*u i) +
      x i*stationaryQuit g x i = u i) (t : ℕ) :
    accruedPrize g (Profile.stationary x) i t +
      liveProb (Profile.stationary x) t * u i = u i := by
  have hre : (Profile.stationary x).revise i (fun _ ↦ x i) = Profile.stationary x := by
    funext s j
    by_cases hj : j = i <;> simp [Profile.revise, Profile.stationary, hj]
  have hh (s : ℕ) : coalitionProb (Profile.stationary x) s ∅ = (1-x i)*opponentWait x i := by
    simpa [hre, opponentWait] using
      stationary_product x i (fun _ ↦ x i) s ∅
  induction t with
  | zero => simp [liveProb, accruedPrize]
  | succ t ih =>
    have hr := stationarity_row g x i (fun _ ↦ x i) t
    dsimp only at hr
    rw [hre] at hr
    simp only [accruedPrize, liveProb, hr, hh]
    have hm := congrArg (liveProb (Profile.stationary x) t * ·) h
    linarith only [hm, ih]

private theorem sum_survival_bound {r : ℝ} (hn : 0 ≤ r) (hl : r < 1) (N : ℕ) :
    (∑ t ∈ Finset.range N, r^(t+1)) ≤ 1/(1-r) := by
  have he (n : ℕ) : (∑ t ∈ Finset.range n, r^(t+1))*(1-r) = r-r^(n+1) := by
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, add_mul, ih, pow_succ r (k+1)]
      ring
  apply (le_div_iff₀ (sub_pos.mpr hl)).mpr
  rw [he]
  linarith only [hl, pow_nonneg hn (N+1)]

private theorem stationary_bounds (g : Game I) (x u : I → ℝ)
    (hx : StationaryExit x)
    (hq : ∀ i, stationaryQuit g x i ≤ u i)
    (hw : ∀ i, stationaryCash g x i + opponentWait x i * u i ≤ u i)
    (hbest : ∀ i, (1-x i)*(stationaryCash g x i + opponentWait x i*u i) +
      x i * stationaryQuit g x i = u i) (i : I) (q : ℕ → ℝ) (hlegal : Legal q)
    {N : ℕ} (hN : 0 < N) :
    let C := |g.live i - u i| / (1 - opponentWait x i)
    |expectedAverage g (Profile.stationary x) i N - u i| ≤ C/N ∧
      expectedAverage g ((Profile.stationary x).revise i q) i N ≤ u i + C/N := by
  dsimp only
  let σ := Profile.stationary x
  let τ := σ.revise i q
  let r := opponentWait x i
  let M := |g.live i-u i|
  let C := M/(1-r)
  have hM : 0 ≤ M := abs_nonneg _
  have hcast : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hon_law : σ.revise i (fun _ ↦ x i) = σ := by
    funext t j
    by_cases hj : j = i <;> simp [Profile.revise, Profile.stationary, σ, hj]
  have hon (t : ℕ) :
      |accruedPrize g σ i (t+1) + liveProb σ (t+1)*g.live i-u i| ≤ M * r^(t+1) := by
    have hb := stage_account g x u i hx.1 (hq i) (hw i) (fun _ ↦ x i)
      (fun _ ↦ hx.1 i) (t+1)
    change 0 ≤ liveProb (σ.revise i (fun _ ↦ x i)) (t+1) ∧ _ at hb
    rw [hon_law] at hb
    have he : accruedPrize g σ i (t+1)+liveProb σ (t+1)*g.live i-u i =
        liveProb σ (t+1)*(g.live i-u i) := by
      linarith only [stage_account_eq g x u i (hbest i) (t+1)]
    rw [he, abs_mul, abs_of_nonneg hb.1, mul_comm]
    exact mul_le_mul_of_nonneg_left hb.2.1 hM
  have hdev (t : ℕ) :
      accruedPrize g τ i (t+1) + liveProb τ (t+1)*g.live i ≤ u i+M*r^(t+1) := by
    have hb := stage_account g x u i hx.1 (hq i) (hw i) q hlegal (t+1)
    have hm := mul_le_mul_of_nonneg_left (le_abs_self (g.live i-u i)) hb.1
    have hn := mul_le_mul_of_nonneg_left hb.2.1 hM
    linarith only [hb.2.2, hm, hn]
  have hsum : (∑ t ∈ Finset.range N, M*r^(t+1)) ≤ C := by
    rw [← Finset.mul_sum]
    have hgeom := mul_le_mul_of_nonneg_left
      (sum_survival_bound (opponentWait_unit hx.1 i).1 (hx.2 i) N) hM
    simpa [C, div_eq_mul_inv] using hgeom
  constructor
  · change |expectedAverage g σ i N - u i| ≤ C/N
    have he : expectedAverage g σ i N-u i =
        ((∑ t ∈ Finset.range N, (accruedPrize g σ i (t+1) +
          liveProb σ (t+1)*g.live i)) - (N:ℝ)*u i) / N := by
      unfold expectedAverage
      field_simp
      simp only [mul_comm]
    rw [he, abs_div, abs_of_pos hcast]
    apply div_le_div_of_nonneg_right _ hcast.le
    have ht := Finset.abs_sum_le_sum_abs (s := Finset.range N)
      (fun t ↦ accruedPrize g σ i (t+1)+liveProb σ (t+1)*g.live i-u i)
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at ht
    exact ht.trans ((Finset.sum_le_sum fun t _ ↦ hon t).trans hsum)
  · change expectedAverage g τ i N ≤ u i+C/N
    have ht := Finset.sum_le_sum (s := Finset.range N) (fun t _ ↦ hdev t)
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at ht
    rw [expectedAverage, div_le_iff₀ hcast]
    calc
      _ ≤ (N:ℝ)*u i+C := by rw [Finset.sum_add_distrib]; linarith only [ht, hsum]
      _ = _ := by field_simp

/-- A stationary solution of the waiting-versus-quitting inequalities, with a
positive rival hazard for everyone, gives a uniform Nash payoff. -/
theorem uniform_of_stationary_exit (g : Game I) (x : I → ℝ)
    (hx : StationaryExit x) (hcomp : StationaryComparisons g x) :
    ∃ u, HasUniformPayoff g u := by
  let wait i := stationaryCash g x i / (1 - opponentWait x i)
  let u i := if x i = 1 then stationaryQuit g x i else wait i
  have hu (i : I) :
      stationaryQuit g x i ≤ u i ∧
      stationaryCash g x i + opponentWait x i*u i ≤ u i ∧
      (1-x i)*(stationaryCash g x i + opponentWait x i*u i) +
        x i * stationaryQuit g x i = u i := by
    have hden := sub_pos.mpr (hx.2 i)
    have heq : stationaryCash g x i + opponentWait x i * wait i = wait i := by
      have hm : wait i * (1 - opponentWait x i) = stationaryCash g x i :=
        div_mul_cancel₀ _ hden.ne'
      linarith only [hm]
    by_cases h1 : x i = 1
    · have hp : 0 < x i := h1.symm ▸ one_pos
      have hle := (hcomp i).2 hp
      simp only [u, if_pos h1, h1, sub_self, zero_mul, zero_add, one_mul, le_refl, and_true,
        true_and]
      unfold stationaryDifference at hle
      linarith only [hle]
    · have hlt := lt_of_le_of_ne (hx.1 i).2 h1
      have hl := (hcomp i).1 hlt
      have hq' : stationaryQuit g x i ≤ wait i := by
        apply (le_div_iff₀ hden).mpr
        unfold stationaryDifference at hl
        linarith only [hl]
      simp only [u, if_neg h1, heq]
      refine ⟨hq', le_rfl, ?_⟩
      by_cases h0 : x i = 0
      · simp [h0]
      · have hh := (hcomp i).2 (lt_of_le_of_ne (hx.1 i).1 (Ne.symm h0))
        have hg : wait i ≤ stationaryQuit g x i := by
          apply (div_le_iff₀ hden).mpr
          unfold stationaryDifference at hh
          linarith only [hh]
        rw [le_antisymm hg hq']
        ring
  refine ⟨u, ?_⟩
  intro ε hε
  let C i := |g.live i-u i|/(1-opponentWait x i)
  let B := ∑ i, C i
  have hC (i : I) : 0 ≤ C i := div_nonneg (abs_nonneg _) (sub_nonneg.mpr (hx.2 i).le)
  have hB (i : I) : C i ≤ B :=
    Finset.single_le_sum (fun j _ ↦ hC j) (Finset.mem_univ i)
  obtain ⟨H, hH⟩ := exists_nat_gt (2*B/ε)
  refine ⟨Profile.stationary x, H+1, fun i _ ↦ hx.1 i, Nat.zero_lt_succ _, ?_⟩
  intro N hN i
  have hn : 0 < N := (Nat.zero_lt_succ H).trans_le hN
  have hN' : (H:ℝ) ≤ N := Nat.cast_le.mpr ((Nat.le_succ H).trans hN)
  have hsmall : C i / N ≤ ε/2 := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr hn)).mpr
    have ht := (div_lt_iff₀ hε).mp (hH.trans_le hN')
    linarith only [ht, hB i]
  have all (q : ℕ → ℝ) (hq : Legal q) :=
    stationary_bounds g x u hx (fun j ↦ (hu j).1) (fun j ↦ (hu j).2.1)
      (fun j ↦ (hu j).2.2) i q hq hn
  have hh := (all (fun _ ↦ x i) (fun _ ↦ hx.1 i)).1
  change |expectedAverage g (Profile.stationary x) i N - u i| ≤ C i / N at hh
  refine ⟨hh.trans (by linarith), ?_⟩
  intro q hq
  have hd := (all q hq).2
  change expectedAverage g ((Profile.stationary x).revise i q) i N ≤ u i + C i / N at hd
  linarith only [hd, (abs_le.mp hh).1, hsmall]

#print axioms uniform_of_stationary_exit

end

end PlanarQuitting
