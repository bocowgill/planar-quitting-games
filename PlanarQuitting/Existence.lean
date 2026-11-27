module

public import PlanarQuitting.PayoffClosure
import Mathlib.Data.Fintype.EquivFin

/-!
# Uniform Nash payoffs for planar quitting games

Transport the finite coordinate proof through a bijection of players.
The bijection preserves all coalition probabilities and arbitrary
unilateral behavioral deviations.
-/

@[expose] public section

namespace PlanarQuitting

universe u

open scoped BigOperators

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def Game.relabel (g : Game I) (e : I ≃ J) : Game J :=
  ⟨fun i ↦ g.live (e.symm i), fun A i ↦ g.prize (e.symm.finsetCongr A) (e.symm i)⟩

def Profile.pull (e : I ≃ J) (σ : Profile J) : Profile I :=
  fun t i ↦ σ t (e i)

omit [Fintype I] [Fintype J] in
theorem Profile.pull_revise (e : I ≃ J) (σ : Profile J) (i : I) (q : ℕ → ℝ) :
    (Profile.pull e σ).revise i q = Profile.pull e (σ.revise (e i) q) := by
  classical
  funext t j
  simp [Profile.revise,Profile.pull]

private theorem relabel_coalition (e : I ≃ J) (σ : Profile J) (t : ℕ) (A : Finset I) :
    coalitionProb (Profile.pull e σ) t A = coalitionProb σ t (e.finsetCongr A) := by
  apply Fintype.prod_equiv e
  intro i
  simp [Profile.pull]

private theorem relabel_live (e : I ≃ J) (σ : Profile J) (t : ℕ) :
    liveProb (Profile.pull e σ) t = liveProb σ t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [liveProb,ih,relabel_coalition]

private theorem relabel_accrued (g : Game I) (e : I ≃ J) (σ : Profile J) (i : I) (t : ℕ) :
    accruedPrize g (Profile.pull e σ) i t = accruedPrize (g.relabel e) σ (e i) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [accruedPrize,ih,relabel_live]
    congr 2
    apply Fintype.sum_equiv e.finsetCongr
    intro A
    have empty : e.finsetCongr A = ∅ ↔ A = ∅ := by simp
    simp only [empty,relabel_coalition,Game.relabel,Equiv.symm_apply_apply,
      ← Equiv.finsetCongr_symm]

theorem expectedAverage_relabel (g : Game I) (e : I ≃ J) (σ : Profile J) (i : I) (N : ℕ) :
    expectedAverage g (Profile.pull e σ) i N = expectedAverage (g.relabel e) σ (e i) N := by
  simp [expectedAverage,relabel_accrued,relabel_live,Game.relabel]

/-- Every finite quitting game whose singleton absorbing payoff vectors
lie in an affine plane has a uniform Nash equilibrium payoff. No restriction
is imposed on its rewards from simultaneous quits or from live dates. -/
theorem planar_uniform_payoff (I : Type u) [Fintype I] [DecidableEq I] :
    PlanarExistence I := by
  intro g hplanar
  let e := Fintype.equivFin I
  have h' : PlanarSingletons (g.relabel e) := by
    obtain ⟨b,a,R,h⟩ := hplanar
    refine ⟨fun i ↦ b (e.symm i),fun i ↦ a (e.symm i),fun i ↦ R (e.symm i),fun i j ↦ ?_⟩
    simpa [Game.relabel] using h (e.symm i) (e.symm j)
  obtain ⟨v,hv⟩ := planar_uniform_payoff_fin (Fintype.card I) (g.relabel e) h'
  refine ⟨v ∘ e,fun ε hε ↦ ?_⟩
  obtain ⟨σ,H,hσ,hH,sol⟩ := hv ε hε
  refine ⟨Profile.pull e σ,H,fun i ↦ hσ (e i),hH,fun N hN i ↦ ?_⟩
  rw [expectedAverage_relabel]
  refine ⟨(sol N hN (e i)).1,fun q hq ↦ ?_⟩
  rw [Profile.pull_revise,expectedAverage_relabel]
  exact (sol N hN (e i)).2 q hq

#print axioms planar_uniform_payoff

/-- The initial state is either live or a permanently absorbed coalition. -/
abbrev QuittingState (I : Type*) := Option {A : Finset I // A.Nonempty}

def expectedAverageFrom (g : Game I) (σ : Profile I) (s : QuittingState I) (i : I) (N : ℕ) : ℝ :=
  match s with
  | none => expectedAverage g σ i N
  | some A => if N = 0 then 0 else g.prize A.val i

/-- The same profile and threshold work simultaneously from the live state
and every absorbing state of the quitting game. -/
theorem planar_uniform_payoff_all_states
    (g : Game I) (planar : PlanarSingletons g) :
    ∃ v : QuittingState I → I → ℝ,
      ∀ ε : ℝ, 0 < ε → ∃ (σ : Profile I) (H : ℕ), σ.legal ∧ 1 ≤ H ∧
        ∀ s : QuittingState I, ∀ N : ℕ, H ≤ N → ∀ i,
          |expectedAverageFrom g σ s i N-v s i| ≤ ε ∧
          ∀ q, Legal q → expectedAverageFrom g (σ.revise i q) s i N ≤
            expectedAverageFrom g σ s i N+ε := by
  obtain ⟨u,hu⟩ := planar_uniform_payoff I g planar
  let v : QuittingState I → I → ℝ := fun s ↦
    match s with
    | none => u
    | some A => g.prize A.val
  refine ⟨v,fun ε hε ↦ ?_⟩
  obtain ⟨σ,H,hσ,hH,sol⟩ := hu ε hε
  refine ⟨σ,H,hσ,hH,fun s N hN i ↦ ?_⟩
  cases s with
  | none => exact sol N hN i
  | some A =>
    have hn : N ≠ 0 := Nat.ne_of_gt (hH.trans hN)
    simp only [expectedAverageFrom,hn,ite_false,v,sub_self,abs_zero]
    exact ⟨hε.le,fun _ _ ↦ le_add_of_nonneg_right hε.le⟩

#print axioms planar_uniform_payoff_all_states

end

end PlanarQuitting
