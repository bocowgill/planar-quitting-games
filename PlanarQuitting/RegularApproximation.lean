module

public import PlanarQuitting.RegularExistence
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Approximating a planar representation by regular ones

Interpolate the payoff lines and their marked sites towards the tangents
of a parabola. At the parabola configuration all cross incidences, pair
determinants and triple determinants are nonzero. Along the interpolation
only finitely many parameters can make any of these polynomials vanish.
-/

@[expose] public section

namespace PlanarQuitting

open Set Filter Polynomial
open scoped BigOperators Topology

noncomputable section

variable {n : ℕ}

private def affineFaces (a R : Fin n → Coordinates 2) : Faces (Fin n) (Coordinates 2) :=
  ⟨fun i ↦ a i 0 • LinearMap.proj 0 + a i 1 • LinearMap.proj 1, R⟩

private def dot2 {T : Type*} [Semiring T] (a x : Fin 2 → T) : T :=
  a 0*x 0 + a 1*x 1

private def det2 {T : Type*} [Ring T] (a b : Fin 2 → T) : T :=
  a 0*b 1 - a 1*b 0

private def det3 {T : Type*} [Ring T] (a b c : Fin 2 → T) (d e f : T) : T :=
  det2 a b * f - det2 a c * e + det2 b c * d

private theorem slack_affine (a R : Fin n → Coordinates 2) (i : Fin n) (x : Coordinates 2) :
    (affineFaces a R).slack i x = dot2 (a i) x-dot2 (a i) (R i) := by
  change a i 0*(x 0-R i 0)+a i 1*(x 1-R i 1) = _
  unfold dot2
  ring

private theorem regular_of_dets (a R : Fin n → Coordinates 2)
    (cross : ∀ i j, i ≠ j → dot2 (a i) (R j)-dot2 (a i) (R i) ≠ 0)
    (pair : ∀ i j, i ≠ j → det2 (a i) (a j) ≠ 0)
    (triple : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      det3 (a i) (a j) (a k) (dot2 (a i) (R i)) (dot2 (a j) (R j))
        (dot2 (a k) (R k)) ≠ 0) :
    RegularFaces (affineFaces a R) := by
  constructor
  · intro i j hij
    change (affineFaces a R).slack i (R j) ≠ 0
    rw [slack_affine]
    exact cross i j hij
  · intro x i j k hij hi hj hk
    by_contra! h
    apply triple i j k hij (Ne.symm h.1) (Ne.symm h.2)
    rw [slack_affine, sub_eq_zero] at hi hj hk
    rw [← hi, ← hj, ← hk]
    unfold dot2 det3 det2
    ring
  · intro x y i j hij hi hj hi' hj'
    simp only [slack_affine,sub_eq_zero] at hi hj hi' hj'
    have e₁ := hi.trans hi'.symm
    have e₂ := hj.trans hj'.symm
    have h₀ : det2 (a i) (a j)*(x 0-y 0) = 0 := by
      unfold det2 dot2 at *
      linear_combination a j 1 * e₁ - a i 1 * e₂
    have h₁ : det2 (a i) (a j)*(x 1-y 1) = 0 := by
      unfold det2 dot2 at *
      linear_combination a i 0 * e₂ - a j 0 * e₁
    funext f
    fin_cases f
    · exact sub_eq_zero.mp ((mul_eq_zero.mp h₀).resolve_left (pair i j hij))
    · exact sub_eq_zero.mp ((mul_eq_zero.mp h₁).resolve_left (pair i j hij))

private def seedRow (i : Fin n) : Coordinates 2 := fun j ↦ if j = 0 then -2*(i.val : ℝ) else 1
private def seedSite (i : Fin n) : Coordinates 2 := fun j ↦
  if j = 0 then (i.val : ℝ) else (i.val : ℝ)^2

private theorem cast_ne {i j : Fin n} (h : i ≠ j) : (i.val : ℝ) ≠ j.val :=
  fun e ↦ h (Fin.ext (Nat.cast_injective e))

private theorem seed_cross (i j : Fin n) (hne : i ≠ j) :
    dot2 (seedRow i) (seedSite j)-dot2 (seedRow i) (seedSite i) ≠ 0 := by
  have he : dot2 (seedRow i) (seedSite j)-dot2 (seedRow i) (seedSite i) =
      ((j.val : ℝ)-i.val)^2 := by
    norm_num [dot2,seedRow,seedSite]
    ring
  rw [he]
  exact pow_ne_zero _ (sub_ne_zero.mpr (cast_ne hne.symm))

private theorem seed_pair (i j : Fin n) (hne : i ≠ j) :
    det2 (seedRow i) (seedRow j) ≠ 0 := by
  have he : det2 (seedRow i) (seedRow j) = 2*((j.val : ℝ)-i.val) := by
    norm_num [det2,seedRow]
    ring
  rw [he]
  exact mul_ne_zero (by norm_num) (sub_ne_zero.mpr (cast_ne hne.symm))

private theorem seed_triple (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    det3 (seedRow i) (seedRow j) (seedRow k)
      (dot2 (seedRow i) (seedSite i)) (dot2 (seedRow j) (seedSite j))
      (dot2 (seedRow k) (seedSite k)) ≠ 0 := by
  have he : det3 (seedRow i) (seedRow j) (seedRow k)
      (dot2 (seedRow i) (seedSite i)) (dot2 (seedRow j) (seedSite j))
      (dot2 (seedRow k) (seedSite k)) =
      -2*((j.val : ℝ)-i.val)*((k.val : ℝ)-i.val)*((k.val : ℝ)-j.val) := by
    norm_num [det3,det2,dot2,seedRow,seedSite]
    ring
  rw [he]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (sub_ne_zero.mpr (cast_ne hij.symm)))
    (sub_ne_zero.mpr (cast_ne hik.symm))) (sub_ne_zero.mpr (cast_ne hjk.symm))

private def interpolate (a b : ℝ) : Polynomial ℝ := C a + X * C (b-a)

private theorem eval_interpolate_one (a b : ℝ) : (interpolate a b).eval 1 = b := by
  simp [interpolate]

private def singletonPerturbation (g : Game (Fin n)) (b : Coordinates n)
    (a R : Fin n → Coordinates 2) : Game (Fin n) :=
  ⟨g.live, fun A i ↦ if h : ∃ j : Fin n, A = {j} then
    b i + dot2 (a i) (R (Classical.choose h)) else g.prize A i⟩

private theorem singletonPerturbation_prize (g : Game (Fin n)) (b : Coordinates n)
    (a R : Fin n → Coordinates 2) (i j : Fin n) :
    (singletonPerturbation g b a R).prize {j} i = b i + dot2 (a i) (R j) := by
  unfold singletonPerturbation
  dsimp
  let h : ∃ k : Fin n, ({j} : Finset (Fin n)) = {k} := ⟨j,rfl⟩
  rw [dif_pos h]
  have he : Classical.choose h = j := Finset.singleton_inj.mp (Classical.choose_spec h).symm
  rw [he]

/-- Regular representations approximate the original game in every stage
reward. Nonsingleton prizes and the live payoff do not enter the perturbation. -/
theorem regular_approximation (g : Game (Fin n)) (planar : PlanarSingletons g)
    (e : ℝ) (he : 0 < e) :
    ∃ (g' : Game (Fin n)) (F : Faces (Fin n) (Coordinates 2)) (b : Coordinates n),
      RegularFaces F ∧ (∀ i j, g'.prize {j} i = b i + F.row i (F.site j)) ∧
      (∀ i, |g'.live i-g.live i| ≤ e) ∧ ∀ A i, |g'.prize A i-g.prize A i| ≤ e := by
  classical
  obtain ⟨b,a,R,rep⟩ := planar
  let A (i : Fin n) (k : Fin 2) := interpolate (a i k) (seedRow i k)
  let T (i : Fin n) (k : Fin 2) := interpolate (R i k) (seedSite i k)
  let ax (x : ℝ) (i : Fin n) (k : Fin 2) := (A i k).eval x
  let tx (x : ℝ) (i : Fin n) (k : Fin 2) := (T i k).eval x
  let P (i j : Fin n) : Polynomial ℝ := if i = j then 1 else
    (dot2 (A i) (T j)-dot2 (A i) (T i))*det2 (A i) (A j)
  let Q (i j k : Fin n) : Polynomial ℝ := if i ≠ j ∧ i ≠ k ∧ j ≠ k then
    det3 (A i) (A j) (A k) (dot2 (A i) (T i)) (dot2 (A j) (T j))
      (dot2 (A k) (T k)) else 1
  let bad := (∏ i, ∏ j, P i j)*(∏ i, ∏ j, ∏ k, Q i j k)
  have pval (x : ℝ) (i j : Fin n) (h : i ≠ j) :
      (P i j).eval x = (dot2 (ax x i) (tx x j)-dot2 (ax x i) (tx x i))*det2 (ax x i) (ax x j) := by
    simp [P,h,ax,tx,dot2,det2]
  have qval (x : ℝ) (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      (Q i j k).eval x = det3 (ax x i) (ax x j) (ax x k)
        (dot2 (ax x i) (tx x i)) (dot2 (ax x j) (tx x j)) (dot2 (ax x k) (tx x k)) := by
    simp [Q,hij,hik,hjk,ax,tx,det3,det2,dot2]
  have ax₁ (i : Fin n) : ax 1 i = seedRow i := by funext k; exact eval_interpolate_one _ _
  have tx₁ (i : Fin n) : tx 1 i = seedSite i := by funext k; exact eval_interpolate_one _ _
  have hp₁ (i j : Fin n) : (P i j).eval 1 ≠ 0 := by
    by_cases h : i = j
    · simp [P,h]
    · rw [pval 1 i j h,ax₁,ax₁,tx₁,tx₁]
      exact mul_ne_zero (seed_cross i j h) (seed_pair i j h)
  have hq₁ (i j k : Fin n) : (Q i j k).eval 1 ≠ 0 := by
    by_cases h : i ≠ j ∧ i ≠ k ∧ j ≠ k
    · rw [qval 1 i j k h.1 h.2.1 h.2.2,ax₁,ax₁,ax₁,tx₁,tx₁,tx₁]
      exact seed_triple i j k h.1 h.2.1 h.2.2
    · simp [Q,h]
  have hb₁ : bad.eval 1 ≠ 0 := by
    simp only [bad,eval_mul,eval_prod]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ ↦
        Finset.prod_ne_zero_iff.mpr fun j _ ↦ hp₁ i j)
      (Finset.prod_ne_zero_iff.mpr fun i _ ↦ Finset.prod_ne_zero_iff.mpr fun j _ ↦
        Finset.prod_ne_zero_iff.mpr fun k _ ↦ hq₁ i j k)
  have finite : {x : ℝ | bad.IsRoot x}.Finite :=
    finite_setOfPred_isRoot (fun h ↦ hb₁ (by simp [h]))
  have near (i j : Fin n) :
      ∀ᶠ x : ℝ in 𝓝 0, |b i + dot2 (ax x i) (tx x j)-g.prize {j} i| < e := by
    have hc : Continuous fun x : ℝ ↦ b i + dot2 (ax x i) (tx x j)-g.prize {j} i := by
      have lin (a b : ℝ) : Continuous fun x : ℝ ↦ (interpolate a b).eval x := by
        simp only [interpolate,eval_add,eval_mul,eval_C,eval_X]
        exact continuous_const.add (continuous_id.mul continuous_const)
      unfold dot2
      exact (continuous_const.add
        (((lin (a i 0) _).mul (lin (R j 0) _)).add
          ((lin (a i 1) _).mul (lin (R j 1) _)))).sub continuous_const
    have hn : |b i + dot2 (ax 0 i) (tx 0 j)-g.prize {j} i| < e := by
      simp only [ax,tx,A,T,interpolate,eval_add,eval_mul,eval_C,eval_X,zero_mul,add_zero,
        dot2,rep]
      rw [show b i + (a i 0*R j 0+a i 1*R j 1) - (b i+a i 0*R j 0+a i 1*R j 1) = 0 by ring,
        abs_zero]
      exact he
    exact (isOpen_lt hc.abs continuous_const).mem_nhds hn
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp
    (eventually_all.mpr fun i ↦ eventually_all.mpr (near i))
  obtain ⟨x,hx,hbad⟩ := ((Ioo_infinite hδ).sdiff finite).nonempty
  have hxb : x ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball,dist_zero_right,Real.norm_of_nonneg hx.1.le]
    exact hx.2
  have hxne : bad.eval x ≠ 0 := hbad
  have hnP (i j : Fin n) : (P i j).eval x ≠ 0 := by
    intro h
    apply hxne
    simp only [bad,eval_mul,eval_prod]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (Finset.prod_eq_zero (Finset.mem_univ j) h),zero_mul]
  have hnQ (i j k : Fin n) : (Q i j k).eval x ≠ 0 := by
    intro h
    apply hxne
    simp only [bad,eval_mul,eval_prod]
    have h₁ : ∏ k, (Q i j k).eval x = 0 := Finset.prod_eq_zero (Finset.mem_univ k) h
    have h₂ : ∏ j, ∏ k, (Q i j k).eval x = 0 := Finset.prod_eq_zero (Finset.mem_univ j) h₁
    have h₃ : ∏ i, ∏ j, ∏ k, (Q i j k).eval x = 0 := Finset.prod_eq_zero (Finset.mem_univ i) h₂
    rw [h₃,mul_zero]
  let g' := singletonPerturbation g b (ax x) (tx x)
  refine ⟨g',affineFaces (ax x) (tx x),b,
    regular_of_dets _ _
      (fun i j h ↦ (mul_ne_zero_iff.mp (pval x i j h ▸ hnP i j)).1)
      (fun i j h ↦ (mul_ne_zero_iff.mp (pval x i j h ▸ hnP i j)).2)
      (fun i j k hij hik hjk ↦ qval x i j k hij hik hjk ▸ hnQ i j k),?_,?_,?_⟩
  · intro i j
    exact singletonPerturbation_prize g b (ax x) (tx x) i j
  · intro i
    change |g.live i-g.live i| ≤ e
    simpa using he.le
  · intro S i
    by_cases h : ∃ j : Fin n, S = {j}
    · obtain ⟨j,rfl⟩ := h
      rw [singletonPerturbation_prize]
      exact (hball hxb i j).le
    · change |(if h : ∃ j : Fin n, S = {j} then
          b i + dot2 (ax x i) (tx x (Classical.choose h)) else g.prize S i)-g.prize S i| ≤ e
      simpa [h] using he.le

#print axioms regular_approximation

end

end PlanarQuitting
