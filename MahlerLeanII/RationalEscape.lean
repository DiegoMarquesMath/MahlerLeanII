import MahlerLeanII.Basic
import MahlerLeanII.SparseEscape
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! Necessity in Theorem 1.2. A nonconstant rational function with an
obstructed normalized coefficient has a counterexample on every open interval
avoiding its poles. -/

noncomputable section
namespace MahlerLeanII
open Set Polynomial Reconstruction Filter Topology

/-- On every open pole-free interval a nonconstant rational function has
a compact subinterval with upper and inverse Lipschitz bounds. -/
private theorem regular_interval (R : RatFunc ℝ) (hn : R ∉ Set.range (RatFunc.C : ℝ →+* RatFunc ℝ))
    {a b : ℝ} (hab : a < b) (hpole : ∀ x ∈ Ioo a b, R.denom.eval x ≠ 0) :
    ∃ l u m M : ℝ, l < u ∧ Icc l u ⊆ Ioo a b ∧ 0 < m ∧ 0 ≤ M ∧
      (∀ x ∈ Icc l u, ∀ y ∈ Icc l u,
        m*|x-y| ≤ |R.num.eval x/R.denom.eval x-R.num.eval y/R.denom.eval y|) ∧
      (∀ x ∈ Icc l u, ∀ y ∈ Icc l u,
        |R.num.eval x/R.denom.eval x-R.num.eval y/R.denom.eval y| ≤ M*|x-y|) := by
  let f := fun x => R.num.eval x / R.denom.eval x
  have ha (x) (hx : x ∈ Ioo a b) : AnalyticAt ℝ f x :=
    (AnalyticOnNhd.eval_polynomial (𝕜 := ℝ) R.num x (mem_univ _)).div
      (AnalyticOnNhd.eval_polynomial (𝕜 := ℝ) R.denom x (mem_univ _)) (hpole x hx)
  have ex : ∃ x ∈ Ioo a b, deriv f x ≠ 0 := by
    by_contra! hz
    obtain ⟨c,hc⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun x hx => (ha x hx).differentiableAt.differentiableWithinAt) (fun x hx => hz x hx)
    have eq : R.num = Polynomial.C c * R.denom := by
      apply Polynomial.eq_of_infinite_eval_eq
      apply (Set.Ioo_infinite hab).mono
      intro x hx
      change R.num.eval x = (Polynomial.C c * R.denom).eval x
      rw [Polynomial.eval_mul,Polynomial.eval_C]
      exact (div_eq_iff (hpole _ hx)).mp (hc x hx)
    apply hn
    refine ⟨c,?_⟩
    calc RatFunc.C c = algebraMap _ (RatFunc ℝ) (Polynomial.C c) := (RatFunc.algebraMap_C c).symm
         _ = algebraMap _ _ R.num / algebraMap _ _ R.denom := by
           rw [eq,map_mul,mul_div_cancel_right₀ _ (RatFunc.algebraMap_ne_zero R.denom_ne_zero)]
         _ = R := R.num_div_denom
  obtain ⟨z,hz,hd⟩ := ex
  have hc := (ha z hz).deriv.continuousAt.abs
  have pos := abs_pos.mpr hd
  let m := |deriv f z|/2
  let M := |deriv f z|+1
  have lo : m < |deriv f z| := by dsimp [m]; linarith
  have hi : |deriv f z| < M := by dsimp [M]; linarith
  have near : ∀ᶠ x in 𝓝 z, x ∈ Ioo a b ∧ m < |deriv f x| ∧ |deriv f x| < M := by
    filter_upwards [isOpen_Ioo.mem_nhds hz,hc.eventually (lt_mem_nhds lo),
      hc.eventually (gt_mem_nhds hi)] with x h h₁ h₂
    exact ⟨h,h₁,h₂⟩
  obtain ⟨ε,hε,ball⟩ := Metric.mem_nhds_iff.mp near
  let l := z-ε/2
  let u := z+ε/2
  have sub (x) (hx : x ∈ Icc l u) : x ∈ Ioo a b ∧ m < |deriv f x| ∧ |deriv f x| < M := by
    apply ball
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    obtain ⟨hl,hu⟩ := hx
    dsimp [l,u] at hl hu
    constructor <;> linarith
  have diff (x) (hx : x ∈ Icc l u) : DifferentiableAt ℝ f x := (ha x (sub x hx).1).differentiableAt
  refine ⟨l,u,m,M,by dsimp [l,u]; linarith,fun x hx => (sub x hx).1,by dsimp [m]; positivity,
    by dsimp [M]; positivity,?_,?_⟩
  · have slope {x y : ℝ} (hx : x ∈ Icc l u) (hy : y ∈ Icc l u) (hxy : x < y) :
        m*|x-y| ≤ |f x-f y| := by
      have inc : Icc x y ⊆ Icc l u := Icc_subset_Icc hx.1 hy.2
      obtain ⟨c,hc,he⟩ := exists_deriv_eq_slope f hxy
        (fun z hz => (diff z (inc hz)).continuousAt.continuousWithinAt)
        (fun z hz => (diff z (inc ⟨hz.1.le,hz.2.le⟩)).differentiableWithinAt)
      have lower := (sub c (inc ⟨hc.1.le,hc.2.le⟩)).2.1.le
      rw [he,abs_div,abs_sub_comm y x,abs_sub_comm (f y) (f x)] at lower
      exact (le_div_iff₀ (abs_pos.mpr (sub_ne_zero.mpr hxy.ne))).mp lower
    intro x hx y hy
    rcases lt_trichotomy x y with h | rfl | h
    · exact slope hx hy h
    · simp
    · simpa only [abs_sub_comm y x,abs_sub_comm (f y) (f x)] using slope hy hx h
  · intro x hx y hy
    exact Convex.norm_image_sub_le_of_norm_deriv_le diff (fun z hz => (sub z hz).2.2.le) (convex_Icc l u) hy hx

/-- The only omitted coefficient of the denominator is its leading coefficient, one. -/
private theorem good_of_free (R : RatFunc ℝ) (h : ∀ w, ScaleApproximable
    (freeCoefficients R.num R.denom R.num.natDegree R.denom.natDegree w)) :
    (∀ j, ScaleApproximable (R.num.coeff j)) ∧ (∀ j, ScaleApproximable (R.denom.coeff j)) := by
  have rat0 : ScaleApproximable 0 := by simpa using rational_scaleApproximable 0
  constructor
  · intro j
    by_cases hj : j < R.num.natDegree+1
    · simpa only [freeCoefficients,Fin.addCases_left] using h ((⟨j,hj⟩ : Fin (R.num.natDegree+1)).castAdd R.denom.natDegree)
    · rwa [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
  · intro j
    rcases lt_trichotomy j R.denom.natDegree with hj | rfl | hj
    · simpa only [freeCoefficients,Fin.addCases_right] using h ((⟨j,hj⟩ : Fin R.denom.natDegree).natAdd (R.num.natDegree+1))
    · rw [R.monic_denom.coeff_natDegree]
      simpa using rational_scaleApproximable 1
    · rwa [Polynomial.coeff_eq_zero_of_natDegree_lt hj]

/-- The single-point consequence of the rational escape theorem needed for
the classification. The interval is arbitrary and the coefficient obstruction
is derived from Definition 1.1. -/
theorem escape_of_bad_coefficients (R : RatFunc ℝ) (hn : R ∉ Set.range (RatFunc.C : ℝ →+* RatFunc ℝ))
    (hb : ¬ ((∀ j, ScaleApproximable (R.num.coeff j)) ∧ (∀ j, ScaleApproximable (R.denom.coeff j))))
    {a b : ℝ} (hab : a < b) (hpole : ∀ x ∈ Ioo a b, R.denom.eval x ≠ 0) :
    ∃ ξ ∈ Ioo a b, Liouville ξ ∧ ¬rationalOrLiouville (R.eval (RingHom.id ℝ) ξ) := by
  classical
  obtain ⟨w,hw⟩ := not_forall.mp (fun h => hb (good_of_free R h))
  obtain ⟨ν,_,ob⟩ := (not_scaleApproximable_iff _).mp hw
  obtain ⟨l,u,m,M,hlu,sub,hm,hM,inv,lip⟩ := regular_interval R hn hab hpole
  have count := Counting.two_height_count (le_refl R.num.natDegree) rfl R.monic_denom
    R.isCoprime_num_denom w ob hM hm (fun x hx => hpole x (sub hx)) inv
  obtain ⟨ξ,hξ,hL,he⟩ := Escape.point_escape_of_sparse_count hlu hM
    (by unfold Counting.blockOrder; omega) lip count
  exact ⟨ξ,sub hξ,hL,he⟩

end MahlerLeanII
