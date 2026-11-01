import MahlerLeanII.Synchronization
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith

/-! Arithmetic and local metric bounds for evaluating a quotient of integer
polynomials on a finite tuple. These bounds apply both to the construction of
the coefficient field and to evaluation at a Liouville argument. -/

noncomputable section
namespace MahlerLeanII.Evaluation
open MvPolynomial Filter Set Topology

/-- Evaluate an integral polynomial on a real tuple. -/
def val {s : ℕ} (P : MvPolynomial (Fin s) ℤ) (x : Fin s → ℝ) : ℝ := aeval x P

private theorem clear_eval {s : ℕ} (P : MvPolynomial (Fin s) ℤ) :
    ∃ d : ℕ, ∀ (h : ℕ) (a : Fin s → ℤ), 0 < h → ∃ z : ℤ,
      (z:ℝ) = (h:ℝ)^d * val P (fun i => (a i : ℝ)/h) := by
  apply P.induction_on
  · intro c
    exact ⟨0,fun _ _ _ => ⟨c, by simp [val]⟩⟩
  · rintro p q ⟨dp,hp⟩ ⟨dq,hq⟩
    refine ⟨dp+dq,?_⟩
    intro h a hh
    obtain ⟨u,hu⟩ := hp h a hh
    obtain ⟨v,hv⟩ := hq h a hh
    refine ⟨u*(h:ℤ)^dq+v*(h:ℤ)^dp,?_⟩
    push_cast
    rw [hu,hv,pow_add]
    simp only [val,map_add]
    ring
  · rintro p i ⟨dp,hp⟩
    refine ⟨dp+1,?_⟩
    intro h a hh
    obtain ⟨u,hu⟩ := hp h a hh
    refine ⟨u*a i,?_⟩
    push_cast
    rw [hu,pow_succ]
    simp only [val,map_mul,aeval_X]
    have hn : (h:ℝ) ≠ 0 := by exact_mod_cast hh.ne'
    field_simp

private theorem diff_val {s : ℕ} (P : MvPolynomial (Fin s) ℤ) (v : Fin s → ℝ) :
    ContDiffAt ℝ 1 (val P) v := by
  have h (i : Fin s) : AnalyticAt ℝ (fun x : Fin s → ℝ => x i) v :=
    (ContinuousLinearMap.proj i : (Fin s → ℝ) →L[ℝ] ℝ).analyticAt v
  exact (AnalyticAt.aeval_mvPolynomial h P).contDiffAt

private theorem integer_ratio (a b : ℤ) :
    ∃ c : ℤ, (a:ℝ)/b = (c:ℝ)/(b.natAbs:ℝ) := by
  have absden : (b.natAbs:ℝ) = |(b:ℝ)| := by rw [← Int.cast_abs,← Int.natCast_natAbs,Int.cast_natCast]
  by_cases hb : 0 ≤ (b:ℝ)
  · exact ⟨a,by rw [absden,abs_of_nonneg hb]⟩
  · exact ⟨-a,by rw [absden,abs_of_neg (lt_of_not_ge hb),Int.cast_neg,neg_div_neg_eq]⟩

/-- Near a point off the zero set of the denominator, evaluation has linear
error in the coordinates and polynomial denominator height. All constants
and the degree bound precede the rational approximation. -/
theorem rational_evaluation_control {s : ℕ} (F G : MvPolynomial (Fin s) ℤ)
    (v : Fin s → ℝ) (hg : val G v ≠ 0) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 1 ≤ C ∧ ∃ d : ℕ, 1 ≤ d ∧
      ∀ (h : ℕ) (p : Fin s → ℤ) (δ : ℝ), 1 ≤ h → 0 ≤ δ → δ ≤ η →
      (∀ i, |v i-(p i:ℝ)/h| ≤ δ) →
      ∃ a : ℤ, ∃ q : ℕ, 1 ≤ q ∧ (q:ℝ) ≤ C*(h:ℝ)^d ∧
        |val F v / val G v - (a:ℝ)/q| ≤ C*δ := by
  let f := fun x => val F x / val G x
  have gcont := (diff_val G v).continuousAt
  have fdiff : ContDiffAt ℝ 1 f v := (diff_val F v).div (diff_val G v) hg
  obtain ⟨K,U,hU,lip⟩ := fdiff.exists_lipschitzOnWith
  have near : ∀ᶠ y in 𝓝 v, y ∈ U ∧ val G y ≠ 0 ∧ |val G y| < |val G v|+1 := by
    filter_upwards [hU, gcont.eventually_ne hg, gcont.abs.eventually
      (gt_mem_nhds (by linarith : |val G v| < |val G v|+1))] with y hu hn hb
    exact ⟨hu,hn,hb⟩
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp near
  obtain ⟨dF,clF⟩ := clear_eval F
  obtain ⟨dG,clG⟩ := clear_eval G
  let C := max (K:ℝ) (|val G v|+1)
  have hC : 1 ≤ C := (by linarith [abs_nonneg (val G v)] : 1 ≤ |val G v|+1).trans (le_max_right _ _)
  refine ⟨R/2,by positivity,C,hC,dF+dG+1,by omega,?_⟩
  intro h p δ hh hδ hη he
  let y := fun i => (p i:ℝ)/h
  have hd : dist v y ≤ δ := by
    rw [dist_eq_norm, pi_norm_le_iff_of_nonneg hδ]
    exact he
  have hy : y ∈ Metric.ball v R := by rw [Metric.mem_ball,dist_comm]; linarith
  obtain ⟨hyU,hgy,hgyb⟩ := hball hy
  obtain ⟨A,hA⟩ := clF h p hh
  obtain ⟨B,hB⟩ := clG h p hh
  let q := B*(h:ℤ)^dF
  let a := A*(h:ℤ)^dG
  have hhp : (0:ℝ) < h := by exact_mod_cast hh
  have qval : (q:ℝ) = (h:ℝ)^(dF+dG) * val G y := by
    dsimp [q]; push_cast; rw [hB,pow_add]; ring
  have aval : (a:ℝ) = (h:ℝ)^(dF+dG) * val F y := by
    dsimp [a]; push_cast; rw [hA,pow_add]; ring
  have qne : q ≠ 0 := by
    have : (q:ℝ) ≠ 0 := qval.trans_ne (mul_ne_zero (pow_pos hhp _).ne' hgy)
    exact_mod_cast this
  obtain ⟨a',ha'⟩ := integer_ratio a q
  have eq : f y = (a':ℝ)/(q.natAbs:ℝ) := by
    rw [← ha',aval,qval,mul_div_mul_left _ _ (pow_pos hhp _).ne']
  refine ⟨a',q.natAbs,Int.natAbs_pos.mpr qne,?_,?_⟩
  · rw [← Int.cast_natCast (R := ℝ) q.natAbs,Int.natCast_natAbs,Int.cast_abs,qval,abs_mul,
      abs_of_pos (pow_pos hhp _),mul_comm]
    exact mul_le_mul (hgyb.le.trans (le_max_right _ _))
      (pow_le_pow_right₀ (by exact_mod_cast hh) (by omega)) (pow_nonneg hhp.le _)
      (by linarith)
  · rw [← eq]
    have he := lip.dist_le_mul v (mem_of_mem_nhds hU) y hyU
    rw [Real.dist_eq] at he
    exact he.trans (mul_le_mul (le_max_left _ _) hd dist_nonneg (by linarith))

/-- The real quantity has rational approximants of all orders with arbitrarily
large common denominators for the entire tuple. -/
def JointFast {s : ℕ} (v : Fin s → ℝ) : Prop :=
  ∀ N b₀ : ℕ, ∃ h : ℕ, max 2 b₀ ≤ h ∧ ∃ p : Fin s → ℤ,
    ∀ i, |v i-(p i:ℝ)/h| ≤ 1/(h:ℝ)^N

/-- Synchronize finitely many coefficient approximations with a Liouville
argument by taking its denominator as the scale. -/
theorem jointFast_cons {s : ℕ} {v : Fin s → ℝ} (hv : ∀ i, ScaleApproximable (v i))
    {ξ : ℝ} (hξ : Liouville ξ) : JointFast (Fin.cons ξ v) := by
  intro N b₀
  let M := N+1
  obtain ⟨D,hD,H₀,hH₀,hs⟩ := simultaneous_approximation v hv M (by dsimp [M]; omega)
  obtain ⟨b,hb,a,_,ha⟩ := frequently_atTop.mp (hξ.frequently_exists_num ((D+1)*M))
    (max H₀ (max 2 b₀))
  have bh : H₀ ≤ b := (le_max_left _ _).trans hb
  obtain ⟨h,hh,hhb,c,hc⟩ := hs b bh
  have hbpos : 0 < b := by omega
  let H := b*h
  have hHbig : b ≤ H := Nat.le_mul_of_pos_right _ hh
  have hprod : H ≤ b^(D+1) := by
    dsimp [H]; rw [pow_succ,mul_comm (b^D)]; gcongr
  have hfloat : (H:ℝ) ≤ (b:ℝ)^(D+1) := by exact_mod_cast hprod
  have Hpos : (0:ℝ) < H := by exact_mod_cast hbpos.trans_le hHbig
  have Hone : 1 ≤ (H:ℝ) := by exact_mod_cast (show 1 ≤ H by omega)
  have hj : 1/(H:ℝ)^M ≤ 1/(H:ℝ)^N :=
    one_div_le_one_div_of_le (pow_pos Hpos _) (pow_le_pow_right₀ Hone (by dsimp [M]; omega))
  refine ⟨H,((le_max_right _ _).trans hb).trans hHbig,Fin.cons (a*(h:ℤ)) (fun i => c i*(b:ℤ)),?_⟩
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [Fin.cons_zero]
    have eq : ((a*(h:ℤ):ℤ):ℝ)/H = (a:ℝ)/b := by
      dsimp [H]; push_cast; exact mul_div_mul_right _ _ (by exact_mod_cast (show h ≠ 0 by omega))
    rw [eq]
    apply ha.le.trans
    apply le_trans _ hj
    apply one_div_le_one_div_of_le (pow_pos Hpos _)
    rw [pow_mul]
    exact pow_le_pow_left₀ Hpos.le hfloat _
  · simp only [Fin.cons_succ]
    have eq : ((c i*(b:ℤ):ℤ):ℝ)/H = (c i:ℝ)/h := by
      dsimp [H]; push_cast; rw [mul_comm (b:ℝ)]; exact mul_div_mul_right _ _ (by exact_mod_cast hbpos.ne')
    rw [eq]
    apply (hc i).trans
    simpa only [H,Nat.cast_mul] using hj

end MahlerLeanII.Evaluation
