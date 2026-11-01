import MahlerLeanII.EvaluationControl
import MahlerLeanII.Basic

/-! Transfer the local error and height estimates to the two approximation
properties used in the classification. -/

noncomputable section
namespace MahlerLeanII.Evaluation
open MvPolynomial

/-- A quotient of integral polynomials in scale-approximable coefficients is
again scale-approximable at every sufficiently large scale. -/
theorem scale_quotient {s : ℕ} (F G : MvPolynomial (Fin s) ℤ) (v : Fin s → ℝ)
    (hv : ∀ i, ScaleApproximable (v i)) (hg : val G v ≠ 0) :
    ScaleApproximable (val F v / val G v) := by
  intro N hN
  obtain ⟨η,hη,C,hC,d,hd,control⟩ := rational_evaluation_control F G v hg
  let M := d*N+1
  obtain ⟨D,hD,H₀,hH₀,approx⟩ := simultaneous_approximation v hv M (by dsimp [M]; omega)
  obtain ⟨B,hB⟩ := exists_nat_gt (max (1/η) (max C (C^(N+1))))
  refine ⟨D*d+1,by omega,max H₀ B,hH₀.trans (le_max_left _ _),?_⟩
  intro H hH
  obtain ⟨h,hh,hhD,p,hp⟩ := approx H ((le_max_left _ _).trans hH)
  have hHone : 1 ≤ (H:ℝ) := by exact_mod_cast (show 1 ≤ H by omega)
  have hhone : 1 ≤ (h:ℝ) := by exact_mod_cast hh
  have big : max (1/η) (max C (C^(N+1))) ≤ (H:ℝ) :=
    hB.le.trans (by exact_mod_cast (le_max_right H₀ B).trans hH)
  let Z := (H:ℝ)*h
  have hZ : (H:ℝ) ≤ Z := le_mul_of_one_le_right (by linarith) hhone
  have hZone := hHone.trans hZ
  have hZpos : 0 < Z := by linarith
  have hpow : Z ≤ Z^M := le_self_pow₀ hZone (by dsimp [M]; omega)
  have heta : 1/Z^M ≤ η := (div_le_iff₀ (pow_pos hZpos _)).mpr (by
    have he := (div_le_iff₀ hη).mp (((le_max_left _ _).trans big).trans (hZ.trans hpow))
    linarith only [he,mul_comm (Z^M) η])
  obtain ⟨a,q,hq,hqC,he⟩ := control h p (1/Z^M) hh (by positivity) heta hp
  have cH := (le_max_left C (C^(N+1))).trans ((le_max_right _ _).trans big)
  have hden : (q:ℝ) ≤ (H:ℝ)^(D*d+1) := calc
    (q:ℝ) ≤ C*(h:ℝ)^d := hqC
    _ ≤ (H:ℝ)*((H:ℝ)^D)^d :=
      mul_le_mul cH (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hhD) _) (by positivity) (by positivity)
    _ = _ := by rw [pow_succ,pow_mul,mul_comm]
  refine ⟨a,q,hq,by exact_mod_cast hden,?_⟩
  have hHq : (H:ℝ)*q ≤ C*Z^d := calc
    (H:ℝ)*q ≤ (H:ℝ)*(C*(h:ℝ)^d) := by gcongr
    _ ≤ (H:ℝ)^d*(C*(h:ℝ)^d) := by
      exact mul_le_mul_of_nonneg_right (le_self_pow₀ hHone (by omega)) (by positivity)
    _ = C*Z^d := by dsimp [Z]; rw [mul_pow]; ring
  have cZ := ((le_max_right C (C^(N+1))).trans ((le_max_right _ _).trans big)).trans hZ
  have main : C*((H:ℝ)*q)^N ≤ Z^M := calc
    C*((H:ℝ)*q)^N ≤ C*(C*Z^d)^N :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hHq _) (by linarith)
    _ = C^(N+1)*Z^(d*N) := by rw [mul_pow,pow_succ,pow_mul]; ring
    _ ≤ Z*Z^(d*N) := by gcongr
    _ = Z^M := by dsimp [M]; rw [pow_succ,mul_comm]
  apply he.trans
  rw [mul_one_div,div_le_div_iff₀ (pow_pos hZpos _) (by positivity)]
  simpa only [one_mul] using main

/-- On a tuple with joint approximations of arbitrarily high order, every
defined rational expression with integral coefficients is rational or Liouville. -/
theorem rationalOrLiouville_of_jointFast {s : ℕ} (F G : MvPolynomial (Fin s) ℤ)
    (v : Fin s → ℝ) (hj : JointFast v) (hg : val G v ≠ 0) :
    rationalOrLiouville (val F v / val G v) := by
  classical
  let z := val F v / val G v
  by_cases hi : Irrational z
  · apply Or.inr
    intro N
    obtain ⟨η,hη,C,hC,d,hd,control⟩ := rational_evaluation_control F G v hg
    let M := d*N+1
    obtain ⟨B,hB⟩ := exists_nat_gt (max (1/η) (C*(2*C)^N))
    obtain ⟨h,hh,p,hp⟩ := hj M B
    have hone : 1 ≤ (h:ℝ) := by exact_mod_cast (show 1 ≤ h by omega)
    have hpos : 0 < (h:ℝ) := by linarith
    have big : max (1/η) (C*(2*C)^N) < (h:ℝ) :=
      hB.trans_le (by exact_mod_cast (le_max_right 2 B).trans hh)
    have heη := (div_le_iff₀ hη).mp (((le_max_left _ _).trans big.le).trans
      (le_self_pow₀ (n := M) hone (by dsimp [M]; omega)))
    have heta : 1/(h:ℝ)^M ≤ η := (div_le_iff₀ (pow_pos hpos _)).mpr (by
      linarith only [heη,mul_comm ((h:ℝ)^M) η])
    obtain ⟨a,q,hq,hqC,he⟩ := control h p _ (by omega) (by positivity) heta hp
    have qpos : 0 < (q:ℝ) := by exact_mod_cast hq
    have htwo : 2*(q:ℝ) ≤ (2*C)*(h:ℝ)^d := by linarith only [hqC,mul_assoc (2:ℝ) C ((h:ℝ)^d)]
    have hbound : C*(2*(q:ℝ))^N < (h:ℝ)^M := calc
      C*(2*(q:ℝ))^N ≤ C*((2*C)*(h:ℝ)^d)^N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) htwo _) (by linarith)
      _ = (C*(2*C)^N)*(h:ℝ)^(d*N) := by rw [mul_pow,pow_mul]; ring
      _ < (h:ℝ)*(h:ℝ)^(d*N) := mul_lt_mul_of_pos_right ((le_max_right _ _).trans_lt big) (by positivity)
      _ = _ := by dsimp [M]; rw [pow_succ,mul_comm]
    have herr : |z-(a:ℝ)/q| < 1/(2*(q:ℝ))^N := by
      apply he.trans_lt
      rw [mul_one_div,div_lt_div_iff₀ (pow_pos hpos _) (by positivity)]
      simpa using hbound
    refine ⟨2*a,(2*q:ℕ),by exact_mod_cast (show 1 < 2*q by omega),hi.ne_rational _ _,?_⟩
    push_cast
    simpa only [mul_div_mul_left _ _ (by norm_num : (2:ℝ) ≠ 0)] using herr
  · exact Or.inl (by simpa only [Irrational,Set.mem_range,not_not] using hi)

end MahlerLeanII.Evaluation
