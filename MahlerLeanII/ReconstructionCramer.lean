import MahlerLeanII.ReconstructionMatrix
import Mathlib.Analysis.NormedSpace.Alternating.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Polynomial

/-! Cramer's rule for the normalized interpolation equations of Section 4. -/

noncomputable section

namespace MahlerLeanII.Reconstruction

open Polynomial Finset Matrix

/-- Free coefficients in the same order as the columns of the normalized matrix. -/
def freeCoefficients (P Q : ℝ[X]) (r s : ℕ) : Fin (r + 1 + s) → ℝ :=
  Fin.addCases (fun j : Fin (r + 1) => P.coeff j) (fun j : Fin s => Q.coeff j)

/-- The omitted monic term produces the right side of the interpolation system. -/
def normalizedRhs {n : ℕ} (s : ℕ) (x y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => y i * x i ^ s

/-- The same real coefficient vector will carry both the error and height bounds. -/
def cramerCoefficients {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (t : Fin n → ℝ) :
    Fin n → ℝ := fun j => M.cramer t j / M.det

/-- The original coefficient vector solves the exact system, including when the
denominator is constant and there is no second block of free coefficients. -/
theorem normalized_system_exact {r s : ℕ} {P Q : ℝ[X]} (hP : P.natDegree ≤ r)
    (hQ : Q.natDegree = s) (hmonic : Q.Monic) (x : Fin (r + 1 + s) → ℝ)
    (hx : ∀ i, Q.eval (x i) ≠ 0) :
    let y := fun i => P.eval (x i) / Q.eval (x i)
    (normalizedMatrix r s x y) *ᵥ (freeCoefficients P Q r s) = normalizedRhs s x y := by
  dsimp only
  funext i
  let z := x i
  have pval : (∑ j : Fin (r + 1), z ^ (j : ℕ) * P.coeff j) = P.eval z := by
    rw [Polynomial.eval_eq_sum_range' (show P.natDegree < r + 1 by omega)]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  have qval : (∑ j : Fin s, z ^ (j : ℕ) * Q.coeff j) + z ^ s = Q.eval z := by
    rw [Polynomial.eval_eq_sum_range' (show Q.natDegree < s + 1 by omega), Finset.sum_range_succ,
      ← Fin.sum_univ_eq_sum_range]
    have hl : Q.coeff s = 1 := hQ ▸ hmonic.coeff_natDegree
    simp only [hl, one_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  change (∑ j, normalizedMatrix r s x _ i j * freeCoefficients P Q r s j) = _
  rw [Fin.sum_univ_add]
  simp only [normalizedMatrix, freeCoefficients, Matrix.of_apply, Fin.addCases_left,
    Fin.addCases_right, normalizedRhs]
  change (∑ j : Fin (r + 1), z ^ (j : ℕ) * P.coeff j) +
    (∑ j : Fin s, (-(P.eval z / Q.eval z) * z ^ (j : ℕ)) * Q.coeff j) =
      P.eval z / Q.eval z * z ^ s
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, pval]
  have hx' : Q.eval z ≠ 0 := hx i
  field_simp [hx']
  rw [← qval]
  ring

private def continuousRowDet (n : ℕ) :
    ContinuousAlternatingMap ℝ (Fin n → ℝ) ℝ (Fin n) :=
  { Matrix.detRowAlternating (R := ℝ) (n := Fin n) with
    cont := (show Continuous (fun M : Fin n → Fin n → ℝ => (Matrix.of M).det) from
      (continuous_id : Continuous (fun M : Fin n → Fin n → ℝ => M)).matrix_det) }

private theorem rows_norm_le {n : ℕ} {f : Fin n → Fin n → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hf : ∀ i j, |f i j| ≤ K) : ‖f‖ ≤ K := by
  apply (pi_norm_le_iff_of_nonneg hK).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg hK).mpr
  intro j
  simpa only [Real.norm_eq_abs] using hf i j

/-- Uniform boundedness and a Lipschitz estimate for the determinant on a box
of real matrices. No separation assumption is needed here. -/
theorem determinant_box_bounds (n : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧
      (∀ M : Matrix (Fin n) (Fin n) ℝ, (∀ i j, |M i j| ≤ K) → |M.det| ≤ C) ∧
      (∀ M N : Matrix (Fin n) (Fin n) ℝ, ∀ ε : ℝ, 0 ≤ ε →
        (∀ i j, |M i j| ≤ K) → (∀ i j, |N i j| ≤ K) →
        (∀ i j, |M i j - N i j| ≤ ε) → |M.det - N.det| ≤ C * ε) := by
  let F := continuousRowDet n
  let A := ‖F‖ * K ^ n
  let B := ‖F‖ * (n : ℝ) * K ^ (n - 1)
  have ha : 0 ≤ A := by dsimp [A]; positivity
  have hb : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨1 + A + B, by linarith, ?_, ?_⟩
  · intro M hM
    have hm := F.le_opNorm_mul_pow_of_le (m := fun i j => M i j) (rows_norm_le hK hM)
    have hh : |M.det| ≤ A := by simpa only [Real.norm_eq_abs] using hm
    linarith
  · intro M N ε he hM hN hdiff
    let u : Fin n → Fin n → ℝ := fun i j => M i j
    let v : Fin n → Fin n → ℝ := fun i j => N i j
    have hu : ‖u‖ ≤ K := rows_norm_le hK hM
    have hv : ‖v‖ ≤ K := rows_norm_le hK hN
    have huv : ‖u - v‖ ≤ ε := rows_norm_le he hdiff
    have hh := F.norm_image_sub_le u v
    change ‖M.det - N.det‖ ≤ _ at hh
    rw [Real.norm_eq_abs, Fintype.card_fin] at hh
    calc |M.det - N.det| ≤ _ := hh
         _ ≤ B * ε := by
           dsimp [B]
           gcongr
           exact max_le hu hv
         _ ≤ (1 + A + B) * ε := mul_le_mul_of_nonneg_right (by linarith) he

/-- Cramer's numerators at an exact solution are its coordinates times the
determinant. This identity also holds for singular matrices. -/
theorem cramer_of_solution {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    {t θ : Fin n → ℝ} (hsol : M *ᵥ θ = t) (j : Fin n) :
    M.cramer t j = M.det * θ j := by
  subst t
  rw [Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
    Matrix.smul_mulVec, Matrix.one_mulVec]
  rfl

end MahlerLeanII.Reconstruction
