import MahlerLeanII.EvaluationArithmetic
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! Section 3. Evaluate the numerator and denominator as integral
polynomials in the argument and in their coefficients. -/

noncomputable section
namespace MahlerLeanII
open Evaluation

/-- Proposition 3.1 in normalized coefficients, including constant maps. -/
theorem evaluation_of_coefficients (P Q : Polynomial ℝ)
    (hP : ∀ j, ScaleApproximable (P.coeff j)) (hQ : ∀ j, ScaleApproximable (Q.coeff j))
    {ξ : ℝ} (hξ : Liouville ξ) (hden : Q.eval ξ ≠ 0) :
    rationalOrLiouville (P.eval ξ / Q.eval ξ) := by
  let d := max P.natDegree Q.natDegree + 1
  let v : Fin (d+d) → ℝ := Fin.addCases (fun i : Fin d => P.coeff i) (fun i : Fin d => Q.coeff i)
  have good (i) : ScaleApproximable (v i) := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [v,Fin.addCases_left] using hP (j:ℕ)
    · simpa only [v,Fin.addCases_right] using hQ (j:ℕ)
  let z : Fin (d+d+1) → ℝ := Fin.cons ξ v
  let pol : (Fin d → Fin (d+d)) → MvPolynomial (Fin (d+d+1)) ℤ := fun idx =>
    ∑ j : Fin d, MvPolynomial.X (idx j).succ * (MvPolynomial.X 0)^(j:ℕ)
  have formula (idx : Fin d → Fin (d+d)) (p : Polynomial ℝ) (hd : p.natDegree < d)
      (h : ∀ i : Fin d, v (idx i) = p.coeff i) : val (pol idx) z = p.eval ξ := by
    rw [Polynomial.eval_eq_sum_range' hd,← Fin.sum_univ_eq_sum_range]
    simp only [val,pol,map_sum,map_mul,map_pow,MvPolynomial.aeval_X,z,Fin.cons_succ,Fin.cons_zero,h]
  have hp := formula (fun j => j.castAdd d) P (by dsimp [d]; omega) (by intro j; exact Fin.addCases_left j)
  have hq := formula (fun j => Fin.natAdd d j) Q (by dsimp [d]; omega) (by intro j; exact Fin.addCases_right j)
  rw [← hp,← hq]
  exact rationalOrLiouville_of_jointFast _ _ z (jointFast_cons good hξ) (hq.trans_ne hden)

end MahlerLeanII
