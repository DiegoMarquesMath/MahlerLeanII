import MahlerLeanII.EvaluationArithmetic

/-! The subfield with carrier given by Definition 1.1. -/

noncomputable section
namespace MahlerLeanII
open Evaluation MvPolynomial

private theorem pair_approximable {x y : ℝ} (hx : ScaleApproximable x)
    (hy : ScaleApproximable y) (i : Fin 2) : ScaleApproximable (![x,y] i) := by
  fin_cases i
  · exact hx
  · exact hy

/-- Proposition 2.3. The carrier of the field is exactly the set of
scale-approximable reals. No closure operation is applied to the set. -/
def coefficientSubfield : Subfield ℝ where
  carrier := coefficientSet
  zero_mem' := by simpa using rational_scaleApproximable 0
  one_mem' := by simpa using rational_scaleApproximable 1
  add_mem' := by
    intro x y hx hy
    change ScaleApproximable (x + y)
    have e : val ((X 0 : MvPolynomial (Fin 2) ℤ) + X 1) ![x,y] = x+y := by
      unfold val
      rw [map_add,aeval_X,aeval_X]
      rfl
    have oneval : val (1 : MvPolynomial (Fin 2) ℤ) ![x,y] = 1 := map_one _
    rw [← e]
    simpa only [oneval,div_one] using
      scale_quotient ((X 0 : MvPolynomial (Fin 2) ℤ) + X 1) 1 ![x,y] (pair_approximable hx hy) (oneval.trans_ne one_ne_zero)
  mul_mem' := by
    intro x y hx hy
    change ScaleApproximable (x * y)
    have e : val ((X 0 : MvPolynomial (Fin 2) ℤ) * X 1) ![x,y] = x*y := by
      unfold val
      rw [map_mul,aeval_X,aeval_X]
      rfl
    have oneval : val (1 : MvPolynomial (Fin 2) ℤ) ![x,y] = 1 := map_one _
    rw [← e]
    simpa only [oneval,div_one] using
      scale_quotient ((X 0 : MvPolynomial (Fin 2) ℤ) * X 1) 1 ![x,y] (pair_approximable hx hy) (oneval.trans_ne one_ne_zero)
  neg_mem' := by
    intro x hx
    have all (i : Fin 1) : ScaleApproximable (![x] i) := by fin_cases i; exact hx
    simpa [val] using scale_quotient (-X 0) 1 ![x] all (by simp [val])
  inv_mem' := by
    intro x hx
    by_cases hz : x = 0
    · subst x; simpa using rational_scaleApproximable 0
    · have all (i : Fin 1) : ScaleApproximable (![x] i) := by fin_cases i; exact hx
      simpa [val] using scale_quotient 1 (X 0) ![x] all (by simpa [val] using hz)

@[simp] theorem mem_coefficientSubfield (x : ℝ) :
    x ∈ coefficientSubfield ↔ ScaleApproximable x := Iff.rfl

end MahlerLeanII
