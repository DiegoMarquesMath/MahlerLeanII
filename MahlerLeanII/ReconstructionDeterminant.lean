import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Determinant identities for Section 4

The polynomial family here is arbitrary, with degrees below the matrix size.
The specialization to the normalized reconstruction family is developed in
`ReconstructionMatrix.lean`, using coprimality to prove that the coefficient
matrix is nonsingular. No claim of the complete reconstruction lemma is made
in this file.
-/

set_option autoImplicit false

namespace MahlerLeanII.Reconstruction

open Polynomial Finset

/-- Evaluation equals the Vandermonde matrix times the coefficient matrix.
Unlike the triangular special case in mathlib, all columns may have any
degree strictly below `n`. -/
theorem evaluation_matrix_factorization {n : ℕ}
    (x : Fin n → ℝ) (p : Fin n → ℝ[X])
    (hdeg : ∀ j, (p j).natDegree < n) :
    Matrix.of (fun i j => (p j).eval (x i)) =
      Matrix.vandermonde x * Matrix.of (fun (i j : Fin n) => (p j).coeff i) := by
  classical
  ext i j
  simp_rw [Matrix.mul_apply, eval, Matrix.of_apply, eval₂]
  simp only [Matrix.vandermonde]
  have hsupp : (p j).support ⊆ range n := supp_subset_range (hdeg j)
  rw [sum_eq_of_subset _ (fun k => zero_mul (x i ^ k)) hsupp,
    ← Fin.sum_univ_eq_sum_range]
  congr
  ext k
  rw [mul_comm, Matrix.of_apply, RingHom.id_apply]

/-- The Vandermonde factor for a general polynomial evaluation determinant. -/
theorem evaluation_det_factorization {n : ℕ}
    (x : Fin n → ℝ) (p : Fin n → ℝ[X])
    (hdeg : ∀ j, (p j).natDegree < n) :
    (Matrix.of (fun i j => (p j).eval (x i))).det =
      (∏ i : Fin n, ∏ j ∈ Ioi i, (x j - x i)) *
        (Matrix.of (fun (i j : Fin n) => (p j).coeff i)).det := by
  rw [evaluation_matrix_factorization x p hdeg, Matrix.det_mul, Matrix.det_vandermonde]

/-- Distinct abscissae preserve nonsingularity of the coefficient matrix.
The nonsingularity hypothesis is explicit; its application to the manuscript's
particular polynomial family is not assumed as a project axiom. -/
theorem evaluation_det_ne_zero {n : ℕ}
    (x : Fin n → ℝ) (p : Fin n → ℝ[X])
    (hdeg : ∀ j, (p j).natDegree < n)
    (hx : Function.Injective x)
    (hcoeff : (Matrix.of (fun (i j : Fin n) => (p j).coeff i)).det ≠ 0) :
    (Matrix.of (fun i j => (p j).eval (x i))).det ≠ 0 := by
  rw [evaluation_matrix_factorization x p hdeg, Matrix.det_mul]
  exact mul_ne_zero (Matrix.det_vandermonde_ne_zero_iff.mpr hx) hcoeff

/-- Dividing row `i` by `q i` divides the determinant by the product of the
`q i`. The identity also holds for Lean's totalized division; its interpretation
as normalization of a pole-free rational function requires nonzero `q i`. -/
theorem divided_evaluation_det_factorization {n : ℕ}
    (x : Fin n → ℝ) (p : Fin n → ℝ[X]) (q : Fin n → ℝ)
    (hdeg : ∀ j, (p j).natDegree < n) :
    (Matrix.of (fun i j => (p j).eval (x i) / q i)).det =
      ((∏ i : Fin n, ∏ j ∈ Ioi i, (x j - x i)) *
        (Matrix.of (fun (i j : Fin n) => (p j).coeff i)).det) / ∏ i, q i := by
  classical
  calc
    (Matrix.of (fun i j => (p j).eval (x i) / q i)).det =
        (∏ i, (q i)⁻¹) * (Matrix.of (fun i j => (p j).eval (x i))).det := by
      simpa only [Matrix.of_apply, div_eq_mul_inv, mul_comm] using
        Matrix.det_mul_column (fun i => (q i)⁻¹)
          (Matrix.of (fun i j => (p j).eval (x i)))
    _ = _ := by
      rw [evaluation_det_factorization x p hdeg, Finset.prod_inv_distrib]
      simp only [div_eq_mul_inv]
      ring

end MahlerLeanII.Reconstruction
