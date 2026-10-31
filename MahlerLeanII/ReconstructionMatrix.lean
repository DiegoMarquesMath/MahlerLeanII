import MahlerLeanII.ReconstructionAlgebra
import MahlerLeanII.ReconstructionDeterminant
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The normalized reconstruction matrix

This file specializes the general determinant identities to the polynomial
family in Section 4. Coprimality, rather than an assumed determinant condition,
gives the nonzero coefficient determinant.

The dimension is written `(r + 1) + s` to follow the two coefficient blocks.
It is the manuscript's `n = r + s + 1`. Strict polynomial degree bounds retain
the case `s = 0`, when the second block is empty.

The perturbation estimates and rational height bound are separate steps.
-/

set_option autoImplicit false

noncomputable section

namespace MahlerLeanII.Reconstruction

open Polynomial Finset

private theorem bounded_relation_mem {r s : ℕ} {P Q : ℝ[X]}
    (hP : P.natDegree ≤ r) (hQ : Q.natDegree ≤ s)
    (z : Polynomial.degreeLT ℝ (r + 1) × Polynomial.degreeLT ℝ s) :
    Q * (z.1 : ℝ[X]) - P * (z.2 : ℝ[X]) ∈
      Polynomial.degreeLT ℝ (r + 1 + s) := by
  have hU : (z.1 : ℝ[X]).natDegree ≤ r := by
    apply Polynomial.natDegree_le_of_degree_le
    apply Polynomial.mem_degreeLE.mp
    simpa only [Polynomial.degreeLT_succ_eq_degreeLE] using z.1.property
  have hW : (z.2 : ℝ[X]).natDegree ≤ s :=
    Polynomial.natDegree_le_of_degree_le
      (le_of_lt (Polynomial.mem_degreeLT.mp z.2.property))
  apply Polynomial.mem_degreeLT.mpr
  exact (Polynomial.degree_le_of_natDegree_le
    (relation_natDegree_le hP hQ hU hW)).trans_lt
      (Nat.cast_lt.mpr (by omega : r + s < r + 1 + s))

/-- The bounded-degree map `(U,W) ↦ Q*U-P*W` in the reconstruction proof. -/
def boundedPolynomialMap {r s : ℕ} (P Q : ℝ[X])
    (hP : P.natDegree ≤ r) (hQ : Q.natDegree ≤ s) :
    (Polynomial.degreeLT ℝ (r + 1) × Polynomial.degreeLT ℝ s) →ₗ[ℝ]
      Polynomial.degreeLT ℝ (r + 1 + s) where
  toFun z := ⟨Q * (z.1 : ℝ[X]) - P * (z.2 : ℝ[X]),
    bounded_relation_mem hP hQ z⟩
  map_add' z z' := by
    apply Subtype.ext
    change Q * ((z.1 : ℝ[X]) + (z'.1 : ℝ[X])) -
        P * ((z.2 : ℝ[X]) + (z'.2 : ℝ[X])) =
      (Q * (z.1 : ℝ[X]) - P * (z.2 : ℝ[X])) +
        (Q * (z'.1 : ℝ[X]) - P * (z'.2 : ℝ[X]))
    ring
  map_smul' c z := by
    apply Subtype.ext
    change Q * (c • (z.1 : ℝ[X])) - P * (c • (z.2 : ℝ[X])) =
      c • (Q * (z.1 : ℝ[X]) - P * (z.2 : ℝ[X]))
    simp only [Polynomial.smul_eq_C_mul]
    ring

@[simp]
theorem bounded_polynomial_map_apply {r s : ℕ} {P Q : ℝ[X]}
    (hP : P.natDegree ≤ r) (hQ : Q.natDegree ≤ s)
    (z : Polynomial.degreeLT ℝ (r + 1) × Polynomial.degreeLT ℝ s) :
    (boundedPolynomialMap P Q hP hQ z : ℝ[X]) =
      Q * (z.1 : ℝ[X]) - P * (z.2 : ℝ[X]) := rfl

/-- Coprimality makes the bounded-degree map injective, including when `s=0`. -/
theorem bounded_polynomial_map_injective {r s : ℕ} {P Q : ℝ[X]}
    (hP : P.natDegree ≤ r) (hQ : Q.natDegree ≤ s)
    (hcop : IsCoprime P Q) (hQzero : Q ≠ 0) (hQdegree : Q.natDegree = s) :
    Function.Injective (boundedPolynomialMap P Q hP hQ) := by
  have hW (W : Polynomial.degreeLT ℝ s) : (W : ℝ[X]).degree < Q.degree := by
    rw [Polynomial.degree_eq_natDegree hQzero, hQdegree]
    exact Polynomial.mem_degreeLT.mp W.property
  intro z z' hz
  have hrel := congrArg
    (fun v : Polynomial.degreeLT ℝ (r + 1 + s) => (v : ℝ[X])) hz
  change Q * (z.1 : ℝ[X]) - P * (z.2 : ℝ[X]) =
    Q * (z'.1 : ℝ[X]) - P * (z'.2 : ℝ[X]) at hrel
  obtain ⟨hU, hW'⟩ := polynomial_map_injective hcop hQzero (hW z.2) (hW z'.2) hrel
  exact Prod.ext (Subtype.ext hU) (Subtype.ext hW')

/-- The column polynomials `X^j Q` for `j ≤ r`, followed by `-X^j P` for `j < s`. -/
def reconstructionFamily (P Q : ℝ[X]) (r s : ℕ) : Fin (r + 1 + s) → ℝ[X] :=
  Fin.addCases (fun j : Fin (r + 1) => X ^ (j : ℕ) * Q)
    (fun j : Fin s => -(X ^ (j : ℕ) * P))

/-- The two polynomial blocks are the images of the standard domain basis. -/
theorem bounded_polynomial_map_basis {r s : ℕ} {P Q : ℝ[X]}
    (hP : P.natDegree ≤ r) (hQ : Q.natDegree ≤ s) (j : Fin (r + 1 + s)) :
    (boundedPolynomialMap P Q hP hQ (Polynomial.degreeLT.basisProd ℝ (r + 1) s j) :
      ℝ[X]) = reconstructionFamily P Q r s j := by
  refine Fin.addCases ?_ ?_ j
  · intro k
    simp [reconstructionFamily, mul_comm]
  · intro k
    simp [reconstructionFamily, mul_comm]

/-- Every column polynomial has degree below the matrix size. -/
theorem reconstruction_family_natDegree_lt {r s : ℕ} {P Q : ℝ[X]}
    (hP : P.natDegree ≤ r) (hQ : Q.natDegree ≤ s) (j : Fin (r + 1 + s)) :
    (reconstructionFamily P Q r s j).natDegree < r + 1 + s := by
  have hm := Polynomial.mem_degreeLT.mp
    (boundedPolynomialMap P Q hP hQ (Polynomial.degreeLT.basisProd ℝ (r + 1) s j)).property
  rw [bounded_polynomial_map_basis hP hQ j] at hm
  by_cases hz : reconstructionFamily P Q r s j = 0
  · simpa only [hz, Polynomial.natDegree_zero] using (by omega : 0 < r + 1 + s)
  · exact (Polynomial.natDegree_lt_iff_degree_lt hz).mpr hm

/-- The coefficient matrix depends only on the polynomial pair and its degree bounds. -/
def reconstructionCoefficientMatrix (P Q : ℝ[X]) (r s : ℕ) :
    Matrix (Fin (r + 1 + s)) (Fin (r + 1 + s)) ℝ :=
  Matrix.of (fun i j => (reconstructionFamily P Q r s j).coeff i)

/-- The coefficient determinant is nonzero for a coprime pair with `deg Q = s`.
This discharges the nonsingularity hypothesis of the general determinant lemmas. -/
theorem reconstruction_coefficient_det_ne_zero {r s : ℕ} {P Q : ℝ[X]}
    (hP : P.natDegree ≤ r) (hQ : Q.natDegree ≤ s)
    (hcop : IsCoprime P Q) (hQzero : Q ≠ 0) (hQdegree : Q.natDegree = s) :
    (reconstructionCoefficientMatrix P Q r s).det ≠ 0 := by
  classical
  let f := boundedPolynomialMap P Q hP hQ
  let b := Polynomial.degreeLT.basisProd ℝ (r + 1) s
  let c := Polynomial.degreeLT.basis ℝ (r + 1 + s)
  let e : (Polynomial.degreeLT ℝ (r + 1) × Polynomial.degreeLT ℝ s) ≃ₗ[ℝ]
      Polynomial.degreeLT ℝ (r + 1 + s) :=
    f.linearEquivOfInjective
      (bounded_polynomial_map_injective hP hQ hcop hQzero hQdegree)
      (Polynomial.degreeLT.addLinearEquiv ℝ (r + 1) s).finrank_eq.symm
  have hcomp : e.symm.toLinearMap.comp f = LinearMap.id := by
    apply LinearMap.ext
    intro z
    change e.symm (e z) = z
    exact e.symm_apply_apply z
  have hleft : LinearMap.toMatrix c b e.symm.toLinearMap *
      LinearMap.toMatrix b c f = 1 := by
    rw [← LinearMap.toMatrix_comp b c b, hcomp, LinearMap.toMatrix_id]
  have hmatrix : reconstructionCoefficientMatrix P Q r s =
      LinearMap.toMatrix b c f := by
    ext i j
    change (reconstructionFamily P Q r s j).coeff i =
      LinearMap.toMatrix (Polynomial.degreeLT.basisProd ℝ (r + 1) s)
        (Polynomial.degreeLT.basis ℝ (r + 1 + s)) (boundedPolynomialMap P Q hP hQ) i j
    rw [LinearMap.toMatrix_apply, Polynomial.degreeLT.basis_repr,
      bounded_polynomial_map_basis hP hQ j]
  rw [hmatrix]
  exact Matrix.det_ne_zero_of_left_inverse hleft

/-- The square interpolation matrix with the leading denominator coefficient omitted. -/
def normalizedMatrix (r s : ℕ) (x y : Fin (r + 1 + s) → ℝ) :
    Matrix (Fin (r + 1 + s)) (Fin (r + 1 + s)) ℝ :=
  Matrix.of (fun i => Fin.addCases (fun j : Fin (r + 1) => x i ^ (j : ℕ))
    (fun j : Fin s => -(y i) * x i ^ (j : ℕ)))

/-- At exact values of `P/Q`, the normalized matrix is the evaluation matrix
of the column polynomials divided row by row by `Q(x_i)`. -/
theorem normalized_matrix_eq_divided_evaluation {r s : ℕ} {P Q : ℝ[X]}
    (x : Fin (r + 1 + s) → ℝ) (hQx : ∀ i, Q.eval (x i) ≠ 0) :
    normalizedMatrix r s x (fun i => P.eval (x i) / Q.eval (x i)) =
      Matrix.of (fun i j => (reconstructionFamily P Q r s j).eval (x i) /
        Q.eval (x i)) := by
  ext i j
  refine Fin.addCases ?_ ?_ j
  · intro k
    simp [normalizedMatrix, reconstructionFamily, hQx i]
  · intro k
    simp only [normalizedMatrix, reconstructionFamily, Matrix.of_apply,
      Fin.addCases_right, Polynomial.eval_neg, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, div_eq_mul_inv]
    ring

/-- The exact determinant identity in `eq:vandermonde-minor`.
Its coefficient determinant is independent of the abscissae. -/
theorem normalized_det_factorization {r s : ℕ} {P Q : ℝ[X]}
    (hP : P.natDegree ≤ r) (hQ : Q.natDegree ≤ s)
    (x : Fin (r + 1 + s) → ℝ) (hQx : ∀ i, Q.eval (x i) ≠ 0) :
    (normalizedMatrix r s x (fun i => P.eval (x i) / Q.eval (x i))).det =
      (reconstructionCoefficientMatrix P Q r s).det *
        (∏ i : Fin (r + 1 + s), ∏ j ∈ Ioi i, (x j - x i)) /
          ∏ i, Q.eval (x i) := by
  rw [normalized_matrix_eq_divided_evaluation x hQx]
  rw [divided_evaluation_det_factorization x (reconstructionFamily P Q r s)
    (fun i => Q.eval (x i)) (reconstruction_family_natDegree_lt hP hQ)]
  simp only [reconstructionCoefficientMatrix, mul_comm]

/-- A pole-free list of distinct abscissae gives a nonsingular exact interpolation matrix. -/
theorem normalized_det_ne_zero {r s : ℕ} {P Q : ℝ[X]}
    (hP : P.natDegree ≤ r) (hQ : Q.natDegree ≤ s)
    (hcop : IsCoprime P Q) (hQzero : Q ≠ 0) (hQdegree : Q.natDegree = s)
    (x : Fin (r + 1 + s) → ℝ) (hx : Function.Injective x)
    (hQx : ∀ i, Q.eval (x i) ≠ 0) :
    (normalizedMatrix r s x (fun i => P.eval (x i) / Q.eval (x i))).det ≠ 0 := by
  rw [normalized_det_factorization hP hQ x hQx]
  apply div_ne_zero
  · apply mul_ne_zero (reconstruction_coefficient_det_ne_zero hP hQ hcop hQzero hQdegree)
    have hv : (Matrix.vandermonde x).det ≠ 0 :=
      Matrix.det_vandermonde_ne_zero_iff.mpr hx
    simpa only [Matrix.det_vandermonde] using hv
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => hQx i)

/-- The manuscript's nonzero constant can be chosen before the abscissae. -/
theorem reconstruction_determinant_constant {r s : ℕ} {P Q : ℝ[X]}
    (hP : P.natDegree ≤ r) (hQ : Q.natDegree ≤ s)
    (hcop : IsCoprime P Q) (hQzero : Q ≠ 0) (hQdegree : Q.natDegree = s) :
    ∃ cR : ℝ, cR ≠ 0 ∧ ∀ x : Fin (r + 1 + s) → ℝ,
      (∀ i, Q.eval (x i) ≠ 0) →
      (normalizedMatrix r s x (fun i => P.eval (x i) / Q.eval (x i))).det =
        cR * (∏ i : Fin (r + 1 + s), ∏ j ∈ Ioi i, (x j - x i)) /
          ∏ i, Q.eval (x i) := by
  refine ⟨(reconstructionCoefficientMatrix P Q r s).det,
    reconstruction_coefficient_det_ne_zero hP hQ hcop hQzero hQdegree, ?_⟩
  intro x hQx
  exact normalized_det_factorization hP hQ x hQx

end MahlerLeanII.Reconstruction
