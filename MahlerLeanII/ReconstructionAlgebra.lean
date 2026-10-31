import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic

/-!
# Algebraic lemmas for Section 4

These lemmas cover the algebraic part of stable rational interpolation.
They do not assert the perturbation bound or the height estimate in Lemma 4.1.
The strict degree condition uses `degree`, not `natDegree`, so the zero
polynomial is still admissible when the denominator has degree zero.
-/

set_option autoImplicit false

namespace MahlerLeanII.Reconstruction

open Polynomial

/-- The kernel argument for the normalized polynomial map in Section 4.
No Liouville approximation or coefficient-field result is assumed. -/
theorem kernel_trivial {P Q U W : ℝ[X]}
    (hcop : IsCoprime P Q) (hQ : Q ≠ 0)
    (hWdeg : W.degree < Q.degree) (hrel : Q * U - P * W = 0) :
    U = 0 ∧ W = 0 := by
  have hmul : Q * U = P * W := sub_eq_zero.mp hrel
  have hdvd : Q ∣ W := hcop.symm.dvd_of_dvd_mul_left ⟨U, hmul.symm⟩
  have hW : W = 0 := Polynomial.eq_zero_of_dvd_of_degree_lt hdvd hWdeg
  have hQU : Q * U = 0 := by simpa only [hW, mul_zero] using hmul
  exact ⟨(mul_eq_zero.mp hQU).resolve_left hQ, hW⟩

/-- Injectivity of the polynomial map on the normalized denominator chart. -/
theorem polynomial_map_injective {P Q U₁ U₂ W₁ W₂ : ℝ[X]}
    (hcop : IsCoprime P Q) (hQ : Q ≠ 0)
    (hW₁ : W₁.degree < Q.degree) (hW₂ : W₂.degree < Q.degree)
    (hrel : Q * U₁ - P * W₁ = Q * U₂ - P * W₂) :
    U₁ = U₂ ∧ W₁ = W₂ := by
  have hdeg : (W₁ - W₂).degree < Q.degree :=
    (Polynomial.degree_sub_le W₁ W₂).trans_lt (max_lt hW₁ hW₂)
  have hdiff : Q * (U₁ - U₂) - P * (W₁ - W₂) = 0 := by
    calc
      Q * (U₁ - U₂) - P * (W₁ - W₂) =
          (Q * U₁ - P * W₁) - (Q * U₂ - P * W₂) := by ring
      _ = 0 := sub_eq_zero.mpr hrel
  obtain ⟨hU, hW⟩ := kernel_trivial hcop hQ hdeg hdiff
  exact ⟨sub_eq_zero.mp hU, sub_eq_zero.mp hW⟩

/-- The cross-product polynomial has degree at most `r+s`. -/
theorem relation_natDegree_le {r s : ℕ} {P Q U W : ℝ[X]}
    (hP : P.natDegree ≤ r) (hQ : Q.natDegree ≤ s)
    (hU : U.natDegree ≤ r) (hW : W.natDegree ≤ s) :
    (Q * U - P * W).natDegree ≤ r + s := by
  have hQU : (Q * U).natDegree ≤ r + s := by
    simpa only [Nat.add_comm] using Polynomial.natDegree_mul_le_of_le hQ hU
  have hPW : (P * W).natDegree ≤ r + s :=
    Polynomial.natDegree_mul_le_of_le hP hW
  exact (Polynomial.natDegree_sub_le _ _).trans (max_le hQU hPW)

/-- A cross-product relation at `r+s+1` distinct points is a polynomial identity. -/
theorem relation_eq_zero_of_samples {r s : ℕ} {P Q U W : ℝ[X]}
    (hP : P.natDegree ≤ r) (hQ : Q.natDegree ≤ s)
    (hU : U.natDegree ≤ r) (hW : W.natDegree ≤ s)
    (x : Fin (r + s + 1) → ℝ) (hx : Function.Injective x)
    (heval : ∀ i, (Q * U - P * W).eval (x i) = 0) :
    Q * U - P * W = 0 := by
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hx heval
  simpa only [Fintype.card_fin] using
    lt_of_le_of_lt (relation_natDegree_le hP hQ hU hW) (Nat.lt_succ_self (r + s))

/-- The corresponding homogeneous evaluation system has trivial kernel.
The degree bounds are the bounds satisfied by the two polynomial blocks. -/
theorem kernel_trivial_of_samples {r s : ℕ} {P Q U W : ℝ[X]}
    (hcop : IsCoprime P Q) (hQzero : Q ≠ 0)
    (hP : P.natDegree ≤ r) (hQ : Q.natDegree ≤ s)
    (hU : U.natDegree ≤ r) (hW : W.natDegree ≤ s)
    (hWdeg : W.degree < Q.degree)
    (x : Fin (r + s + 1) → ℝ) (hx : Function.Injective x)
    (heval : ∀ i, (Q * U - P * W).eval (x i) = 0) :
    U = 0 ∧ W = 0 :=
  kernel_trivial hcop hQzero hWdeg
    (relation_eq_zero_of_samples hP hQ hU hW x hx heval)

end MahlerLeanII.Reconstruction
