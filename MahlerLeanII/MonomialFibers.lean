import MahlerLeanII.RationalEvaluation
import MahlerLeanII.CoefficientField
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Rational fibers and Liouville preservation for monomials

The full strong-Liouville construction in manuscript Section 8 has two
separate mathematical tasks:
  (1) prove that coefficients in the canonical field send Liouville
      arguments to rational-or-Liouville values;
  (2) rule out Liouville inputs in rational fibers using the
      arithmetic of algebraic approximants.

This file formalizes their *unconditional logical bridge* for monomials.
It does not postulate existence of a special coefficient.
-/

noncomputable section
namespace MahlerLeanII

open Polynomial

/-- Any coefficient in the canonical field yields rational-or-Liouville
values for every monomial on Liouville arguments. -/
theorem monomial_rationalOrLiouville
    (σ ξ : ℝ) (m : ℕ)
    (hσ : σ ∈ coefficientSubfield) (hξ : Liouville ξ) :
    rationalOrLiouville (σ * ξ ^ m) := by
  have hp : ∀ j : ℕ, ScaleApproximable ((Polynomial.monomial m σ).coeff j) := by
    intro j
    by_cases h : m = j
    · subst j
      simpa using (mem_coefficientSubfield σ).mp hσ
    · simpa [Polynomial.coeff_monomial, h] using
        (rational_scaleApproximable (0 : ℚ))
  have hq : ∀ j : ℕ, ScaleApproximable ((1 : Polynomial ℝ).coeff j) := by
    intro j
    by_cases h : j = 0
    · subst j
      simpa using rational_scaleApproximable (1 : ℚ)
    · simpa [Polynomial.coeff_one, h] using
        (rational_scaleApproximable (0 : ℚ))
  have he := evaluation_of_coefficients (Polynomial.monomial m σ)
    (1 : Polynomial ℝ) hp hq hξ (by simp)
  simpa [Polynomial.eval_monomial] using he

/-- Exact preservation of Liouville numbers by a monomial of any degree
follows from the canonical coefficient condition and absence of
Liouville points in all rational fibers. -/
theorem monomial_preserves_of_fiber_free
    (σ : ℝ) (m : ℕ) (hσ : σ ∈ coefficientSubfield)
    (hfiber : ∀ (t : ℚ) (ξ : ℝ), Liouville ξ →
      σ * ξ ^ m ≠ (t : ℝ)) :
    ∀ ξ : ℝ, Liouville ξ → Liouville (σ * ξ ^ m) := by
  intro ξ hξ
  rcases monomial_rationalOrLiouville σ ξ m hσ hξ with ⟨t,ht⟩ | hLi
  · exact ((hfiber t ξ hξ) ht.symm).elim
  · exact hLi

/-- The zero fiber of a nonzero monomial does not meet the Liouville
numbers. Thus it suffices to exclude the nonzero rational fibers,
as done in Theorems 1.5 and 9.2 of the manuscript. -/
theorem monomial_preserves_of_nonzero_fibers
    (σ : ℝ) (m : ℕ) (hσ : σ ∈ coefficientSubfield) (hσ0 : σ ≠ 0)
    (hfiber : ∀ t : ℚ, t ≠ 0 → ∀ ξ : ℝ, Liouville ξ →
      σ * ξ ^ m ≠ (t : ℝ)) :
    ∀ ξ : ℝ, Liouville ξ → Liouville (σ * ξ ^ m) := by
  apply monomial_preserves_of_fiber_free σ m hσ
  intro t ξ hξ
  have hx0 : ξ ≠ 0 := by
    intro h
    apply hξ.irrational
    exact ⟨0, by simp [h]⟩
  have hprod : σ * ξ ^ m ≠ 0 := mul_ne_zero hσ0 (pow_ne_zero m hx0)
  by_cases ht : t = 0
  · intro heq
    apply hprod
    simpa [ht] using heq
  · exact hfiber t ht ξ hξ

end MahlerLeanII
