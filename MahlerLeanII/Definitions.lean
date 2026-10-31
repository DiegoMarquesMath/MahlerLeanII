import Mathlib.NumberTheory.Transcendental.Liouville.Basic

/-!
# Approximation at every sufficiently large scale

Definition 1.1 of Diego Marques, *Mahler's Problem on Liouville Numbers
II. Rational Maps*. Natural numbers represent positive integer orders,
denominator exponents, scales and denominators, with explicit lower bounds.
The approximations need not be reduced and zero error is allowed.
-/

namespace MahlerLeanII

/-- Equation (1.3) at one scale. -/
def ApproximationAt (x : ℝ) (N D H : ℕ) : Prop :=
  ∃ p : ℤ, ∃ q : ℕ, 1 ≤ q ∧ q ≤ H ^ D ∧
    |x - (p : ℝ) / (q : ℝ)| ≤ 1 / ((H : ℝ) * (q : ℝ)) ^ N

/-- Definition 1.1. The cutoff depends on `x`, `N` and `D`, not on `H`. -/
def ScaleApproximable (x : ℝ) : Prop :=
  ∀ N : ℕ, 1 ≤ N →
    ∃ D : ℕ, 1 ≤ D ∧
      ∃ H₀ : ℕ, 2 ≤ H₀ ∧ ∀ H : ℕ, H₀ ≤ H → ApproximationAt x N D H

/-- The underlying set of the manuscript's coefficient field.
No field structure is assumed in this definition. -/
def coefficientSet : Set ℝ := {x | ScaleApproximable x}

/-- The set `Q ∪ Lio`, using mathlib's standard Liouville predicate. -/
def rationalOrLiouville (x : ℝ) : Prop :=
  (∃ r : ℚ, (r : ℝ) = x) ∨ Liouville x

/-- Equation (5.1). Membership in the obstructed scale family additionally
requires `2 ≤ H`; the strict approximation inequalities are recorded here. -/
def ObstructedAt (x : ℝ) (N D H : ℕ) : Prop :=
  ∀ p : ℤ, ∀ q : ℕ, 1 ≤ q → q ≤ H ^ D →
    1 / ((H : ℝ) * (q : ℝ)) ^ N < |x - (p : ℝ) / (q : ℝ)|

end MahlerLeanII
