import MahlerLeanII.Definitions
import Mathlib.Tactic

namespace MahlerLeanII

/-- Negating the non-strict error bound gives a strict obstruction. -/
theorem not_approximationAt_iff (x : ℝ) (N D H : ℕ) :
    ¬ ApproximationAt x N D H ↔ ObstructedAt x N D H := by
  classical
  simp [ApproximationAt, ObstructedAt]

/-- Lemma 5.1. For one fixed order, every denominator exponent admits
obstructed scales beyond every cutoff. The order is chosen first. -/
theorem not_scaleApproximable_iff (x : ℝ) :
    ¬ ScaleApproximable x ↔
      ∃ N : ℕ, 1 ≤ N ∧ ∀ D : ℕ, 1 ≤ D →
        ∀ H₀ : ℕ, 2 ≤ H₀ → ∃ H : ℕ, H₀ ≤ H ∧ ObstructedAt x N D H := by
  classical
  constructor
  · intro hx
    by_contra hbad
    apply hx
    intro N hN
    by_contra horder
    apply hbad
    refine ⟨N, hN, ?_⟩
    intro D hD H₀ hH₀
    by_contra hcutoff
    apply horder
    refine ⟨D, hD, H₀, hH₀, ?_⟩
    intro H hH
    by_contra hscale
    exact hcutoff ⟨H, hH, (not_approximationAt_iff x N D H).mp hscale⟩
  · rintro ⟨N, hN, hbad⟩ hx
    obtain ⟨D, hD, H₀, hH₀, happrox⟩ := hx N hN
    obtain ⟨H, hH, hobs⟩ := hbad D hD H₀ hH₀
    exact (not_approximationAt_iff x N D H).mpr hobs (happrox H hH)

end MahlerLeanII
