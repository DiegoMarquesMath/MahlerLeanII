import MahlerLeanII.Definitions
import Mathlib.Tactic

namespace MahlerLeanII

/-- The rational inclusion in Lemma 2.1. -/
theorem rational_scaleApproximable (r : ℚ) : ScaleApproximable (r : ℝ) := by
  intro N _hN
  refine ⟨1, by omega, max 2 r.den, le_max_left _ _, ?_⟩
  intro H hH
  refine ⟨r.num, r.den, Nat.succ_le_of_lt r.den_pos, ?_, ?_⟩
  · simpa only [pow_one] using (le_max_right 2 r.den).trans hH
  · simp only [Rat.cast_def, sub_self, abs_zero]
    positivity

/-- The irrational case of Lemma 2.1. Doubling both parts of an approximant
ensures a denominator greater than one, even when its original denominator is one. -/
theorem liouville_of_scaleApproximable_of_irrational
    {x : ℝ} (hx : ScaleApproximable x) (hi : Irrational x) : Liouville x := by
  intro N
  obtain ⟨D, _hD, H₀, _hH₀, happrox⟩ := hx (N + 1) (by omega)
  let H := max H₀ 4
  obtain ⟨p, q, hq, _hqD, herr⟩ := happrox H (le_max_left _ _)
  have hH : (4 : ℝ) ≤ H := by exact_mod_cast (le_max_right H₀ 4)
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := lt_of_lt_of_le (by norm_num) hqR
  have hbase : (1 : ℝ) < (H : ℝ) * q := by nlinarith
  have htwice : (2 : ℝ) * q ≤ (H : ℝ) * q := by nlinarith
  have hpowers : ((2 : ℝ) * q) ^ N < ((H : ℝ) * q) ^ (N + 1) := by
    calc
      ((2 : ℝ) * q) ^ N ≤ ((H : ℝ) * q) ^ N :=
        pow_le_pow_left₀ (by positivity) htwice N
      _ < ((H : ℝ) * q) ^ (N + 1) :=
        pow_lt_pow_right₀ hbase (Nat.lt_succ_self N)
  have hbound : |x - (p : ℝ) / q| < 1 / ((2 : ℝ) * q) ^ N :=
    lt_of_le_of_lt herr (one_div_lt_one_div_of_lt (by positivity) hpowers)
  refine ⟨2 * p, (2 * q : ℕ), ?_, hi.ne_rational _ _, ?_⟩
  · exact_mod_cast (show 1 < 2 * q by omega)
  · have hcancel : ((2 * p : ℤ) : ℝ) / ((2 * q : ℕ) : ℝ) =
        (p : ℝ) / (q : ℝ) := by
      push_cast
      exact mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)
    simp only [Int.cast_natCast]
    rw [hcancel]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hbound

/-- The second inclusion in Lemma 2.1, without assuming that `coefficientSet`
already has a field structure. -/
theorem scaleApproximable_rationalOrLiouville
    {x : ℝ} (hx : ScaleApproximable x) : rationalOrLiouville x := by
  classical
  by_cases hi : Irrational x
  · exact Or.inr (liouville_of_scaleApproximable_of_irrational hx hi)
  · exact Or.inl (by simpa only [Irrational, Set.mem_range, not_not] using hi)

end MahlerLeanII
