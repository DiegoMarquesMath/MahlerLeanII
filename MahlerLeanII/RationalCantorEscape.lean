import MahlerLeanII.SparseCantor
import MahlerLeanII.RationalEscape
import MahlerLeanII.Classification

/-!
# Theorem 1.3: finite-exponent Cantor escape for rational maps

The obstruction coefficient and its order are fixed *before* the choice
of interval. Therefore the target irrationality exponent is uniform in
the interval, exactly as required in the manuscript.
-/

noncomputable section
namespace MahlerLeanII
open Set MahlerLeanII.Escape

/-- The full Cantor refinement of Theorem 1.3, with an arbitrary
nonempty open pole-free interval and a target exponent independent of it.
A coefficient outside the canonical field provides the obstruction. -/
theorem rational_cantor_escape_of_bad_coefficients
    (R : RatFunc ℝ)
    (hn : R ∉ Set.range (RatFunc.C : ℝ →+* RatFunc ℝ))
    (hb : ¬ ((∀ j, ScaleApproximable (R.num.coeff j)) ∧
      (∀ j, ScaleApproximable (R.denom.coeff j)))) :
    ∃ τ : ℕ, 3 < τ ∧ ∀ (a b : ℝ), a < b →
      (∀ x ∈ Ioo a b, R.denom.eval x ≠ 0) →
      ∃ K : Set ℝ, ∃ B : ℕ,
        K.Nonempty ∧ IsCompact K ∧ Perfect K ∧
        IsTotallyDisconnected K ∧ K ⊆ Ioo a b ∧ 2 ≤ B ∧
        (∀ x ∈ K, Liouville x) ∧
        (∀ x ∈ K, MahlerLean.EventualTargetAvoidance
          (R.num.eval x / R.denom.eval x) τ B) ∧
        (∀ x ∈ K, ¬ rationalOrLiouville
          (R.num.eval x / R.denom.eval x)) ∧
        (∀ x ∈ K,
          MahlerLean.irrationalityExponent
            (R.num.eval x / R.denom.eval x) ≤ (τ : EReal)) := by
  classical
  obtain ⟨w,hw⟩ := not_forall.mp (fun h => hb (good_of_free R h))
  obtain ⟨ν,_,ob⟩ := (not_scaleApproximable_iff _).mp hw
  let t := Counting.blockOrder
    (R.num.natDegree + 1 + R.denom.natDegree)
    (max R.num.natDegree R.denom.natDegree) ν
  have ht : 1 ≤ t := by dsimp [t,Counting.blockOrder]; omega
  refine ⟨t+3,by omega,?_⟩
  intro a b hab hpole
  obtain ⟨l,u,m,M,hlu,hsub,hm,hM,hinv,hlip⟩ :=
    regular_interval R hn hab hpole
  have count : Counting.SparseCount
      (fun x => R.num.eval x / R.denom.eval x) (Icc l u) M t := by
    simpa only [t] using
      Counting.two_height_count
        (le_refl R.num.natDegree) rfl R.monic_denom
        R.isCoprime_num_denom w ob hM hm
        (fun x hx => hpole x (hsub hx)) hinv
  obtain ⟨K,B,hne,hcomp,hperf,hdisc,hsubset,hB,hsource,htarget,houtside,hexp⟩ :=
    cantor_escape_of_sparse_count hlu hM ht hlip count
  refine ⟨K,B,hne,hcomp,hperf,hdisc,hsubset.trans hsub,hB,
    hsource,?_,houtside,?_⟩
  · intro x hx
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using htarget x hx
  · intro x hx
    exact hexp x hx

/-- Theorem 1.3 stated using membership in the rational function field.
The excluded coefficient, and hence the exponent, is independent of the
interval chosen afterwards. -/
theorem rational_cantor_escape (R : RatFunc ℝ)
    (hn : R ∉ Set.range (RatFunc.C : ℝ →+* RatFunc ℝ))
    (hbad : R ∉ Set.range (coefficientEmbedding coefficientSubfield)) :
    ∃ τ : ℕ, 3 < τ ∧ ∀ (a b : ℝ), a < b →
      (∀ x ∈ Ioo a b, R.denom.eval x ≠ 0) →
      ∃ K : Set ℝ, ∃ B : ℕ,
        K.Nonempty ∧ IsCompact K ∧ Perfect K ∧
        IsTotallyDisconnected K ∧ K ⊆ Ioo a b ∧ 2 ≤ B ∧
        (∀ x ∈ K, Liouville x) ∧
        (∀ x ∈ K, MahlerLean.EventualTargetAvoidance
          (R.num.eval x / R.denom.eval x) τ B) ∧
        (∀ x ∈ K, ¬ rationalOrLiouville
          (R.num.eval x / R.denom.eval x)) ∧
        (∀ x ∈ K,
          MahlerLean.irrationalityExponent
            (R.num.eval x / R.denom.eval x) ≤ (τ : EReal)) := by
  apply rational_cantor_escape_of_bad_coefficients R hn
  intro h
  exact hbad ((definedOver_iff_normalized_coefficients coefficientSubfield R).mpr h)

end MahlerLeanII
