import MahlerLeanII.ExactPreservation

/-!
# Rational fibers as polynomial zero sets

This module converts the rational-fiber exclusion used in
`ExactPreservation.lean` into the explicit normalized condition of
Corollary 1.4, namely the absence of Liouville roots of `P - t Q`
for every rational `t`.
-/

noncomputable section
namespace MahlerLeanII
open Set Polynomial

/-- On a pole-free set, the exclusion of rational images is equivalent to
excluding Liouville zeros of every `P - t Q`. -/
theorem rationalFiberFreeOn_iff_polynomial (R : RatFunc ℝ)
    {U : Set ℝ} (hU : U ⊆ realDomain R) :
    RationalFiberFreeOn R U ↔
      ∀ t : ℚ, ∀ x : ℝ, x ∈ U → Liouville x →
        (R.num - Polynomial.C (t : ℝ) * R.denom).eval x ≠ 0 := by
  constructor
  · intro hfiber t x hx hL hzero
    apply hfiber x hx hL
    refine ⟨t, ?_⟩
    have hden : R.denom.eval x ≠ 0 := hU hx
    have heq : R.num.eval x = (t : ℝ) * R.denom.eval x := by
      simpa only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_C, sub_eq_zero] using hzero
    change (t : ℝ) = R.num.eval x / R.denom.eval x
    exact (eq_div_iff hden).2 heq.symm
  · intro hroot x hx hL hrat
    obtain ⟨t, ht⟩ := hrat
    have hden : R.denom.eval x ≠ 0 := hU hx
    have heq : (t : ℝ) = R.num.eval x / R.denom.eval x := by
      change (t : ℝ) = R.num.eval x / R.denom.eval x at ht
      exact ht
    have hprod : R.num.eval x = (t : ℝ) * R.denom.eval x :=
      ((eq_div_iff hden).1 heq).symm
    apply hroot t x hx hL
    simpa only [Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, sub_eq_zero] using hprod

/-- Corollary 1.4, with its literal normalized-polynomial fiber criterion,
on any nonempty pole-free open interval. -/
theorem exact_preservation_polynomial_fibers_interval (R : RatFunc ℝ)
    (hn : R ∉ Set.range (RatFunc.C : ℝ →+* RatFunc ℝ))
    {a b : ℝ} (hab : a < b)
    (hpole : ∀ x ∈ Ioo a b, R.denom.eval x ≠ 0) :
    MailletOn R (Ioo a b) ↔
      R ∈ Set.range (coefficientEmbedding coefficientSubfield) ∧
        (∀ t : ℚ, ∀ x : ℝ, x ∈ Ioo a b → Liouville x →
          (R.num - Polynomial.C (t : ℝ) * R.denom).eval x ≠ 0) := by
  constructor
  · intro h
    obtain ⟨hcoeff, hfib⟩ := (exact_preservation_on_interval_iff R hn hab hpole).mp h
    exact ⟨hcoeff,
      (rationalFiberFreeOn_iff_polynomial R (fun x hx => hpole x hx)).mp hfib⟩
  · rintro ⟨hcoeff, hzeros⟩
    apply (exact_preservation_on_interval_iff R hn hab hpole).mpr
    exact ⟨hcoeff,
      (rationalFiberFreeOn_iff_polynomial R (fun x hx => hpole x hx)).mpr hzeros⟩

/-- Corollary 1.4 on the entire real domain, in the manuscript's exact form. -/
theorem exact_preservation_polynomial_fibers_domain (R : RatFunc ℝ)
    (hn : R ∉ Set.range (RatFunc.C : ℝ →+* RatFunc ℝ)) :
    MailletOn R (realDomain R) ↔
      R ∈ Set.range (coefficientEmbedding coefficientSubfield) ∧
        (∀ t : ℚ, ∀ x : ℝ, x ∈ realDomain R → Liouville x →
          (R.num - Polynomial.C (t : ℝ) * R.denom).eval x ≠ 0) := by
  constructor
  · intro h
    obtain ⟨hcoeff, hfib⟩ := (exact_preservation_on_domain_iff R hn).mp h
    exact ⟨hcoeff, (rationalFiberFreeOn_iff_polynomial R (fun _ hx => hx)).mp hfib⟩
  · rintro ⟨hcoeff, hzeros⟩
    apply (exact_preservation_on_domain_iff R hn).mpr
    exact ⟨hcoeff, (rationalFiberFreeOn_iff_polynomial R (fun _ hx => hx)).mpr hzeros⟩

/-- Corollary 1.4 on any nonempty open pole-free set (in particular on
unbounded open intervals). The literal normalized-polynomial condition
is uniform in the rational fiber parameter. -/
theorem exact_preservation_polynomial_fibers_open (R : RatFunc ℝ)
    (hn : R ∉ Set.range (RatFunc.C : ℝ →+* RatFunc ℝ))
    {U : Set ℝ} (hopen : IsOpen U) (hne : U.Nonempty)
    (hsub : U ⊆ realDomain R) :
    MailletOn R U ↔
      R ∈ Set.range (coefficientEmbedding coefficientSubfield) ∧
        (∀ t : ℚ, ∀ x : ℝ, x ∈ U → Liouville x →
          (R.num - Polynomial.C (t : ℝ) * R.denom).eval x ≠ 0) := by
  constructor
  · intro hmap
    obtain ⟨a, b, hab, hI⟩ := hopen.exists_Ioo_subset hne
    have hpole : ∀ x ∈ Ioo a b, R.denom.eval x ≠ 0 :=
      fun x hx => hsub (hI hx)
    have hlocal : MailletOn R (Ioo a b) :=
      fun x hx hL => hmap x (hI hx) hL
    have hcoeff : R ∈ Set.range (coefficientEmbedding coefficientSubfield) :=
      ((exact_preservation_on_interval_iff R hn hab hpole).mp hlocal).1
    have hfiber : RationalFiberFreeOn R U :=
      fun x hx hL hr => (hmap x hx hL).irrational hr
    exact ⟨hcoeff, (rationalFiberFreeOn_iff_polynomial R hsub).mp hfiber⟩
  · rintro ⟨hcoeff, hzero⟩ x hx hL
    obtain ⟨hP, hQ⟩ :=
      (definedOver_iff_normalized_coefficients coefficientSubfield R).mp hcoeff
    have hE : rationalOrLiouville (R.eval (RingHom.id ℝ) x) :=
      evaluation_of_coefficients R.num R.denom hP hQ hL (hsub hx)
    have hfiber : RationalFiberFreeOn R U :=
      (rationalFiberFreeOn_iff_polynomial R hsub).mpr hzero
    rcases hE with hr | hLi
    · exact (hfiber x hx hL hr).elim
    · exact hLi

end MahlerLeanII
