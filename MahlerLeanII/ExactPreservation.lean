import MahlerLeanII.Classification

/-!
# Exact preservation: Corollary 1.4

The coefficient condition characterizes images in `ℚ ∪ 𝓛`.
Maillet's property is obtained by separately excluding rational images
of Liouville points. Both directions below are proved from the existing
rational-evaluation and escape theorems, without new axioms.
-/

noncomputable section
namespace MahlerLeanII
open Set

/-- Maillet's property on a prescribed subset of the real domain. -/
def MailletOn (R : RatFunc ℝ) (U : Set ℝ) : Prop :=
  ∀ x : ℝ, x ∈ U → Liouville x → Liouville (R.eval (RingHom.id ℝ) x)

/-- The rational fibers of `R` contain no Liouville point of `U`. -/
def RationalFiberFreeOn (R : RatFunc ℝ) (U : Set ℝ) : Prop :=
  ∀ x : ℝ, x ∈ U → Liouville x →
    ¬ ∃ q : ℚ, (q : ℝ) = R.eval (RingHom.id ℝ) x

/-- Corollary 1.4 on a nonempty pole-free open interval. -/
theorem exact_preservation_on_interval_iff (R : RatFunc ℝ)
    (hn : R ∉ Set.range (RatFunc.C : ℝ →+* RatFunc ℝ))
    {a b : ℝ} (hab : a < b)
    (hpole : ∀ x ∈ Ioo a b, R.denom.eval x ≠ 0) :
    MailletOn R (Ioo a b) ↔
      R ∈ Set.range (coefficientEmbedding coefficientSubfield) ∧
        RationalFiberFreeOn R (Ioo a b) := by
  constructor
  · intro hmap
    have hcoeff : R ∈ Set.range (coefficientEmbedding coefficientSubfield) := by
      apply (definedOver_iff_normalized_coefficients coefficientSubfield R).mpr
      by_contra hbad
      obtain ⟨x, hx, hL, he⟩ := escape_of_bad_coefficients R hn hbad hab hpole
      exact he (Or.inr (hmap x hx hL))
    refine ⟨hcoeff, ?_⟩
    intro x hx hL hrat
    exact (hmap x hx hL).irrational hrat
  · rintro ⟨hcoeff, hfiber⟩ x hx hL
    obtain ⟨hP, hQ⟩ :=
      (definedOver_iff_normalized_coefficients coefficientSubfield R).mp hcoeff
    have hE : rationalOrLiouville (R.eval (RingHom.id ℝ) x) :=
      evaluation_of_coefficients R.num R.denom hP hQ hL (hpole x hx)
    rcases hE with hrat | hLi
    · exact (hfiber x hx hL hrat).elim
    · exact hLi

/-- Corollary 1.4 on the full real domain of a nonconstant rational map. -/
theorem exact_preservation_on_domain_iff (R : RatFunc ℝ)
    (hn : R ∉ Set.range (RatFunc.C : ℝ →+* RatFunc ℝ)) :
    MailletOn R (realDomain R) ↔
      R ∈ Set.range (coefficientEmbedding coefficientSubfield) ∧
        RationalFiberFreeOn R (realDomain R) := by
  constructor
  · intro hmap
    obtain ⟨c, hc⟩ := R.denom.exists_max_root R.denom_ne_zero
    have hno : ∀ x ∈ Ioo c (c + 1), R.denom.eval x ≠ 0 := by
      intro x hx hroot
      exact (not_le_of_gt hx.1) (hc x hroot)
    have hlocal : MailletOn R (Ioo c (c + 1)) :=
      fun x hx hL => hmap x (hno x hx) hL
    obtain ⟨hcoeff, _⟩ :=
      (exact_preservation_on_interval_iff R hn
        (show c < c + 1 by linarith) hno).mp hlocal
    refine ⟨hcoeff, ?_⟩
    intro x hx hL hrat
    exact (hmap x hx hL).irrational hrat
  · rintro ⟨hcoeff, hfiber⟩ x hx hL
    obtain ⟨hP, hQ⟩ :=
      (definedOver_iff_normalized_coefficients coefficientSubfield R).mp hcoeff
    have hE : rationalOrLiouville (R.eval (RingHom.id ℝ) x) :=
      evaluation_of_coefficients R.num R.denom hP hQ hL hx
    rcases hE with hrat | hLi
    · exact (hfiber x hx hL hrat).elim
    · exact hLi

end MahlerLeanII
