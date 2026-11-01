import MahlerLeanII.CoefficientField
import MahlerLeanII.RationalCoefficients
import MahlerLeanII.RationalEvaluation
import MahlerLeanII.RationalEscape

/-! Theorem 1.2 (rational classification) in the Part II manuscript. -/

noncomputable section
namespace MahlerLeanII
open Set

/-- The real domain of a rational function in its canonical reduced representation. -/
def realDomain (R : RatFunc ℝ) : Set ℝ := {x | R.denom.eval x ≠ 0}

/-- Theorem 1.2. Being defined over the coefficient field is equivalent to mapping
Liouville numbers into the rationals union the Liouville numbers on the real
domain, or on some nonempty open interval in that domain. -/
theorem rational_classification (R : RatFunc ℝ)
    (hn : R ∉ Set.range (RatFunc.C : ℝ →+* RatFunc ℝ)) :
    List.TFAE [
      R ∈ Set.range (coefficientEmbedding coefficientSubfield),
      MapsTo (fun x => R.eval (RingHom.id ℝ) x)
        ({x : ℝ | Liouville x} ∩ realDomain R) {y | rationalOrLiouville y},
      ∃ V : Set ℝ, V.Nonempty ∧ IsOpen V ∧ V.OrdConnected ∧ V ⊆ realDomain R ∧
        MapsTo (fun x => R.eval (RingHom.id ℝ) x)
          ({x : ℝ | Liouville x} ∩ V) {y | rationalOrLiouville y}] := by
  tfae_have 1 → 2 := by
    intro hR x hx
    obtain ⟨hP,hQ⟩ := (definedOver_iff_normalized_coefficients coefficientSubfield R).mp hR
    exact evaluation_of_coefficients R.num R.denom hP hQ hx.1 hx.2
  tfae_have 2 → 3 := by
    intro hall
    obtain ⟨c,hc⟩ := R.denom.exists_max_root R.denom_ne_zero
    let V := Ioo c (c+1)
    have hpole : V ⊆ realDomain R := by
      intro x hx hroot
      exact (not_le_of_gt hx.1) (hc x hroot)
    exact ⟨V,nonempty_Ioo.mpr (by linarith),isOpen_Ioo,ordConnected_Ioo,hpole,
      fun _ hx => hall ⟨hx.1,hpole hx.2⟩⟩
  tfae_have 3 → 1 := by
    rintro ⟨V,hne,hopen,_,hsub,hlocal⟩
    obtain ⟨a,b,hab,hI⟩ := hopen.exists_Ioo_subset hne
    apply (definedOver_iff_normalized_coefficients coefficientSubfield R).mpr
    by_contra hbad
    obtain ⟨x,hx,hL,he⟩ := escape_of_bad_coefficients R hn hbad hab (fun _ hx => hsub (hI hx))
    exact he (hlocal ⟨hL,hI hx⟩)
  tfae_finish

end MahlerLeanII
