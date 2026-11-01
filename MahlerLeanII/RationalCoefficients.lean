import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Tactic

/-! The natural embedding K(X) into ℝ(X) and the unique monic reduced pair. -/

noncomputable section
namespace MahlerLeanII
open Polynomial

private theorem polynomial_nonZeroDivisors (K : Subfield ℝ) :
    nonZeroDivisors K[X] ≤ (nonZeroDivisors ℝ[X]).comap (Polynomial.mapRingHom K.subtype) := by
  intro p hp
  change p.map K.subtype ∈ nonZeroDivisors ℝ[X]
  apply mem_nonZeroDivisors_iff_ne_zero.mpr
  intro h
  apply (mem_nonZeroDivisors_iff_ne_zero.mp hp)
  apply Polynomial.map_injective K.subtype Subtype.val_injective
  simpa only [Polynomial.map_zero] using h

/-- Extend coefficients by the inclusion of a real subfield. -/
def coefficientEmbedding (K : Subfield ℝ) : RatFunc K →+* RatFunc ℝ :=
  RatFunc.mapRingHom (Polynomial.mapRingHom K.subtype) (polynomial_nonZeroDivisors K)

private theorem embed_fraction (K : Subfield ℝ) (p q : K[X]) :
    coefficientEmbedding K (algebraMap _ (RatFunc K) p / algebraMap _ _ q) =
      algebraMap _ (RatFunc ℝ) (p.map K.subtype) / algebraMap _ _ (q.map K.subtype) := by
  exact RatFunc.map_apply_div _ (polynomial_nonZeroDivisors K) p q

private theorem normalized_pair (R : RatFunc ℝ) {p q : ℝ[X]} (hq : q.Monic) (hc : IsCoprime p q)
    (he : R = algebraMap _ _ p / algebraMap _ _ q) : R.num = p ∧ R.denom = q := by
  have cross := (RatFunc.num_mul_eq_mul_denom_iff hq.ne_zero).2 he
  have d₁ : q ∣ R.denom := hc.symm.dvd_of_dvd_mul_left
    (cross ▸ (dvd_mul_left q R.num) : q ∣ p * R.denom)
  have d₂ : R.denom ∣ q := R.isCoprime_num_denom.symm.dvd_of_dvd_mul_left
    (cross.symm ▸ (dvd_mul_left R.denom p) : R.denom ∣ R.num * q)
  have eq := Polynomial.eq_of_monic_of_dvd_of_natDegree_le hq R.monic_denom d₁
    (Polynomial.natDegree_le_of_dvd d₂ hq.ne_zero)
  exact ⟨mul_right_cancel₀ hq.ne_zero (by simpa only [eq] using cross),eq⟩

/-- Remark 2.4. Membership in the image of K(X) is equivalent to all the
coefficients of the real monic reduced pair belonging to K. -/
theorem definedOver_iff_normalized_coefficients (K : Subfield ℝ) (R : RatFunc ℝ) :
    R ∈ Set.range (coefficientEmbedding K) ↔
      (∀ j, R.num.coeff j ∈ K) ∧ (∀ j, R.denom.coeff j ∈ K) := by
  constructor
  · rintro ⟨g,rfl⟩
    have he : coefficientEmbedding K g =
        algebraMap _ _ (g.num.map K.subtype) / algebraMap _ _ (g.denom.map K.subtype) := by
      calc _ = coefficientEmbedding K (algebraMap _ (RatFunc K) g.num / algebraMap _ _ g.denom) :=
                congrArg _ g.num_div_denom.symm
           _ = _ := embed_fraction K _ _
    obtain ⟨hp,hq⟩ := normalized_pair _ (g.monic_denom.map K.subtype)
      (g.isCoprime_num_denom.map (Polynomial.mapRingHom K.subtype)) he
    rw [hp,hq]
    exact ⟨fun j => by change (g.num.map K.subtype).coeff j ∈ K; rw [Polynomial.coeff_map]; exact (g.num.coeff j).property,
           fun j => by rw [Polynomial.coeff_map]; exact (g.denom.coeff j).property⟩
  · rintro ⟨hP,hQ⟩
    have lift (p : ℝ[X]) (hp : ∀ j, p.coeff j ∈ K) : ∃ q : K[X], q.map K.subtype = p :=
      (Polynomial.mem_lifts p).mp ((Polynomial.lifts_iff_coeff_lifts p).mpr
        (fun j => ⟨⟨_,hp j⟩,rfl⟩))
    obtain ⟨p,hp⟩ := lift _ hP
    obtain ⟨q,hq⟩ := lift _ hQ
    exact ⟨algebraMap _ _ p / algebraMap _ _ q,by rw [embed_fraction,hp,hq,R.num_div_denom]⟩

end MahlerLeanII
