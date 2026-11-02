import MahlerLeanII.SparseCantorTopology
import MahlerLean.FusionConclusion
import MahlerLean.IrrationalityExponent

/-!
# Full Cantor refinement of the sparse counting criterion

This theorem makes no rationality assumption on the function. It takes the
exact sparse counting estimate of manuscript Proposition 5.3 as an explicit
hypothesis, and produces a compact nonempty perfect totally disconnected
set of Liouville inputs with one common target-denominator cutoff.
-/

noncomputable section
namespace MahlerLeanII.Escape
open Set MahlerLeanII.Counting

/-- Full Cantor version of Proposition 6.1, using the unchanged source
and target estimates and a common cutoff across all Cantor branches. -/
theorem cantor_escape_of_sparse_count {f : ℝ → ℝ} {l u M : ℝ} {t : ℕ}
    (hlu : l < u) (hM : 0 ≤ M) (ht : 1 ≤ t)
    (hlip : ∀ x ∈ Icc l u, ∀ y ∈ Icc l u,
      |f x - f y| ≤ M * |x-y|)
    (hc : SparseCount f (Icc l u) M t) :
    ∃ K : Set ℝ, ∃ B : ℕ,
      K.Nonempty ∧
      IsCompact K ∧
      Perfect K ∧
      IsTotallyDisconnected K ∧
      K ⊆ Icc l u ∧
      2 ≤ B ∧
      (∀ x ∈ K, Liouville x) ∧
      (∀ x ∈ K, MahlerLean.EventualTargetAvoidance (f x) (t+3) B) ∧
      (∀ x ∈ K, ¬ rationalOrLiouville (f x)) ∧
      (∀ x ∈ K,
        MahlerLean.irrationalityExponent (f x) ≤ ((t+3 : ℕ) : EReal)) := by
  classical
  obtain ⟨L,hL,count⟩ := hc
  obtain ⟨H,hH⟩ := exists_nat_gt (max 2 (32*L/(u-l)))
  have hH₂ : 2 ≤ H := by
    exact_mod_cast ((le_max_left _ _).trans hH.le : (2:ℝ) ≤ H)
  have hp : 0 < (H:ℝ) := by exact_mod_cast (show 0 < H by omega)
  have hHone : 1 ≤ (H:ℝ) := by
    linarith [(le_max_left _ _).trans hH.le]
  have rootTail : L*((H:ℝ)^(t+1))⁻¹ ≤ (u-l)/32 := by
    have hh := (div_le_iff₀ (sub_pos.mpr hlu)).1
      ((le_max_right _ _).trans hH.le : 32*L/(u-l) ≤ (H:ℝ))
    have hz := mul_le_mul_of_nonneg_right
      (le_self_pow₀ (n := t+1) hHone (by omega))
      (sub_nonneg.mpr hlu.le)
    rw [← div_eq_mul_inv, div_le_div_iff₀ (pow_pos hp _)]
    nlinarith only [hh,hz]
    norm_num
  let d : SparseBinaryInputs f := {
    I := Icc l u
    M := M
    L := L
    t := t
    hM := hM
    ht := ht
    hlip := hlip
    count := count
    root := ⟨l,u,hlu,fun _ hx => hx,H,hH₂,rootTail⟩
  }
  let K := cantorLimitSet d
  refine ⟨K,H,?_,?_,?_,?_,?_,hH₂,?_,?_,?_,?_⟩
  · exact cantorLimitSet_nonempty d
  · exact cantorLimitSet_compact d
  · exact cantorLimitSet_perfect d
  · exact cantorLimitSet_isTotallyDisconnected d
  · simpa only [d] using cantorLimitSet_subset_ambient d
  · intro x hx
    exact cantorLimitSet_liouville d hx
  · intro x hx
    simpa only [d] using cantorLimitSet_target_avoidance d hx
  · intro x hx
    exact cantorLimitSet_image_outside_E d hx
  · intro x hx
    simpa only [d] using cantorLimitSet_irrationalityExponent_le d hx

end MahlerLeanII.Escape
