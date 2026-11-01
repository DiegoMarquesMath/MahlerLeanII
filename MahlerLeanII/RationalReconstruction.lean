import MahlerLeanII.ReconstructionHeight
import MahlerLeanII.ReconstructionStability

/-! The joint reconstruction bounds (4.2) and (4.3) used in (5.14). -/

noncomputable section
namespace MahlerLeanII.Reconstruction
open Matrix Polynomial Finset

theorem nodeSeparation_eq {n : ℕ} (x : Fin n → ℝ) :
    nodeSeparation x = ∏ i, ∏ j ∈ Finset.Ioi i, |x i - x j| := by
  simp only [nodeSeparation, Finset.abs_prod, abs_sub_comm]

/-- For rational abscissae and ordinates, the same integer vector and positive
denominator satisfy (4.2) and (4.3). Both constants are independent of the
nodes, their heights and the ordinate error. No fractions need be in lowest terms. -/
theorem rational_reconstruction_bounds {r s : ℕ} {P Q : ℝ[X]}
    (hP : P.natDegree ≤ r) (hQ : Q.natDegree = s) (hmonic : Q.Monic) (hcop : IsCoprime P Q)
    {I : Set ℝ} (hI : IsCompact I) (hfree : ∀ z ∈ I, Q.eval z ≠ 0) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (p a : Fin (r+1+s) → ℤ) (q b : Fin (r+1+s) → ℕ),
        (∀ i, 0 < q i) → (∀ i, 0 < b i) →
      ∀ (S B : ℝ), 1 ≤ S → 1 ≤ B → (∀ i, (q i : ℝ) < 2*S) → (∀ i, (b i : ℝ) < 2*B) →
      let x := fun i => (p i : ℝ)/q i
      let y := fun i => (a i : ℝ)/b i
      (∀ i, x i ∈ I) → Function.Injective x → ∀ δ : ℝ, 0 ≤ δ →
      (∀ i, |y i - P.eval (x i)/Q.eval (x i)| ≤ δ) → δ ≤ c₀*nodeSeparation x →
      ∃ h : ℕ, 0 < h ∧ (h : ℝ) ≤ C₀ * S^((r+1+s)*max r s) * B^(r+1+s) ∧
      ∃ c : Fin (r+1+s) → ℤ,
        ‖(fun j => (c j : ℝ)/h) - freeCoefficients P Q r s‖ ≤ C₀*δ/nodeSeparation x := by
  classical
  obtain ⟨c₀,hc₀,C,hC,stable⟩ := normalized_stability_on_compact hP hQ hmonic hcop hI hfree
  let n := r+1+s
  let d := max r s
  let F := ((2:ℝ)^d * 2)^n
  let C₀ := max C (F*C)
  have hCC : C ≤ C₀ := le_max_left _ _
  refine ⟨c₀, hc₀, C₀, hC.trans_le hCC, ?_⟩
  intro p a q b hq hb S B hS hB hqS hbB x y hx hdist δ hδ herr hsmall
  let M := normalizedMatrix r s x y
  obtain ⟨hM, hMb, he⟩ := stable x hx hdist y δ hδ herr hsmall
  obtain ⟨h, hh, hbound, c, hc⟩ := normalized_rational_height r s p a q b hq hb S B hS hqS hbB hM
  have hSp : 0 ≤ S := by linarith
  have hBp : 0 ≤ B := by linarith
  refine ⟨h, hh, hbound.trans ?_, c, ?_⟩
  · calc ((2*S)^d * (2*B))^n * |M.det| =
          (F * |M.det|) * S^(n*d) * B^n := by
            dsimp [F]
            simp only [mul_pow, ← pow_mul, Nat.mul_comm d n]
            ring
         _ ≤ C₀ * S^(n*d) * B^n := by
           apply mul_le_mul_of_nonneg_right _ (pow_nonneg hBp _)
           apply mul_le_mul_of_nonneg_right _ (pow_nonneg hSp _)
           exact (mul_le_mul_of_nonneg_left hMb (by dsimp [F]; positivity)).trans (le_max_right _ _)
  · have hv : cramerCoefficients M (normalizedRhs s x y) = fun j => (c j : ℝ)/h := funext hc
    rw [← hv]
    exact he.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCC hδ)
      (nodeSeparation_pos hdist).le)

end MahlerLeanII.Reconstruction
