import MahlerLeanII.ReconstructionCramer

/-! Row clearing and the common denominator in (4.3). -/

noncomputable section
namespace MahlerLeanII.Reconstruction
open Matrix Finset

private theorem clear_power (p : ℤ) {q : ℕ} (hq : 0 < q) {j d : ℕ} (hj : j ≤ d) :
    (q : ℝ)^d * ((p : ℝ) / q)^j =
      ((p^j * (q : ℤ)^(d-j) : ℤ) : ℝ) := by
  have splitPow : (q : ℝ)^d = (q : ℝ)^j * (q : ℝ)^(d-j) := by
    rw [← pow_add, Nat.add_sub_of_le hj]
  rw [splitPow, div_pow]
  push_cast
  have hn : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  field_simp [hn]

private theorem det_after_clearing {n : ℕ} (w : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (Z : Matrix (Fin n) (Fin n) ℤ)
    (h : ∀ i j, (Z i j : ℝ) = w i * A i j) :
    (Z.det : ℝ) = (∏ i, w i) * A.det := by
  have eqM : Z.map (fun z : ℤ => (z : ℝ)) = Matrix.of (fun i j => w i * A i j) :=
    Matrix.ext h
  rw [Int.cast_det, eqM, Matrix.det_mul_column]

/-- If row multipliers clear both sides of an invertible real system, a single
positive denominator represents its Cramer solution. Its size is exactly the
absolute determinant of the cleared system. -/
theorem common_denominator_of_row_clearing {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (t w : Fin n → ℝ)
    (Z : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ)
    (hM : M.det ≠ 0) (hw : ∀ i, 0 < w i)
    (hz : ∀ i j, (Z i j : ℝ) = w i * M i j)
    (hb : ∀ i, (b i : ℝ) = w i * t i) :
    ∃ h : ℕ, 0 < h ∧ (h : ℝ) = (∏ i, w i) * |M.det| ∧
      ∃ c : Fin n → ℤ, ∀ j, cramerCoefficients M t j = (c j : ℝ) / h := by
  classical
  have hp : 0 < ∏ i, w i := Finset.prod_pos (fun i _ => hw i)
  have hd := det_after_clearing w M Z hz
  have hdn : (Z.det : ℝ) ≠ 0 := hd.trans_ne (mul_ne_zero hp.ne' hM)
  have hzi : Z.det ≠ 0 := by exact_mod_cast hdn
  have hnum (j : Fin n) :
      (Z.cramer b j : ℝ) = (∏ i, w i) * M.cramer t j := by
    rw [Matrix.cramer_apply, Matrix.cramer_apply]
    apply det_after_clearing
    intro i k
    by_cases hkj : k = j
    · subst k
      simpa only [Matrix.updateCol_self] using hb i
    · simpa only [Matrix.updateCol_ne hkj] using hz i k
  have habs : ((Z.det.natAbs : ℕ) : ℝ) = |(Z.det : ℝ)| := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  refine ⟨Z.det.natAbs, Int.natAbs_pos.mpr hzi, ?_, ?_⟩
  · rw [habs, hd, abs_mul, abs_of_pos hp]
  · have hrat (j : Fin n) : cramerCoefficients M t j =
          (Z.cramer b j : ℝ) / (Z.det : ℝ) := by
      unfold cramerCoefficients
      rw [hnum, hd]
      field_simp [hp.ne', hM]
    by_cases hpos : 0 ≤ (Z.det : ℝ)
    · refine ⟨Z.cramer b, fun j => ?_⟩
      rw [hrat, habs, abs_of_nonneg hpos]
    · refine ⟨fun j => -(Z.cramer b j), fun j => ?_⟩
      rw [hrat, habs, abs_of_neg (lt_of_not_ge hpos), Int.cast_neg, neg_div_neg_eq]

/-- For rational samples with denominator bounds, the Cramer solution of the
normalized system has a common denominator bounded by the product of the
row multipliers times the real determinant. The fractions may be unreduced. -/
theorem normalized_rational_height (r s : ℕ)
    (p a : Fin (r + 1 + s) → ℤ) (q b : Fin (r + 1 + s) → ℕ)
    (hq : ∀ i, 0 < q i) (hb : ∀ i, 0 < b i) (S B : ℝ)
    (hS : 1 ≤ S)
    (hqS : ∀ i, (q i : ℝ) < 2*S) (hbB : ∀ i, (b i : ℝ) < 2*B) :
    let x := fun i => (p i : ℝ) / q i
    let y := fun i => (a i : ℝ) / b i
    let M := normalizedMatrix r s x y
    M.det ≠ 0 → ∃ h : ℕ, 0 < h ∧
      (h : ℝ) ≤ ((2*S)^(max r s) * (2*B))^(r+1+s) * |M.det| ∧
      ∃ c : Fin (r+1+s) → ℤ, ∀ j,
        cramerCoefficients M (normalizedRhs s x y) j = (c j : ℝ) / h := by
  intro x y M hM
  let d := max r s
  let w := fun i => (q i : ℝ)^d * (b i : ℝ)
  let mon := fun i (j : ℕ) => (p i)^j * (q i : ℤ)^(d-j)
  let Z : Matrix (Fin (r+1+s)) (Fin (r+1+s)) ℤ := Matrix.of (fun i =>
    Fin.addCases (fun k : Fin (r+1) => (b i : ℤ) * mon i k)
      (fun k : Fin s => -(a i) * mon i k))
  let tZ := fun i => (a i) * mon i s
  have hpq (i) (j : ℕ) (hj : j ≤ d) : (mon i j : ℝ) = (q i : ℝ)^d * x i ^ j :=
    (clear_power (p i) (hq i) hj).symm
  have cancel (i) : y i * (b i : ℝ) = (a i : ℝ) := by
    dsimp [y]
    exact div_mul_cancel₀ _ (by exact_mod_cast (hb i).ne')
  have zh (i j) : (Z i j : ℝ) = w i * M i j := by
    refine Fin.addCases ?_ ?_ j
    · intro k
      simp only [Z, M, normalizedMatrix, Matrix.of_apply, Fin.addCases_left,
        Int.cast_mul, Int.cast_natCast]
      rw [hpq i k ((Nat.le_of_lt_succ k.isLt).trans (le_max_left r s))]
      dsimp [w]
      ring
    · intro k
      simp only [Z, M, normalizedMatrix, Matrix.of_apply, Fin.addCases_right,
        Int.cast_mul, Int.cast_neg]
      rw [hpq i k (k.isLt.le.trans (le_max_right r s)), ← cancel i]
      dsimp [w]
      ring
  have th (i) : (tZ i : ℝ) = w i * normalizedRhs s x y i := by
    simp only [tZ, Int.cast_mul, hpq i s (le_max_right r s), normalizedRhs]
    rw [← cancel i]
    dsimp [w]
    ring
  have hw (i) : 0 < w i := by
    have h1 := hq i
    have h2 := hb i
    dsimp [w]
    positivity
  obtain ⟨h, hh, hhval, c, hc⟩ :=
    common_denominator_of_row_clearing M (normalizedRhs s x y) w Z tZ hM hw zh th
  refine ⟨h, hh, ?_, c, hc⟩
  rw [hhval]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  calc (∏ i, w i) ≤ ∏ _i : Fin (r+1+s), ((2*S)^d * (2*B)) := by
         apply Finset.prod_le_prod (fun i _ => (hw i).le)
         intro i _
         exact mul_le_mul (pow_le_pow_left₀ (by positivity) (hqS i).le _)
           (hbB i).le (by positivity) (by positivity)
       _ = _ := by simp [d]

end MahlerLeanII.Reconstruction
