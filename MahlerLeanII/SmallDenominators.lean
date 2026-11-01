import MahlerLean.SmallTargetWitnessBox
import MahlerLean.SmallTargetDyadicSums

/-! Small target denominators in Proposition 5.3. The packing and finite-cover
lemmas are imported from the author's Part I. The dyadic summation below adapts
its small-target estimate to an arbitrary integer exponent and the cutoff √S. -/

noncomputable section
namespace MahlerLeanII.Counting
open Set MahlerLean

/-- The exponent is `t+3`; thus the real cutoff satisfies `T^t = S^A`. -/
def targetMargin (t : ℕ) (M : ℝ) (S A b : ℕ) :=
  2*((b:ℝ)^(t+3))⁻¹ + 4*M*((S:ℝ)^A)⁻¹

private theorem numerator_bound (t : ℕ) {v F M : ℝ} {S A b : ℕ} {a : ℤ}
    (hM : 0 ≤ M) (hS : 0 < S) (hb : 0 < b) (hv : |v| ≤ F)
    (herr : |v-(a:ℝ)/b| ≤ targetMargin t M S A b) :
    |(a:ℝ)| ≤ (F+2+4*M)*b := by
  have hs : 1 ≤ (S:ℝ) := by exact_mod_cast hS
  have hb' : 1 ≤ (b:ℝ) := by exact_mod_cast hb
  have hb0 : (0:ℝ) < b := by exact_mod_cast hb
  have p := inv_le_one_of_one_le₀ (one_le_pow₀ hb' (n := t+3))
  have q := inv_le_one_of_one_le₀ (one_le_pow₀ hs (n := A))
  have mm := mul_le_mul_of_nonneg_left q (by positivity : 0 ≤ 4*M)
  have hrev := abs_sub_abs_le_abs_sub ((a:ℝ)/b) v
  rw [abs_sub_comm ((a:ℝ)/b) v] at hrev
  have hab : |(a:ℝ)/b| ≤ F+2+4*M := by unfold targetMargin at herr; linarith
  rw [abs_div,abs_of_pos hb0] at hab
  exact (div_le_iff₀ hb0).1 hab

private theorem margin_block (t : ℕ) {M B : ℝ} {S A b : ℕ}
    (hB : 0 < B) (hb : B ≤ (b : ℝ)) :
    targetMargin t M S A b ≤ 2*(B^(t+3))⁻¹+4*M*((S:ℝ)^A)⁻¹ := by
  have h := inv_anti₀ (pow_pos hB (t+3)) (pow_le_pow_left₀ hB.le hb _)
  unfold targetMargin
  linarith

private theorem dyadic_tail (e : ℕ) (t : Finset ℕ) {H : ℝ} (hH : 0 < H) :
    (∑ k ∈ t, (((2 : ℝ)^k*H)^(e+1))⁻¹) ≤ 2*(H^(e+1))⁻¹ := by
  have hterm (k : ℕ) : (((2 : ℝ)^k*H)^(e+1))⁻¹ ≤
      ((1 : ℝ)/2)^k*(H^(e+1))⁻¹ := by
    have hp : (2 : ℝ)^k ≤ ((2 : ℝ)^(e+1))^k :=
      pow_le_pow_left₀ (by norm_num) (by simpa only [pow_one] using
        (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega : 1 ≤ e+1))) k
    have hi := inv_anti₀ (by positivity : (0 : ℝ) < 2^k) hp
    have hh := mul_le_mul_of_nonneg_right hi (by positivity : 0 ≤ (H^(e+1))⁻¹)
    calc
      (((2 : ℝ)^k*H)^(e+1))⁻¹ = (((2 : ℝ)^(e+1))^k)⁻¹*(H^(e+1))⁻¹ := by
        rw [mul_pow, mul_inv_rev, ← pow_mul, Nat.mul_comm k (e+1), pow_mul]
        ring
      _ ≤ ((1 : ℝ)/2)^k*(H^(e+1))⁻¹ := by simpa only [inv_pow, one_div] using hh
  let n := t.sup id + 1
  have ht : t ⊆ Finset.range n := by
    intro k hk
    apply Finset.mem_range.mpr
    have hh : k ≤ t.sup id := Finset.le_sup (f := id) hk
    dsimp [n]
    omega
  have hsum : (∑ k ∈ t, ((1 : ℝ)/2)^k) ≤ 2 :=
    (Finset.sum_le_sum_of_subset_of_nonneg ht (by intros; positivity)).trans
      (sum_geometric_two_le n)
  calc
    (∑ k ∈ t, (((2 : ℝ)^k*H)^(e+1))⁻¹) ≤
        ∑ k ∈ t, ((1 : ℝ)/2)^k*(H^(e+1))⁻¹ := Finset.sum_le_sum (fun k _ ↦ hterm k)
    _ = (∑ k ∈ t, ((1 : ℝ)/2)^k)*(H^(e+1))⁻¹ := by rw [Finset.sum_mul]
    _ ≤ 2*(H^(e+1))⁻¹ := mul_le_mul_of_nonneg_right hsum (by positivity)


private theorem block_raw (t : ℕ)
    (S : Finset ℚ) {f : ℝ → ℝ} {a b F M m B : ℝ} {Q A : ℕ}
    (hF : 0 ≤ F) (hM : 0 ≤ M) (hm : 0 < m) (hB : 1 ≤ B) (hQ : 0 < Q)
    (hf : ∀ x ∈ Icc a b, |f x| ≤ F)
    (hinv : ∀ x ∈ Icc a b, ∀ z ∈ Icc a b, m*|x-z| ≤ |f x-f z|)
    (hx : ∀ r ∈ S, (r : ℝ) ∈ Icc a b)
    (hden : ∀ r ∈ S, r.den < 2*Q)
    (hw : ∀ r ∈ S, ∃ p : ℤ, ∃ q : ℕ, 0 < q ∧ B ≤ (q : ℝ) ∧ (q : ℝ) < 2*B ∧
      |f r-(p : ℝ)/q| ≤ targetMargin t M Q A q) :
    (S.card : ℝ) ≤ (3*(4*(F+2+4*M)+3)*B^2) *
      (4*(Q : ℝ)^2 * (2*(2*(B^(t+3))⁻¹+4*M*((Q : ℝ)^A)⁻¹)/m)+1) := by
  classical
  let C := F+2+4*M
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let eps := 2*(B^(t+3))⁻¹+4*M*((Q : ℝ)^A)⁻¹
  have heps : 0 ≤ eps := by dsimp [eps]; positivity
  let box := targetWitnessBox B C
  let E (w : ℕ × ℤ) := S.filter (fun r : ℚ ↦ |f r-(w.2 : ℝ)/w.1| ≤ eps)
  have he (w : ℕ × ℤ) : ((E w).card : ℝ) ≤ 4*(Q : ℝ)^2*(2*eps/m)+1 := by
    apply rational_target_neighborhood_card_le (E w) hm heps hQ hinv
    · intro r hr; exact hx r (Finset.mem_filter.mp hr).1
    · intro r hr; exact (Finset.mem_filter.mp hr).2
    · intro r hr; exact hden r (Finset.mem_filter.mp hr).1
  have hcov : ∀ r ∈ S, ∃ w ∈ box, r ∈ E w := by
    intro r hr
    obtain ⟨p,q,hq,hqlo,hqhi,herr⟩ := hw r hr
    have hp := numerator_bound t hM hQ hq (hf r (hx r hr)) herr
    refine ⟨(q,p), mem_targetWitnessBox hC hqhi hp, Finset.mem_filter.mpr ⟨hr, ?_⟩⟩
    exact herr.trans (margin_block t (by linarith : 0 < B) hqlo)
  exact card_le_of_uniform_cell_bound S box E (by positivity)
    (targetWitnessBox_card_le hB hC) hcov (fun w _ ↦ he w)

/-- One small block: main H-sensitive term and a quadratic block error.
All constants depend only on the fixed interval data, not A,Q,B,H. -/
private theorem block_count (t : ℕ)
    (S : Finset ℚ) {f : ℝ → ℝ} {a b F M m B : ℝ} {Q A : ℕ}
    (hF : 0 ≤ F) (hM : 0 ≤ M) (hm : 0 < m) (hB : 1 ≤ B) (hQ : 0 < Q) (hA : 2 ≤ A)
    (hf : ∀ x ∈ Icc a b, |f x| ≤ F)
    (hinv : ∀ x ∈ Icc a b, ∀ z ∈ Icc a b, m*|x-z| ≤ |f x-f z|)
    (hx : ∀ r ∈ S, (r : ℝ) ∈ Icc a b)
    (hden : ∀ r ∈ S, r.den < 2*Q)
    (hw : ∀ r ∈ S, ∃ p : ℤ, ∃ q : ℕ, 0 < q ∧ B ≤ (q : ℝ) ∧ (q : ℝ) < 2*B ∧
      |f r-(p : ℝ)/q| ≤ targetMargin t M Q A q) :
    (S.card : ℝ) ≤ (16*(3*(4*(F+2+4*M)+3))/m)*(Q : ℝ)^2*(B^(t+1))⁻¹ +
      ((3*(4*(F+2+4*M)+3))*(32*M/m+1))*B^2 := by
  have hc := block_raw t S hF hM hm hB hQ hf hinv hx hden hw
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hBp : 0 < B := by linarith
  have hid : B^2*(B^(t+3))⁻¹ = (B^(t+1))⁻¹ := by
    have he : B^(t+3) = B^(t+1)*B^2 := by rw [← pow_add]
    rw [he, mul_inv_rev]
    field_simp
  have hQA : (Q : ℝ)^2*((Q : ℝ)^A)⁻¹ ≤ 1 := by
    have hh := pow_le_pow_right₀ hQ1 hA
    exact (mul_inv_le_iff₀ (pow_pos hQ0 A)).mpr (by simpa using hh)
  let K := 3*(4*(F+2+4*M)+3)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have heq : (K*B^2)*(4*(Q : ℝ)^2*(2*(2*(B^(t+3))⁻¹+4*M*((Q : ℝ)^A)⁻¹)/m)+1) =
      (16*K/m)*(Q : ℝ)^2*(B^(t+1))⁻¹ + (K*(32*M/m*((Q : ℝ)^2*((Q : ℝ)^A)⁻¹)+1))*B^2 := by
    rw [← hid]
    ring
  change (S.card : ℝ) ≤ (16*K/m)*(Q : ℝ)^2*(B^(t+1))⁻¹ + (K*(32*M/m+1))*B^2
  change (S.card : ℝ) ≤ (K*B^2)*_ at hc
  rw [heq] at hc
  refine hc.trans ?_
  gcongr
  simpa using mul_le_mul_of_nonneg_left hQA (show 0 ≤ 32*M/m by positivity)


/-- Uniform small-height contribution in (5.8). -/
theorem small_denominator_count (t : ℕ)
    {f : ℝ → ℝ} {a b F M m : ℝ}
    (hF : 0 ≤ F) (hM : 0 ≤ M) (hm : 0 < m)
    (hf : ∀ x ∈ Icc a b, |f x| ≤ F)
    (hinv : ∀ x ∈ Icc a b, ∀ z ∈ Icc a b, m*|x-z| ≤ |f x-f z|) :
    ∃ C_low C_err : ℝ, 0 < C_low ∧ 0 < C_err ∧
      ∀ A Q : ℕ, 3 ≤ A → 0 < Q → ∀ H : ℝ, 1 ≤ H → ∀ S : Finset ℚ,
        (∀ r ∈ S, r.den < 2*Q) →
        (∀ r ∈ S, (r : ℝ) ∈ Icc a b) →
        (∀ r ∈ S, ∃ k : ℕ, (2 : ℝ)^k*H < Real.sqrt (Q : ℝ) ∧
          ∃ p : ℤ, ∃ q : ℕ, 0 < q ∧ (2 : ℝ)^k*H ≤ (q : ℝ) ∧
            (q : ℝ) < 2*((2 : ℝ)^k*H) ∧
            |f r-(p : ℝ)/q| ≤ targetMargin t M Q A q) →
        (S.card : ℝ) ≤ C_low*(Q : ℝ)^2*(H^(t+1))⁻¹ + C_err*(Q : ℝ) := by
  classical
  let K : ℝ := 3*(4*(F+2+4*M)+3)
  let C₀ : ℝ := 16*K/m
  let C₁ : ℝ := K*(32*M/m+1)
  have hK : 0 < K := by dsimp [K]; positivity
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  have hC₁ : 0 < C₁ := by dsimp [C₁]; positivity
  refine ⟨2*C₀, 2*C₁, by positivity, by positivity, ?_⟩
  intro A Q hA hQ H hH S hden hx hw
  have hHpos : 0 < H := by linarith
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ
  choose k hk using (fun r : ↑S ↦ hw r r.property)
  let inds : Finset ℕ := Finset.univ.image k
  let B (j : ℕ) : ℝ := (2 : ℝ)^j*H
  let E (j : ℕ) : Finset ℚ := S.filter (fun r : ℚ ↦ ∃ p : ℤ, ∃ q : ℕ,
    0 < q ∧ B j ≤ (q : ℝ) ∧ (q : ℝ) < 2*B j ∧ |f r-(p : ℝ)/q| ≤ targetMargin t M Q A q)
  have hsmall : ∀ j ∈ inds, B j < Real.sqrt (Q : ℝ) := by
    intro j hj
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hj
    exact (hk r).1
  have hcover : ∀ r ∈ S, ∃ j ∈ inds, r ∈ E j := by
    intro r hr
    exact ⟨k ⟨r,hr⟩, Finset.mem_image.mpr ⟨⟨r,hr⟩, Finset.mem_univ _, rfl⟩,
      Finset.mem_filter.mpr ⟨hr, (hk ⟨r,hr⟩).2⟩⟩
  have hbound : ∀ j ∈ inds, ((E j).card : ℝ) ≤ C₀*(Q : ℝ)^2*((B j)^(t+1))⁻¹+C₁*(B j)^2 := by
    intro j _
    have hBj : 1 ≤ B j := by
      have hh := one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num) (n := j)
      dsimp [B]
      nlinarith
    exact block_count t (E j) hF hM hm hBj hQ (by omega) hf hinv
      (fun r hr ↦ hx r (Finset.mem_filter.mp hr).1)
      (fun r hr ↦ hden r (Finset.mem_filter.mp hr).1)
      (fun r hr ↦ (Finset.mem_filter.mp hr).2)
  have hc := card_le_sum_of_finite_cover S inds E
    (fun j ↦ C₀*(Q : ℝ)^2*((B j)^(t+1))⁻¹+C₁*(B j)^2) hcover hbound
  have hi := dyadic_tail t inds hHpos
  have hs := dyadic_square_sum_le inds hHpos.le hsmall
  have he : (Real.sqrt (Q:ℝ))^2 = (Q:ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  rw [he] at hs
  calc
    (S.card : ℝ) ≤ ∑ j ∈ inds, (C₀*(Q : ℝ)^2*((B j)^(t+1))⁻¹+C₁*(B j)^2) := hc
    _ = C₀*(Q : ℝ)^2*(∑ j ∈ inds, ((B j)^(t+1))⁻¹)+C₁*(∑ j ∈ inds, (B j)^2) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ C₀*(Q : ℝ)^2*(2*(H^(t+1))⁻¹)+C₁*(2*(Q : ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_left hi (by positivity))
        (mul_le_mul_of_nonneg_left hs hC₁.le)
    _ = _ := by ring


end MahlerLeanII.Counting
