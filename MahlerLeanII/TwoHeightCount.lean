import MahlerLeanII.ObstructedCounting
import MahlerLeanII.SmallDenominators

/-! Two-height counting on obstructed scales, Proposition 5.3. -/

noncomputable section
namespace MahlerLeanII.Counting
open Finset Set Polynomial Reconstruction

/-- The cutoff is written `b^t < S^A`, equivalently `b < S^(A/t)` for `t > 0`. -/
def Resonant (f : ℝ → ℝ) (M : ℝ) (t S A H : ℕ) (r : ℚ) : Prop :=
  ∃ a : ℤ, ∃ b : ℕ, H ≤ b ∧ (b:ℝ)^t < (S:ℝ)^A ∧
    |f r-(a:ℝ)/b| ≤ targetMargin t M S A b

/-- Form of (5.8) uniform even over arbitrary finite families of resonant
centers in the fixed compact interval. Scales may depend on A, but are
chosen before both H and the family of centers. -/
def SparseCount (f : ℝ → ℝ) (I : Set ℝ) (M : ℝ) (t : ℕ) : Prop :=
  ∃ L : ℝ, 0 < L ∧ ∀ A : ℕ, 3 ≤ A → ∃ C : ℝ, 0 < C ∧
    ∀ Smin : ℕ, ∃ S : ℕ, Smin ≤ S ∧ 2 ≤ S ∧ ∀ H : ℕ, 2 ≤ H →
      ∀ F : Finset ℚ, (∀ r ∈ F, (r:ℝ) ∈ I) → (∀ r ∈ F, r.den < 2*S) →
        (∀ r ∈ F, Resonant f M t S A H r) →
        (F.card : ℝ) ≤ L*(S:ℝ)^2*((H:ℝ)^(t+1))⁻¹ + C*S

private theorem dyadic {H v : ℝ} (hH : 0 < H) (hv : H ≤ v) :
    ∃ k : ℕ, (2:ℝ)^k*H ≤ v ∧ v < 2*((2:ℝ)^k*H) := by
  obtain ⟨k,lo,hi⟩ := exists_nat_pow_near
    ((le_div_iff₀ hH).2 (by simpa using hv) : 1 ≤ v/H) (by norm_num : (1:ℝ) < 2)
  refine ⟨k,(le_div_iff₀ hH).1 lo,?_⟩
  have := (div_lt_iff₀ hH).1 hi
  rw [pow_succ] at this
  linarith only [this, mul_assoc ((2:ℝ)^k) 2 H, mul_left_comm ((2:ℝ)^k) 2 H,
    mul_assoc (2:ℝ) (2^k) H]

private theorem dyadic_index {S A i : ℕ} {H : ℝ} (hH : 1 ≤ H)
    (h : (2:ℝ)^i*H < (S:ℝ)^A) : i < S*A := by
  have hS : (S:ℝ) ≤ (2:ℝ)^S := by exact_mod_cast (Nat.lt_two_pow_self (n := S)).le
  apply (pow_lt_pow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp
  calc (2:ℝ)^i ≤ 2^i*H := le_mul_of_one_le_right (by positivity) hH
       _ < _ := h
       _ ≤ ((2:ℝ)^S)^A := pow_le_pow_left₀ (Nat.cast_nonneg _) hS _
       _ = _ := (pow_mul _ _ _).symm

private theorem large_block_margin {t A S b : ℕ} {B M : ℝ} (hM : 0 ≤ M)
    (hB : 1 ≤ B) (hb : B ≤ (b:ℝ)) (hcut : B^t < (S:ℝ)^A) :
    targetMargin t M S A b ≤ (2+4*M)/B^t := by
  have hBp : 0 < B := by linarith
  have hpow : B^t ≤ (b:ℝ)^(t+3) :=
    (pow_le_pow_right₀ hB (by omega : t ≤ t+3)).trans
      (pow_le_pow_left₀ hBp.le hb _)
  have i₁ := inv_anti₀ (pow_pos hBp _) hpow
  have i₂ := inv_anti₀ (pow_pos hBp _) hcut.le
  unfold targetMargin
  rw [div_eq_mul_inv, add_mul]
  gcongr

/-- The two-height estimate (5.8) for a rational function, assuming the
derivative bounds in their metric form on the pole-free interval. -/
theorem two_height_count {r s : ℕ} {P Q : ℝ[X]}
    (hP : P.natDegree ≤ r) (hQ : Q.natDegree = s) (hmonic : Q.Monic) (hcop : IsCoprime P Q)
    (w : Fin (r+1+s)) {ν : ℕ}
    (ob : ∀ D : ℕ, 1 ≤ D → ∀ H : ℕ, 2 ≤ H →
      ∃ S : ℕ, H ≤ S ∧ ObstructedAt (freeCoefficients P Q r s w) ν D S)
    {l u M m : ℝ} (hM : 0 ≤ M) (hm : 0 < m)
    (hfree : ∀ z ∈ Icc l u, Q.eval z ≠ 0)
    (hinv : ∀ x ∈ Icc l u, ∀ z ∈ Icc l u,
      m*|x-z| ≤ |P.eval x/Q.eval x-P.eval z/Q.eval z|) :
    SparseCount (fun x => P.eval x/Q.eval x) (Icc l u) M (blockOrder (r+1+s) (max r s) ν) := by
  classical
  let f := fun x => P.eval x/Q.eval x
  let n := r+1+s
  let t := blockOrder n (max r s) ν
  have ht : 0 < t := by dsimp [t,blockOrder]; omega
  have fcont : ContinuousOn f (Icc l u) := P.continuousOn.div Q.continuousOn hfree
  obtain ⟨F₀, hF₀⟩ := isCompact_Icc.exists_bound_of_continuousOn fcont
  have hfb (z) (hz : z ∈ Icc l u) : |f z| ≤ |F₀| := (hF₀ z hz).trans (le_abs_self _)
  obtain ⟨L,E,hL,hE,small⟩ := small_denominator_count t (abs_nonneg _) hM hm hfb hinv
  refine ⟨L,hL,fun A hA => ⟨E+(n:ℝ)*A,by positivity,?_⟩⟩
  intro Smin
  obtain ⟨S,hmin,hS,large⟩ := obstructed_scales_exclude_large_blocks hP hQ hmonic hcop
    w ob isCompact_Icc hfree (2+4*M) (by positivity) A Smin
  refine ⟨S,hmin,hS,?_⟩
  intro H hH F hx hd hw
  have hHr : 1 ≤ (H:ℝ) := by exact_mod_cast (show 1 ≤ H by omega)
  let B := fun k : ℕ => (2:ℝ)^k*H
  have hB (k) : 1 ≤ B k := one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)) hHr
  let Bin := fun (k : ℕ) (r : ℚ) => ∃ a : ℤ, ∃ b : ℕ, 0 < b ∧ B k ≤ (b:ℝ) ∧
    (b:ℝ) < 2*B k ∧ |f r-(a:ℝ)/b| ≤ targetMargin t M S A b
  have cell (r : ℚ) (hr : r ∈ F) : ∃ k : ℕ, (B k)^t < (S:ℝ)^A ∧ Bin k r := by
    obtain ⟨a,b,hh,hcut,herr⟩ := hw r hr
    obtain ⟨k,lo,hi⟩ := dyadic (H := (H:ℝ)) (v := (b:ℝ)) (by linarith) (by exact_mod_cast hh)
    exact ⟨k,(pow_le_pow_left₀ (by positivity) lo _).trans_lt hcut,a,b,by omega,lo,hi,herr⟩
  let short := fun r => ∃ k : ℕ, B k < Real.sqrt S ∧ Bin k r
  let G := F.filter short
  let J := F.filter (fun r => ¬short r)
  have gs := small A S hA (by omega) H hHr G
    (fun r hr => hd r (mem_filter.mp hr).1) (fun r hr => hx r (mem_filter.mp hr).1)
    (fun _ hr => (mem_filter.mp hr).2)
  let inds := (range (S*A)).filter (fun k => Real.sqrt S ≤ B k ∧ (B k)^t < (S:ℝ)^A)
  let family := fun k => J.filter (Bin k)
  have cov (r) (hr : r ∈ J) : ∃ k ∈ inds, r ∈ family k := by
    obtain ⟨k,hcut,hbin⟩ := cell r (mem_filter.mp hr).1
    have big : Real.sqrt S ≤ B k := le_of_not_gt (fun h => (mem_filter.mp hr).2 ⟨k,h,hbin⟩)
    have high : B k < (S:ℝ)^A := (le_self_pow₀ (hB k) ht.ne').trans_lt hcut
    exact ⟨k,mem_filter.mpr ⟨mem_range.mpr (dyadic_index hHr high),big,hcut⟩,
      mem_filter.mpr ⟨hr,hbin⟩⟩
  have each (k) (hk : k ∈ inds) : (family k).card < n := by
    obtain ⟨_,hbig,hcut⟩ := mem_filter.mp hk
    by_contra! hmany
    obtain ⟨x,hxrange⟩ := Function.Embedding.exists_of_card_le_finset
      (α := Fin n) (s := family k) (by simpa using hmany)
    have hmem (i) : x i ∈ family k := hxrange ⟨i,rfl⟩
    have hfmem (i) : x i ∈ F := (mem_filter.mp (mem_filter.mp (hmem i)).1).1
    have hwit (i) : Bin k (x i) := (mem_filter.mp (hmem i)).2
    choose a b hb hlo hhi he using hwit
    have hSB : (S:ℝ) ≤ (B k)^2 := (Real.sq_sqrt (Nat.cast_nonneg _)).symm.le.trans
      (pow_le_pow_left₀ (Real.sqrt_nonneg _) hbig _)
    apply large (B k) (hB k) hSB (((le_self_pow₀ (hB k) ht.ne').trans_lt hcut).le)
      x x.injective (fun i => hx _ (hfmem i)) (fun i => hd _ (hfmem i)) a b hb hhi
    intro i
    rw [abs_sub_comm]
    exact (he i).trans (large_block_margin hM (hB k) (hlo i) hcut)
  have size : (inds.card : ℝ) ≤ (S:ℝ)*A := by
    exact_mod_cast (card_filter_le _ _).trans_eq (card_range (S*A))
  have jl : (J.card : ℝ) ≤ ((S:ℝ)*A)*n :=
    MahlerLean.card_le_of_uniform_cell_bound J inds family (Nat.cast_nonneg n) size cov
      (fun k hk => by exact_mod_cast (each k hk).le)
  have sum : (G.card : ℝ)+(J.card : ℝ) = (F.card : ℝ) := by
    exact_mod_cast (filter_card_add_filter_neg_card_eq_card (s := F) short)
  change (F.card : ℝ) ≤ L*(S:ℝ)^2*((H:ℝ)^(t+1))⁻¹ + (E+(n:ℝ)*A)*S
  linarith only [gs,jl,sum]

end MahlerLeanII.Counting
