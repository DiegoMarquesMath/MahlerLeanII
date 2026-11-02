import MahlerLeanII.SparseEscape
import MahlerLean.FareySupply
import MahlerLean.FusionConclusion

/-!
# Binary branching at sparse obstructed scales

The one-branch sparse escape construction is upgraded to two strictly
separated children at each stage. The source and target estimates are
identical to the single-branch construction; the cutoff is common to the
two children. The slightly stronger height threshold absorbs the
one-third splitting loss in the inherited tail budget.

This file supplies the arithmetic branching step for the full Cantor
refinement of manuscript Proposition 6.1.
-/

noncomputable section
namespace MahlerLeanII.Escape
open Set Finset Counting

/-- An interval and lower target cutoff with sufficient arithmetic
room for a binary successor. -/
structure SparseNode (I : Set ℝ) (L : ℝ) (t : ℕ) where
  l : ℝ
  u : ℝ
  width : l < u
  within : Icc l u ⊆ I
  H : ℕ
  two : 2 ≤ H
  tail : L*((H:ℝ)^(t+1))⁻¹ ≤ (u-l)/32

/-- Two disjoint successors sharing the selected rational center,
the source scale and the next target cutoff. -/
structure SparseBinaryStep {f : ℝ → ℝ} {I : Set ℝ} {L : ℝ} {t : ℕ}
    (v : SparseNode I L t) (j : ℕ) where
  leftChild : SparseNode I L t
  rightChild : SparseNode I L t
  left_nested : Icc leftChild.l leftChild.u ⊆ Ioo v.l v.u
  right_nested : Icc rightChild.l rightChild.u ⊆ Ioo v.l v.u
  separated : leftChild.u < rightChild.l
  left_growth : v.H < leftChild.H
  right_growth : v.H < rightChild.H
  center : ℚ
  den : 2 ≤ center.den
  source_left : ∀ x ∈ Icc leftChild.l leftChild.u,
    0 < |x-(center:ℝ)| ∧ |x-(center:ℝ)| < ((center.den:ℝ)^(j+3))⁻¹
  source_right : ∀ x ∈ Icc rightChild.l rightChild.u,
    0 < |x-(center:ℝ)| ∧ |x-(center:ℝ)| < ((center.den:ℝ)^(j+3))⁻¹
  target_left : ∀ x ∈ Icc leftChild.l leftChild.u, ∀ a : ℤ, ∀ b : ℕ,
    v.H ≤ b → b < leftChild.H →
      ((b:ℝ)^(t+3))⁻¹ < |f x-(a:ℝ)/b|
  target_right : ∀ x ∈ Icc rightChild.l rightChild.u, ∀ a : ℤ, ∀ b : ℕ,
    v.H ≤ b → b < rightChild.H →
      ((b:ℝ)^(t+3))⁻¹ < |f x-(a:ℝ)/b|

/-- The counting hypothesis yields two binary successors, not merely
one point, at any prescribed stage. It uses only the sparse sets of scales
from the actual two-height count; it does not require all large scales. -/
theorem exists_sparse_binary_step {f : ℝ → ℝ} {I : Set ℝ} {M L : ℝ} {t : ℕ}
    (hM : 0 ≤ M) (ht : 1 ≤ t)
    (hlip : ∀ x ∈ I, ∀ y ∈ I, |f x-f y| ≤ M*|x-y|)
    (count : ∀ A : ℕ, 3 ≤ A → ∃ C : ℝ, 0 < C ∧
      ∀ Smin : ℕ, ∃ S : ℕ, Smin ≤ S ∧ 2 ≤ S ∧ ∀ H : ℕ, 2 ≤ H →
      ∀ F : Finset ℚ, (∀ r ∈ F, (r:ℝ) ∈ I) → (∀ r ∈ F, r.den < 2*S) →
        (∀ r ∈ F, Resonant f M t S A H r) →
        (F.card : ℝ) ≤ L*(S:ℝ)^2*((H:ℝ)^(t+1))⁻¹+C*S)
    (v : SparseNode I L t) (j : ℕ) : Nonempty (SparseBinaryStep (f := f) v j) := by
  classical
  let k := j+3
  let A := k*t
  let W := v.u-v.l
  let mid := (v.l+v.u)/2
  have wpos : 0 < W := sub_pos.mpr v.width
  have hmid : v.l < mid := by dsimp [mid]; linarith [v.width]
  have widthMid : mid-v.l = W/2 := by dsimp [mid,W]; ring
  have kpos : 0 < k := by dsimp [k]; omega
  have hkA : k ≤ A := by dsimp [A]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hA : 3 ≤ A := (by dsimp [k]; omega : 3 ≤ k).trans hkA
  obtain ⟨s₀, supply⟩ := MahlerLean.sourceFractions_quarter_supply v.l mid hmid
  obtain ⟨C,hC,sc⟩ := count A hA
  let threshold := max (64*C/W) (max (4/W) (384*L*(2:ℝ)^A))
  obtain ⟨S,hSmin,hS,countS⟩ := sc (max s₀ (max (v.H+1) ⌈threshold⌉₊))
  have hsupply := supply S ((le_max_left _ _).trans hSmin)
  have hHH : v.H < S := (le_max_left _ _).trans ((le_max_right _ _).trans hSmin)
  have hth : threshold ≤ (S:ℝ) := (Nat.le_ceil _).trans (by
    exact_mod_cast (le_max_right _ _).trans ((le_max_right _ _).trans hSmin))
  have Spos : (0:ℝ) < S := by exact_mod_cast (show 0 < S by omega)
  have Sone : 1 ≤ (S:ℝ) := by exact_mod_cast (show 1 ≤ S by omega)
  have hbudget := (div_le_iff₀ wpos).1 ((le_max_left _ _).trans hth : 64*C/W ≤ (S:ℝ))
  have hsize := (div_le_iff₀ wpos).1
    ((le_max_left _ _).trans ((le_max_right _ _).trans hth) : 4/W ≤ (S:ℝ))
  have hnext : 256*L*(2:ℝ)^A ≤ S :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hth)
  let all := MahlerLean.sourceFractions v.l mid S
  let bad := all.filter (Resonant f M t S A v.H)
  have hrs (r) (hr : r ∈ all) := (MahlerLean.mem_sourceFractions v.l mid S r).1 hr
  have parent (r) (hr : r ∈ all) : (r:ℝ) ∈ Icc v.l v.u := by
    have hh := hrs r hr
    exact ⟨hh.1, hh.2.1.trans (by dsimp [mid]; linarith [v.width])⟩
  have badCount := countS v.H v.two bad
    (fun r hr => v.within (parent r (mem_filter.mp hr).1))
    (fun r hr => (hrs r (mem_filter.mp hr).1).2.2.2)
    (fun _ hr => (mem_filter.mp hr).2)
  have hlt : bad.card < all.card := by
    have ht₁ := mul_le_mul_of_nonneg_right v.tail (sq_nonneg (S:ℝ))
    have ht₂ := mul_le_mul_of_nonneg_right hbudget Spos.le
    rw [widthMid] at hsupply
    change 1/4*(W/2)*(S:ℝ)^2 ≤ (all.card:ℝ) at hsupply
    have : (bad.card : ℝ) < (all.card : ℝ) := by
      change L*((v.H:ℝ)^(t+1))⁻¹*(S:ℝ)^2 ≤ W/32*(S:ℝ)^2 at ht₁
      nlinarith only [badCount,ht₁,ht₂,hsupply,mul_pos wpos (sq_pos_of_pos Spos)]
    exact_mod_cast this
  obtain ⟨r,hr,hsafe⟩ := MahlerLean.exists_safe_center all bad hlt
  have safe : ¬ Resonant f M t S A v.H r := fun h => hsafe (mem_filter.mpr ⟨hr,h⟩)
  have hrp := parent r hr
  have hbounds := hrs r hr
  let ρ := ((2*(S:ℝ))^A)⁻¹
  have ρpos : 0 < ρ := by dsimp [ρ]; positivity
  have ρpow : ρ ≤ ((S:ℝ)^A)⁻¹ :=
    inv_anti₀ (pow_pos Spos A) (pow_le_pow_left₀ Spos.le (by linarith) _)
  have ρlen : ρ ≤ W/4 := calc
    ρ ≤ ((S:ℝ)^A)⁻¹ := ρpow
    _ ≤ (S:ℝ)⁻¹ := inv_anti₀ Spos (le_self_pow₀ Sone (by omega))
    _ ≤ W/4 := by rw [← one_div, div_le_iff₀ Spos]; nlinarith only [hsize]
  let lo := (r:ℝ)+ρ/4
  let hi := (r:ℝ)+ρ/2
  have hchild (x) (hx : x ∈ Icc lo hi) : x ∈ Icc v.l v.u := by
    obtain ⟨hx₁,hx₂⟩ := hx
    dsimp [lo,hi] at hx₁ hx₂
    have hrhi := hbounds.2.1
    dsimp [mid] at hrhi
    dsimp [W] at ρlen
    exact ⟨by linarith [hrp.1], by linarith⟩
  have clos (x) (hx : x ∈ Icc lo hi) : 0 < |x-(r:ℝ)| ∧ |x-(r:ℝ)| < ρ := by
    have h1 := hx.1; have h2 := hx.2
    dsimp [lo,hi] at h1 h2
    rw [abs_of_pos (by linarith)]
    constructor <;> linarith
  let T := S^k
  have Sk : (S:ℝ) ≤ (S:ℝ)^k := le_self_pow₀ Sone kpos.ne'
  have ST : S ≤ T := by exact_mod_cast Sk
  have tail : L*((T:ℝ)^(t+1))⁻¹ ≤ (ρ/12)/32 := by
    have e1 : (T:ℝ)^(t+1) = (S:ℝ)^A*(S:ℝ)^k := by
      dsimp [T,A]; push_cast; rw [pow_succ,← pow_mul]
    have e2 : (ρ/12)/32 = 1/(384*((2:ℝ)^A*(S:ℝ)^A)) := by
      dsimp [ρ]; rw [mul_pow]; ring
    rw [e1,e2,← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
    have hh := mul_le_mul_of_nonneg_right (hnext.trans Sk) (pow_nonneg Spos.le A)
    linarith only [hh]

  let leftU := lo + ρ/12
  let rightL := hi - ρ/12
  have hleftU : lo < leftU := by dsimp [leftU]; linarith
  have hrightL : rightL < hi := by dsimp [rightL]; linarith
  have hseparate : leftU < rightL := by
    dsimp [leftU,rightL,lo,hi]
    linarith [ρpos]

  have hleft (x : ℝ) (hx : x ∈ Icc lo leftU) : x ∈ Icc lo hi := by
    dsimp [leftU] at hx
    exact ⟨hx.1,by linarith [hx.2,hseparate]⟩
  have hright (x : ℝ) (hx : x ∈ Icc rightL hi) : x ∈ Icc lo hi := by
    dsimp [rightL] at hx
    exact ⟨by linarith [hx.1,hseparate],hx.2⟩

  have hnested_left (x : ℝ) (hx : x ∈ Icc lo leftU) : x ∈ Ioo v.l v.u := by
    have hxlo := hx.1
    have hxhi := (hleft x hx).2
    dsimp [lo,hi,mid,W] at hxlo hxhi
    have hrlo := hbounds.1
    have hrhi := hbounds.2.1
    dsimp [W] at ρlen
    constructor <;> linarith [ρpos,ρlen,v.width]
  have hnested_right (x : ℝ) (hx : x ∈ Icc rightL hi) : x ∈ Ioo v.l v.u := by
    have hxlo := (hright x hx).1
    have hxhi := hx.2
    dsimp [lo,hi,mid,W] at hxlo hxhi
    have hrlo := hbounds.1
    have hrhi := hbounds.2.1
    dsimp [W] at ρlen
    constructor <;> linarith [ρpos,ρlen,v.width]

  let lc : SparseNode I L t := ⟨lo,leftU,hleftU,
    fun _ hx => v.within (hchild _ (hleft _ hx)),
    T,hS.trans ST,by
      change L*((T:ℝ)^(t+1))⁻¹ ≤ (leftU-lo)/32
      convert tail using 1 <;> dsimp [leftU] <;> ring⟩
  let rc : SparseNode I L t := ⟨rightL,hi,hrightL,
    fun _ hx => v.within (hchild _ (hright _ hx)),
    T,hS.trans ST,by
      change L*((T:ℝ)^(t+1))⁻¹ ≤ (hi-rightL)/32
      convert tail using 1 <;> dsimp [rightL] <;> ring⟩

  have src : ∀ x ∈ Icc lo hi,
      0 < |x-(r:ℝ)| ∧ |x-(r:ℝ)| < ((r.den:ℝ)^(j+3))⁻¹ := by
    intro x hx
    have hq : (r.den:ℝ) ≤ 2*(S:ℝ) := by exact_mod_cast hbounds.2.2.2.le
    refine ⟨(clos x hx).1,(clos x hx).2.trans_le ?_⟩
    apply inv_anti₀ (pow_pos (by exact_mod_cast r.den_pos) k)
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hq k).trans
      (pow_le_pow_right₀ (by linarith) hkA)

  have tgt : ∀ x ∈ Icc lo hi, ∀ a : ℤ, ∀ b : ℕ,
      v.H ≤ b → b < T → ((b:ℝ)^(t+3))⁻¹ < |f x-(a:ℝ)/b| := by
    intro x hx a b hlo hhi
    have hcut : (b:ℝ)^t < (S:ℝ)^A := by
      have hbt : (b:ℝ) < (S:ℝ)^k := by exact_mod_cast hhi
      rw [show A = k*t by rfl, pow_mul]
      exact pow_lt_pow_left₀ hbt (Nat.cast_nonneg _) (by omega)
    have hc : targetMargin t M S A b < |f r-(a:ℝ)/b| :=
      lt_of_not_ge (fun h => safe ⟨a,b,hlo,hcut,h⟩)
    have hm := (hlip x (v.within (hchild x hx)) r (v.within hrp)).trans
      (mul_le_mul_of_nonneg_left ((clos x hx).2.le.trans ρpow) hM)
    exact MahlerLean.safety_transfer _ _ _ _ _ (by positivity) (by positivity)
      (by simpa only [targetMargin, mul_assoc] using hc) hm

  refine ⟨⟨lc,rc,hnested_left,hnested_right,hseparate,
    hHH.trans_le ST,hHH.trans_le ST,r,hS.trans hbounds.2.2.1,?_,?_,?_,?_⟩⟩
  · intro x hx
    exact src x (hleft x hx)
  · intro x hx
    exact src x (hright x hx)
  · intro x hx a b hlo hhi
    exact tgt x (hleft x hx) a b hlo hhi
  · intro x hx a b hlo hhi
    exact tgt x (hright x hx) a b hlo hhi

end MahlerLeanII.Escape
