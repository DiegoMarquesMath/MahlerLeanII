import MahlerLeanII.TwoHeightCount
import MahlerLean.FareySupply
import MahlerLean.FusionConclusion

/-! One branch of the sparse-scale construction, sufficient for Theorem 1.2. -/

noncomputable section
namespace MahlerLeanII.Escape
open Set Finset Counting

private structure Node (I : Set ℝ) (L : ℝ) (t : ℕ) where
  l : ℝ
  u : ℝ
  width : l < u
  within : Icc l u ⊆ I
  H : ℕ
  two : 2 ≤ H
  tail : L*((H:ℝ)^(t+1))⁻¹ ≤ (u-l)/64

private structure Step {f : ℝ → ℝ} {I : Set ℝ} {L : ℝ} {t : ℕ}
    (v : Node I L t) (j : ℕ) where
  child : Node I L t
  inside : Icc child.l child.u ⊆ Icc v.l v.u
  growth : v.H < child.H
  center : ℚ
  den : 2 ≤ center.den
  source : ∀ x ∈ Icc child.l child.u,
    0 < |x-(center:ℝ)| ∧ |x-(center:ℝ)| < ((center.den:ℝ)^(j+3))⁻¹
  target : ∀ x ∈ Icc child.l child.u, ∀ a : ℤ, ∀ b : ℕ, v.H ≤ b → b < child.H →
    ((b:ℝ)^(t+3))⁻¹ < |f x-(a:ℝ)/b|

private theorem next {f : ℝ → ℝ} {I : Set ℝ} {M L : ℝ} {t : ℕ}
    (hM : 0 ≤ M) (ht : 1 ≤ t)
    (hlip : ∀ x ∈ I, ∀ y ∈ I, |f x-f y| ≤ M*|x-y|)
    (count : ∀ A : ℕ, 3 ≤ A → ∃ C : ℝ, 0 < C ∧
      ∀ Smin : ℕ, ∃ S : ℕ, Smin ≤ S ∧ 2 ≤ S ∧ ∀ H : ℕ, 2 ≤ H →
      ∀ F : Finset ℚ, (∀ r ∈ F, (r:ℝ) ∈ I) → (∀ r ∈ F, r.den < 2*S) →
        (∀ r ∈ F, Resonant f M t S A H r) →
        (F.card : ℝ) ≤ L*(S:ℝ)^2*((H:ℝ)^(t+1))⁻¹+C*S)
    (v : Node I L t) (j : ℕ) : Nonempty (Step (f := f) v j) := by
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
  let threshold := max (64*C/W) (max (4/W) (256*L*(2:ℝ)^A))
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
      change L*((v.H:ℝ)^(t+1))⁻¹*(S:ℝ)^2 ≤ W/64*(S:ℝ)^2 at ht₁
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
  have tail : L*((T:ℝ)^(t+1))⁻¹ ≤ (hi-lo)/64 := by
    have e1 : (T:ℝ)^(t+1) = (S:ℝ)^A*(S:ℝ)^k := by
      dsimp [T,A]; push_cast; rw [pow_succ,← pow_mul]
    have e2 : (hi-lo)/64 = 1/(256*((2:ℝ)^A*(S:ℝ)^A)) := by
      dsimp [hi,lo,ρ]; rw [mul_pow]; ring
    rw [e1,e2,← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
    have hh := mul_le_mul_of_nonneg_right (hnext.trans Sk) (pow_nonneg Spos.le A)
    linarith only [hh]
  let c : Node I L t := ⟨lo,hi,by dsimp [lo,hi]; linarith,fun _ h => v.within (hchild _ h),
    T,hS.trans ST,tail⟩
  refine ⟨⟨c,hchild,hHH.trans_le ST,r,hS.trans hbounds.2.2.1,?_,?_⟩⟩
  · intro x hx
    have hq : (r.den:ℝ) ≤ 2*(S:ℝ) := by exact_mod_cast hbounds.2.2.2.le
    refine ⟨(clos x hx).1,(clos x hx).2.trans_le ?_⟩
    apply inv_anti₀ (pow_pos (by exact_mod_cast r.den_pos) k)
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hq k).trans
      (pow_le_pow_right₀ (by linarith) hkA)
  · intro x hx a b hlo hhi
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

/-- The single-point consequence of Proposition 6.1. The lower bound on the
image applies to unreduced target fractions and so also rules out rational values. -/
theorem point_escape_of_sparse_count {f : ℝ → ℝ} {l u M : ℝ} {t : ℕ}
    (hlu : l < u) (hM : 0 ≤ M) (ht : 1 ≤ t)
    (hlip : ∀ x ∈ Icc l u, ∀ y ∈ Icc l u, |f x-f y| ≤ M*|x-y|)
    (hc : SparseCount f (Icc l u) M t) :
    ∃ ξ ∈ Icc l u, Liouville ξ ∧ ¬rationalOrLiouville (f ξ) := by
  classical
  obtain ⟨L,hL,count⟩ := hc
  obtain ⟨H,hH⟩ := exists_nat_gt (max 2 (64*L/(u-l)))
  have hH₂ : 2 ≤ H := by exact_mod_cast ((le_max_left _ _).trans hH.le : (2:ℝ) ≤ H)
  have hp : 0 < (H:ℝ) := by exact_mod_cast (show 0 < H by omega)
  have hHone : 1 ≤ (H:ℝ) := by linarith [(le_max_left _ _).trans hH.le]
  have rootTail : L*((H:ℝ)^(t+1))⁻¹ ≤ (u-l)/64 := by
    have hh := (div_le_iff₀ (sub_pos.mpr hlu)).1
      ((le_max_right _ _).trans hH.le : 64*L/(u-l) ≤ (H:ℝ))
    have hz := mul_le_mul_of_nonneg_right (le_self_pow₀ (n := t+1) hHone (by omega))
      (sub_nonneg.mpr hlu.le)
    rw [← div_eq_mul_inv, div_le_iff₀ (pow_pos hp _)]
    nlinarith only [hh,hz]
  let root : Node (Icc l u) L t := ⟨l,u,hlu,fun _ h=>h,H,hH₂,rootTail⟩
  let step := fun (j : ℕ) (v : Node (Icc l u) L t) =>
    Classical.choice (next hM ht hlip count v j)
  let nodes : ℕ → Node (Icc l u) L t := Nat.rec (motive := fun _ => Node (Icc l u) L t)
    root (fun j v => (step j v).child)
  let J := fun n => Icc (nodes n).l (nodes n).u
  obtain ⟨ξ,hξ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed J
    (fun j => (step j (nodes j)).inside) (fun j => nonempty_Icc.mpr (nodes j).width.le)
    isCompact_Icc (fun _ => isClosed_Icc)
  have mem := Set.mem_iInter.mp hξ
  have hLi := MahlerLean.liouville_of_source_approximations ξ
    (fun j => (step j (nodes j)).center) (fun j => (step j (nodes j)).den)
    (fun j => (step j (nodes j)).source ξ (mem (j+1)))
  have avoid := MahlerLean.target_avoidance_from_blocks (f ξ) (t+3) (fun j => (nodes j).H)
    (strictMono_nat_of_lt_succ (fun j => (step j (nodes j)).growth))
    (fun j => (step j (nodes j)).target ξ (mem (j+1)))
  refine ⟨ξ, mem 0, hLi, ?_⟩
  rintro (⟨z,hz⟩ | hLi')
  · let b := (nodes 0).H * z.den
    have hb : (nodes 0).H ≤ b := Nat.le_mul_of_pos_right _ z.den_pos
    have eq : (f ξ) = (((nodes 0).H : ℤ)*z.num : ℤ) / (b:ℝ) := by
      rw [← hz,Rat.cast_def]
      dsimp [b]; push_cast
      have h0 : ((nodes 0).H : ℝ) ≠ 0 := by
        exact_mod_cast (show (nodes 0).H ≠ 0 by have := (nodes 0).two; omega)
      field_simp
    have hv := avoid (((nodes 0).H:ℤ)*z.num) b hb
    rw [← eq,sub_self,abs_zero] at hv
    exact (not_lt_of_ge (by positivity)) hv
  · exact MahlerLean.not_liouville_of_eventual_target_avoidance _ _ _ avoid hLi'

end MahlerLeanII.Escape
