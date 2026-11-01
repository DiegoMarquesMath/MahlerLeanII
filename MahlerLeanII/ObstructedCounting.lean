import MahlerLeanII.RationalReconstruction
import MahlerLeanII.Obstruction
import MahlerLean.FareySeparation

/-! Scarcity of distinct centers in a large target block in Proposition 5.3.
The only Part I result used in this file is rational separation. -/

noncomputable section
namespace MahlerLeanII.Counting
open Finset Polynomial Reconstruction

/-- Number of factors in the Vandermonde product. -/
def pairCount (n : ℕ) := ∑ i : Fin n, (Finset.Ioi i).card

theorem twice_pairCount (n : ℕ) : 2 * pairCount n = n*(n-1) := by
  classical
  unfold pairCount
  simp only [Fin.card_Ioi]
  have hrev (i : Fin n) : n-1-(i : ℕ) = (Fin.rev i : ℕ) := by rw [Fin.val_rev]; omega
  simp_rw [hrev]
  have hs : (∑ i : Fin n, (Fin.rev i : ℕ)) = ∑ i : Fin n, (i : ℕ) :=
    Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin n)) (fun i : Fin n => (i : ℕ))
  rw [hs, Nat.mul_comm 2]
  simpa only [← Fin.sum_univ_eq_sum_range] using Finset.sum_range_id_mul_two n

/-- A version of (5.13) with no logarithms or real exponents. -/
theorem farey_vandermonde_lower {n S : ℕ} (hS : 0 < S) (u : Fin n → ℚ)
    (hu : Function.Injective u) (hd : ∀ i, (u i).den < 2*S) :
    1 ≤ (4:ℝ)^(pairCount n) * (S:ℝ)^(2*pairCount n) *
      nodeSeparation (fun i => (u i : ℝ)) := by
  classical
  let T := 4*(S:ℝ)^2
  have hT : 0 < T := by dsimp [T]; positivity
  have bound : (1/T)^(pairCount n) ≤ nodeSeparation (fun i => (u i : ℝ)) := by
    rw [nodeSeparation_eq, pairCount, ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod (by intros; positivity)
    intro i _
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod (by intros; positivity)
    intro j hj
    exact (MahlerLean.denominator_block_separation S hS _ _
      (hu.ne (Finset.mem_Ioi.mp hj).ne) (hd i) (hd j)).le
  rw [one_div, inv_pow, ← one_div] at bound
  have z := (div_le_iff₀ (pow_pos hT _)).mp bound
  simpa only [T, mul_pow, ← pow_mul, mul_comm] using z

/-- The integer `τ-3` from (5.4). -/
def blockOrder (n d ν : ℕ) : ℕ := 7 + 4*pairCount n + (2+2*(n*d)+n)*ν

private theorem slack {S B δ K : ℝ} {j t : ℕ} (hS : S ≤ B^2) (hB : 1 ≤ B)
    (hδ : 0 ≤ δ) (hj : 2+j ≤ t) (herr : δ*B^t ≤ K) : S*(δ*B^j) ≤ K := by
  calc S*(δ*B^j) = δ*(S*B^j) := by ring
       _ ≤ δ*(B^2*B^j) := by gcongr
       _ ≤ δ*B^t := by rw [← pow_add]; exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB hj) hδ
       _ ≤ _ := herr

/-- The conclusion needed for one large dyadic target block. The same scale
works for every block and choice of distinct rational centers. -/
def ExcludesLargeBlocks {r s : ℕ} (P Q : ℝ[X]) (I : Set ℝ) (S A t : ℕ) (K : ℝ) : Prop :=
  ∀ B : ℝ, 1 ≤ B → (S:ℝ) ≤ B^2 → B ≤ (S:ℝ)^A →
  ∀ u : Fin (r+1+s) → ℚ, Function.Injective u → (∀ i, (u i : ℝ) ∈ I) →
    (∀ i, (u i).den < 2*S) →
  ∀ (a : Fin (r+1+s) → ℤ) (b : Fin (r+1+s) → ℕ), (∀ i, 0 < b i) →
    (∀ i, (b i : ℝ) < 2*B) →
    (∀ i, |(a i : ℝ)/b i - P.eval (u i : ℝ)/Q.eval (u i : ℝ)| ≤ K/B^t) → False

/-- The large-block argument in Proposition 5.3. The order of obstruction is
fixed before `A`, and the threshold is uniform in target heights and centers. -/
theorem obstructed_scales_exclude_large_blocks {r s : ℕ} {P Q : ℝ[X]}
    (hP : P.natDegree ≤ r) (hQ : Q.natDegree = s) (hmonic : Q.Monic) (hcop : IsCoprime P Q)
    (w : Fin (r+1+s)) {ν : ℕ}
    (ob : ∀ D : ℕ, 1 ≤ D → ∀ H : ℕ, 2 ≤ H →
      ∃ S : ℕ, H ≤ S ∧ ObstructedAt (freeCoefficients P Q r s w) ν D S)
    {I : Set ℝ} (hI : IsCompact I) (hfree : ∀ z ∈ I, Q.eval z ≠ 0)
    (K : ℝ) (hK : 0 ≤ K) (A Hmin : ℕ) :
    ∃ S : ℕ, Hmin ≤ S ∧ 2 ≤ S ∧
      ExcludesLargeBlocks (r := r) (s := s) P Q I S A (blockOrder (r+1+s) (max r s) ν) K := by
  classical
  let n := r+1+s
  let d := max r s
  let k := 2*pairCount n
  let G := (4:ℝ)^(pairCount n)
  let e := 2+2*(n*d)+n
  let t := blockOrder n d ν
  have hG : 0 < G := by dsimp [G]; positivity
  obtain ⟨c₀,hc₀,C,hC,rec⟩ := rational_reconstruction_bounds hP hQ hmonic hcop hI hfree
  let W := C^ν * C * G
  let cut := max C (max (G*K/c₀) (W*K))
  let D := n*d+A*n+1
  obtain ⟨S,hS,hob⟩ := ob D (by dsimp [D]; omega) (max (max Hmin 2) ⌈cut⌉₊)
    ((le_max_right Hmin 2).trans (le_max_left _ _))
  have hbase : max Hmin 2 ≤ S := (le_max_left _ _).trans hS
  have hS2 : 2 ≤ S := (le_max_right _ _).trans hbase
  have hSp : (0:ℝ) < S := by exact_mod_cast (show 0 < S by omega)
  have hS1 : 1 ≤ (S:ℝ) := by exact_mod_cast (show 1 ≤ S by omega)
  have hc : cut ≤ (S:ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right _ _).trans hS)
  have hCS : C ≤ (S:ℝ) := (le_max_left _ _).trans hc
  have hbudget : G*K ≤ c₀*S := by
    have := (div_le_iff₀ hc₀).mp ((le_max_left _ _).trans ((le_max_right _ _).trans hc))
    linarith
  have hfinal : W*K ≤ (S:ℝ) := (le_max_right _ _).trans ((le_max_right _ _).trans hc)
  refine ⟨S,(le_max_left _ _).trans hbase,hS2,?_⟩
  intro B hB hSB hBA u hu hIu hden a b hb hbB herr
  let x := fun i => (u i : ℝ)
  let δ := K/B^t
  let V := nodeSeparation x
  have hx : Function.Injective x := Rat.cast_injective.comp hu
  have hV : 0 < V := nodeSeparation_pos hx
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hBp : 0 < B := by linarith
  have hs0 : δ*B^t ≤ K := (div_mul_cancel₀ K (pow_pos hBp t).ne').le
  have hs (j : ℕ) (hj : 2+j ≤ t) : δ*B^j ≤ K/S := by
    apply (le_div_iff₀ hSp).2
    simpa only [mul_comm (δ*B^j)] using slack hSB hB hδ hj hs0
  have hsep : 1 ≤ G*(S:ℝ)^k*V :=
    farey_vandermonde_lower (by omega : 0 < S) u hu hden
  have invV : 1/V ≤ G*(S:ℝ)^k := (div_le_iff₀ hV).2 hsep
  have hSexp (j : ℕ) : (S:ℝ)^j ≤ B^(2*j) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ hSp.le hSB _
  have herrV : δ/V ≤ G*(δ*B^(2*k)) := calc
    δ/V = δ*(1/V) := by ring
    _ ≤ δ*(G*(S:ℝ)^k) := mul_le_mul_of_nonneg_left invV hδ
    _ ≤ δ*(G*B^(2*k)) := by gcongr; exact hSexp k
    _ = _ := by ring
  have hj₁ : 2+2*k ≤ t := by dsimp [t,blockOrder,k]; omega
  have hsmall : δ ≤ c₀*V := (div_le_iff₀ hV).1 <| herrV.trans <| calc
    G*(δ*B^(2*k)) ≤ G*(K/S) := mul_le_mul_of_nonneg_left (hs _ hj₁) hG.le
    _ ≤ c₀ := by rw [← mul_div_assoc]; exact (div_le_iff₀ hSp).2 hbudget
  have hqd (i) : ((u i).den : ℝ) < 2*(S:ℝ) := by exact_mod_cast hden i
  have hr := rec (fun i => (u i).num) a (fun i => (u i).den) b
    (fun i => (u i).den_pos) hb S B hS1 hB hqd hbB
  simp only [← Rat.cast_def] at hr
  obtain ⟨h,hh,hhgt,c,he⟩ := hr hIu hx δ hδ herr hsmall
  have hdenD : h ≤ S^D := by
    have bound : (h:ℝ) ≤ (S:ℝ)^D := hhgt.trans <| calc
      C*(S:ℝ)^(n*d)*B^n ≤ (S:ℝ)*(S:ℝ)^(n*d)*((S:ℝ)^A)^n := by gcongr
      _ = (S:ℝ)^D := by rw [show D = (n*d+A*n)+1 by rfl, pow_succ (S:ℝ) (n*d+A*n),
        pow_add (S:ℝ) (n*d) (A*n), pow_mul (S:ℝ) A n]; ring
    exact_mod_cast bound
  have hSh : (S:ℝ)*h ≤ C*B^e := calc
    (S:ℝ)*h ≤ (S:ℝ)*(C*(S:ℝ)^(n*d)*B^n) := mul_le_mul_of_nonneg_left hhgt hSp.le
    _ ≤ B^2*(C*B^(2*(n*d))*B^n) := by gcongr; exact hSexp (n*d)
    _ = _ := by dsimp [e]; rw [pow_add,pow_add]; ring
  let err := |freeCoefficients P Q r s w - (c w : ℝ)/h|
  have hθ : err ≤ C * G * (δ*B^(2*k)) := by
    have hw := (norm_le_pi_norm ((fun j => (c j : ℝ)/h) - freeCoefficients P Q r s) w).trans he
    change |(c w : ℝ)/h - freeCoefficients P Q r s w| ≤ _ at hw
    rw [abs_sub_comm] at hw
    calc err ≤ C*δ/V := hw
         _ = C*(δ/V) := by ring
         _ ≤ C*(G*(δ*B^(2*k))) := mul_le_mul_of_nonneg_left herrV hC.le
         _ = _ := by ring
  have hj₂ : 2+(2*k+e*ν) ≤ t := by dsimp [t,blockOrder,k,e]; omega
  have hscaled : ((S:ℝ)*h)^ν * err ≤ 1 := calc
    _ ≤ (C*B^e)^ν * (C*G*(δ*B^(2*k))) :=
      mul_le_mul (pow_le_pow_left₀ (by positivity) hSh _) hθ (abs_nonneg _) (by positivity)
    _ = W*(δ*B^(2*k+e*ν)) := by dsimp [W]; rw [mul_pow,← pow_mul,pow_add]; ring
    _ ≤ W*(K/S) := mul_le_mul_of_nonneg_left (hs _ hj₂) (by dsimp [W]; positivity)
    _ ≤ 1 := by rw [← mul_div_assoc]; exact (div_le_iff₀ hSp).2 (by simpa using hfinal)
  have contradiction := (div_lt_iff₀ (show 0 < ((S:ℝ)*h)^ν by positivity)).1
    (hob (c w) h (by omega) hdenD)
  change 1 < err * ((S:ℝ)*h)^ν at contradiction
  linarith only [hscaled, contradiction, mul_comm err (((S:ℝ)*h)^ν)]

end MahlerLeanII.Counting
