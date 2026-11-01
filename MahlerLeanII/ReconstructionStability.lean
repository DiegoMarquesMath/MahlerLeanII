import MahlerLeanII.ReconstructionCramer
import Mathlib.Analysis.Normed.Group.Bounded

/-! Uniform stability of normalized rational interpolation, (4.2). -/

noncomputable section
namespace MahlerLeanII.Reconstruction
open Polynomial Matrix Finset Set

/-- Absolute Vandermonde product. -/
def nodeSeparation {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  |∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (x j - x i)|

theorem nodeSeparation_pos {n : ℕ} {x : Fin n → ℝ} (hx : Function.Injective x) :
    0 < nodeSeparation x := by
  unfold nodeSeparation
  rw [← det_vandermonde]
  exact abs_pos.mpr (det_vandermonde_ne_zero_iff.mpr hx)

private theorem separation_bounded {n : ℕ} {I : Set ℝ} (hI : IsCompact I) :
    ∃ G : ℝ, 0 < G ∧ ∀ x : Fin n → ℝ, (∀ i, x i ∈ I) → nodeSeparation x ≤ G := by
  have hc : Continuous (nodeSeparation (n := n)) := by unfold nodeSeparation; fun_prop
  obtain ⟨G, hG⟩ := (isCompact_univ_pi (fun _ : Fin n => hI)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨|G|+1, by positivity, fun x hx => ?_⟩
  have hb := hG x (fun i _ => hx i)
  simpa only [Real.norm_eq_abs, nodeSeparation, abs_abs] using
    hb.trans ((le_abs_self G).trans (by linarith : |G| ≤ |G|+1))

private def markedMatrix {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (t : Fin n → ℝ) (j : Option (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  match j with
  | none => M
  | some k => M.updateCol k t

private def sampleMatrix (r s : ℕ) (x y : Fin (r+1+s) → ℝ)
    (j : Option (Fin (r+1+s))) :=
  markedMatrix (normalizedMatrix r s x y) (normalizedRhs s x y) j

/-- Entry bounds hold simultaneously for the denominator determinant and all
Cramer numerators, since each column is a monomial or an ordinate times a monomial. -/
private theorem sample_entries {r s : ℕ} (x y z : Fin (r+1+s) → ℝ) {U Y ε : ℝ}
    (hU : 1 ≤ U) (hY : 1 ≤ Y) (he : 0 ≤ ε)
    (hx : ∀ i, |x i| ≤ U) (hy : ∀ i, |y i| ≤ Y) (hz : ∀ i, |z i| ≤ Y)
    (hd : ∀ i, |y i-z i| ≤ ε) (j : Option (Fin (r+1+s))) (i k : Fin (r+1+s)) :
    |sampleMatrix r s x y j i k| ≤ Y*U^(max r s) ∧
    |sampleMatrix r s x z j i k| ≤ Y*U^(max r s) ∧
    |sampleMatrix r s x y j i k - sampleMatrix r s x z j i k| ≤ U^(max r s)*ε := by
  let good := fun (a b : ℝ) => |a| ≤ Y*U^(max r s) ∧ |b| ≤ Y*U^(max r s) ∧
      |a-b| ≤ U^(max r s)*ε
  have mon (e : ℕ) (hj : e ≤ max r s) (α β : ℝ) (ha : |α| ≤ Y) (hb : |β| ≤ Y)
      (hab : |α-β| ≤ ε) : good (α*x i^e) (β*x i^e) := by
    have hp : |x i^e| ≤ U^(max r s) := by
      rw [abs_pow]
      exact (pow_le_pow_left₀ (abs_nonneg _) (hx i) _).trans (pow_le_pow_right₀ hU hj)
    dsimp [good]
    rw [← sub_mul, abs_mul, abs_mul, abs_mul]
    exact ⟨mul_le_mul ha hp (abs_nonneg _) (by linarith),
      mul_le_mul hb hp (abs_nonneg _) (by linarith),
      (mul_le_mul hab hp (abs_nonneg _) he).trans_eq (mul_comm _ _)⟩
  have main (l : Fin (r+1+s)) :
      good (normalizedMatrix r s x y i l) (normalizedMatrix r s x z i l) := by
    refine Fin.addCases ?_ ?_ l
    · intro m
      simpa [normalizedMatrix] using mon m ((Nat.le_of_lt_succ m.isLt).trans (le_max_left r s))
        1 1 (by simpa) (by simpa) (by simpa)
    · intro m
      simpa [normalizedMatrix] using mon m (m.isLt.le.trans (le_max_right r s))
        (-y i) (-z i) (by simpa using hy i) (by simpa using hz i)
          (by rw [neg_sub_neg, abs_sub_comm]; exact hd i)
  change good _ _
  cases j with
  | none => exact main k
  | some l =>
    by_cases h : k = l
    · subst k
      simpa [sampleMatrix, markedMatrix, normalizedRhs] using
        mon s (le_max_right r s) (y i) (z i) (hy i) (hz i) (hd i)
    · simpa [sampleMatrix, markedMatrix, Matrix.updateCol_ne h] using main k

private theorem perturb_div {d e a b θ L δ V m : ℝ}
    (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hV : 0 < V) (hm : 0 < m)
    (ha : d ≠ 0) (hlower : m*V/2 ≤ |d|)
    (hden : |d-e| ≤ L*δ) (hnum : |a-b| ≤ L*δ) (hexact : b=e*θ) :
    |a/d-θ| ≤ ((2*(1+|θ|)*L)/m)*δ/V := by
  have hnum' : |a-θ*d| ≤ (1+|θ|)*L*δ := by
    calc |a-θ*d| = |(a-b) - θ*(d-e)| := by rw [hexact]; ring_nf
         _ ≤ |a-b| + |θ*(d-e)| := abs_sub _ _
         _ ≤ L*δ + |θ| * (L*δ) := by rw [abs_mul]; gcongr
         _ = _ := by ring
  have hpos : 0 < m*V/2 := by positivity
  have hnon : 0 ≤ (1+|θ|)*L*δ := by positivity
  rw [show a/d-θ = (a-θ*d)/d by field_simp, abs_div]
  calc |a-θ*d|/|d| ≤ ((1+|θ|)*L*δ)/(m*V/2) :=
         div_le_div₀ hnon hnum' hpos hlower
       _ = _ := by field_simp

/-- Quantitative stability of the actual Cramer solution, under the manuscript's
compactness, coprimality, monicity and pole-free hypotheses. The constants are
chosen before the nodes and ordinates. The right hand side uses any upper bound
for the ordinate errors, hence in particular their maximum. -/
theorem normalized_stability_on_compact {r s : ℕ} {P Q : ℝ[X]} (hP : P.natDegree ≤ r)
    (hQ : Q.natDegree = s) (hmonic : Q.Monic) (hcop : IsCoprime P Q)
    {I : Set ℝ} (hI : IsCompact I) (hfree : ∀ z ∈ I, Q.eval z ≠ 0) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (x : Fin (r+1+s) → ℝ), (∀ i, x i ∈ I) → Function.Injective x →
      ∀ (y : Fin (r+1+s) → ℝ) (δ : ℝ), 0 ≤ δ →
      (∀ i, |y i - P.eval (x i) / Q.eval (x i)| ≤ δ) → δ ≤ c₀ * nodeSeparation x →
      let M := normalizedMatrix r s x y
      M.det ≠ 0 ∧ |M.det| ≤ C ∧
        ‖cramerCoefficients M (normalizedRhs s x y) - freeCoefficients P Q r s‖ ≤
          C*δ/nodeSeparation x := by
  classical
  let n := r+1+s
  let d := max r s
  let D := (reconstructionCoefficientMatrix P Q r s).det
  let θ := freeCoefficients P Q r s
  have hD : 0 < |D| := abs_pos.mpr
    (reconstruction_coefficient_det_ne_zero hP hQ.le hcop hmonic.ne_zero hQ)
  obtain ⟨X, hX⟩ := hI.exists_bound_of_continuousOn (f := fun t : ℝ => t) continuousOn_id
  obtain ⟨Z, hZ⟩ := hI.exists_bound_of_continuousOn Q.continuousOn
  obtain ⟨Y, hY⟩ := hI.exists_bound_of_continuousOn (P.continuousOn.div Q.continuousOn hfree)
  let U := 1+|X|+|Z|+|Y|
  have hU : 1 ≤ U := by dsimp [U]; linarith [abs_nonneg X, abs_nonneg Z, abs_nonneg Y]
  have hUpos : 0 < U := by linarith
  have bounds (z : ℝ) (hz : z ∈ I) : |z| ≤ U ∧ |Q.eval z| ≤ U ∧ |P.eval z/Q.eval z| ≤ U := by
    have hx₁ := (hX z hz).trans (le_abs_self _)
    have hq₁ := (hZ z hz).trans (le_abs_self _)
    have hy₁ := (hY z hz).trans (le_abs_self _)
    simp only [Real.norm_eq_abs] at hx₁ hq₁ hy₁
    change |P.eval z / Q.eval z| ≤ |Y| at hy₁
    dsimp [U]
    constructor
    · linarith [abs_nonneg Z, abs_nonneg Y]
    constructor
    · linarith [abs_nonneg X, abs_nonneg Y]
    · linarith [abs_nonneg X, abs_nonneg Z]
  obtain ⟨G, hG, gapBound⟩ := separation_bounded (n := n) hI
  obtain ⟨K, hK, detBound, detDiff⟩ := determinant_box_bounds n
    (K := (U+1)*U^d) (by positivity)
  let m := |D| / U^n
  let L := K * U^d
  have hm : 0 < m := by dsimp [m]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  let c₀ := min (1/G) (m/(2*L))
  let C := max K (2*(1+‖θ‖)*L/m)
  refine ⟨c₀, lt_min (by positivity) (by positivity), C, hK.trans_le (le_max_left _ _), ?_⟩
  intro x hx hxinj y δ hδ herr hsmall
  let z := fun i => P.eval (x i)/Q.eval (x i)
  let V := nodeSeparation x
  let M := normalizedMatrix r s x y
  let M₀ := normalizedMatrix r s x z
  have hV : 0 < V := nodeSeparation_pos hxinj
  have hVmax : V ≤ G := gapBound x hx
  have hδone : δ ≤ 1 := calc
    δ ≤ c₀*V := hsmall
    _ ≤ (1/G)*G := mul_le_mul (min_le_left _ _) hVmax hV.le (by positivity)
    _ = 1 := by field_simp
  have hbudget : L*δ ≤ m*V/2 := calc
    L*δ ≤ L*((m/(2*L))*V) := by
      apply mul_le_mul_of_nonneg_left _ hL.le
      exact hsmall.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hV.le)
    _ = _ := by field_simp
  have hvx (i) := (bounds _ (hx i)).1
  have hvz (i) : |z i| ≤ U := (bounds _ (hx i)).2.2
  have hvy (i) : |y i| ≤ U+1 := by
    have hh := abs_sub_abs_le_abs_sub (y i) (z i)
    have hh' : |y i-z i| ≤ δ := herr i
    linarith [hvz i]
  have ha (j : Option (Fin n)) (i k : Fin n) :=
    sample_entries x y z hU (by linarith : 1 ≤ U+1) hδ hvx hvy
      (fun i => (hvz i).trans (by linarith)) herr j i k
  have hdiff (j : Option (Fin n)) :
      |(sampleMatrix r s x y j).det-(sampleMatrix r s x z j).det| ≤ L*δ :=
    (detDiff _ _ (U^d*δ) (by positivity) (fun i k => (ha j i k).1)
      (fun i k => (ha j i k).2.1) (fun i k => (ha j i k).2.2)).trans_eq (by dsimp [L]; ring)
  have hQx (i) : Q.eval (x i) ≠ 0 := hfree _ (hx i)
  have hprod : (∏ i, Q.eval (x i)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hQx i)
  have prodBound : |∏ i, Q.eval (x i)| ≤ U^n := by
    rw [Finset.abs_prod]
    calc (∏ i, |Q.eval (x i)|) ≤ ∏ _i : Fin n, U :=
           Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun i _ => (bounds _ (hx i)).2.1)
         _ = _ := by simp
  have hD₀ : |M₀.det| * |∏ i, Q.eval (x i)| = |D| * V := by
    have he := normalized_det_factorization hP hQ.le x hQx
    change M₀.det = D * _ / _ at he
    have hh := congrArg abs ((eq_div_iff hprod).mp he)
    simpa only [abs_mul, nodeSeparation, V] using hh
  have hlow₀ : m*V ≤ |M₀.det| := calc
    m*V = (|D| * V)/U^n := by dsimp [m]; ring
    _ ≤ _ := (div_le_iff₀ (by positivity)).mpr
      (hD₀.symm.le.trans (mul_le_mul_of_nonneg_left prodBound (abs_nonneg _)))
  have hden : |M.det-M₀.det| ≤ L*δ := hdiff none
  have hlower : m*V/2 ≤ |M.det| := by
    have hreverse := abs_sub_abs_le_abs_sub M₀.det M.det
    rw [abs_sub_comm M₀.det M.det] at hreverse
    linarith
  have hM : M.det ≠ 0 := abs_pos.mp ((by positivity : 0 < m*V/2).trans_le hlower)
  have hMbound : |M.det| ≤ K := detBound M (fun i k => (ha none i k).1)
  refine ⟨hM, hMbound.trans (le_max_left _ _), ?_⟩
  apply (pi_norm_le_iff_of_nonneg (div_nonneg (mul_nonneg
    (le_trans hK.le (le_max_left _ _)) hδ) hV.le)).mpr
  intro j
  rw [Real.norm_eq_abs]
  change |M.cramer (normalizedRhs s x y) j / M.det - θ j| ≤ C*δ/V
  have hnum : |M.cramer (normalizedRhs s x y) j - M₀.cramer (normalizedRhs s x z) j| ≤ L*δ :=
    hdiff (some j)
  have hex := cramer_of_solution (normalized_system_exact hP hQ hmonic x hQx) j
  have est := perturb_div hL.le hδ hV hm hM hlower hden hnum hex
  apply est.trans
  apply div_le_div_of_nonneg_right _ hV.le
  apply mul_le_mul_of_nonneg_right _ hδ
  apply le_trans _ (le_max_right K _)
  have hj : |θ j| ≤ ‖θ‖ := norm_le_pi_norm θ j
  gcongr

end MahlerLeanII.Reconstruction
