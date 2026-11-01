import MahlerLeanII.Basic
import Mathlib.Tactic

/-! Simultaneous scale approximation and the coefficient subfield, Section 2. -/

namespace MahlerLeanII

private theorem extend_fraction (p : ℤ) (h k : ℕ) (hk : 0 < k) :
    ((p*(k:ℤ) : ℤ):ℝ)/((h*k:ℕ):ℝ) = (p:ℝ)/h := by
  push_cast
  have hn : (k:ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  exact mul_div_mul_right _ _ hn

/-- Lemma 2.2 for a finite list. The scale is universal after the exponent and
cutoff, and a single denominator serves every member of the list. -/
theorem simultaneous_list (xs : List ℝ) (hxs : ∀ x ∈ xs, ScaleApproximable x)
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ D : ℕ, 1 ≤ D ∧ ∃ H₀ : ℕ, 2 ≤ H₀ ∧ ∀ H : ℕ, H₀ ≤ H →
      ∃ h : ℕ, 1 ≤ h ∧ h ≤ H^D ∧ ∀ x ∈ xs, ∃ a : ℤ,
        |x-(a:ℝ)/h| ≤ 1/((H:ℝ)*h)^N := by
  induction xs with
  | nil => exact ⟨1,by omega,2,by omega,fun H hH => ⟨1,by omega,by simpa using
        (by omega : 1 ≤ H),by simp⟩⟩
  | cons x xs ih =>
    obtain ⟨D,hD,H₁,hH₁,vec⟩ := ih (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
    obtain ⟨E,hE,H₂,hH₂,one⟩ := hxs x (by simp) (N*(D+1)) (Nat.mul_pos hN (by omega))
    refine ⟨E+(E+1)*D,by omega,max H₁ H₂,hH₁.trans (le_max_left _ _),?_⟩
    intro H hH
    obtain ⟨a,k,hk,hkH,hen⟩ := one H ((le_max_right _ _).trans hH)
    have hHk : H ≤ H*k := Nat.le_mul_of_pos_right _ hk
    obtain ⟨l,hl,hlH,hes⟩ := vec (H*k) (((le_max_left _ _).trans hH).trans hHk)
    have hmul : H*k ≤ H^(E+1) := by rw [pow_succ, Nat.mul_comm (H^E)]; gcongr
    have bound : k*l ≤ H^(E+(E+1)*D) := by
      rw [pow_add,pow_mul]
      exact Nat.mul_le_mul hkH (hlH.trans (Nat.pow_le_pow_left hmul _))
    refine ⟨k*l, Nat.mul_pos hk hl, bound, ?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · refine ⟨a*(l:ℤ),?_⟩
      rw [extend_fraction a k l hl]
      apply hen.trans
      have hl' : ((l:ℕ):ℝ) ≤ ((H:ℝ)*k)^D := by exact_mod_cast hlH
      have hpr : (H:ℝ)*(k*l:ℕ) ≤ ((H:ℝ)*k)^(D+1) := by
        push_cast; rw [pow_succ,← mul_assoc]
        simpa only [mul_comm ((H:ℝ)*k)] using
          mul_le_mul_of_nonneg_left hl' (show 0 ≤ (H:ℝ)*k by positivity)
      have base : 0 < (H:ℝ)*(k*l:ℕ) := by
        have : 2 ≤ H := hH₁.trans ((le_max_left _ _).trans hH)
        positivity
      apply one_div_le_one_div_of_le (pow_pos base _)
      rw [Nat.mul_comm N _, pow_mul]
      exact pow_le_pow_left₀ base.le hpr _
    · obtain ⟨b,hb⟩ := hes y hy
      refine ⟨b*(k:ℤ),?_⟩
      rw [Nat.mul_comm k l, extend_fraction b l k hk]
      push_cast at hb ⊢
      simpa only [mul_assoc, mul_comm (l:ℝ) (k:ℝ)] using hb

/-- Finite-vector form of Lemma 2.2; a coordinatewise bound expresses the
same sup-norm estimate. -/
theorem simultaneous_approximation {s : ℕ} (x : Fin s → ℝ)
    (hx : ∀ i, ScaleApproximable (x i)) (N : ℕ) (hN : 1 ≤ N) :
    ∃ D : ℕ, 1 ≤ D ∧ ∃ H₀ : ℕ, 2 ≤ H₀ ∧ ∀ H : ℕ, H₀ ≤ H →
      ∃ h : ℕ, 1 ≤ h ∧ h ≤ H^D ∧ ∃ p : Fin s → ℤ,
        ∀ i, |x i-(p i:ℝ)/h| ≤ 1/((H:ℝ)*h)^N := by
  classical
  have hall : ∀ y ∈ List.ofFn x, ScaleApproximable y := by
    intro y hy
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hy
    exact hx i
  obtain ⟨D,hD,H₀,hH₀,hs⟩ := simultaneous_list (List.ofFn x) hall N hN
  refine ⟨D,hD,H₀,hH₀,?_⟩
  intro H hH
  obtain ⟨h,hh,hbound,hn⟩ := hs H hH
  have each (i) := hn (x i) (List.mem_ofFn.mpr ⟨i,rfl⟩)
  choose p hp using each
  exact ⟨h,hh,hbound,p,hp⟩

end MahlerLeanII
