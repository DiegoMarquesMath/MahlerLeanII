import MahlerLeanII.SparseCantorTree
import MahlerLean.FusionConclusion
import MahlerLean.IrrationalityExponent

/-!
Coherent branches through the binary fusion tree.

A point of the limit set belongs to exactly one interval at each level.
This turns the levelwise compact construction into a genuine branch, whose
fusion invariants can be packaged in the existing FusionData structure.
-/

noncomputable section
namespace MahlerLeanII.Escape

open Set

/-- Distinct nodes at one level are strictly ordered and separated. -/
theorem cantorStage_order_separated_of_ne {f : ℝ → ℝ} (d : SparseBinaryInputs f) :
    ∀ n : ℕ, ∀ omega eta : CantorPath n, omega ≠ eta →
      (cantorStage d n omega).u < (cantorStage d n eta).l ∨
      (cantorStage d n eta).u < (cantorStage d n omega).l := by
  intro n
  induction n with
  | zero =>
      intro omega eta hne
      exact (hne (Subsingleton.elim omega eta)).elim
  | succ n ih =>
      intro omega eta hne
      by_cases htail : Fin.tail omega = Fin.tail eta
      · have hbit : omega 0 ≠ eta 0 := by
          intro hzero
          apply hne
          rw [← Fin.cons_self_tail omega, ← Fin.cons_self_tail eta, hzero, htail]
        cases homega : omega 0 <;> cases heta : eta 0
        · exact (hbit (by simp [homega, heta])).elim
        · left
          rw [cantorStage_succ, cantorStage_succ]
          simp only [homega, heta]
          rw [← htail]
          exact (cantorTransition d n (Fin.tail omega)).separated
        · right
          rw [cantorStage_succ, cantorStage_succ]
          simp only [homega, heta]
          rw [htail]
          exact (cantorTransition d n (Fin.tail eta)).separated
        · exact (hbit (by simp [homega, heta])).elim
      · rcases ih (Fin.tail omega) (Fin.tail eta) htail with hparent | hparent
        · left
          have hnomega := cantorStage_nested d n omega
          have hneta := cantorStage_nested d n eta
          have hright :
              (cantorStage d (n + 1) omega).u <
                (cantorStage d n (Fin.tail omega)).u :=
            (hnomega (right_mem_Icc.mpr
              (cantorStage d (n + 1) omega).width.le)).2
          have hleft :
              (cantorStage d n (Fin.tail eta)).l <
                (cantorStage d (n + 1) eta).l :=
            (hneta (left_mem_Icc.mpr
              (cantorStage d (n + 1) eta).width.le)).1
          linarith
        · right
          have hnomega := cantorStage_nested d n omega
          have hneta := cantorStage_nested d n eta
          have hright :
              (cantorStage d (n + 1) eta).u <
                (cantorStage d n (Fin.tail eta)).u :=
            (hneta (right_mem_Icc.mpr
              (cantorStage d (n + 1) eta).width.le)).2
          have hleft :
              (cantorStage d n (Fin.tail omega)).l <
                (cantorStage d (n + 1) omega).l :=
            (hnomega (left_mem_Icc.mpr
              (cantorStage d (n + 1) omega).width.le)).1
          linarith

/-- A point belongs to at most one node interval at each depth. -/
theorem cantorStage_path_unique {f : ℝ → ℝ} (d : SparseBinaryInputs f)
    (n : ℕ) {omega eta : CantorPath n} {x : ℝ}
    (homega : x ∈ Icc (cantorStage d n omega).l (cantorStage d n omega).u)
    (heta : x ∈ Icc (cantorStage d n eta).l (cantorStage d n eta).u) :
    omega = eta := by
  by_contra hne
  rcases cantorStage_order_separated_of_ne d n omega eta hne with h | h
  · linarith [homega.2, heta.1]
  · linarith [heta.2, homega.1]

/-- The unique address containing a limit-set point at level n. -/
noncomputable def cantorPathAt {f : ℝ → ℝ} (d : SparseBinaryInputs f)
    (x : ℝ) (hx : x ∈ cantorLimitSet d) (n : ℕ) : CantorPath n :=
  Classical.choose (mem_iUnion.mp ((mem_iInter.mp hx) n))

theorem cantorPathAt_mem {f : ℝ → ℝ} (d : SparseBinaryInputs f)
    (x : ℝ) (hx : x ∈ cantorLimitSet d) (n : ℕ) :
    x ∈ Icc (cantorStage d n (cantorPathAt d x hx n)).l
            (cantorStage d n (cantorPathAt d x hx n)).u :=
  Classical.choose_spec (mem_iUnion.mp ((mem_iInter.mp hx) n))

/-- The level addresses of a limit-set point form a coherent branch. -/
theorem cantorPathAt_tail {f : ℝ → ℝ} (d : SparseBinaryInputs f)
    (x : ℝ) (hx : x ∈ cantorLimitSet d) (n : ℕ) :
    Fin.tail (cantorPathAt d x hx (n + 1)) = cantorPathAt d x hx n := by
  have hchild := cantorPathAt_mem d x hx (n + 1)
  have hparent_open :=
    cantorStage_nested d n (cantorPathAt d x hx (n + 1)) hchild
  have hparent :
      x ∈ Icc (cantorStage d n (Fin.tail (cantorPathAt d x hx (n + 1)))).l
              (cantorStage d n (Fin.tail (cantorPathAt d x hx (n + 1)))).u :=
    ⟨hparent_open.1.le, hparent_open.2.le⟩
  exact cantorStage_path_unique d n hparent (cantorPathAt_mem d x hx n)

/-- Every point of the sparse binary limit set is Liouville. -/
theorem cantorLimitSet_liouville {f : ℝ → ℝ} (d : SparseBinaryInputs f)
    {x : ℝ} (hx : x ∈ cantorLimitSet d) :
    Liouville x := by
  let center : ℕ → ℚ :=
    fun n => (cantorTransition d n (cantorPathAt d x hx n)).center
  have hden (n : ℕ) : 2 ≤ (center n).den :=
    (cantorTransition d n (cantorPathAt d x hx n)).den
  apply MahlerLean.liouville_of_source_approximations x center hden
  intro n
  have h := cantorStage_source d n
    (cantorPathAt d x hx (n + 1)) x
    (cantorPathAt_mem d x hx (n + 1))
  rw [cantorPathAt_tail d x hx n] at h
  simpa only [center] using h

/-- The binary construction has a single target-denominator cutoff
valid for every point of the final Cantor set. -/
theorem cantorLimitSet_target_avoidance {f : ℝ → ℝ} (d : SparseBinaryInputs f)
    {x : ℝ} (hx : x ∈ cantorLimitSet d) :
    MahlerLean.EventualTargetAvoidance (f x) (d.t + 3) d.root.H := by
  let T : ℕ → ℕ := fun n => (cantorStage d n (cantorPathAt d x hx n)).H
  have hT : StrictMono T := strictMono_nat_of_lt_succ (fun n => by
    have h := cantorStage_cutoff_growth d n
      (cantorPathAt d x hx (n + 1))
    rw [cantorPathAt_tail d x hx n] at h
    exact h)
  have hav : MahlerLean.EventualTargetAvoidance (f x) (d.t + 3) (T 0) :=
    MahlerLean.target_avoidance_from_blocks (f x) (d.t+3) T hT (by
      intro n a b hlo hhi
      have h := cantorStage_target d n
        (cantorPathAt d x hx (n + 1)) x
        (cantorPathAt_mem d x hx (n + 1)) a b
      rw [cantorPathAt_tail d x hx n] at h
      exact h hlo hhi)
  simpa [T,cantorStage] using hav

/-- The common eventual target bound excludes both rational and
Liouville values for every point of the Cantor set. -/
theorem cantorLimitSet_image_outside_E {f : ℝ → ℝ} (d : SparseBinaryInputs f)
    {x : ℝ} (hx : x ∈ cantorLimitSet d) :
    ¬ rationalOrLiouville (f x) := by
  have avoid := cantorLimitSet_target_avoidance d hx
  rintro (⟨z,hz⟩ | hLi')
  · let b := d.root.H * z.den
    have hb : d.root.H ≤ b := Nat.le_mul_of_pos_right _ z.den_pos
    have heq : (f x) = (((d.root.H : ℤ)*z.num : ℤ) / (b : ℝ)) := by
      rw [← hz,Rat.cast_def]
      dsimp [b]
      push_cast
      have h0 : ((d.root.H : ℝ)) ≠ 0 := by
        exact_mod_cast (show d.root.H ≠ 0 by have := d.root.two; omega)
      field_simp
    have hv := avoid (((d.root.H:ℤ)*z.num)) b hb
    rw [← heq,sub_self,abs_zero] at hv
    exact (not_lt_of_ge (by positivity)) hv
  · exact MahlerLean.not_liouville_of_eventual_target_avoidance
      (f x) (d.t+3) d.root.H avoid hLi'

/-- Uniformly bounded irrationality exponent of every target value. -/
theorem cantorLimitSet_irrationalityExponent_le {f : ℝ → ℝ} (d : SparseBinaryInputs f)
    {x : ℝ} (hx : x ∈ cantorLimitSet d) :
    MahlerLean.irrationalityExponent (f x) ≤ ((d.t + 3 : ℕ) : EReal) :=
  MahlerLean.irrationalityExponent_le_of_eventual_target_avoidance
    (cantorLimitSet_target_avoidance d hx)

end MahlerLeanII.Escape
