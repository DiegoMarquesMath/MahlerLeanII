import MahlerLeanII.SparseCantorSubtree
import Mathlib.Topology.Perfect
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecificLimits.Basic

/-!
Topological completion of the binary fusion construction.

The arithmetic part of the Cantor refinement is already contained in
CantorBranches.  This module proves the shrinking-node and endpoint facts
needed for perfectness and total disconnectedness.
-/

noncomputable section
namespace MahlerLeanII.Escape

open Set Filter
open scoped Topology

/-- A level-(n+1) interval has width bounded by a geometric quantity
depending only on n. -/
theorem cantorStage_width_lt_two_pow {f : ℝ → ℝ} (d : SparseBinaryInputs f)
    (n : ℕ) (omega : CantorPath (n + 1)) :
    (cantorStage d (n + 1) omega).u -
        (cantorStage d (n + 1) omega).l <
      2 * (((2 : ℝ) ^ n)⁻¹) := by
  let t := cantorTransition d n (Fin.tail omega)
  have hleft :=
    cantorStage_source d n omega
      (cantorStage d (n + 1) omega).l
      (left_mem_Icc.mpr (cantorStage d (n + 1) omega).width.le)
  have hright :=
    cantorStage_source d n omega
      (cantorStage d (n + 1) omega).u
      (right_mem_Icc.mpr (cantorStage d (n + 1) omega).width.le)
  dsimp only at hleft hright
  have hq2 : 2 ≤ (cantorTransition d n (Fin.tail omega)).center.den :=
    (cantorTransition d n (Fin.tail omega)).den
  have hq2r :
      (2 : ℝ) ≤ ((cantorTransition d n (Fin.tail omega)).center.den : ℝ) := by
    exact_mod_cast hq2
  have h2n_pos : 0 < (2 : ℝ) ^ n := by positivity
  have hq_pos :
      0 < ((cantorTransition d n (Fin.tail omega)).center.den : ℝ) := by
    positivity
  have hpow_base :
      (2 : ℝ) ^ (n + 3) ≤
        ((cantorTransition d n (Fin.tail omega)).center.den : ℝ) ^ (n + 3) := by
    gcongr
  have hpow_exp : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (n + 3) := by
    rw [pow_add]
    nlinarith [h2n_pos]
  have hpow :
      (2 : ℝ) ^ n ≤
        ((cantorTransition d n (Fin.tail omega)).center.den : ℝ) ^ (n + 3) :=
    hpow_exp.trans hpow_base
  have hinv :
      (((cantorTransition d n (Fin.tail omega)).center.den : ℝ) ^ (n + 3))⁻¹ ≤
        ((2 : ℝ) ^ n)⁻¹ := by
    rw [inv_le_inv₀ (pow_pos hq_pos _) h2n_pos]
    exact hpow
  have hl := (abs_lt.mp hleft.2)
  have hr := (abs_lt.mp hright.2)
  have hwidth :
      (cantorStage d (n + 1) omega).u -
          (cantorStage d (n + 1) omega).l <
        2 * (((cantorTransition d n (Fin.tail omega)).center.den : ℝ) ^
          (n + 3))⁻¹ := by
    linarith
  exact hwidth.trans_le (by gcongr)

/-- No left endpoint of a node belongs to the full limit set. -/
theorem cantorStage_left_not_mem_limitSet {f : ℝ → ℝ} (d : SparseBinaryInputs f)
    (n : ℕ) (omega : CantorPath n) :
    (cantorStage d n omega).l ∉ cantorLimitSet d := by
  intro hx
  have hxnode :
      (cantorStage d n omega).l ∈
        Icc (cantorStage d n omega).l (cantorStage d n omega).u :=
    left_mem_Icc.mpr (cantorStage d n omega).width.le
  have hpath :
      cantorPathAt d (cantorStage d n omega).l hx n = omega :=
    cantorStage_path_unique d n
      (cantorPathAt_mem d (cantorStage d n omega).l hx n) hxnode
  have hchild :=
    cantorStage_nested d n
      (cantorPathAt d (cantorStage d n omega).l hx (n + 1))
      (cantorPathAt_mem d (cantorStage d n omega).l hx (n + 1))
  rw [cantorPathAt_tail d (cantorStage d n omega).l hx n, hpath] at hchild
  exact (lt_irrefl _ hchild.1)

/-- No right endpoint of a node belongs to the full limit set. -/
theorem cantorStage_right_not_mem_limitSet {f : ℝ → ℝ} (d : SparseBinaryInputs f)
    (n : ℕ) (omega : CantorPath n) :
    (cantorStage d n omega).u ∉ cantorLimitSet d := by
  intro hx
  have hxnode :
      (cantorStage d n omega).u ∈
        Icc (cantorStage d n omega).l (cantorStage d n omega).u :=
    right_mem_Icc.mpr (cantorStage d n omega).width.le
  have hpath :
      cantorPathAt d (cantorStage d n omega).u hx n = omega :=
    cantorStage_path_unique d n
      (cantorPathAt_mem d (cantorStage d n omega).u hx n) hxnode
  have hchild :=
    cantorStage_nested d n
      (cantorPathAt d (cantorStage d n omega).u hx (n + 1))
      (cantorPathAt_mem d (cantorStage d n omega).u hx (n + 1))
  rw [cantorPathAt_tail d (cantorStage d n omega).u hx n, hpath] at hchild
  exact (lt_irrefl _ hchild.2)

/-- At a sufficiently deep level all node intervals are shorter than any
prescribed positive epsilon. -/
theorem exists_cantorStage_width_lt {f : ℝ → ℝ} (d : SparseBinaryInputs f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ ∀ omega : CantorPath n,
      (cantorStage d n omega).u - (cantorStage d n omega).l < ε := by
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨k, hk⟩ :=
    exists_pow_lt_of_lt_one hε2 (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨k + 1, by omega, ?_⟩
  intro omega
  have hw := cantorStage_width_lt_two_pow d k omega
  have hk' : (((2 : ℝ) ^ k)⁻¹) < ε / 2 := by
    simpa [one_div, inv_pow] using hk
  nlinarith [hw, hk']

/-- The full binary limit set is perfect. -/
theorem cantorLimitSet_perfect {f : ℝ → ℝ} (d : SparseBinaryInputs f) :
    Perfect (cantorLimitSet d) := by
  refine ⟨(cantorLimitSet_compact d).isClosed, ?_⟩
  rw [preperfect_iff_nhds]
  intro x hx U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨n, _hn, hwidth⟩ := exists_cantorStage_width_lt d hε
  let parent : CantorPath n := cantorPathAt d x hx n
  let child : CantorPath (n + 1) := cantorPathAt d x hx (n + 1)
  let sibling : CantorPath (n + 1) := Fin.cons (! child 0) parent
  have hsibTail : Fin.tail sibling = parent := by
    simp [sibling]
  obtain ⟨y, hyK, hyNode⟩ := cantorLimitSet_meets_node d sibling
  have hyParentOpen := cantorStage_nested d n sibling hyNode
  rw [hsibTail] at hyParentOpen
  have hyParent :
      y ∈ Icc (cantorStage d n parent).l (cantorStage d n parent).u :=
    ⟨hyParentOpen.1.le, hyParentOpen.2.le⟩
  have hxParent :
      x ∈ Icc (cantorStage d n parent).l (cantorStage d n parent).u := by
    simpa [parent] using cantorPathAt_mem d x hx n
  have hsib_ne_child : sibling ≠ child := by
    intro h
    have h0 := congrFun h 0
    dsimp [sibling] at h0
    cases hbit : child 0 <;> simp [hbit] at h0
  have hyne : y ≠ x := by
    intro hyx
    subst y
    apply hsib_ne_child
    have huniq :=
      cantorStage_path_unique d (n + 1) hyNode
        (cantorPathAt_mem d x hx (n + 1))
    simpa [child] using huniq
  have habs :
      |y - x| ≤
        (cantorStage d n parent).u - (cantorStage d n parent).l := by
    rw [abs_le]
    constructor <;> linarith [hxParent.1, hxParent.2, hyParent.1, hyParent.2]
  have hdist : dist y x < ε := by
    rw [Real.dist_eq]
    exact habs.trans_lt (hwidth parent)
  have hyU : y ∈ U := by
    apply hball
    simpa [Metric.mem_ball, dist_comm] using hdist
  exact ⟨y, ⟨hyU, hyK⟩, hyne⟩

/-- The full binary limit set is totally disconnected. -/
theorem cantorLimitSet_isTotallyDisconnected {f : ℝ → ℝ} (d : SparseBinaryInputs f) :
    IsTotallyDisconnected (cantorLimitSet d) := by
  rw [isTotallyDisconnected_iff_lt]
  intro x hx y hy hxy
  obtain ⟨n, _hn, hwidth⟩ :=
    exists_cantorStage_width_lt d (sub_pos.mpr hxy)
  let omega : CantorPath n := cantorPathAt d x hx n
  let eta : CantorPath n := cantorPathAt d y hy n
  have hxNode :
      x ∈ Icc (cantorStage d n omega).l (cantorStage d n omega).u := by
    simpa [omega] using cantorPathAt_mem d x hx n
  have hyNode :
      y ∈ Icc (cantorStage d n eta).l (cantorStage d n eta).u := by
    simpa [eta] using cantorPathAt_mem d y hy n
  have hne : omega ≠ eta := by
    intro heq
    have hySame :
        y ∈ Icc (cantorStage d n omega).l (cantorStage d n omega).u := by
      rw [heq]
      exact hyNode
    have hw := hwidth omega
    linarith [hxNode.1, hxNode.2, hySame.1, hySame.2]
  rcases cantorStage_order_separated_of_ne d n omega eta hne with hsep | hsep
  · let z := (cantorStage d n omega).u
    have hxz_le : x ≤ z := hxNode.2
    have hxz_ne : x ≠ z := by
      intro h
      apply cantorStage_right_not_mem_limitSet d n omega
      simpa [z, ← h] using hx
    have hxz : x < z := lt_of_le_of_ne hxz_le hxz_ne
    have hzy : z < y := hsep.trans_le hyNode.1
    exact ⟨z, cantorStage_right_not_mem_limitSet d n omega, ⟨hxz, hzy⟩⟩
  · exfalso
    linarith [hyNode.2, hxNode.1]

end MahlerLeanII.Escape
