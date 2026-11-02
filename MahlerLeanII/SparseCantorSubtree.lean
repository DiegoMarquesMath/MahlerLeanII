import MahlerLeanII.SparseCantorBranches

/-!
Subtrees of the binary fusion tree.

For perfectness we need a point of the global limit set inside every
prescribed node interval.  We obtain one by following the left child
indefinitely and applying Cantor's intersection theorem to the resulting
nested compact intervals.
-/

noncomputable section
namespace MahlerLeanII.Escape

open Set

/-- Extend a finite binary address by repeatedly choosing the left child. -/
def leftDescendantPath {n : ℕ} (omega : CantorPath n) :
    (k : ℕ) → CantorPath (n + k)
  | 0 => omega
  | k + 1 => Fin.cons false (leftDescendantPath omega k)

@[simp]
theorem leftDescendantPath_zero {n : ℕ} (omega : CantorPath n) :
    leftDescendantPath omega 0 = omega := rfl

@[simp]
theorem leftDescendantPath_succ {n : ℕ} (omega : CantorPath n) (k : ℕ) :
    leftDescendantPath omega (k + 1) =
      Fin.cons false (leftDescendantPath omega k) := rfl

theorem tail_leftDescendantPath_succ {n : ℕ} (omega : CantorPath n) (k : ℕ) :
    Fin.tail (leftDescendantPath omega (k + 1)) =
      leftDescendantPath omega k := by
  rw [leftDescendantPath_succ]
  funext i
  simp [Fin.tail]

/-- The interval obtained after k further left-child choices below omega. -/
def cantorSubtreeLevel {f : ℝ → ℝ} (d : SparseBinaryInputs f)
    {n : ℕ} (omega : CantorPath n) (k : ℕ) : Set ℝ :=
  Icc (cantorStage d (n + k) (leftDescendantPath omega k)).l
      (cantorStage d (n + k) (leftDescendantPath omega k)).u

theorem cantorSubtreeLevel_nonempty {f : ℝ → ℝ} (d : SparseBinaryInputs f)
    {n : ℕ} (omega : CantorPath n) (k : ℕ) :
    (cantorSubtreeLevel d omega k).Nonempty := by
  exact nonempty_Icc.mpr
    (cantorStage d (n + k) (leftDescendantPath omega k)).width.le

theorem cantorSubtreeLevel_compact {f : ℝ → ℝ} (d : SparseBinaryInputs f)
    {n : ℕ} (omega : CantorPath n) (k : ℕ) :
    IsCompact (cantorSubtreeLevel d omega k) :=
  isCompact_Icc

theorem cantorSubtreeLevel_nested {f : ℝ → ℝ} (d : SparseBinaryInputs f)
    {n : ℕ} (omega : CantorPath n) (k : ℕ) :
    cantorSubtreeLevel d omega (k + 1) ⊆ cantorSubtreeLevel d omega k := by
  intro x hx
  have h :=
    cantorStage_nested d (n + k) (leftDescendantPath omega (k + 1)) hx
  rw [tail_leftDescendantPath_succ omega k] at h
  exact ⟨h.1.le, h.2.le⟩

/-- The compact limit obtained by following the left subtree below omega. -/
def cantorSubtreeLimit {f : ℝ → ℝ} (d : SparseBinaryInputs f)
    {n : ℕ} (omega : CantorPath n) : Set ℝ :=
  ⋂ k : ℕ, cantorSubtreeLevel d omega k

theorem cantorSubtreeLimit_nonempty {f : ℝ → ℝ} (d : SparseBinaryInputs f)
    {n : ℕ} (omega : CantorPath n) :
    (cantorSubtreeLimit d omega).Nonempty := by
  unfold cantorSubtreeLimit
  exact IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun k => cantorSubtreeLevel d omega k)
    (cantorSubtreeLevel_nested d omega)
    (cantorSubtreeLevel_nonempty d omega)
    (cantorSubtreeLevel_compact d omega 0)
    (fun k => (cantorSubtreeLevel_compact d omega k).isClosed)

theorem cantorSubtreeLimit_subset_node {f : ℝ → ℝ} (d : SparseBinaryInputs f)
    {n : ℕ} (omega : CantorPath n) :
    cantorSubtreeLimit d omega ⊆
      Icc (cantorStage d n omega).l (cantorStage d n omega).u := by
  intro x hx
  have h0 : x ∈ cantorSubtreeLevel d omega 0 := (mem_iInter.mp hx) 0
  simpa [cantorSubtreeLevel] using h0

/-- Every subtree limit point belongs to the global Cantor limit set. -/
theorem cantorSubtreeLimit_subset_limitSet {f : ℝ → ℝ} (d : SparseBinaryInputs f)
    {n : ℕ} (omega : CantorPath n) :
    cantorSubtreeLimit d omega ⊆ cantorLimitSet d := by
  intro x hx
  rw [cantorLimitSet, mem_iInter]
  intro m
  by_cases hmn : m ≤ n
  · have hn : x ∈ cantorLevel d n := by
      exact mem_iUnion.mpr
        ⟨omega, cantorSubtreeLimit_subset_node d omega hx⟩
    have hanti : Antitone (cantorLevel d) :=
      antitone_nat_of_succ_le (cantorLevel_nested d)
    exact hanti hmn hn
  · have hnm : n ≤ m := Nat.le_of_lt (lt_of_not_ge hmn)
    rcases Nat.exists_eq_add_of_le hnm with ⟨k, rfl⟩
    have hk : x ∈ cantorSubtreeLevel d omega k := (mem_iInter.mp hx) k
    exact mem_iUnion.mpr ⟨leftDescendantPath omega k, hk⟩

/-- Every node interval contains at least one point of the global limit set. -/
theorem cantorLimitSet_meets_node {f : ℝ → ℝ} (d : SparseBinaryInputs f)
    {n : ℕ} (omega : CantorPath n) :
    ∃ x ∈ cantorLimitSet d,
      x ∈ Icc (cantorStage d n omega).l (cantorStage d n omega).u := by
  obtain ⟨x, hx⟩ := cantorSubtreeLimit_nonempty d omega
  exact ⟨x, cantorSubtreeLimit_subset_limitSet d omega hx,
    cantorSubtreeLimit_subset_node d omega hx⟩

end MahlerLeanII.Escape
