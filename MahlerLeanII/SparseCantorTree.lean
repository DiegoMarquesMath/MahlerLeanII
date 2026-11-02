import MahlerLeanII.SparseCantorStep
import Mathlib.Data.Fin.Tuple.Basic

/-!
The binary tree of sparse-scale successors and its compact level sets.

A node at depth n is indexed by a Boolean n-tuple. We store the newest
choice at coordinate zero, so the parent of omega : Fin (n+1) -> Bool
is Fin.tail omega. This convention makes primitive recursion on the
depth definitionally simple.
-/

noncomputable section
namespace MahlerLeanII.Escape

open Set Counting

/-- Input data for the sparse-scale binary construction. The quantitative
counting estimate is a proof field, not an axiom or assumed conclusion. -/
structure SparseBinaryInputs (f : ℝ → ℝ) where
  I : Set ℝ
  M : ℝ
  L : ℝ
  t : ℕ
  hM : 0 ≤ M
  ht : 1 ≤ t
  hlip : ∀ x ∈ I, ∀ y ∈ I, |f x - f y| ≤ M * |x-y|
  count : ∀ A : ℕ, 3 ≤ A → ∃ C : ℝ, 0 < C ∧
    ∀ Smin : ℕ, ∃ S : ℕ, Smin ≤ S ∧ 2 ≤ S ∧ ∀ H : ℕ, 2 ≤ H →
    ∀ F : Finset ℚ, (∀ r ∈ F, (r:ℝ) ∈ I) → (∀ r ∈ F, r.den < 2*S) →
      (∀ r ∈ F, Resonant f M t S A H r) →
      (F.card : ℝ) ≤ L*(S:ℝ)^2*((H:ℝ)^(t+1))⁻¹ + C*S
  root : SparseNode I L t

/-- Binary addresses of nodes at depth n. -/
abbrev CantorPath (n : ℕ) := Fin n → Bool

/-- The fusion stage attached to a binary address. -/
noncomputable def cantorStage {f : ℝ → ℝ} (d : SparseBinaryInputs f) :
    (n : ℕ) → CantorPath n → SparseNode d.I d.L d.t
  | 0, _ => d.root
  | n + 1, omega =>
      let parent := cantorStage d n (Fin.tail omega)
      let t := Classical.choice (exists_sparse_binary_step d.hM d.ht d.hlip d.count parent n)
      if omega 0 then t.rightChild else t.leftChild

/-- The chosen binary transition at a node. -/
noncomputable def cantorTransition {f : ℝ → ℝ} (d : SparseBinaryInputs f)
    (n : ℕ) (omega : CantorPath n) :
    SparseBinaryStep (f := f) (cantorStage d n omega) n :=
  Classical.choice (exists_sparse_binary_step d.hM d.ht d.hlip d.count (cantorStage d n omega) n)

theorem cantorStage_succ {f : ℝ → ℝ} (d : SparseBinaryInputs f)
    (n : ℕ) (omega : CantorPath (n + 1)) :
    cantorStage d (n + 1) omega =
      if omega 0 then
        (cantorTransition d n (Fin.tail omega)).rightChild
      else
        (cantorTransition d n (Fin.tail omega)).leftChild := rfl

@[simp]
theorem cantorStage_cons_false {f : ℝ → ℝ} (d : SparseBinaryInputs f)
    (n : ℕ) (omega : CantorPath n) :
    cantorStage d (n + 1) (Fin.cons false omega) =
      (cantorTransition d n omega).leftChild := by
  rw [cantorStage_succ]
  have htail :
      @Fin.tail n (fun _ : Fin (n + 1) => Bool) (Fin.cons false omega) = omega := by
    simp
  rw [htail]
  simp

@[simp]
theorem cantorStage_cons_true {f : ℝ → ℝ} (d : SparseBinaryInputs f)
    (n : ℕ) (omega : CantorPath n) :
    cantorStage d (n + 1) (Fin.cons true omega) =
      (cantorTransition d n omega).rightChild := by
  rw [cantorStage_succ]
  have htail :
      @Fin.tail n (fun _ : Fin (n + 1) => Bool) (Fin.cons true omega) = omega := by
    simp
  rw [htail]
  simp

/-- Every child interval lies strictly inside its parent interval. -/
theorem cantorStage_nested {f : ℝ → ℝ} (d : SparseBinaryInputs f)
    (n : ℕ) (omega : CantorPath (n + 1)) :
    Icc (cantorStage d (n + 1) omega).l
        (cantorStage d (n + 1) omega).u ⊆
      Ioo (cantorStage d n (Fin.tail omega)).l
          (cantorStage d n (Fin.tail omega)).u := by
  rw [cantorStage_succ]
  by_cases h : omega 0
  · simp only [h]
    exact (cantorTransition d n (Fin.tail omega)).right_nested
  · simp only [h]
    exact (cantorTransition d n (Fin.tail omega)).left_nested

/-- The target cutoff grows strictly along every edge of the tree. -/
theorem cantorStage_cutoff_growth {f : ℝ → ℝ} (d : SparseBinaryInputs f)
    (n : ℕ) (omega : CantorPath (n + 1)) :
    (cantorStage d n (Fin.tail omega)).H <
      (cantorStage d (n + 1) omega).H := by
  rw [cantorStage_succ]
  by_cases h : omega 0
  · simp only [h]
    exact (cantorTransition d n (Fin.tail omega)).right_growth
  · simp only [h]
    exact (cantorTransition d n (Fin.tail omega)).left_growth

/-- Source approximation inherited by every child. -/
theorem cantorStage_source {f : ℝ → ℝ} (d : SparseBinaryInputs f)
    (n : ℕ) (omega : CantorPath (n + 1))
    (x : ℝ)
    (hx : x ∈ Icc (cantorStage d (n + 1) omega).l
                    (cantorStage d (n + 1) omega).u) :
    let t := cantorTransition d n (Fin.tail omega)
    0 < |x - (t.center : ℝ)| ∧
      |x - (t.center : ℝ)| <
        (((t.center.den : ℕ) : ℝ) ^ (n + 3))⁻¹ := by
  rw [cantorStage_succ] at hx
  by_cases h : omega 0
  · simp only [h] at hx
    exact (cantorTransition d n (Fin.tail omega)).source_right x hx
  · simp only [h] at hx
    exact (cantorTransition d n (Fin.tail omega)).source_left x hx

/-- Target avoidance inherited by every child. -/
theorem cantorStage_target {f : ℝ → ℝ} (d : SparseBinaryInputs f)
    (n : ℕ) (omega : CantorPath (n + 1))
    (x : ℝ)
    (hx : x ∈ Icc (cantorStage d (n + 1) omega).l
                    (cantorStage d (n + 1) omega).u)
    (a : ℤ) (b : ℕ)
    (hlo : (cantorStage d n (Fin.tail omega)).H ≤ b)
    (hhi : b < (cantorStage d (n + 1) omega).H) :
    ((b : ℝ) ^ (d.t + 3))⁻¹ < |f x - (a : ℝ) / (b : ℝ)| := by
  rw [cantorStage_succ] at hx hhi
  by_cases h : omega 0
  · simp only [h] at hx hhi
    exact (cantorTransition d n (Fin.tail omega)).target_right x hx a b hlo hhi
  · simp only [h] at hx hhi
    exact (cantorTransition d n (Fin.tail omega)).target_left x hx a b hlo hhi

/-- The two children of a node are strictly separated. -/
theorem cantorStage_siblings_separated {f : ℝ → ℝ} (d : SparseBinaryInputs f)
    (n : ℕ) (omega : CantorPath n) :
    (cantorStage d (n + 1) (Fin.cons false omega)).u <
      (cantorStage d (n + 1) (Fin.cons true omega)).l := by
  simp only [cantorStage_cons_false, cantorStage_cons_true]
  exact (cantorTransition d n omega).separated

/-- Compact union of all intervals at one depth. -/
def cantorLevel {f : ℝ → ℝ} (d : SparseBinaryInputs f) (n : ℕ) : Set ℝ :=
  ⋃ omega : CantorPath n,
    Icc (cantorStage d n omega).l (cantorStage d n omega).u

theorem cantorLevel_compact {f : ℝ → ℝ} (d : SparseBinaryInputs f) (n : ℕ) :
    IsCompact (cantorLevel d n) := by
  unfold cantorLevel
  exact isCompact_iUnion fun _ => isCompact_Icc

theorem cantorLevel_nonempty {f : ℝ → ℝ} (d : SparseBinaryInputs f) (n : ℕ) :
    (cantorLevel d n).Nonempty := by
  let omega : CantorPath n := fun _ => false
  have hnon :
      (Icc (cantorStage d n omega).l (cantorStage d n omega).u).Nonempty :=
    nonempty_Icc.mpr (cantorStage d n omega).width.le
  exact hnon.mono (subset_iUnion (fun eta : CantorPath n =>
    Icc (cantorStage d n eta).l (cantorStage d n eta).u) omega)

theorem cantorLevel_nested {f : ℝ → ℝ} (d : SparseBinaryInputs f) (n : ℕ) :
    cantorLevel d (n + 1) ⊆ cantorLevel d n := by
  intro x hx
  rcases mem_iUnion.mp hx with ⟨omega, homega⟩
  have hp : x ∈ Icc (cantorStage d n (Fin.tail omega)).l
                    (cantorStage d n (Fin.tail omega)).u := by
    have h := cantorStage_nested d n omega homega
    exact ⟨h.1.le, h.2.le⟩
  exact mem_iUnion.mpr ⟨Fin.tail omega, hp⟩

/-- The compact limit set of the full binary fusion tree. -/
def cantorLimitSet {f : ℝ → ℝ} (d : SparseBinaryInputs f) : Set ℝ :=
  ⋂ n : ℕ, cantorLevel d n

theorem cantorLimitSet_nonempty {f : ℝ → ℝ} (d : SparseBinaryInputs f) :
    (cantorLimitSet d).Nonempty := by
  unfold cantorLimitSet
  exact IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => cantorLevel d n)
    (cantorLevel_nested d)
    (cantorLevel_nonempty d)
    (cantorLevel_compact d 0)
    (fun n => (cantorLevel_compact d n).isClosed)

theorem cantorLimitSet_compact {f : ℝ → ℝ} (d : SparseBinaryInputs f) :
    IsCompact (cantorLimitSet d) := by
  have hclosed : IsClosed (cantorLimitSet d) := by
    unfold cantorLimitSet
    exact isClosed_iInter fun n => (cantorLevel_compact d n).isClosed
  have hsub : cantorLimitSet d ⊆ cantorLevel d 0 := by
    unfold cantorLimitSet
    exact iInter_subset _ 0
  exact (cantorLevel_compact d 0).of_isClosed_subset hclosed hsub

theorem cantorLimitSet_subset_ambient {f : ℝ → ℝ} (d : SparseBinaryInputs f) :
    cantorLimitSet d ⊆ d.I := by
  intro x hx
  have hx0 : x ∈ cantorLevel d 0 := (mem_iInter.mp hx) 0
  rcases mem_iUnion.mp hx0 with ⟨omega, homega⟩
  exact (cantorStage d 0 omega).within homega

end MahlerLeanII.Escape
