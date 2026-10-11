module

public import Mathlib

@[expose] public section

/-!
# Signed fibers and exact equality deficits

This module formalizes the pointwise algebra in ED.1--ED.6 of the written
Gate 3 proof, together with the truncation identity used in the inverse
extrusion argument.

The four real inputs `dU`, `dV`, `nU`, and `nV` are arbitrary. In the
geometric application, the first two are roof deficits and the last two
are niche barriers. In particular, a signed fiber length is not silently
replaced by its positive part. Nonemptiness is a separate conclusion.

The final deficit theorems are arithmetic statements with explicit
hypotheses. They do not assert sharp cap bounds, identify an integral
with area, or classify a geometric maximizer.
-/

namespace AmbidextrousSofa

/-! ## The exact four-wall fiber -/

/-- The signed fiber length in ED.1. It is allowed to be negative. -/
noncomputable def signedFiberLength (dU dV nU nV : ℝ) : ℝ :=
  1 - max dV nU - max dU nV

/-- The points satisfying all four vertical wall inequalities. -/
def fourWallFiber (dU dV nU nV : ℝ) : Set ℝ :=
  {y | dV ≤ y ∧ nU ≤ y ∧ y ≤ 1 - dU ∧ y ≤ 1 - nV}

/-- The four wall inequalities give a closed interval, possibly empty. -/
theorem fourWallFiber_eq_Icc (dU dV nU nV : ℝ) :
    fourWallFiber dU dV nU nV =
      Set.Icc (max dV nU) (1 - max dU nV) := by
  ext y
  simp only [fourWallFiber, Set.mem_ofPred_eq, Set.mem_Icc, max_le_iff, le_sub_comm (a := y),
    and_assoc]

/-- A signed fiber has nonnegative length exactly when the fiber is nonempty. -/
theorem fourWallFiber_nonempty_iff (dU dV nU nV : ℝ) :
    (fourWallFiber dU dV nU nV).Nonempty ↔
      0 ≤ signedFiberLength dU dV nU nV := by
  rw [fourWallFiber_eq_Icc, Set.nonempty_Icc, signedFiberLength, sub_nonneg, le_sub_comm]

/-- A point in the four-wall fiber certifies nonnegative signed length. -/
theorem signedFiberLength_nonneg_of_mem (dU dV nU nV y : ℝ)
    (hy : y ∈ fourWallFiber dU dV nU nV) :
    0 ≤ signedFiberLength dU dV nU nV :=
  (fourWallFiber_nonempty_iff dU dV nU nV).mp ⟨y, hy⟩

/-! ## Pointwise partition defects -/

/-- The positive-part identity used in both parts of ED.2. -/
private theorem max_sub_eq (a b : ℝ) : max a b - b = max (a - b) 0 := by
  rw [← max_sub_sub_right, sub_self]

/-- The nonnegative defect charged on the middle interval in ED.2. -/
noncomputable def middlePartitionDefect (dU dV nU nV : ℝ) : ℝ :=
  max (dV - nU) 0 + max (dU - nV) 0

/-- The nonnegative defect charged outside the middle interval in ED.2. -/
noncomputable def exteriorPartitionDefect (dU dV nU nV : ℝ) : ℝ :=
  max (nU - dV) 0 + max (nV - dU) 0

/-- The middle comparison is an exact identity, even for negative signed fibers. -/
theorem middle_partition_defect_identity (dU dV nU nV : ℝ) :
    (1 - nU - nV) - signedFiberLength dU dV nU nV =
      middlePartitionDefect dU dV nU nV := by
  rw [signedFiberLength, middlePartitionDefect, ← max_sub_eq, ← max_sub_eq]; ring

/-- The exterior comparison is an exact identity, even for negative signed fibers. -/
theorem exterior_partition_defect_identity (dU dV nU nV : ℝ) :
    (1 - dU - dV) - signedFiberLength dU dV nU nV =
      exteriorPartitionDefect dU dV nU nV := by
  rw [signedFiberLength, exteriorPartitionDefect, ← max_sub_eq, ← max_sub_eq, max_comm nU,
    max_comm nV]
  ring

theorem middlePartitionDefect_nonneg (dU dV nU nV : ℝ) :
    0 ≤ middlePartitionDefect dU dV nU nV := by
  unfold middlePartitionDefect; positivity

theorem exteriorPartitionDefect_nonneg (dU dV nU nV : ℝ) :
    0 ≤ exteriorPartitionDefect dU dV nU nV := by
  unfold exteriorPartitionDefect; positivity

end AmbidextrousSofa
