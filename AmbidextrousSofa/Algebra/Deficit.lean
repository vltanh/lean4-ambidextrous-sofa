import Mathlib

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

@[simp]
theorem mem_fourWallFiber (dU dV nU nV y : ℝ) :
    y ∈ fourWallFiber dU dV nU nV ↔
      dV ≤ y ∧ nU ≤ y ∧ y ≤ 1 - dU ∧ y ≤ 1 - nV :=
  Iff.rfl

/-- The four wall inequalities give a closed interval, possibly empty. -/
theorem fourWallFiber_eq_Icc (dU dV nU nV : ℝ) :
    fourWallFiber dU dV nU nV =
      Set.Icc (max dV nU) (1 - max dU nV) := by
  ext y
  change (dV ≤ y ∧ nU ≤ y ∧ y ≤ 1 - dU ∧ y ≤ 1 - nV) ↔
    (max dV nU ≤ y ∧ y ≤ 1 - max dU nV)
  constructor
  · rintro ⟨hdV, hnU, hdU, hnV⟩
    refine ⟨max_le hdV hnU, ?_⟩
    have hUpper : max dU nV ≤ 1 - y :=
      max_le (by linarith) (by linarith)
    linarith
  · rintro ⟨hLower, hUpper⟩
    refine ⟨(le_max_left dV nU).trans hLower,
      (le_max_right dV nU).trans hLower, ?_, ?_⟩
    · have hdU : dU ≤ max dU nV := le_max_left dU nV
      linarith
    · have hnV : nV ≤ max dU nV := le_max_right dU nV
      linarith

/-- A signed fiber has nonnegative length exactly when the fiber is nonempty. -/
theorem fourWallFiber_nonempty_iff (dU dV nU nV : ℝ) :
    (fourWallFiber dU dV nU nV).Nonempty ↔
      0 ≤ signedFiberLength dU dV nU nV := by
  rw [fourWallFiber_eq_Icc]
  constructor
  · rintro ⟨y, hy⟩
    change max dV nU ≤ y ∧ y ≤ 1 - max dU nV at hy
    unfold signedFiberLength
    linarith [hy.1, hy.2]
  · intro hLength
    refine ⟨max dV nU, ?_⟩
    change max dV nU ≤ max dV nU ∧ max dV nU ≤ 1 - max dU nV
    refine ⟨le_rfl, ?_⟩
    unfold signedFiberLength at hLength
    linarith

/-- A point in the four-wall fiber certifies nonnegative signed length. -/
theorem signedFiberLength_nonneg_of_mem (dU dV nU nV y : ℝ)
    (hy : y ∈ fourWallFiber dU dV nU nV) :
    0 ≤ signedFiberLength dU dV nU nV :=
  (fourWallFiber_nonempty_iff dU dV nU nV).mp ⟨y, hy⟩

/-! ## Pointwise partition defects -/

/-- The positive-part identity used in both parts of ED.2. -/
theorem max_sub_left_eq_max_sub_zero (a b : ℝ) :
    max a b - a = max (b - a) 0 := by
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab, max_eq_left (sub_nonneg.mpr hab)]
  · rw [max_eq_left hba, max_eq_right (sub_nonpos.mpr hba), sub_self]

/-- The same positive-part identity with the second argument subtracted. -/
theorem max_sub_right_eq_max_sub_zero (a b : ℝ) :
    max a b - b = max (a - b) 0 := by
  rw [max_comm a b]
  exact max_sub_left_eq_max_sub_zero b a

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
  unfold signedFiberLength middlePartitionDefect
  have hV := max_sub_right_eq_max_sub_zero dV nU
  have hU := max_sub_right_eq_max_sub_zero dU nV
  linarith

/-- The exterior comparison is an exact identity, even for negative signed fibers. -/
theorem exterior_partition_defect_identity (dU dV nU nV : ℝ) :
    (1 - dU - dV) - signedFiberLength dU dV nU nV =
      exteriorPartitionDefect dU dV nU nV := by
  unfold signedFiberLength exteriorPartitionDefect
  have hV := max_sub_left_eq_max_sub_zero dV nU
  have hU := max_sub_left_eq_max_sub_zero dU nV
  linarith

theorem middlePartitionDefect_nonneg (dU dV nU nV : ℝ) :
    0 ≤ middlePartitionDefect dU dV nU nV := by
  unfold middlePartitionDefect
  exact add_nonneg (le_max_right (dV - nU) 0) (le_max_right (dU - nV) 0)

theorem exteriorPartitionDefect_nonneg (dU dV nU nV : ℝ) :
    0 ≤ exteriorPartitionDefect dU dV nU nV := by
  unfold exteriorPartitionDefect
  exact add_nonneg (le_max_right (nU - dV) 0) (le_max_right (nV - dU) 0)

/-- The exact middle equality conditions in ED.6. -/
theorem middlePartitionDefect_eq_zero_iff (dU dV nU nV : ℝ) :
    middlePartitionDefect dU dV nU nV = 0 ↔ dV ≤ nU ∧ dU ≤ nV := by
  unfold middlePartitionDefect
  constructor
  · intro hZero
    have hV0 : 0 ≤ max (dV - nU) 0 := le_max_right (dV - nU) 0
    have hU0 : 0 ≤ max (dU - nV) 0 := le_max_right (dU - nV) 0
    have hV : dV - nU ≤ max (dV - nU) 0 := le_max_left (dV - nU) 0
    have hU : dU - nV ≤ max (dU - nV) 0 := le_max_left (dU - nV) 0
    constructor <;> linarith
  · rintro ⟨hV, hU⟩
    rw [max_eq_right (sub_nonpos.mpr hV),
      max_eq_right (sub_nonpos.mpr hU), add_zero]

/-- The exact exterior equality conditions in ED.6. -/
theorem exteriorPartitionDefect_eq_zero_iff (dU dV nU nV : ℝ) :
    exteriorPartitionDefect dU dV nU nV = 0 ↔ nU ≤ dV ∧ nV ≤ dU := by
  unfold exteriorPartitionDefect
  constructor
  · intro hZero
    have hV0 : 0 ≤ max (nU - dV) 0 := le_max_right (nU - dV) 0
    have hU0 : 0 ≤ max (nV - dU) 0 := le_max_right (nV - dU) 0
    have hV : nU - dV ≤ max (nU - dV) 0 := le_max_left (nU - dV) 0
    have hU : nV - dU ≤ max (nV - dU) 0 := le_max_left (nV - dU) 0
    constructor <;> linarith
  · rintro ⟨hV, hU⟩
    rw [max_eq_right (sub_nonpos.mpr hV),
      max_eq_right (sub_nonpos.mpr hU), add_zero]

/-- Dropping the middle partition defect gives the corresponding pointwise bound. -/
theorem signedFiberLength_le_middle (dU dV nU nV : ℝ) :
    signedFiberLength dU dV nU nV ≤ 1 - nU - nV := by
  have hIdentity := middle_partition_defect_identity dU dV nU nV
  have hNonneg := middlePartitionDefect_nonneg dU dV nU nV
  linarith

/-- Dropping the exterior partition defect gives the corresponding pointwise bound. -/
theorem signedFiberLength_le_exterior (dU dV nU nV : ℝ) :
    signedFiberLength dU dV nU nV ≤ 1 - dU - dV := by
  have hIdentity := exterior_partition_defect_identity dU dV nU nV
  have hNonneg := exteriorPartitionDefect_nonneg dU dV nU nV
  linarith

/-! ## The four-term arithmetic deficit -/

/-- The unconditional arithmetic decomposition underlying ED.5.

All five parameters are real numbers. In particular, `area` and `envelope`
are not assertions that a geometric area has already been identified.
-/
theorem four_term_deficit_identity (M area envelope scoreU scoreV : ℝ) :
    M - area =
      (M / 2 - scoreU) + (M / 2 - scoreV) +
        (scoreU + scoreV - envelope) + (envelope - area) := by
  ring

/-- Substitute explicitly identified partition and filling defects into the decomposition. -/
theorem four_term_deficit_of_eq
    (M area envelope scoreU scoreV partitionDefect fillDefect : ℝ)
    (hPartition : scoreU + scoreV - envelope = partitionDefect)
    (hFill : envelope - area = fillDefect) :
    M - area =
      (M / 2 - scoreU) + (M / 2 - scoreV) + partitionDefect + fillDefect := by
  have hIdentity := four_term_deficit_identity M area envelope scoreU scoreV
  linarith

/-- Explicit bounds and nonnegative defects imply the corresponding arithmetic upper bound. -/
theorem area_le_of_deficit_bounds
    (M area envelope scoreU scoreV partitionDefect fillDefect : ℝ)
    (hPartition : scoreU + scoreV - envelope = partitionDefect)
    (hFill : envelope - area = fillDefect)
    (hScoreU : scoreU ≤ M / 2)
    (hScoreV : scoreV ≤ M / 2)
    (hPartitionNonneg : 0 ≤ partitionDefect)
    (hFillNonneg : 0 ≤ fillDefect) :
    area ≤ M := by
  have hIdentity := four_term_deficit_of_eq
    M area envelope scoreU scoreV partitionDefect fillDefect hPartition hFill
  linarith

/-- Under explicit deficit bounds, equality holds exactly when all four terms vanish.

This is an algebraic equality criterion. Applying it to original bodies still
requires the geometric identifications and cap bounds stated as hypotheses here.
-/
theorem area_eq_iff_deficits_vanish
    (M area envelope scoreU scoreV partitionDefect fillDefect : ℝ)
    (hPartition : scoreU + scoreV - envelope = partitionDefect)
    (hFill : envelope - area = fillDefect)
    (hScoreU : scoreU ≤ M / 2)
    (hScoreV : scoreV ≤ M / 2)
    (hPartitionNonneg : 0 ≤ partitionDefect)
    (hFillNonneg : 0 ≤ fillDefect) :
    area = M ↔
      scoreU = M / 2 ∧ scoreV = M / 2 ∧ partitionDefect = 0 ∧ fillDefect = 0 := by
  have hIdentity := four_term_deficit_of_eq
    M area envelope scoreU scoreV partitionDefect fillDefect hPartition hFill
  constructor
  · intro hArea
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨hU, hV, hPartitionZero, hFillZero⟩
    linarith

/-! ## The pointwise extrusion deficit -/

/-- The exact truncation identity used to reverse vertical extrusion.

The identity is valid for arbitrary real `n` and `ε`; no positivity
assumptions are needed for this algebraic step.
-/
theorem extrusion_truncation_identity (n ε : ℝ) :
    ε + max (n - ε) 0 - n = max (ε - n) 0 := by
  rcases le_total n ε with hnε | hεn
  · rw [max_eq_right (sub_nonpos.mpr hnε),
      max_eq_left (sub_nonneg.mpr hnε), add_zero]
  · rw [max_eq_left (sub_nonneg.mpr hεn),
      max_eq_right (sub_nonpos.mpr hεn)]
    ring

theorem extrusion_truncation_nonneg (n ε : ℝ) :
    0 ≤ ε + max (n - ε) 0 - n := by
  rw [extrusion_truncation_identity]
  exact le_max_right (ε - n) 0

/-- The pointwise extrusion deficit vanishes exactly when the shift is at most `n`. -/
theorem extrusion_truncation_eq_zero_iff (n ε : ℝ) :
    ε + max (n - ε) 0 - n = 0 ↔ ε ≤ n := by
  rw [extrusion_truncation_identity]
  constructor
  · intro hZero
    have hBound : ε - n ≤ max (ε - n) 0 := le_max_left (ε - n) 0
    linarith
  · intro hεn
    exact max_eq_right (sub_nonpos.mpr hεn)

/-- The pointwise extrusion deficit is strictly positive exactly below the shift. -/
theorem extrusion_truncation_pos_iff (n ε : ℝ) :
    0 < ε + max (n - ε) 0 - n ↔ n < ε := by
  rw [extrusion_truncation_identity]
  constructor
  · intro hPositive
    by_contra hNot
    have hεn : ε ≤ n := le_of_not_gt hNot
    have hZero : max (ε - n) 0 = 0 := max_eq_right (sub_nonpos.mpr hεn)
    linarith
  · intro hnε
    have hBound : ε - n ≤ max (ε - n) 0 := le_max_left (ε - n) 0
    linarith

end AmbidextrousSofa
