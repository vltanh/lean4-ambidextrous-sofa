module

public import AmbidextrousSofa.Geometry.BarrierAnalysis
public import AmbidextrousSofa.Measure.Partition
public import AmbidextrousSofa.ExactConstant

@[expose] public section

/-!
# Actual cap scores and the elementary width branch

The scalar score is now instantiated with the actual cap roof, its actual
horizontal projection endpoints, and the full partial barrier including the
terminal wall. All those functions have the measurability and integrability
properties established in the preceding modules.

This file proves the elementary bound `capScore U α ≤ capWidth U / 2`.
It uses only the cap's height at most one and the barrier's nonnegativity.
Consequently widths strictly below `M` are a strictly suboptimal scalar
branch. No universal bound for larger widths is assumed or claimed.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

/-- The deficit of the zero-extended actual cap roof from the strip height. -/
def roofDeficit (U : Set Plane) (x : ℝ) : ℝ := 1 - capRoof U x

/-- The width of the actual horizontal projection. -/
def capWidth (U : Set Plane) : ℝ := horizontalRight U - horizontalLeft U

/-- The scalar spatial score, with the body's own projection window and
its entire partial barrier. -/
def capScore (U : Set Plane) (α : ℝ) : ℝ :=
  spatialScore (Icc (horizontalLeft U) (horizontalRight U))
    (middleHalfInterval (horizontalLeft U) (horizontalRight U))
    (roofDeficit U) (partialBarrier U α)

theorem IsDownwardCap.measurable_roofDeficit {U : Set Plane} (hU : IsDownwardCap U) :
    Measurable (roofDeficit U) :=
  measurable_const.sub hU.measurable_capRoof

theorem IsDownwardCap.capWidth_nonneg {U : Set Plane} (hU : IsDownwardCap U) : 0 ≤ capWidth U :=
  sub_nonneg.mpr (horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact)

/-- The quarter points and the middle half of a centered horizontal projection `[-2C, 2C]`. -/
theorem centered_quarter_points {U : Set Plane} {C : ℝ} (hl : horizontalLeft U = -2 * C)
    (hr : horizontalRight U = 2 * C) :
    horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4 = -C ∧
      horizontalRight U - (horizontalRight U - horizontalLeft U) / 4 = C ∧
      middleHalfInterval (horizontalLeft U) (horizontalRight U) = Icc (-C) C := by
  rw [middleHalfInterval, hl, hr]
  exact ⟨by ring, by ring, by congr 1 <;> ring⟩

/-- The score is an ordinary exterior roof integral minus a middle barrier integral. -/
theorem capScore_eq_integrals (U : Set Plane) (α : ℝ) :
    capScore U α =
      (∫ x in Icc (horizontalLeft U) (horizontalRight U) \
          middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x) -
        ∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U), partialBarrier U α x := by
  simp only [capScore, spatialScore, roofDeficit, sub_sub_cancel]

/-- At a full quarter-turn the retained terminal wall has already been proved
redundant for a downward cap; the score therefore uses the whole swept niche. -/
theorem IsDownwardCap.capScore_pi_div_two {U : Set Plane} (hU : IsDownwardCap U) :
    capScore U (Real.pi / 2) =
      (∫ x in Icc (horizontalLeft U) (horizontalRight U) \
          middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x) -
        ∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U),
          sweptNiche U (Real.pi / 2) x := by
  simp only [capScore_eq_integrals, hU.partialBarrier_pi_div_two]

/-- The elementary scalar branch. It holds for every real `α`: the roof is
at most one and the barrier is nonnegative. For meaningful passage angles,
the separate barrier analysis also guarantees both integrals are integrable. -/
theorem IsDownwardCap.capScore_le_half_width {U : Set Plane}
    (hU : IsDownwardCap U) (α : ℝ) : capScore U α ≤ capWidth U / 2 := by
  rw [capScore_eq_integrals, sub_le_iff_le_add]
  calc _ ≤ ∫ _ in Icc (horizontalLeft U) (horizontalRight U) \
          middleHalfInterval (horizontalLeft U) (horizontalRight U), (1 : ℝ) :=
        setIntegral_mono_on ((hU.integrableOn_capRoof_Icc _ _).mono_set sdiff_subset)
          ((integrableOn_const measure_Icc_lt_top.ne).mono_set sdiff_subset)
          (measurableSet_Icc.diff (measurableSet_middleHalfInterval _ _))
          fun x _ => capRoof_le_one hU.isCompact hU.inStrip x
    _ = capWidth U / 2 := by
        rw [setIntegral_const, smul_eq_mul, mul_one, volumeReal_exterior_middleHalfInterval
          (horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact), capWidth]
    _ ≤ _ := le_add_of_nonneg_right (integral_nonneg (partialBarrier_nonneg U α))

/-- A scalar competitor at the reference value must survive the width cutoff. -/
theorem IsDownwardCap.width_ge_M_of_capScore_ge_half_M {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hScore : M / 2 ≤ capScore U α) : M ≤ capWidth U := by
  linarith [hU.capScore_le_half_width α]

end AmbidextrousSofa
