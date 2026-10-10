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

theorem measurable_roofDeficit {K : Set Plane} (hK : IsCompact K)
    (hK0 : ∀ p ∈ K, 0 ≤ p.2) : Measurable (roofDeficit K) :=
  measurable_const.sub (measurable_capRoof hK hK0)

theorem IsDownwardCap.measurable_roofDeficit {U : Set Plane} (hU : IsDownwardCap U) :
    Measurable (roofDeficit U) :=
  measurable_const.sub hU.measurable_capRoof

theorem IsDownwardCap.capWidth_nonneg {U : Set Plane} (hU : IsDownwardCap U) :
    0 ≤ capWidth U :=
  sub_nonneg.mpr (horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact)

/-- The score is an ordinary exterior roof integral minus a middle barrier integral. -/
theorem capScore_eq_integrals (U : Set Plane) (α : ℝ) :
    capScore U α =
      (∫ x in Icc (horizontalLeft U) (horizontalRight U) \
          middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x) -
        ∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U), partialBarrier U α x := by
  unfold capScore spatialScore roofDeficit
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun _ => by ring)

/-- At a full quarter-turn the retained terminal wall has already been proved
redundant for a downward cap; the score therefore uses the whole swept niche. -/
theorem IsDownwardCap.capScore_pi_div_two {U : Set Plane} (hU : IsDownwardCap U) :
    capScore U (Real.pi / 2) =
      (∫ x in Icc (horizontalLeft U) (horizontalRight U) \
          middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x) -
        ∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U),
          sweptNiche U (Real.pi / 2) x := by
  rw [capScore_eq_integrals]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => hU.partialBarrier_pi_div_two x)

/-- The elementary scalar branch. It holds for every real `α`: the roof is
at most one and the barrier is nonnegative. For meaningful passage angles,
the separate barrier analysis also guarantees both integrals are integrable. -/
theorem IsDownwardCap.capScore_le_half_width {U : Set Plane}
    (hU : IsDownwardCap U) (α : ℝ) : capScore U α ≤ capWidth U / 2 := by
  let I := Icc (horizontalLeft U) (horizontalRight U)
  let J := middleHalfInterval (horizontalLeft U) (horizontalRight U)
  have hRoof : IntegrableOn (capRoof U) (I \ J) :=
    (hU.integrableOn_capRoof_Icc (horizontalLeft U) (horizontalRight U)).mono_set sdiff_subset
  have hOneI : IntegrableOn (fun _ : ℝ => (1 : ℝ)) I :=
    integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hOne : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (I \ J) := hOneI.mono_set sdiff_subset
  have hRoofBound : (∫ x in I \ J, capRoof U x) ≤ ∫ _x in I \ J, (1 : ℝ) :=
    integral_mono hRoof hOne (fun x => capRoof_le_one hU.isCompact hU.inStrip x)
  have hBarrierNonneg : 0 ≤ ∫ x in J, partialBarrier U α x :=
    integral_nonneg (fun x => partialBarrier_nonneg U α x)
  have hExteriorMeasure : volume.real (I \ J) = capWidth U / 2 :=
    volumeReal_exterior_middleHalfInterval
      (horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact)
  have hOneIntegral : (∫ _x in I \ J, (1 : ℝ)) = capWidth U / 2 := by
    rw [setIntegral_const, smul_eq_mul, mul_one, hExteriorMeasure]
  rw [capScore_eq_integrals]
  change (∫ x in I \ J, capRoof U x) - (∫ x in J, partialBarrier U α x) ≤ capWidth U / 2
  linarith

/-- A scalar competitor at the reference value must survive the width cutoff. -/
theorem IsDownwardCap.width_ge_M_of_capScore_ge_half_M {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hScore : M / 2 ≤ capScore U α) :
    M ≤ capWidth U := by
  have hBound := hU.capScore_le_half_width α
  linarith

end AmbidextrousSofa
