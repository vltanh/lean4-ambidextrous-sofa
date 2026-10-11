module

public import AmbidextrousSofa.Geometry.AngularDomain
public import AmbidextrousSofa.Measure.CapScore

@[expose] public section

/-!
# The actual two-cap area inequality and exact deficit

Both caps are constructed from the original compact connected body. Its
connected projection gives a physical point in every horizontal fiber, which
justifies replacing positive-part fiber length by signed fiber length. Roof
and barrier measurability, integrability, and the common middle-half domain
are supplied by the preceding geometric results.

The main area inequality bounds the actual body by its two actual cap scores.
The exact deficit separates the two scalar score deficits, the partition
defect, and the area missing from the physical envelope. No sharp scalar cap
bound is assumed in either theorem. Establishing those bounds on the full cap
domain remains a later task.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

/-- The interval is defined from the original body's own projection endpoints. -/
def bodyProjectionInterval (S : Set Plane) : Set ℝ := Icc (horizontalLeft S) (horizontalRight S)

def bodyMiddleInterval (S : Set Plane) : Set ℝ :=
  middleHalfInterval (horizontalLeft S) (horizontalRight S)

/-- The physical envelope defined by both actual hull caps and both whole-angle barriers. -/
def actualCapEnvelope (S : Set Plane) (α γ : ℝ) : Set Plane :=
  fourWallEnvelope (bodyProjectionInterval S)
    (roofDeficit (upperHullCap S)) (roofDeficit (reflectedHullCap S))
    (partialBarrier (upperHullCap S) α) (partialBarrier (reflectedHullCap S) γ)

/-- The exact integrated partition loss for the actual pair of caps. -/
def actualPartitionDefect (S : Set Plane) (α γ : ℝ) : ℝ :=
  integratedPartitionDefect (bodyProjectionInterval S) (bodyMiddleInterval S)
    (roofDeficit (upperHullCap S)) (roofDeficit (reflectedHullCap S))
    (partialBarrier (upperHullCap S) α) (partialBarrier (reflectedHullCap S) γ)

theorem actualPartitionDefect_nonneg (S : Set Plane) (α γ : ℝ) : 0 ≤ actualPartitionDefect S α γ :=
  integratedPartitionDefect_nonneg _ _ _ _ _ _

theorem bodyProjectionInterval_eq_projection {S : Set Plane} (hS : IsCompact S)
    (hconn : IsConnected S) : bodyProjectionInterval S = horizontalProjection S :=
  (horizontalProjection_eq_Icc_of_isConnected hS hconn).symm

/-- Geometric containment in the actual four-wall envelope. -/
theorem subset_actualCapEnvelope {S : Set Plane} (hS : IsCompact S)
    (hconn : IsConnected S) (hstrip : S ⊆ unitStrip) {α γ : ℝ}
    (hU : AngularConstraints S (upperHullCap S) α)
    (hV : AngularConstraints (reflect '' S) (reflectedHullCap S) γ) :
    S ⊆ actualCapEnvelope S α γ := fun p hp => by
  have hroof := originalPoint_roof_bounds hS hstrip hp
  have hupper : partialBarrier (reflectedHullCap S) γ p.1 ≤ 1 - p.2 :=
    hV.partialBarrier_le (image_reflect_subset_unitStrip hstrip) (mem_image_of_mem reflect hp)
  exact ⟨bodyProjectionInterval_eq_projection hS hconn ▸ mem_image_of_mem Prod.fst hp, hroof.1,
    hU.partialBarrier_le hstrip hp, by unfold roofDeficit; linarith [hroof.2], by linarith⟩

/-- ED.5 instantiated by the original hull caps, their actual barriers, and ordinary missing area.
The identity is valid for every comparison constant; it does not claim scalar optimality. -/
theorem actual_cap_four_term_deficit (C : ℝ) {S : Set Plane} (hS : IsCompact S)
    (hconn : IsConnected S) (hstrip : S ⊆ unitStrip) {α γ : ℝ}
    (hU : AngularConstraints S (upperHullCap S) α)
    (hV : AngularConstraints (reflect '' S) (reflectedHullCap S) γ) :
    C - volume.real S = (C / 2 - capScore (upperHullCap S) α) +
      (C / 2 - capScore (reflectedHullCap S) γ) + actualPartitionDefect S α γ +
        volume.real (actualCapEnvelope S α γ \ S) := by
  have hcapU := isDownwardCap_upperHullCap hconn.nonempty hS hstrip
  have hcapV := isDownwardCap_reflectedHullCap hconn.nonempty hS hstrip
  have hlr := horizontalLeft_le_horizontalRight hconn.nonempty hS
  have hsub := subset_actualCapEnvelope hS hconn hstrip hU hV
  have hidentity := actualBody_four_term_deficit_identity C hsub hS.measurableSet
    measurableSet_Icc (measurableSet_middleHalfInterval _ _) (middleHalfInterval_subset hlr)
    measure_Icc_lt_top.ne (middleHalfInterval_measure_balance hlr)
    hcapU.measurable_roofDeficit hcapV.measurable_roofDeficit
    (measurable_partialBarrier hcapU.isCompact hU.angle_pos hU.angle_le)
    (measurable_partialBarrier hcapV.isCompact hV.angle_pos hV.angle_le)
    (hcapU.integrableOn_roofDeficit_Icc _ _) (hcapV.integrableOn_roofDeficit_Icc _ _)
    (integrableOn_partialBarrier_Icc hcapU.isCompact hU.angle_pos hU.angle_le _ _)
    (integrableOn_partialBarrier_Icc hcapV.isCompact hV.angle_pos hV.angle_le _ _)
    -- Connectedness supplies an original point in every fiber, hence nonnegative length.
    ((ae_restrict_mem measurableSet_Icc).mono (signedFiberLength_nonneg_on_of_subset_projection
      hsub (bodyProjectionInterval_eq_projection hS hconn).subset))
  -- Both caps use exactly the original left and right endpoints.
  obtain ⟨hU', hV'⟩ := hullCaps_horizontalProjection_eq_original hS hconn hstrip
  simpa only [capScore, actualPartitionDefect, actualCapEnvelope, bodyProjectionInterval,
    bodyMiddleInterval, horizontalLeft, horizontalRight, hU', hV'] using hidentity

/-- The actual compact connected body is bounded by its two genuine cap scores.
All regularity and integration hypotheses are discharged here. -/
theorem volumeReal_le_actual_capScore_sum {S : Set Plane} (hS : IsCompact S)
    (hconn : IsConnected S) (hstrip : S ⊆ unitStrip) {α γ : ℝ}
    (hU : AngularConstraints S (upperHullCap S) α)
    (hV : AngularConstraints (reflect '' S) (reflectedHullCap S) γ) :
    volume.real S ≤ capScore (upperHullCap S) α + capScore (reflectedHullCap S) γ := by
  have h := actual_cap_four_term_deficit 0 hS hconn hstrip hU hV
  have h0 := actualPartitionDefect_nonneg S α γ
  have h1 : 0 ≤ volume.real (actualCapEnvelope S α γ \ S) := measureReal_nonneg
  linarith

end AmbidextrousSofa
