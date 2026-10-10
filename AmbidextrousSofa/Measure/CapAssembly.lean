import AmbidextrousSofa.Geometry.AngularDomain
import AmbidextrousSofa.Measure.CapScore

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
def bodyProjectionInterval (S : Set Plane) : Set ℝ :=
  Icc (horizontalLeft S) (horizontalRight S)

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

theorem actualPartitionDefect_nonneg (S : Set Plane) (α γ : ℝ) :
    0 ≤ actualPartitionDefect S α γ :=
  integratedPartitionDefect_nonneg _ _ _ _ _ _

theorem bodyProjectionInterval_eq_projection {S : Set Plane} (hS : IsCompact S)
    (hconn : IsConnected S) : bodyProjectionInterval S = horizontalProjection S :=
  (horizontalProjection_eq_Icc_of_isConnected hS hconn).symm

/-- Both caps use exactly the original left and right endpoints. -/
theorem hullCaps_endpoints_eq_original {S : Set Plane} (hS : IsCompact S)
    (hconn : IsConnected S) (hstrip : S ⊆ unitStrip) :
    horizontalLeft (upperHullCap S) = horizontalLeft S ∧
      horizontalRight (upperHullCap S) = horizontalRight S ∧
      horizontalLeft (reflectedHullCap S) = horizontalLeft S ∧
      horizontalRight (reflectedHullCap S) = horizontalRight S := by
  have hproj := hullCaps_horizontalProjection_eq_original hS hconn hstrip
  exact ⟨congrArg sInf hproj.1, congrArg sSup hproj.1,
    congrArg sInf hproj.2, congrArg sSup hproj.2⟩

/-- Geometric containment in the actual four-wall envelope. -/
theorem subset_actualCapEnvelope {S : Set Plane} (hS : IsCompact S)
    (hconn : IsConnected S) (hstrip : S ⊆ unitStrip) {α γ : ℝ}
    (hU : AngularConstraints S (upperHullCap S) α)
    (hV : AngularConstraints (reflect '' S) (reflectedHullCap S) γ) :
    S ⊆ actualCapEnvelope S α γ := by
  intro p hp
  have hroof := originalPoint_roof_bounds hS hstrip hp
  have hlower := hU.partialBarrier_le hstrip hp
  have hupper := hV.partialBarrier_le (image_reflect_subset_unitStrip hstrip)
    (mem_image_of_mem reflect hp)
  change partialBarrier (reflectedHullCap S) γ p.1 ≤ 1 - p.2 at hupper
  change p.1 ∈ bodyProjectionInterval S ∧
    p.2 ∈ fourWallFiber (roofDeficit (upperHullCap S) p.1)
      (roofDeficit (reflectedHullCap S) p.1)
      (partialBarrier (upperHullCap S) α p.1)
      (partialBarrier (reflectedHullCap S) γ p.1)
  constructor
  · rw [bodyProjectionInterval_eq_projection hS hconn]
    exact mem_image_of_mem Prod.fst hp
  · change (1 - capRoof (reflectedHullCap S) p.1 ≤ p.2 ∧
      partialBarrier (upperHullCap S) α p.1 ≤ p.2 ∧
      p.2 ≤ 1 - (1 - capRoof (upperHullCap S) p.1) ∧
      p.2 ≤ 1 - partialBarrier (reflectedHullCap S) γ p.1)
    exact ⟨hroof.1, hlower, by linarith [hroof.2], by linarith⟩

/-- Connectedness supplies a genuine original point at every fiber, hence nonnegative signed length. -/
theorem actual_signedFiberLength_nonneg {S : Set Plane} (hS : IsCompact S)
    (hconn : IsConnected S) (hstrip : S ⊆ unitStrip) {α γ : ℝ}
    (hU : AngularConstraints S (upperHullCap S) α)
    (hV : AngularConstraints (reflect '' S) (reflectedHullCap S) γ) :
    ∀ x ∈ bodyProjectionInterval S,
      0 ≤ signedFiberLength (roofDeficit (upperHullCap S) x)
        (roofDeficit (reflectedHullCap S) x)
        (partialBarrier (upperHullCap S) α x) (partialBarrier (reflectedHullCap S) γ x) := by
  apply signedFiberLength_nonneg_on_of_subset_projection (subset_actualCapEnvelope hS hconn hstrip hU hV)
  rw [bodyProjectionInterval_eq_projection hS hconn]
  exact Subset.rfl

/-- The actual compact connected body is bounded by its two genuine cap scores.
All regularity and integration hypotheses are discharged here. -/
theorem volumeReal_le_actual_capScore_sum {S : Set Plane} (hS : IsCompact S)
    (hconn : IsConnected S) (hstrip : S ⊆ unitStrip) {α γ : ℝ}
    (hU : AngularConstraints S (upperHullCap S) α)
    (hV : AngularConstraints (reflect '' S) (reflectedHullCap S) γ) :
    volume.real S ≤ capScore (upperHullCap S) α + capScore (reflectedHullCap S) γ := by
  have hcapU := isDownwardCap_upperHullCap hconn.nonempty hS hstrip
  have hcapV := isDownwardCap_reflectedHullCap hconn.nonempty hS hstrip
  have hlr := horizontalLeft_le_horizontalRight hconn.nonempty hS
  have hsub := subset_actualCapEnvelope hS hconn hstrip hU hV
  have hprojection : bodyProjectionInterval S ⊆ Prod.fst '' S := by
    rw [bodyProjectionInterval_eq_projection hS hconn]
    exact Subset.rfl
  have harea := volumeReal_le_spatialScore_sum_middleHalf hlr hsub
    hcapU.measurable_roofDeficit hcapV.measurable_roofDeficit
    (measurable_partialBarrier hcapU.isCompact hU.angle_pos hU.angle_le)
    (measurable_partialBarrier hcapV.isCompact hV.angle_pos hV.angle_le)
    (hcapU.integrableOn_roofDeficit_Icc (horizontalLeft S) (horizontalRight S))
    (hcapV.integrableOn_roofDeficit_Icc (horizontalLeft S) (horizontalRight S))
    (integrableOn_partialBarrier_Icc hcapU.isCompact hU.angle_pos hU.angle_le
      (horizontalLeft S) (horizontalRight S))
    (integrableOn_partialBarrier_Icc hcapV.isCompact hV.angle_pos hV.angle_le
      (horizontalLeft S) (horizontalRight S)) hprojection
  obtain ⟨hUL, hUR, hVL, hVR⟩ := hullCaps_endpoints_eq_original hS hconn hstrip
  simpa only [capScore, hUL, hUR, hVL, hVR] using harea

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
  have hnonneg : ∀ᵐ x ∂volume.restrict (bodyProjectionInterval S),
      0 ≤ signedFiberLength (roofDeficit (upperHullCap S) x)
        (roofDeficit (reflectedHullCap S) x)
        (partialBarrier (upperHullCap S) α x) (partialBarrier (reflectedHullCap S) γ x) := by
    filter_upwards [ae_restrict_mem (show MeasurableSet (bodyProjectionInterval S) from
      measurableSet_Icc)] with x hx
    exact actual_signedFiberLength_nonneg hS hconn hstrip hU hV x hx
  have hidentity := actualBody_four_term_deficit_identity C
    (subset_actualCapEnvelope hS hconn hstrip hU hV) hS.measurableSet measurableSet_Icc
    (measurableSet_middleHalfInterval (horizontalLeft S) (horizontalRight S))
    (middleHalfInterval_subset hlr)
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    (middleHalfInterval_measure_balance hlr)
    hcapU.measurable_roofDeficit hcapV.measurable_roofDeficit
    (measurable_partialBarrier hcapU.isCompact hU.angle_pos hU.angle_le)
    (measurable_partialBarrier hcapV.isCompact hV.angle_pos hV.angle_le)
    (hcapU.integrableOn_roofDeficit_Icc (horizontalLeft S) (horizontalRight S))
    (hcapV.integrableOn_roofDeficit_Icc (horizontalLeft S) (horizontalRight S))
    (integrableOn_partialBarrier_Icc hcapU.isCompact hU.angle_pos hU.angle_le
      (horizontalLeft S) (horizontalRight S))
    (integrableOn_partialBarrier_Icc hcapV.isCompact hV.angle_pos hV.angle_le
      (horizontalLeft S) (horizontalRight S)) hnonneg
  obtain ⟨hUL, hUR, hVL, hVR⟩ := hullCaps_endpoints_eq_original hS hconn hstrip
  simpa only [capScore, actualPartitionDefect, actualCapEnvelope,
    bodyProjectionInterval, bodyMiddleInterval, hUL, hUR, hVL, hVR] using hidentity

/-! ## Supplying the constraints from independent genuine passages -/

/-- Two genuine, independently parametrized terminal passages produce the two actual cap constraints.
The endpoint angles are independent; neither path is required to be monotone. -/
theorem hullCap_constraints_of_terminal_passages {S : Set Plane}
    (hS : IsCompact S) (hne : S.Nonempty) (hstrip : S ⊆ unitStrip)
    {lower upper : RigidMotionPath}
    (hlower : Passage S lowerHall incomingArm lowerOutgoingArm lower)
    (hupper : Passage S upperHall incomingArm upperOutgoingArm upper)
    (hlower0 : lower.angle 0 = 0) (hupper0 : upper.angle 0 = 0)
    {α γ : ℝ} (hlower1 : -lower.angle 1 = α) (hupper1 : upper.angle 1 = γ)
    (hα0 : 0 < α) (hαL : α ≤ Real.pi / 2)
    (hγ0 : 0 < γ) (hγL : γ ≤ Real.pi / 2) :
    AngularConstraints S (upperHullCap S) α ∧
      AngularConstraints (reflect '' S) (reflectedHullCap S) γ := by
  have hKh := isCompact_actualHull hS
  have hKn := actualHull_nonempty hne
  have hKstrip := actualHull_subset_unitStrip hstrip
  have hU := (hlower.angularConstraints_of_terminal hS hne hlower0 hlower1 hα0 hαL).upperCap
    hKh hKn (fun p hp => (hKstrip hp).1)
  have hSh := isCompact_image_reflect hS
  have hSn := hne.image reflect
  have hSstrip := image_reflect_subset_unitStrip hstrip
  have hupperRef0 : upper.reflected.angle 0 = 0 := by
    simp only [RigidMotionPath.reflected, hupper0, neg_zero]
  have hupperRef1 : -upper.reflected.angle 1 = γ := by
    simpa only [RigidMotionPath.reflected, neg_neg] using hupper1
  have hV := (hupper.reflected.angularConstraints_of_terminal hSh hSn
    hupperRef0 hupperRef1 hγ0 hγL).upperCap
    (isCompact_actualHull hSh) (actualHull_nonempty hSn)
    (fun p hp => (actualHull_subset_unitStrip hSstrip hp).1)
  exact ⟨hU, by simpa only [reflectedHullCap, actualHull_reflect] using hV⟩

/-- An end-to-end area inequality for normalized genuine terminal passages in the stated angle range.
The remaining reach dichotomy is not added as an implicit premise of `IsAmbidextrous`. -/
theorem volumeReal_le_capScore_sum_of_terminal_passages {S : Set Plane}
    (hS : IsCompact S) (hconn : IsConnected S) (hstrip : S ⊆ unitStrip)
    {lower upper : RigidMotionPath}
    (hlower : Passage S lowerHall incomingArm lowerOutgoingArm lower)
    (hupper : Passage S upperHall incomingArm upperOutgoingArm upper)
    (hlower0 : lower.angle 0 = 0) (hupper0 : upper.angle 0 = 0)
    {α γ : ℝ} (hlower1 : -lower.angle 1 = α) (hupper1 : upper.angle 1 = γ)
    (hα0 : 0 < α) (hαL : α ≤ Real.pi / 2)
    (hγ0 : 0 < γ) (hγL : γ ≤ Real.pi / 2) :
    volume.real S ≤ capScore (upperHullCap S) α + capScore (reflectedHullCap S) γ := by
  have hconstraints := hullCap_constraints_of_terminal_passages hS hconn.nonempty hstrip
    hlower hupper hlower0 hupper0 hlower1 hupper1 hα0 hαL hγ0 hγL
  exact volumeReal_le_actual_capScore_sum hS hconn hstrip hconstraints.1 hconstraints.2

end AmbidextrousSofa
