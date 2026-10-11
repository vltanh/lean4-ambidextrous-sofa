module

public import AmbidextrousSofa.Analysis.SelectedPressureLimit
public import AmbidextrousSofa.Analysis.PartialEndpointMoments

@[expose] public section

/-!
# Proper endpoint pressure limits

Uniform convergence of the literal rescaled finite barriers identifies
both moving endpoint pressures. Actual finite inward/outward endpoint
variations determine the selected face-height limits without assuming
Hausdorff continuity of vertical face heights.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace AmbidextrousSofa

def partialRightEndpointPressure (U : Set Plane) (α : ℝ) : ℝ :=
  rightEndpointPressure (capRoof U) (partialBarrier U α)
    (horizontalLeft U) (horizontalRight U)

def partialLeftEndpointPressure (U : Set Plane) (α : ℝ) : ℝ :=
  leftEndpointPressure (capRoof U) (partialBarrier U α)
    (horizontalLeft U) (horizontalRight U)

theorem IsDownwardCap.partialEndpointPressure_sum_nonneg {U : Set Plane}
    (hU : IsDownwardCap U) (α : ℝ) : 0 ≤ partialRightEndpointPressure U α + partialLeftEndpointPressure U α := by
  have h x := add_nonneg (capRoof_nonneg hU.isCompact (fun p hp => (hU.inStrip hp).1) x)
    (partialBarrier_nonneg U α x)
  unfold partialRightEndpointPressure partialLeftEndpointPressure rightEndpointPressure
    leftEndpointPressure
  linarith [h (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4),
    h (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4)]

namespace PartialGrid

open FinitePolygon AngularGrid

variable {α : TerminalAngle} {hαL : (α : ℝ) < Real.pi / 2}

def rightPressure (U : Set Plane) (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2) (grid : Finset QuarterAngle) : ℝ :=
  rightEndpointPressure (capRoof U) (finiteBarrier U (normal α grid) (pairList α grid) (some (terminalIndex α hαL grid)))
    (horizontalLeft U) (horizontalRight U)

def leftPressure (U : Set Plane) (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2) (grid : Finset QuarterAngle) : ℝ :=
  leftEndpointPressure (capRoof U) (finiteBarrier U (normal α grid) (pairList α grid) (some (terminalIndex α hαL grid)))
    (horizontalLeft U) (horizontalRight U)

section

variable {U : ℕ → Set Plane} {K : Set Plane} (hHausdorff : CapHausdorffTendsto U K)
  (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K) {level : ℕ → ℕ}
  (hlevel : Tendsto level atTop atTop) {a b : ℝ} (hbox : ∀ n, U n ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
include hHausdorff hU hK hlevel hbox

/-- Rescaled dense sampling, changing caps, and moving sections converge
with the whole terminal wall retained. -/
theorem finiteBarrier_dyadic_tendsto {t : ℕ → ℝ} {x : ℝ} (htmem : ∀ n, t n ∈ Icc a b)
    (ht : Tendsto t atTop (𝓝 x)) :
    Tendsto (fun n => finiteBarrier (U n) (normal α (dyadic (level n)))
      (pairList α (dyadic (level n))) (some (terminalIndex α hαL (dyadic (level n)))) (t n)) atTop
      (𝓝 (partialBarrier K α x)) := by
  have huniform : TendstoUniformlyOn
      (fun n (p : (CompactCap × TerminalAngle) × ℝ) =>
        barrier p.1.1.carrier p.1.2 (dyadic (level n)) p.2)
      (fun p => partialBarrier p.1.1.carrier p.1.2 p.2) atTop
      ((boxedCaps (Icc a b ×ˢ Icc (0 : ℝ) 1) ×ˢ univ) ×ˢ Icc a b) := fun v hv =>
    hlevel.eventually (tendstoUniformlyOn_dyadic_box (isCompact_Icc.prod isCompact_Icc) a b v hv)
  simpa only [finiteBarrier_eq_barrier, IsDownwardCap.toCompactCap_carrier] using
    huniform.tendsto_comp continuous_partialCapBarrier.continuousAt.continuousWithinAt
      (tendsto_nhdsWithin_iff.mpr
        ⟨((IsDownwardCap.tendsto_toCompactCap hU hK hHausdorff).prodMk_nhds
          tendsto_const_nhds).prodMk_nhds ht, .of_forall fun n => ⟨⟨hbox n, mem_univ α⟩, htmem n⟩⟩)

/-- Both moving pressures converge. -/
private theorem pressure_tendsto (hwidth : horizontalLeft K < horizontalRight K) :
    Tendsto (fun n => rightPressure (U n) α hαL (dyadic (level n))) atTop
      (𝓝 (partialRightEndpointPressure K α)) ∧
    Tendsto (fun n => leftPressure (U n) α hαL (dyadic (level n))) atTop
      (𝓝 (partialLeftEndpointPressure K α)) := by
  have hl := hHausdorff.horizontalLeft_tendsto (fun n => (hU n).isCompact)
    (fun n => (hU n).nonempty) hK.isCompact hK.nonempty
  have hr := hHausdorff.horizontalRight_tendsto (fun n => (hU n).isCompact)
    (fun n => (hU n).nonempty) hK.isCompact hK.nonempty
  have hlr n := horizontalLeft_le_horizontalRight (hU n).nonempty (hU n).isCompact
  have hL := (hHausdorff.middleLeft_roof_tendsto hU hK hwidth).add
    (finiteBarrier_dyadic_tendsto (hαL := hαL) hHausdorff hU hK hlevel hbox
      (fun n => (hU n).projection_subset_Icc_of_box (hbox n)
        ⟨by linarith [hlr n], by linarith [hlr n]⟩) (hl.add ((hr.sub hl).div_const 4)))
  have hR := (hHausdorff.middleRight_roof_tendsto hU hK hwidth).add
    (finiteBarrier_dyadic_tendsto (hαL := hαL) hHausdorff hU hK hlevel hbox
      (fun n => (hU n).projection_subset_Icc_of_box (hbox n)
        ⟨by linarith [hlr n], by linarith [hlr n]⟩) (hr.sub ((hr.sub hl).div_const 4)))
  exact ⟨((hR.const_mul 3).sub hL).div_const 4, ((hL.const_mul 3).sub hR).div_const 4⟩

theorem rightPressure_tendsto (hwidth : horizontalLeft K < horizontalRight K) :
    Tendsto (fun n => rightPressure (U n) α hαL (dyadic (level n))) atTop
      (𝓝 (partialRightEndpointPressure K α)) :=
  (pressure_tendsto hHausdorff hU hK hlevel hbox hwidth).1

theorem leftPressure_tendsto (hwidth : horizontalLeft K < horizontalRight K) :
    Tendsto (fun n => leftPressure (U n) α hαL (dyadic (level n))) atTop
      (𝓝 (partialLeftEndpointPressure K α)) :=
  (pressure_tendsto hHausdorff hU hK hlevel hbox hwidth).2

end

variable {target : Set Plane} {U : ℕ → Set Plane} {a b : ℝ} {level : ℕ → ℕ}
  {coefficient : ℕ → ℝ} (hTarget : IsDownwardCap target)
  (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
  (hU : ∀ n, IsSelectedPolygon target α hαL a b (level n) (coefficient n) (U n))
  (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
  (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
  (hwidth : 1 < capWidth target)
include hTarget hTargetBox hU hHausdorff hlevel hc hrate hwidth

/-- Finite approximate complementarity determines the selected face-height
limit. No claim about continuity of the target face is used here. -/
theorem selected_right_height_tendsto (hslack : horizontalRight target < b) :
    Tendsto (fun n => capRoof (U n) (horizontalRight (U n))) atTop
      (𝓝 (max (partialRightEndpointPressure target α) 0)) := by
  have hcap n : IsDownwardCap (U n) := (hU n).isCap
  refine ((rightPressure_tendsto (hαL := hαL) hHausdorff hcap hTarget hlevel
    (fun n => (hU n).inBox) (by unfold capWidth at hwidth; linarith)).max
      tendsto_const_nhds).congr_dist (squeeze_zero' (.of_forall fun _ => dist_nonneg) ?_
        (endpointSelectionError_tendsto a b hrate))
  filter_upwards [(hHausdorff.capWidth_tendsto hcap hTarget).eventually (Ioi_mem_nhds hwidth),
    (hHausdorff.horizontalRight_tendsto (fun n => (hcap n).isCompact) (fun n => (hcap n).nonempty)
      hTarget.isCompact hTarget.nonempty).eventually (Iio_mem_nhds hslack)] with n hW hR
  rw [dist_comm, Real.dist_eq]
  exact (hU n).abs_right_complementarity_le hTarget hTargetBox (hc n) hW.le hR

theorem selected_left_height_tendsto (hslack : a < horizontalLeft target) :
    Tendsto (fun n => capRoof (U n) (horizontalLeft (U n))) atTop
      (𝓝 (max (partialLeftEndpointPressure target α) 0)) := by
  have hcap n : IsDownwardCap (U n) := (hU n).isCap
  refine ((leftPressure_tendsto (hαL := hαL) hHausdorff hcap hTarget hlevel
    (fun n => (hU n).inBox) (by unfold capWidth at hwidth; linarith)).max
      tendsto_const_nhds).congr_dist (squeeze_zero' (.of_forall fun _ => dist_nonneg) ?_
        (endpointSelectionError_tendsto a b hrate))
  filter_upwards [(hHausdorff.capWidth_tendsto hcap hTarget).eventually (Ioi_mem_nhds hwidth),
    (hHausdorff.horizontalLeft_tendsto (fun n => (hcap n).isCompact) (fun n => (hcap n).nonempty)
      hTarget.isCompact hTarget.nonempty).eventually (Ioi_mem_nhds hslack)] with n hW hL
  rw [dist_comm, Real.dist_eq]
  exact (hU n).abs_left_complementarity_le hTarget hTargetBox (hc n) hW.le hL

theorem right_complementarity_of_height_tendsto (hslack : horizontalRight target < b)
    (hface : Tendsto (fun n => capRoof (U n) (horizontalRight (U n))) atTop
      (𝓝 (capRoof target (horizontalRight target)))) :
    capRoof target (horizontalRight target) = max (partialRightEndpointPressure target α) 0 :=
  tendsto_nhds_unique hface (selected_right_height_tendsto hTarget hTargetBox hU
    hHausdorff hlevel hc hrate hwidth hslack)

theorem left_complementarity_of_height_tendsto (hslack : a < horizontalLeft target)
    (hface : Tendsto (fun n => capRoof (U n) (horizontalLeft (U n))) atTop
      (𝓝 (capRoof target (horizontalLeft target)))) :
    capRoof target (horizontalLeft target) = max (partialLeftEndpointPressure target α) 0 :=
  tendsto_nhds_unique hface (selected_left_height_tendsto hTarget hTargetBox hU
    hHausdorff hlevel hc hrate hwidth hslack)

end PartialGrid

end AmbidextrousSofa
