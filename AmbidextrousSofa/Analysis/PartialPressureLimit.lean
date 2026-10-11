module

public import AmbidextrousSofa.Analysis.SelectedPressureLimit
public import AmbidextrousSofa.Analysis.PartialEndpointMoments

@[expose] public section

/-!
# Proper endpoint pressure limits

The literal rescaled finite barriers, with the whole terminal first wall,
converge uniformly. This identifies both moving endpoint pressures, and the
proper-angle selected polygons of a joint maximum form a selected limit.
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

namespace PartialGrid

open FinitePolygon AngularGrid

variable {α : TerminalAngle} {hαL : (α : ℝ) < Real.pi / 2}

def rightPressure (U : Set Plane) (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2)
    (grid : Finset QuarterAngle) : ℝ :=
  rightEndpointPressure (capRoof U)
    (finiteBarrier U (normal α grid) (pairList α grid) (some (terminalIndex α hαL grid)))
    (horizontalLeft U) (horizontalRight U)

def leftPressure (U : Set Plane) (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2)
    (grid : Finset QuarterAngle) : ℝ :=
  leftEndpointPressure (capRoof U)
    (finiteBarrier U (normal α grid) (pairList α grid) (some (terminalIndex α hαL grid)))
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

theorem rightPressure_tendsto (hwidth : horizontalLeft K < horizontalRight K) :
    Tendsto (fun n => rightPressure (U n) α hαL (dyadic (level n))) atTop
      (𝓝 (partialRightEndpointPressure K α)) :=
  (hHausdorff.endpointPressures_tendsto hU hK hbox
    (finiteBarrier_dyadic_tendsto (hαL := hαL) hHausdorff hU hK hlevel hbox) hwidth).1

theorem leftPressure_tendsto (hwidth : horizontalLeft K < horizontalRight K) :
    Tendsto (fun n => leftPressure (U n) α hαL (dyadic (level n))) atTop
      (𝓝 (partialLeftEndpointPressure K α)) :=
  (hHausdorff.endpointPressures_tendsto hU hK hbox
    (finiteBarrier_dyadic_tendsto (hαL := hαL) hHausdorff hU hK hlevel hbox) hwidth).2

end

/-- The proper-angle selected polygons form a selected limit. -/
theorem selectedLimit {target : Set Plane} {U : ℕ → Set Plane} {a b : ℝ} {level : ℕ → ℕ}
    {coefficient : ℕ → ℝ} (hTarget : IsDownwardCap target)
    (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target α hαL a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hwidth : 1 < capWidth target) :
    SelectedLimit (fun n => normal α (dyadic (level n))) (fun n => pairList α (dyadic (level n)))
      (fun n => some (terminalIndex α hαL (dyadic (level n))))
      (fun n i => coefficient n * stageWeight α (level n) i) target a b coefficient
      (partialBarrier target α) U :=
  ⟨fun n => (hU n).isSelected (hc n), hTarget, hTargetBox, hHausdorff, hrate, hwidth,
    finiteBarrier_dyadic_tendsto hHausdorff (fun n => (hU n).isCap) hTarget hlevel
      fun n => (hU n).inBox⟩

end PartialGrid

end AmbidextrousSofa
