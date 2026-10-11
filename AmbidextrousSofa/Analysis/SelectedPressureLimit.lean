module

public import AmbidextrousSofa.Analysis.CapInteriorRoof
public import AmbidextrousSofa.Analysis.SelectedEndpointMoments
public import Mathlib.Topology.UniformSpace.UniformApproximation

@[expose] public section

/-!
# Moving pressure limits for actual selected polygons

The finite angular niches converge uniformly on the entire boxed cap
domain. Interior roof convergence therefore identifies both moving
pressure terms. Finite complementarity then gives an actual limit for
the selected endpoint heights, including when that limit is zero.

Identifying that height limit with the limiting cap's vertical face is a
separate geometric step: it requires control of curvature near the axis.
The final identification lemmas here state that input explicitly, rather
than treating endpoint heights as continuous under Hausdorff convergence.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace AmbidextrousSofa

def capRightEndpointPressure (U : Set Plane) : ℝ :=
  rightEndpointPressure (capRoof U) (sweptNiche U (Real.pi / 2))
    (horizontalLeft U) (horizontalRight U)

def capLeftEndpointPressure (U : Set Plane) : ℝ :=
  leftEndpointPressure (capRoof U) (sweptNiche U (Real.pi / 2))
    (horizontalLeft U) (horizontalRight U)

theorem capEndpointPressure_sum (U : Set Plane) :
    capRightEndpointPressure U + capLeftEndpointPressure U =
      ((capRoof U (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4) +
        sweptNiche U (Real.pi / 2)
          (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)) +
       (capRoof U (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) +
        sweptNiche U (Real.pi / 2)
          (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4))) / 2 := by
  unfold capRightEndpointPressure capLeftEndpointPressure rightEndpointPressure leftEndpointPressure
  ring

theorem IsDownwardCap.capEndpointPressure_sum_nonneg {U : Set Plane}
    (hU : IsDownwardCap U) : 0 ≤ capRightEndpointPressure U + capLeftEndpointPressure U := by
  have h x := add_nonneg (capRoof_nonneg hU.isCompact (fun p hp => (hU.inStrip hp).1) x)
    (sweptNiche_nonneg U (Real.pi / 2) x)
  rw [capEndpointPressure_sum]
  exact div_nonneg (add_nonneg (h _) (h _)) zero_le_two

theorem IsDownwardCap.projection_subset_Icc_of_box {U : Set Plane}
    (hU : IsDownwardCap U) {a b : ℝ} (hbox : U ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1) :
    Icc (horizontalLeft U) (horizontalRight U) ⊆ Icc a b := by
  rw [← horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
  exact image_subset_iff.2 fun p hp => (hbox hp).1

theorem CapHausdorffTendsto.capWidth_tendsto
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K) :
    Tendsto (fun n => capWidth (U n)) atTop (𝓝 (capWidth K)) :=
  (h.horizontalRight_tendsto (fun n => (hU n).isCompact)
    (fun n => (hU n).nonempty) hK.isCompact hK.nonempty).sub
      (h.horizontalLeft_tendsto (fun n => (hU n).isCompact)
        (fun n => (hU n).nonempty) hK.isCompact hK.nonempty)

namespace AngularGrid

open FinitePolygon

def rightPressure (U : Set Plane) (grid : Finset QuarterAngle) : ℝ :=
  rightEndpointPressure (capRoof U) (finiteBarrier U (normal grid) (pairList grid) none)
    (horizontalLeft U) (horizontalRight U)

def leftPressure (U : Set Plane) (grid : Finset QuarterAngle) : ℝ :=
  leftEndpointPressure (capRoof U) (finiteBarrier U (normal grid) (pairList grid) none)
    (horizontalLeft U) (horizontalRight U)

section

variable {U : ℕ → Set Plane} {K : Set Plane} (hHausdorff : CapHausdorffTendsto U K)
  (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K) {level : ℕ → ℕ}
  (hlevel : Tendsto level atTop atTop) {a b : ℝ} (hbox : ∀ n, U n ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
include hHausdorff hU hK hlevel hbox

/-- Dense sampling, a changing cap, and a changing horizontal section all
converge together. This is the literal finite barrier of the polygon walls. -/
theorem finiteBarrier_dyadic_tendsto {t : ℕ → ℝ} {x : ℝ} (htmem : ∀ n, t n ∈ Icc a b)
    (ht : Tendsto t atTop (𝓝 x)) :
    Tendsto (fun n => finiteBarrier (U n) (normal (dyadic (level n)))
      (pairList (dyadic (level n))) none (t n)) atTop
      (𝓝 (sweptNiche K (Real.pi / 2) x)) := by
  have huniform : TendstoUniformlyOn
      (fun n (p : CompactCap × ℝ) => niche p.1 (dyadic (level n)) p.2)
      (fun p => sweptNiche p.1.carrier (Real.pi / 2) p.2) atTop
      (boxedCaps (Icc a b ×ˢ Icc (0 : ℝ) 1) ×ˢ Icc a b) := fun v hv =>
    hlevel.eventually (tendstoUniformlyOn_dyadic_box (isCompact_Icc.prod isCompact_Icc) a b v hv)
  simpa only [finiteBarrier_eq_niche (hU _), IsDownwardCap.toCompactCap_carrier] using
    huniform.tendsto_comp continuous_capSweptNiche.continuousAt.continuousWithinAt
      (tendsto_nhdsWithin_iff.mpr
        ⟨(IsDownwardCap.tendsto_toCompactCap hU hK hHausdorff).prodMk_nhds ht,
          .of_forall fun n => ⟨hbox n, htmem n⟩⟩)

/-- Both moving pressures converge. -/
private theorem pressure_tendsto (hwidth : horizontalLeft K < horizontalRight K) :
    Tendsto (fun n => rightPressure (U n) (dyadic (level n))) atTop
      (𝓝 (capRightEndpointPressure K)) ∧
    Tendsto (fun n => leftPressure (U n) (dyadic (level n))) atTop
      (𝓝 (capLeftEndpointPressure K)) := by
  have hl := hHausdorff.horizontalLeft_tendsto (fun n => (hU n).isCompact)
    (fun n => (hU n).nonempty) hK.isCompact hK.nonempty
  have hr := hHausdorff.horizontalRight_tendsto (fun n => (hU n).isCompact)
    (fun n => (hU n).nonempty) hK.isCompact hK.nonempty
  have hlr n := horizontalLeft_le_horizontalRight (hU n).nonempty (hU n).isCompact
  have hL := (hHausdorff.middleLeft_roof_tendsto hU hK hwidth).add
    (finiteBarrier_dyadic_tendsto hHausdorff hU hK hlevel hbox
      (fun n => (hU n).projection_subset_Icc_of_box (hbox n)
        ⟨by linarith [hlr n], by linarith [hlr n]⟩) (hl.add ((hr.sub hl).div_const 4)))
  have hR := (hHausdorff.middleRight_roof_tendsto hU hK hwidth).add
    (finiteBarrier_dyadic_tendsto hHausdorff hU hK hlevel hbox
      (fun n => (hU n).projection_subset_Icc_of_box (hbox n)
        ⟨by linarith [hlr n], by linarith [hlr n]⟩) (hr.sub ((hr.sub hl).div_const 4)))
  exact ⟨((hR.const_mul 3).sub hL).div_const 4, ((hL.const_mul 3).sub hR).div_const 4⟩

theorem rightPressure_tendsto (hwidth : horizontalLeft K < horizontalRight K) :
    Tendsto (fun n => rightPressure (U n) (dyadic (level n))) atTop
      (𝓝 (capRightEndpointPressure K)) :=
  (pressure_tendsto hHausdorff hU hK hlevel hbox hwidth).1

theorem leftPressure_tendsto (hwidth : horizontalLeft K < horizontalRight K) :
    Tendsto (fun n => leftPressure (U n) (dyadic (level n))) atTop
      (𝓝 (capLeftEndpointPressure K)) :=
  (pressure_tendsto hHausdorff hU hK hlevel hbox hwidth).2

end

/-- A sequence within an error tending to zero of a convergent sequence has the same limit. -/
private theorem tendsto_of_abs_sub_le {f g e : ℕ → ℝ} {y : ℝ} (hg : Tendsto g atTop (𝓝 y))
    (he : Tendsto e atTop (𝓝 0)) (h : ∀ᶠ n in atTop, |f n - g n| ≤ e n) :
    Tendsto f atTop (𝓝 y) :=
  hg.congr_dist (squeeze_zero' (.of_forall fun _ => dist_nonneg)
    (h.mono fun n hn => by rwa [dist_comm, Real.dist_eq]) he)

variable {target : Set Plane} {U : ℕ → Set Plane} {a b : ℝ} {level : ℕ → ℕ}
  {coefficient : ℕ → ℝ} (hTarget : IsDownwardCap target)
  (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
  (hU : ∀ n, IsSelectedPolygon target a b (level n) (coefficient n) (U n))
  (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
  (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
  (hwidth : 1 < capWidth target)
include hTarget hTargetBox hU hHausdorff hlevel hc hrate hwidth

/-- Finite approximate complementarity determines the selected face-height
limit. No claim about continuity of the target face is used here. -/
theorem selected_right_height_tendsto (hslack : horizontalRight target < b) :
    Tendsto (fun n => capRoof (U n) (horizontalRight (U n))) atTop
      (𝓝 (max (capRightEndpointPressure target) 0)) := by
  have hcap n : IsDownwardCap (U n) := (hU n).isCap
  refine tendsto_of_abs_sub_le ((rightPressure_tendsto hHausdorff hcap hTarget hlevel
    (fun n => (hU n).inBox) (by unfold capWidth at hwidth; linarith)).max tendsto_const_nhds)
    (endpointSelectionError_tendsto a b hrate) ?_
  filter_upwards [(hHausdorff.capWidth_tendsto hcap hTarget).eventually (Ioi_mem_nhds hwidth),
    (hHausdorff.horizontalRight_tendsto (fun n => (hcap n).isCompact) (fun n => (hcap n).nonempty)
      hTarget.isCompact hTarget.nonempty).eventually (Iio_mem_nhds hslack)] with n hW hR
  exact (hU n).abs_right_complementarity_le hTarget hTargetBox (hc n) hW.le hR

theorem selected_left_height_tendsto (hslack : a < horizontalLeft target) :
    Tendsto (fun n => capRoof (U n) (horizontalLeft (U n))) atTop
      (𝓝 (max (capLeftEndpointPressure target) 0)) := by
  have hcap n : IsDownwardCap (U n) := (hU n).isCap
  refine tendsto_of_abs_sub_le ((leftPressure_tendsto hHausdorff hcap hTarget hlevel
    (fun n => (hU n).inBox) (by unfold capWidth at hwidth; linarith)).max tendsto_const_nhds)
    (endpointSelectionError_tendsto a b hrate) ?_
  filter_upwards [(hHausdorff.capWidth_tendsto hcap hTarget).eventually (Ioi_mem_nhds hwidth),
    (hHausdorff.horizontalLeft_tendsto (fun n => (hcap n).isCompact) (fun n => (hcap n).nonempty)
      hTarget.isCompact hTarget.nonempty).eventually (Ioi_mem_nhds hslack)] with n hW hL
  exact (hU n).abs_left_complementarity_le hTarget hTargetBox (hc n) hW.le hL

theorem right_complementarity_of_height_tendsto (hslack : horizontalRight target < b)
    (hface : Tendsto (fun n => capRoof (U n) (horizontalRight (U n))) atTop
      (𝓝 (capRoof target (horizontalRight target)))) :
    capRoof target (horizontalRight target) = max (capRightEndpointPressure target) 0 :=
  tendsto_nhds_unique hface (selected_right_height_tendsto hTarget hTargetBox hU
    hHausdorff hlevel hc hrate hwidth hslack)

theorem left_complementarity_of_height_tendsto (hslack : a < horizontalLeft target)
    (hface : Tendsto (fun n => capRoof (U n) (horizontalLeft (U n))) atTop
      (𝓝 (capRoof target (horizontalLeft target)))) :
    capRoof target (horizontalLeft target) = max (capLeftEndpointPressure target) 0 :=
  tendsto_nhds_unique hface (selected_left_height_tendsto hTarget hTargetBox hU
    hHausdorff hlevel hc hrate hwidth hslack)

end AngularGrid

end AmbidextrousSofa
