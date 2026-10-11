module

public import AmbidextrousSofa.Analysis.CapInteriorRoof
public import AmbidextrousSofa.Analysis.SelectedEndpointMoments
public import Mathlib.Topology.UniformSpace.UniformApproximation

@[expose] public section

/-!
# Moving pressure limits for selected polygons

When the finite barriers converge along every converging sequence of sections, interior roof
convergence identifies both moving pressure terms. Finite complementarity then gives an actual
limit for the selected endpoint heights, including when that limit is zero. For the dyadic
full-turn polygons the finite angular niches converge uniformly on the entire boxed cap domain.

Identifying that height limit with the limiting cap's vertical face is a
separate geometric step: it requires control of curvature near the axis.
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

/-- With a nonnegative barrier the two pressures of a cap have a nonnegative sum. -/
theorem IsDownwardCap.endpointPressure_sum_nonneg {U : Set Plane} (hU : IsDownwardCap U)
    {N : ℝ → ℝ} (hN : ∀ x, 0 ≤ N x) :
    0 ≤ rightEndpointPressure (capRoof U) N (horizontalLeft U) (horizontalRight U) +
      leftEndpointPressure (capRoof U) N (horizontalLeft U) (horizontalRight U) := by
  have h x := add_nonneg (capRoof_nonneg hU.isCompact (fun p hp => (hU.inStrip hp).1) x) (hN x)
  unfold rightEndpointPressure leftEndpointPressure
  linarith [h (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4),
    h (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4)]

/-- Both pressures of a nonnegative barrier are positive when their positive parts are at most
one and both middle roof heights exceed one half. -/
theorem endpointPressures_pos {roof N : ℝ → ℝ} {l r : ℝ} (hN : ∀ x, 0 ≤ N x)
    (hmid : 1 / 2 < roof (l + (r - l) / 4) ∧ 1 / 2 < roof (r - (r - l) / 4))
    (hR : max (rightEndpointPressure roof N l r) 0 ≤ 1)
    (hL : max (leftEndpointPressure roof N l r) 0 ≤ 1) :
    0 < rightEndpointPressure roof N l r ∧ 0 < leftEndpointPressure roof N l r := by
  have hR' := (le_max_left _ _).trans hR
  have hL' := (le_max_left _ _).trans hL
  unfold rightEndpointPressure leftEndpointPressure at *
  constructor <;> linarith [hN (l + (r - l) / 4), hN (r - (r - l) / 4)]

theorem IsDownwardCap.projection_subset_Icc_of_box {U : Set Plane}
    (hU : IsDownwardCap U) {a b : ℝ} (hbox : U ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1) :
    Icc (horizontalLeft U) (horizontalRight U) ⊆ Icc a b := by
  rw [← hU.horizontalProjection_eq_Icc]
  exact image_subset_iff.2 fun p hp => (hbox hp).1

theorem CapHausdorffTendsto.capWidth_tendsto
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K) :
    Tendsto (fun n => capWidth (U n)) atTop (𝓝 (capWidth K)) :=
  (h.horizontalRight_tendsto (fun n => (hU n).isCompact)
    (fun n => (hU n).nonempty) hK.isCompact hK.nonempty).sub
      (h.horizontalLeft_tendsto (fun n => (hU n).isCompact)
        (fun n => (hU n).nonempty) hK.isCompact hK.nonempty)

/-- Both moving pressures converge when the barriers converge along converging sections. -/
theorem CapHausdorffTendsto.endpointPressures_tendsto {U : ℕ → Set Plane} {K : Set Plane}
    (hHausdorff : CapHausdorffTendsto U K) (hU : ∀ n, IsDownwardCap (U n))
    (hK : IsDownwardCap K) {a b : ℝ} (hbox : ∀ n, U n ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    {G : ℕ → ℝ → ℝ} {N : ℝ → ℝ} (hG : ∀ {t : ℕ → ℝ} {x : ℝ}, (∀ n, t n ∈ Icc a b) →
      Tendsto t atTop (𝓝 x) → Tendsto (fun n => G n (t n)) atTop (𝓝 (N x)))
    (hwidth : horizontalLeft K < horizontalRight K) :
    Tendsto (fun n => rightEndpointPressure (capRoof (U n)) (G n) (horizontalLeft (U n))
      (horizontalRight (U n))) atTop
      (𝓝 (rightEndpointPressure (capRoof K) N (horizontalLeft K) (horizontalRight K))) ∧
    Tendsto (fun n => leftEndpointPressure (capRoof (U n)) (G n) (horizontalLeft (U n))
      (horizontalRight (U n))) atTop
      (𝓝 (leftEndpointPressure (capRoof K) N (horizontalLeft K) (horizontalRight K))) := by
  have hl := hHausdorff.horizontalLeft_tendsto (fun n => (hU n).isCompact)
    (fun n => (hU n).nonempty) hK.isCompact hK.nonempty
  have hr := hHausdorff.horizontalRight_tendsto (fun n => (hU n).isCompact)
    (fun n => (hU n).nonempty) hK.isCompact hK.nonempty
  have hlr n := horizontalLeft_le_horizontalRight (hU n).nonempty (hU n).isCompact
  have hL := (hHausdorff.middleLeft_roof_tendsto hU hK hwidth).add
    (hG (fun n => (hU n).projection_subset_Icc_of_box (hbox n)
      ⟨by linarith [hlr n], by linarith [hlr n]⟩) (hl.add ((hr.sub hl).div_const 4)))
  have hR := (hHausdorff.middleRight_roof_tendsto hU hK hwidth).add
    (hG (fun n => (hU n).projection_subset_Icc_of_box (hbox n)
      ⟨by linarith [hlr n], by linarith [hlr n]⟩) (hr.sub ((hr.sub hl).div_const 4)))
  exact ⟨((hR.const_mul 3).sub hL).div_const 4, ((hL.const_mul 3).sub hR).div_const 4⟩

/-- A sequence within an error tending to zero of a convergent sequence has the same limit. -/
private theorem tendsto_of_abs_sub_le {f g e : ℕ → ℝ} {y : ℝ} (hg : Tendsto g atTop (𝓝 y))
    (he : Tendsto e atTop (𝓝 0)) (h : ∀ᶠ n in atTop, |f n - g n| ≤ e n) :
    Tendsto f atTop (𝓝 y) :=
  hg.congr_dist (squeeze_zero' (.of_forall fun _ => dist_nonneg)
    (h.mono fun n hn => by rwa [dist_comm, Real.dist_eq]) he)

namespace FinitePolygon

variable {ι : ℕ → Type*} [∀ n, Fintype (ι n)]

/-- Selected polygons converging to a boxed cap of width above one, with coefficients tending to
zero and with finite barriers converging to `N` along every converging sequence of sections. -/
structure SelectedLimit (normal : ∀ n, ι n → Plane) (corners : ∀ n, List (ι n × ι n))
    (terminal : ∀ n, Option (ι n)) (weight : ∀ n, ι n → ℝ) (target : Set Plane) (a b : ℝ)
    (c : ℕ → ℝ) (N : ℝ → ℝ) (U : ℕ → Set Plane) : Prop where
  selected : ∀ n, IsSelected (normal n) (corners n) (terminal n) (weight n) target a b (c n) (U n)
  target_cap : IsDownwardCap target
  target_box : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1
  hausdorff : CapHausdorffTendsto U target
  coefficient_tendsto : Tendsto c atTop (𝓝 0)
  width : 1 < capWidth target
  barrier_tendsto : ∀ {t : ℕ → ℝ} {x : ℝ}, (∀ n, t n ∈ Icc a b) → Tendsto t atTop (𝓝 x) →
    Tendsto (fun n => finiteBarrier (U n) (normal n) (corners n) (terminal n) (t n)) atTop
      (𝓝 (N x))

namespace SelectedLimit

variable {normal : ∀ n, ι n → Plane} {corners : ∀ n, List (ι n × ι n)}
  {terminal : ∀ n, Option (ι n)} {weight : ∀ n, ι n → ℝ} {target : Set Plane} {a b : ℝ}
  {c : ℕ → ℝ} {N : ℝ → ℝ} {U : ℕ → Set Plane}
  (hS : SelectedLimit normal corners terminal weight target a b c N U)
include hS

theorem isCap (n : ℕ) : IsDownwardCap (U n) := (hS.selected n).isCap

theorem eventually_one_le_capWidth : ∀ᶠ n in atTop, 1 ≤ capWidth (U n) :=
  ((hS.hausdorff.capWidth_tendsto hS.isCap hS.target_cap).eventually
    (Ioi_mem_nhds hS.width)).mono fun _ hn => hn.le

theorem pressures_tendsto :
    Tendsto (fun n => rightEndpointPressure (capRoof (U n))
      (finiteBarrier (U n) (normal n) (corners n) (terminal n)) (horizontalLeft (U n))
      (horizontalRight (U n))) atTop (𝓝 (rightEndpointPressure (capRoof target) N
        (horizontalLeft target) (horizontalRight target))) ∧
    Tendsto (fun n => leftEndpointPressure (capRoof (U n))
      (finiteBarrier (U n) (normal n) (corners n) (terminal n)) (horizontalLeft (U n))
      (horizontalRight (U n))) atTop (𝓝 (leftEndpointPressure (capRoof target) N
        (horizontalLeft target) (horizontalRight target))) :=
  hS.hausdorff.endpointPressures_tendsto hS.isCap hS.target_cap (fun n => (hS.selected n).inBox)
    hS.barrier_tendsto (by have := hS.width; unfold capWidth at this; linarith)

/-- Finite approximate complementarity determines the selected face-height
limit. No claim about continuity of the target face is used here. -/
theorem right_height_tendsto (hslack : horizontalRight target < b) :
    Tendsto (fun n => capRoof (U n) (horizontalRight (U n))) atTop
      (𝓝 (max (rightEndpointPressure (capRoof target) N (horizontalLeft target)
        (horizontalRight target)) 0)) := by
  refine tendsto_of_abs_sub_le (hS.pressures_tendsto.1.max tendsto_const_nhds)
    (endpointSelectionError_tendsto a b hS.coefficient_tendsto) ?_
  filter_upwards [hS.eventually_one_le_capWidth, (hS.hausdorff.horizontalRight_tendsto
    (fun n => (hS.isCap n).isCompact) (fun n => (hS.isCap n).nonempty) hS.target_cap.isCompact
      hS.target_cap.nonempty).eventually (Iio_mem_nhds hslack)] with n hW hR
  exact ((hS.selected n).abs_complementarity_le hS.target_cap hS.target_box hW).1 hR

theorem left_height_tendsto (hslack : a < horizontalLeft target) :
    Tendsto (fun n => capRoof (U n) (horizontalLeft (U n))) atTop
      (𝓝 (max (leftEndpointPressure (capRoof target) N (horizontalLeft target)
        (horizontalRight target)) 0)) := by
  refine tendsto_of_abs_sub_le (hS.pressures_tendsto.2.max tendsto_const_nhds)
    (endpointSelectionError_tendsto a b hS.coefficient_tendsto) ?_
  filter_upwards [hS.eventually_one_le_capWidth, (hS.hausdorff.horizontalLeft_tendsto
    (fun n => (hS.isCap n).isCompact) (fun n => (hS.isCap n).nonempty) hS.target_cap.isCompact
      hS.target_cap.nonempty).eventually (Ioi_mem_nhds hslack)] with n hW hL
  exact ((hS.selected n).abs_complementarity_le hS.target_cap hS.target_box hW).2 hL

end SelectedLimit

end FinitePolygon

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

theorem rightPressure_tendsto (hwidth : horizontalLeft K < horizontalRight K) :
    Tendsto (fun n => rightPressure (U n) (dyadic (level n))) atTop
      (𝓝 (capRightEndpointPressure K)) :=
  (hHausdorff.endpointPressures_tendsto hU hK hbox
    (finiteBarrier_dyadic_tendsto hHausdorff hU hK hlevel hbox) hwidth).1

theorem leftPressure_tendsto (hwidth : horizontalLeft K < horizontalRight K) :
    Tendsto (fun n => leftPressure (U n) (dyadic (level n))) atTop
      (𝓝 (capLeftEndpointPressure K)) :=
  (hHausdorff.endpointPressures_tendsto hU hK hbox
    (finiteBarrier_dyadic_tendsto hHausdorff hU hK hlevel hbox) hwidth).2

end

/-- The dyadic selected polygons of a full-turn target form a selected limit. -/
theorem selectedLimit {target : Set Plane} {U : ℕ → Set Plane} {a b : ℝ} {level : ℕ → ℕ}
    {coefficient : ℕ → ℝ} (hTarget : IsDownwardCap target)
    (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hwidth : 1 < capWidth target) :
    SelectedLimit (fun n => normal (dyadic (level n))) (fun n => pairList (dyadic (level n)))
      (fun _ => none) (fun n i => coefficient n * stageWeight (level n) i) target a b coefficient
      (sweptNiche target (Real.pi / 2)) U :=
  ⟨fun n => (hU n).isSelected (hc n), hTarget, hTargetBox, hHausdorff, hrate, hwidth,
    finiteBarrier_dyadic_tendsto hHausdorff (fun n => (hU n).isCap) hTarget hlevel
      fun n => (hU n).inBox⟩

end AngularGrid

end AmbidextrousSofa
