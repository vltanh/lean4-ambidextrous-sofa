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
  rw [capEndpointPressure_sum]
  exact div_nonneg
    (add_nonneg
      (add_nonneg (capRoof_nonneg hU.isCompact (fun p hp => (hU.inStrip hp).1) _)
        (sweptNiche_nonneg _ _ _))
      (add_nonneg (capRoof_nonneg hU.isCompact (fun p hp => (hU.inStrip hp).1) _)
        (sweptNiche_nonneg _ _ _))) (by norm_num)

theorem IsDownwardCap.projection_subset_Icc_of_box {U : Set Plane}
    (hU : IsDownwardCap U) {a b : ℝ} (hbox : U ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1) :
    Icc (horizontalLeft U) (horizontalRight U) ⊆ Icc a b := by
  rw [← horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
  rintro x ⟨p, hp, rfl⟩
  exact (hbox hp).1

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

/-- Dense sampling, a changing cap, and a changing horizontal section all
converge together. This is the literal finite barrier of the polygon walls. -/
theorem finiteBarrier_dyadic_tendsto {U : ℕ → Set Plane} {K : Set Plane}
    (hHausdorff : CapHausdorffTendsto U K) (hU : ∀ n, IsDownwardCap (U n))
    (hK : IsDownwardCap K) {level : ℕ → ℕ} (hlevel : Tendsto level atTop atTop)
    {a b : ℝ} (hbox : ∀ n, U n ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    {t : ℕ → ℝ} {x : ℝ} (htmem : ∀ n, t n ∈ Icc a b)
    (ht : Tendsto t atTop (𝓝 x)) :
    Tendsto (fun n => finiteBarrier (U n) (normal (dyadic (level n)))
      (pairList (dyadic (level n))) none (t n)) atTop
      (𝓝 (sweptNiche K (Real.pi / 2) x)) := by
  let B : Set Plane := Icc a b ×ˢ Icc (0 : ℝ) 1
  have huniform : TendstoUniformlyOn
      (fun n (p : CompactCap × ℝ) => niche p.1 (dyadic (level n)) p.2)
      (fun p => sweptNiche p.1.carrier (Real.pi / 2) p.2) atTop
      (boxedCaps B ×ˢ Icc a b) := by
    intro v hv
    exact hlevel.eventually
      (tendstoUniformlyOn_dyadic_box (B := B) (isCompact_Icc.prod isCompact_Icc) a b v hv)
  have hp : Tendsto (fun n => ((hU n).toCompactCap, t n)) atTop
      (𝓝[boxedCaps B ×ˢ Icc a b] (hK.toCompactCap, x)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨(IsDownwardCap.tendsto_toCompactCap hU hK hHausdorff).prodMk_nhds ht,
        Eventually.of_forall (fun n => ⟨hbox n, htmem n⟩)⟩
  have hlim := huniform.tendsto_comp
    continuous_capSweptNiche.continuousAt.continuousWithinAt hp
  have heq (n : ℕ) := finiteBarrier_eq_niche (hU n) (dyadic (level n)) (t n)
  simpa only [heq] using hlim

theorem rightPressure_tendsto {U : ℕ → Set Plane} {K : Set Plane}
    (hHausdorff : CapHausdorffTendsto U K) (hU : ∀ n, IsDownwardCap (U n))
    (hK : IsDownwardCap K) {level : ℕ → ℕ} (hlevel : Tendsto level atTop atTop)
    {a b : ℝ} (hbox : ∀ n, U n ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hwidth : horizontalLeft K < horizontalRight K) :
    Tendsto (fun n => rightPressure (U n) (dyadic (level n))) atTop
      (𝓝 (capRightEndpointPressure K)) := by
  have hl := hHausdorff.horizontalLeft_tendsto (fun n => (hU n).isCompact)
    (fun n => (hU n).nonempty) hK.isCompact hK.nonempty
  have hr := hHausdorff.horizontalRight_tendsto (fun n => (hU n).isCompact)
    (fun n => (hU n).nonempty) hK.isCompact hK.nonempty
  have hxleft : ∀ n, horizontalLeft (U n) +
      (horizontalRight (U n) - horizontalLeft (U n)) / 4 ∈ Icc a b := by
    intro n
    apply (hU n).projection_subset_Icc_of_box (hbox n)
    have h := horizontalLeft_le_horizontalRight (hU n).nonempty (hU n).isCompact
    exact ⟨by linarith, by linarith⟩
  have hxright : ∀ n, horizontalRight (U n) -
      (horizontalRight (U n) - horizontalLeft (U n)) / 4 ∈ Icc a b := by
    intro n
    apply (hU n).projection_subset_Icc_of_box (hbox n)
    have h := horizontalLeft_le_horizontalRight (hU n).nonempty (hU n).isCompact
    exact ⟨by linarith, by linarith⟩
  have hNl := finiteBarrier_dyadic_tendsto hHausdorff hU hK hlevel hbox hxleft
    (hl.add ((hr.sub hl).div_const 4))
  have hNr := finiteBarrier_dyadic_tendsto hHausdorff hU hK hlevel hbox hxright
    (hr.sub ((hr.sub hl).div_const 4))
  exact ((((hHausdorff.middleRight_roof_tendsto hU hK hwidth).add hNr).const_mul 3).sub
    ((hHausdorff.middleLeft_roof_tendsto hU hK hwidth).add hNl)).div_const 4

theorem leftPressure_tendsto {U : ℕ → Set Plane} {K : Set Plane}
    (hHausdorff : CapHausdorffTendsto U K) (hU : ∀ n, IsDownwardCap (U n))
    (hK : IsDownwardCap K) {level : ℕ → ℕ} (hlevel : Tendsto level atTop atTop)
    {a b : ℝ} (hbox : ∀ n, U n ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hwidth : horizontalLeft K < horizontalRight K) :
    Tendsto (fun n => leftPressure (U n) (dyadic (level n))) atTop
      (𝓝 (capLeftEndpointPressure K)) := by
  have hl := hHausdorff.horizontalLeft_tendsto (fun n => (hU n).isCompact)
    (fun n => (hU n).nonempty) hK.isCompact hK.nonempty
  have hr := hHausdorff.horizontalRight_tendsto (fun n => (hU n).isCompact)
    (fun n => (hU n).nonempty) hK.isCompact hK.nonempty
  have hxleft : ∀ n, horizontalLeft (U n) +
      (horizontalRight (U n) - horizontalLeft (U n)) / 4 ∈ Icc a b := by
    intro n
    apply (hU n).projection_subset_Icc_of_box (hbox n)
    have h := horizontalLeft_le_horizontalRight (hU n).nonempty (hU n).isCompact
    exact ⟨by linarith, by linarith⟩
  have hxright : ∀ n, horizontalRight (U n) -
      (horizontalRight (U n) - horizontalLeft (U n)) / 4 ∈ Icc a b := by
    intro n
    apply (hU n).projection_subset_Icc_of_box (hbox n)
    have h := horizontalLeft_le_horizontalRight (hU n).nonempty (hU n).isCompact
    exact ⟨by linarith, by linarith⟩
  have hNl := finiteBarrier_dyadic_tendsto hHausdorff hU hK hlevel hbox hxleft
    (hl.add ((hr.sub hl).div_const 4))
  have hNr := finiteBarrier_dyadic_tendsto hHausdorff hU hK hlevel hbox hxright
    (hr.sub ((hr.sub hl).div_const 4))
  exact ((((hHausdorff.middleLeft_roof_tendsto hU hK hwidth).add hNl).const_mul 3).sub
    ((hHausdorff.middleRight_roof_tendsto hU hK hwidth).add hNr)).div_const 4

/-- Finite approximate complementarity determines the selected face-height
limit. No claim about continuity of the target face is used here. -/
theorem selected_right_height_tendsto {target : Set Plane} {U : ℕ → Set Plane}
    {a b : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hwidth : 1 < capWidth target) (hslack : horizontalRight target < b) :
    Tendsto (fun n => capRoof (U n) (horizontalRight (U n))) atTop
      (𝓝 (max (capRightEndpointPressure target) 0)) := by
  have hcapp : ∀ n, IsDownwardCap (U n) := fun n => (hU n).isCap
  have hpositive : horizontalLeft target < horizontalRight target := by
    unfold capWidth at hwidth
    linarith
  have hp := rightPressure_tendsto hHausdorff hcapp hTarget hlevel
    (fun n => (hU n).inBox) hpositive
  have hpmax : Tendsto (fun n => max (rightPressure (U n) (dyadic (level n))) 0)
      atTop (𝓝 (max (capRightEndpointPressure target) 0)) := hp.max tendsto_const_nhds
  have herr := endpointSelectionError_tendsto a b hrate
  have hW : ∀ᶠ n in atTop, 1 ≤ capWidth (U n) :=
    ((hHausdorff.capWidth_tendsto hcapp hTarget).eventually
      (Ioi_mem_nhds hwidth)).mono (fun _ hn => hn.le)
  have hR : ∀ᶠ n in atTop, horizontalRight (U n) < b :=
    (hHausdorff.horizontalRight_tendsto (fun n => (hcapp n).isCompact)
      (fun n => (hcapp n).nonempty) hTarget.isCompact hTarget.nonempty).eventually
        (Iio_mem_nhds hslack)
  have hbound : ∀ᶠ n in atTop,
      |capRoof (U n) (horizontalRight (U n)) -
        max (rightPressure (U n) (dyadic (level n))) 0| ≤
          endpointSelectionError a b (coefficient n) := by
    filter_upwards [hW, hR] with n hnW hnR
    exact (hU n).abs_right_complementarity_le hTarget hTargetBox (hc n) hnW hnR
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa only [sub_zero] using hpmax.sub herr)
    (by simpa only [add_zero] using hpmax.add herr)
  · filter_upwards [hbound] with n hn
    linarith [(abs_le.mp hn).1]
  · filter_upwards [hbound] with n hn
    linarith [(abs_le.mp hn).2]

theorem selected_left_height_tendsto {target : Set Plane} {U : ℕ → Set Plane}
    {a b : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hwidth : 1 < capWidth target) (hslack : a < horizontalLeft target) :
    Tendsto (fun n => capRoof (U n) (horizontalLeft (U n))) atTop
      (𝓝 (max (capLeftEndpointPressure target) 0)) := by
  have hcapp : ∀ n, IsDownwardCap (U n) := fun n => (hU n).isCap
  have hpositive : horizontalLeft target < horizontalRight target := by
    unfold capWidth at hwidth
    linarith
  have hp := leftPressure_tendsto hHausdorff hcapp hTarget hlevel
    (fun n => (hU n).inBox) hpositive
  have hpmax : Tendsto (fun n => max (leftPressure (U n) (dyadic (level n))) 0)
      atTop (𝓝 (max (capLeftEndpointPressure target) 0)) := hp.max tendsto_const_nhds
  have herr := endpointSelectionError_tendsto a b hrate
  have hW : ∀ᶠ n in atTop, 1 ≤ capWidth (U n) :=
    ((hHausdorff.capWidth_tendsto hcapp hTarget).eventually
      (Ioi_mem_nhds hwidth)).mono (fun _ hn => hn.le)
  have hL : ∀ᶠ n in atTop, a < horizontalLeft (U n) :=
    (hHausdorff.horizontalLeft_tendsto (fun n => (hcapp n).isCompact)
      (fun n => (hcapp n).nonempty) hTarget.isCompact hTarget.nonempty).eventually
        (Ioi_mem_nhds hslack)
  have hbound : ∀ᶠ n in atTop,
      |capRoof (U n) (horizontalLeft (U n)) -
        max (leftPressure (U n) (dyadic (level n))) 0| ≤
          endpointSelectionError a b (coefficient n) := by
    filter_upwards [hW, hL] with n hnW hnL
    exact (hU n).abs_left_complementarity_le hTarget hTargetBox (hc n) hnW hnL
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa only [sub_zero] using hpmax.sub herr)
    (by simpa only [add_zero] using hpmax.add herr)
  · filter_upwards [hbound] with n hn
    linarith [(abs_le.mp hn).1]
  · filter_upwards [hbound] with n hn
    linarith [(abs_le.mp hn).2]

theorem right_complementarity_of_height_tendsto
    {target : Set Plane} {U : ℕ → Set Plane} {a b : ℝ}
    {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hwidth : 1 < capWidth target) (hslack : horizontalRight target < b)
    (hface : Tendsto (fun n => capRoof (U n) (horizontalRight (U n))) atTop
      (𝓝 (capRoof target (horizontalRight target)))) :
    capRoof target (horizontalRight target) = max (capRightEndpointPressure target) 0 :=
  tendsto_nhds_unique hface (selected_right_height_tendsto hTarget hTargetBox hU
    hHausdorff hlevel hc hrate hwidth hslack)

theorem left_complementarity_of_height_tendsto
    {target : Set Plane} {U : ℕ → Set Plane} {a b : ℝ}
    {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hwidth : 1 < capWidth target) (hslack : a < horizontalLeft target)
    (hface : Tendsto (fun n => capRoof (U n) (horizontalLeft (U n))) atTop
      (𝓝 (capRoof target (horizontalLeft target)))) :
    capRoof target (horizontalLeft target) = max (capLeftEndpointPressure target) 0 :=
  tendsto_nhds_unique hface (selected_left_height_tendsto hTarget hTargetBox hU
    hHausdorff hlevel hc hrate hwidth hslack)

end AngularGrid

end AmbidextrousSofa
