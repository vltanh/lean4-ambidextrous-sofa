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

theorem partialEndpointPressure_sum (U : Set Plane) (α : ℝ) :
    partialRightEndpointPressure U α + partialLeftEndpointPressure U α =
      ((capRoof U (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4) +
        partialBarrier U α
          (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)) +
       (capRoof U (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) +
        partialBarrier U α
          (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4))) / 2 := by
  unfold partialRightEndpointPressure partialLeftEndpointPressure rightEndpointPressure leftEndpointPressure
  ring

theorem IsDownwardCap.partialEndpointPressure_sum_nonneg {U : Set Plane}
    (hU : IsDownwardCap U) (α : ℝ) : 0 ≤ partialRightEndpointPressure U α + partialLeftEndpointPressure U α := by
  rw [partialEndpointPressure_sum]
  exact div_nonneg
    (add_nonneg
      (add_nonneg (capRoof_nonneg hU.isCompact (fun p hp => (hU.inStrip hp).1) _)
        (partialBarrier_nonneg _ _ _))
      (add_nonneg (capRoof_nonneg hU.isCompact (fun p hp => (hU.inStrip hp).1) _)
        (partialBarrier_nonneg _ _ _))) (by norm_num)

namespace PartialGrid

open FinitePolygon AngularGrid

variable {α : TerminalAngle} {hαL : (α : ℝ) < Real.pi / 2}

def rightPressure (U : Set Plane) (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2) (grid : Finset QuarterAngle) : ℝ :=
  rightEndpointPressure (capRoof U) (finiteBarrier U (normal α grid) (pairList α grid) (some (terminalIndex α hαL grid)))
    (horizontalLeft U) (horizontalRight U)

def leftPressure (U : Set Plane) (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2) (grid : Finset QuarterAngle) : ℝ :=
  leftEndpointPressure (capRoof U) (finiteBarrier U (normal α grid) (pairList α grid) (some (terminalIndex α hαL grid)))
    (horizontalLeft U) (horizontalRight U)

/-- Rescaled dense sampling, changing caps, and moving sections converge
with the whole terminal wall retained. -/
theorem finiteBarrier_dyadic_tendsto {U : ℕ → Set Plane} {K : Set Plane}
    (hHausdorff : CapHausdorffTendsto U K) (hU : ∀ n, IsDownwardCap (U n))
    (hK : IsDownwardCap K) {level : ℕ → ℕ} (hlevel : Tendsto level atTop atTop)
    {a b : ℝ} (hbox : ∀ n, U n ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    {t : ℕ → ℝ} {x : ℝ} (htmem : ∀ n, t n ∈ Icc a b)
    (ht : Tendsto t atTop (𝓝 x)) :
    Tendsto (fun n => finiteBarrier (U n) (normal α (dyadic (level n)))
      (pairList α (dyadic (level n))) (some (terminalIndex α hαL (dyadic (level n)))) (t n)) atTop
      (𝓝 (partialBarrier K α x)) := by
  let B : Set Plane := Icc a b ×ˢ Icc (0 : ℝ) 1
  have huniform : TendstoUniformlyOn
      (fun n (p : (CompactCap × TerminalAngle) × ℝ) =>
        barrier p.1.1.carrier p.1.2 (dyadic (level n)) p.2)
      (fun p => partialBarrier p.1.1.carrier p.1.2 p.2) atTop
      ((boxedCaps B ×ˢ (univ : Set TerminalAngle)) ×ˢ Icc a b) := by
    intro v hv
    exact hlevel.eventually
      (tendstoUniformlyOn_dyadic_box (B := B) (isCompact_Icc.prod isCompact_Icc) a b v hv)
  have hp : Tendsto (fun n => (((hU n).toCompactCap, α), t n)) atTop
      (𝓝[(boxedCaps B ×ˢ (univ : Set TerminalAngle)) ×ˢ Icc a b] ((hK.toCompactCap, α), x)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨((IsDownwardCap.tendsto_toCompactCap hU hK hHausdorff).prodMk_nhds
          tendsto_const_nhds).prodMk_nhds ht,
        Eventually.of_forall (fun n => ⟨⟨hbox n, mem_univ α⟩, htmem n⟩)⟩
  have hlim := huniform.tendsto_comp
    continuous_partialCapBarrier.continuousAt.continuousWithinAt hp
  simpa only [finiteBarrier_eq_barrier] using hlim

theorem rightPressure_tendsto {U : ℕ → Set Plane} {K : Set Plane}
    (hHausdorff : CapHausdorffTendsto U K) (hU : ∀ n, IsDownwardCap (U n))
    (hK : IsDownwardCap K) {level : ℕ → ℕ} (hlevel : Tendsto level atTop atTop)
    {a b : ℝ} (hbox : ∀ n, U n ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hwidth : horizontalLeft K < horizontalRight K) :
    Tendsto (fun n => rightPressure (U n) α hαL (dyadic (level n))) atTop
      (𝓝 (partialRightEndpointPressure K α)) := by
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
  have hNl := finiteBarrier_dyadic_tendsto (α := α) (hαL := hαL) hHausdorff hU hK hlevel hbox hxleft
    (hl.add ((hr.sub hl).div_const 4))
  have hNr := finiteBarrier_dyadic_tendsto (α := α) (hαL := hαL) hHausdorff hU hK hlevel hbox hxright
    (hr.sub ((hr.sub hl).div_const 4))
  exact ((((hHausdorff.middleRight_roof_tendsto hU hK hwidth).add hNr).const_mul 3).sub
    ((hHausdorff.middleLeft_roof_tendsto hU hK hwidth).add hNl)).div_const 4

theorem leftPressure_tendsto {U : ℕ → Set Plane} {K : Set Plane}
    (hHausdorff : CapHausdorffTendsto U K) (hU : ∀ n, IsDownwardCap (U n))
    (hK : IsDownwardCap K) {level : ℕ → ℕ} (hlevel : Tendsto level atTop atTop)
    {a b : ℝ} (hbox : ∀ n, U n ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hwidth : horizontalLeft K < horizontalRight K) :
    Tendsto (fun n => leftPressure (U n) α hαL (dyadic (level n))) atTop
      (𝓝 (partialLeftEndpointPressure K α)) := by
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
  have hNl := finiteBarrier_dyadic_tendsto (α := α) (hαL := hαL) hHausdorff hU hK hlevel hbox hxleft
    (hl.add ((hr.sub hl).div_const 4))
  have hNr := finiteBarrier_dyadic_tendsto (α := α) (hαL := hαL) hHausdorff hU hK hlevel hbox hxright
    (hr.sub ((hr.sub hl).div_const 4))
  exact ((((hHausdorff.middleLeft_roof_tendsto hU hK hwidth).add hNl).const_mul 3).sub
    ((hHausdorff.middleRight_roof_tendsto hU hK hwidth).add hNr)).div_const 4

/-- Finite approximate complementarity determines the selected face-height
limit. No claim about continuity of the target face is used here. -/
theorem selected_right_height_tendsto {target : Set Plane} {U : ℕ → Set Plane}
    {a b : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target α hαL a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hwidth : 1 < capWidth target) (hslack : horizontalRight target < b) :
    Tendsto (fun n => capRoof (U n) (horizontalRight (U n))) atTop
      (𝓝 (max (partialRightEndpointPressure target α) 0)) := by
  have hcapp : ∀ n, IsDownwardCap (U n) := fun n => (hU n).isCap
  have hpositive : horizontalLeft target < horizontalRight target := by
    unfold capWidth at hwidth
    linarith
  have hp := rightPressure_tendsto (α := α) (hαL := hαL) hHausdorff hcapp hTarget hlevel
    (fun n => (hU n).inBox) hpositive
  have hpmax : Tendsto (fun n => max (rightPressure (U n) α hαL (dyadic (level n))) 0)
      atTop (𝓝 (max (partialRightEndpointPressure target α) 0)) := hp.max tendsto_const_nhds
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
        max (rightPressure (U n) α hαL (dyadic (level n))) 0| ≤
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
    (hU : ∀ n, IsSelectedPolygon target α hαL a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hwidth : 1 < capWidth target) (hslack : a < horizontalLeft target) :
    Tendsto (fun n => capRoof (U n) (horizontalLeft (U n))) atTop
      (𝓝 (max (partialLeftEndpointPressure target α) 0)) := by
  have hcapp : ∀ n, IsDownwardCap (U n) := fun n => (hU n).isCap
  have hpositive : horizontalLeft target < horizontalRight target := by
    unfold capWidth at hwidth
    linarith
  have hp := leftPressure_tendsto (α := α) (hαL := hαL) hHausdorff hcapp hTarget hlevel
    (fun n => (hU n).inBox) hpositive
  have hpmax : Tendsto (fun n => max (leftPressure (U n) α hαL (dyadic (level n))) 0)
      atTop (𝓝 (max (partialLeftEndpointPressure target α) 0)) := hp.max tendsto_const_nhds
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
        max (leftPressure (U n) α hαL (dyadic (level n))) 0| ≤
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
    (hU : ∀ n, IsSelectedPolygon target α hαL a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hwidth : 1 < capWidth target) (hslack : horizontalRight target < b)
    (hface : Tendsto (fun n => capRoof (U n) (horizontalRight (U n))) atTop
      (𝓝 (capRoof target (horizontalRight target)))) :
    capRoof target (horizontalRight target) = max (partialRightEndpointPressure target α) 0 :=
  tendsto_nhds_unique hface (selected_right_height_tendsto hTarget hTargetBox hU
    hHausdorff hlevel hc hrate hwidth hslack)

theorem left_complementarity_of_height_tendsto
    {target : Set Plane} {U : ℕ → Set Plane} {a b : ℝ}
    {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target α hαL a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hwidth : 1 < capWidth target) (hslack : a < horizontalLeft target)
    (hface : Tendsto (fun n => capRoof (U n) (horizontalLeft (U n))) atTop
      (𝓝 (capRoof target (horizontalLeft target)))) :
    capRoof target (horizontalLeft target) = max (partialLeftEndpointPressure target α) 0 :=
  tendsto_nhds_unique hface (selected_left_height_tendsto hTarget hTargetBox hU
    hHausdorff hlevel hc hrate hwidth hslack)


end PartialGrid
end AmbidextrousSofa
