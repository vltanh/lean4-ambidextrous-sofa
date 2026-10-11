module

public import AmbidextrousSofa.Analysis.SelectedHorizontalMoment
public import AmbidextrousSofa.Analysis.NichePositiveMiddle
public import AmbidextrousSofa.Analysis.FullWidthGap
public import AmbidextrousSofa.Analysis.FacetPinning

@[expose] public section

/-!
# Pinning the actual horizontal top facet

The positive niche occupies the full open middle interval, because the
actual maximum has width greater than two. Its horizontal source moment
therefore uses the complete available charged length. Any top point
strictly beyond a middle endpoint would remove a positive length from one
of the two charged windows, contradicting that moment. Together with the
previous nonhorizontal pinning theorem this covers every affine middle.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

/-- Every actual height-one point lies above the middle interval when
the middle roof is horizontal. The horizontal source inequality is
constructed from the maximizing cap itself. -/
theorem IsFullCapMaximizer.top_abscissa_mem_middle
    {U : Set Plane} (hU : IsFullCapMaximizer U) (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = 1) {p : Plane} (hp : p ∈ U) (hpone : p.2 = 1) :
    p.1 ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U) := by
  have hw := hU.two_lt_width
  have hwr : capWidth U = horizontalRight U - horizontalLeft U := rfl
  obtain ⟨ha, hb, hab⟩ := hU.isCap.middleChord_endpoints (by linarith)
  set a := horizontalLeft U + capWidth U / 4 with ha_def
  set b := horizontalRight U - capWidth U / 4 with hb_def
  have hA : capRoof U a = 1 := hmiddle a ⟨le_rfl, hab.le⟩
  have hB : capRoof U b = 1 := hmiddle b ⟨hab.le, le_rfl⟩
  have hpA : (a, 1) ∈ U := hA ▸ capRoof_mem hU.isCap.isCompact ha
  have hpB : (b, 1) ∈ U := hB ▸ capRoof_mem hU.isCap.isCompact hb
  have hpTop : (p.1, 1) ∈ U := hpone ▸ hp
  have hpl : p.1 ∈ Icc (horizontalLeft U) (horizontalRight U) := by
    rw [← horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex]
    exact ⟨p, hp, rfl⟩
  have hAff : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c := ⟨0, 1, by simpa using hmiddle⟩
  have hlength : b - a ≤ volume.real
      (middleHalfInterval (horizontalLeft U) (horizontalRight U) ∩
        {x : ℝ | 0 < sweptNiche U (Real.pi / 2) x}) := by
    rw [← Real.volume_real_Ioo_of_le hab.le]
    exact measureReal_mono (fun x hx => ⟨⟨hx.1.le, hx.2.le⟩,
      hU.isCap.sweptNiche_pos_on_open_middle_of_unit_endpoints hw hA hB x hx⟩)
      (measure_ne_top_of_subset inter_subset_left measure_Icc_lt_top.ne)
  refine ⟨le_of_not_gt fun hpa => ?_, le_of_not_gt fun hbp => ?_⟩
  · have hbound := hlength.trans
      ((hU.positive_middle_measure_le_outer_without_top hheight hAff hpTop hpB).trans
        (add_le_add (measureReal_mono (s₂ := Icc (horizontalLeft U) p.1) (fun x hx =>
          ⟨hx.1.1, le_of_not_gt fun hpx => hx.2 ⟨hpx, hx.1.2.trans_lt hab⟩⟩)
          measure_Icc_lt_top.ne) (measureReal_mono sdiff_subset measure_Icc_lt_top.ne)))
    rw [Real.volume_real_Icc_of_le hpl.1, Real.volume_real_Icc_of_le (by linarith)] at hbound
    linarith
  · have hbound := hlength.trans
      ((hU.positive_middle_measure_le_outer_without_top hheight hAff hpA hpTop).trans
        (add_le_add (measureReal_mono sdiff_subset measure_Icc_lt_top.ne)
          (measureReal_mono (s₂ := Icc p.1 (horizontalRight U)) (fun x hx =>
            ⟨le_of_not_gt fun hpx => hx.2 ⟨hab.trans_le hx.1.1, hpx⟩, hx.1.2⟩)
            measure_Icc_lt_top.ne)))
    rw [Real.volume_real_Icc_of_le (by linarith), Real.volume_real_Icc_of_le hpl.2] at hbound
    linarith

end AmbidextrousSofa
