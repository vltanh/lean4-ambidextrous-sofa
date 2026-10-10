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
  let l := horizontalLeft U
  let r := horizontalRight U
  let a := l + capWidth U / 4
  let b := r - capWidth U / 4
  have hw : 0 < capWidth U := lt_trans (by norm_num) hU.two_lt_width
  obtain ⟨ha, hb, hab⟩ := hU.isCap.middleChord_endpoints hw
  have hla : l ≤ a := by dsimp [l, a]; linarith only [hw]
  have hbr : b ≤ r := by dsimp [r, b]; linarith only [hw]
  have hA : capRoof U a = 1 := hmiddle a ⟨le_rfl, hab.le⟩
  have hB : capRoof U b = 1 := hmiddle b ⟨hab.le, le_rfl⟩
  have hpA : (a, 1) ∈ U := by
    have h := capRoof_mem hU.isCap.isCompact (show a ∈ horizontalProjection U from ha)
    rwa [hA] at h
  have hpB : (b, 1) ∈ U := by
    have h := capRoof_mem hU.isCap.isCompact (show b ∈ horizontalProjection U from hb)
    rwa [hB] at h
  have hpTop : (p.1, 1) ∈ U := by simpa only [← hpone, Prod.mk.eta] using hp
  have hpBounds : p.1 ∈ Icc l r := by
    rw [← horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex]
    exact ⟨p, hp, rfl⟩
  have hAff : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval
      (horizontalLeft U) (horizontalRight U), capRoof U x = m * x + c :=
    ⟨0, 1, fun x hx => by simpa only [zero_mul, zero_add] using hmiddle x hx⟩
  have hpos := hU.isCap.sweptNiche_pos_on_open_middle_of_unit_endpoints
    hU.two_lt_width hA hB
  have hlength : b - a ≤ volume.real
      (middleHalfInterval (horizontalLeft U) (horizontalRight U) ∩
        {x : ℝ | 0 < sweptNiche U (Real.pi / 2) x}) := by
    rw [← Real.volume_real_Ioo_of_le hab.le]
    apply measureReal_mono
    · intro x hx
      exact ⟨⟨hx.1.le, hx.2.le⟩, hpos x hx⟩
    · exact measure_ne_top_of_subset inter_subset_left
        (by change volume (Icc a b) ≠ ⊤; rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hfinite (u v : ℝ) : volume (Icc u v) ≠ ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  change a ≤ p.1 ∧ p.1 ≤ b
  constructor
  · by_contra h
    have hpa : p.1 < a := lt_of_not_ge h
    have hmoment := hU.positive_middle_measure_le_outer_without_top hheight hAff hpTop hpB
    have hleft : volume.real (Icc l a \ Ioo p.1 b) ≤ volume.real (Icc l p.1) := by
      apply measureReal_mono _ (hfinite l p.1)
      intro x hx
      refine ⟨hx.1.1, ?_⟩
      by_contra hpx
      exact hx.2 ⟨lt_of_not_ge hpx, hx.1.2.trans_lt hab⟩
    have hright : volume.real (Icc b r \ Ioo p.1 b) ≤ volume.real (Icc b r) :=
      measureReal_mono sdiff_subset (hfinite b r)
    have hbound := hlength.trans (hmoment.trans (add_le_add hleft hright))
    rw [Real.volume_real_Icc_of_le hpBounds.1, Real.volume_real_Icc_of_le hbr] at hbound
    dsimp [a, b, l, r, capWidth] at hbound hpa
    linarith only [hbound, hpa]
  · by_contra h
    have hbp : b < p.1 := lt_of_not_ge h
    have hmoment := hU.positive_middle_measure_le_outer_without_top hheight hAff hpA hpTop
    have hleft : volume.real (Icc l a \ Ioo a p.1) ≤ volume.real (Icc l a) :=
      measureReal_mono sdiff_subset (hfinite l a)
    have hright : volume.real (Icc b r \ Ioo a p.1) ≤ volume.real (Icc p.1 r) := by
      apply measureReal_mono _ (hfinite p.1 r)
      intro x hx
      refine ⟨?_, hx.1.2⟩
      by_contra hpx
      exact hx.2 ⟨hab.trans_le hx.1.1, lt_of_not_ge hpx⟩
    have hbound := hlength.trans (hmoment.trans (add_le_add hleft hright))
    rw [Real.volume_real_Icc_of_le hla, Real.volume_real_Icc_of_le hpBounds.2] at hbound
    dsimp [a, b, l, r, capWidth] at hbound hbp
    linarith only [hbound, hbp]

/-- The literal top support face projects onto precisely the entire
middle interval of an actual horizontal canonical full maximum. -/
theorem IsFullCapMaximizer.horizontalProjection_top_supportFace
    {U : Set Plane} (hU : IsFullCapMaximizer U) (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = 1) :
    horizontalProjection (supportFace U (0, 1)) =
      middleHalfInterval (horizontalLeft U) (horizontalRight U) := by
  have hsupport : support U (0, 1) = 1 := hheight
  apply Subset.antisymm
  · rintro x ⟨p, hp, rfl⟩
    have hpone : p.2 = 1 := by
      simpa only [Set.mem_ofPred_eq, coordDot, mul_zero, mul_one, zero_add, hsupport] using hp.2
    exact hU.top_abscissa_mem_middle hheight hmiddle hp.1 hpone
  · intro x hx
    have hxU : x ∈ horizontalProjection U := by
      rw [horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex]
      exact middleHalfInterval_subset
        (horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact) hx
    refine ⟨(x, capRoof U x), ⟨capRoof_mem hU.isCap.isCompact hxU, ?_⟩, rfl⟩
    simp only [Set.mem_ofPred_eq, coordDot, mul_zero, mul_one, zero_add, hsupport, hmiddle x hx]

/-- All middle slopes are covered, including the horizontal case whose
top atom cannot be handled by the nonhorizontal trimming variation. -/
theorem IsFullCapMaximizer.horizontalProjection_middle_supportFace_at_height_one
    {U : Set Plane} (hU : IsFullCapMaximizer U) (hheight : capHeight U = 1)
    {m c : ℝ} (haffine : ∀ x ∈ middleHalfInterval
      (horizontalLeft U) (horizontalRight U), capRoof U x = m * x + c) :
    horizontalProjection (supportFace U (-m, 1)) =
      middleHalfInterval (horizontalLeft U) (horizontalRight U) := by
  by_cases hm : m = 0
  · subst m
    have hright : capRoof U (horizontalRight U - capWidth U / 4) = 1 :=
      hU.middle_right_eq_one_of_affine_nonneg hheight (le_refl 0) haffine
    have hw : 0 < capWidth U := lt_trans (by norm_num) hU.two_lt_width
    obtain ⟨_, _, hab⟩ := hU.isCap.middleChord_endpoints hw
    have hc : c = 1 := by
      have h := haffine (horizontalRight U - capWidth U / 4) ⟨hab.le, le_rfl⟩
      simpa only [zero_mul, zero_add, hright] using h.symm
    have hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
        capRoof U x = 1 := by
      intro x hx
      simpa only [zero_mul, zero_add, hc] using haffine x hx
    simpa only [neg_zero] using hU.horizontalProjection_top_supportFace hheight hmiddle
  · exact hU.horizontalProjection_middle_supportFace hm haffine

end AmbidextrousSofa
