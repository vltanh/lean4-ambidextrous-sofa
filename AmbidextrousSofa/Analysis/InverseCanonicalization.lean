module

public import AmbidextrousSofa.Analysis.Chord
public import AmbidextrousSofa.Analysis.EndpointPressure
public import AmbidextrousSofa.Analysis.CapTranslation
public import AmbidextrousSofa.Reference.Value

@[expose] public section

/-!
# Recovering the original cap from its reference canonicalization

Middle chord clipping is not injective even when it preserves score. The
inverse at the reference uses its actual geometry. A positive extrusion
strictly increases the score whenever the final barrier is smaller than
the extrusion height at a middle-window point. The reference barrier is
zero at its middle endpoints, so an equal-score extrusion to the reference
must have height zero. The reference middle roof is then one, forcing the
original roof to agree there as well as on the unchanged exterior wings.

These are statements about the actual cap operations. The final inverse
lemma does not assume a universal cap bound: the original score, the proved
reference value, and monotonicity of the two concrete operations determine
their intermediate scores.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem IsDownwardCap.verticalExtrusion_zero {U : Set Plane} (hU : IsDownwardCap U) :
    verticalExtrusion U 0 = U := by
  apply Set.Subset.antisymm
  · intro p hp
    obtain ⟨hp0, q, hq, hqx, hpy⟩ := (mem_verticalExtrusion_iff U 0 p).mp hp
    have h := hU.downward q hq p.2 hp0 (by simpa only [add_zero] using hpy)
    simpa only [hqx, Prod.mk.eta] using h
  · exact hU.subset_verticalExtrusion le_rfl

/-- The charged exterior roof gains exactly the extrusion height. If the
final full barrier has not gained that much at even one middle point,
continuity makes the total score increase strict. The point may be either
endpoint of the middle interval. -/
theorem IsDownwardCap.capScore_lt_verticalExtrusion_of_middle_barrier_lt
    {U : Set Plane} (hU : IsDownwardCap U) {ε x₀ : ℝ} (hε : 0 ≤ ε)
    (hheight : ∀ p ∈ U, p.2 + ε ≤ 1) (hwidth : 0 < capWidth U)
    (hx₀ : x₀ ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U))
    (hsmall : partialBarrier (verticalExtrusion U ε) (Real.pi / 2) x₀ < ε) :
    capScore U (Real.pi / 2) < capScore (verticalExtrusion U ε) (Real.pi / 2) := by
  let V := verticalExtrusion U ε
  let l := horizontalLeft U
  let r := horizontalRight U
  let a := l + (r - l) / 4
  let b := r - (r - l) / 4
  have hV : IsDownwardCap V := hU.isDownwardCap_verticalExtrusion hε hheight
  have hproj : horizontalProjection V = horizontalProjection U :=
    hU.horizontalProjection_verticalExtrusion hε
  have hleft : horizontalLeft V = l := congrArg sInf hproj
  have hright : horizontalRight V = r := congrArg sSup hproj
  have hlr : l < r := by change 0 < r - l at hwidth; linarith
  have hla : l < a := by dsimp [a]; linarith
  have hab : a < b := by dsimp [a, b]; linarith
  have hbr : b < r := by dsimp [b]; linarith
  have hcU : ContinuousOn (capRoof U) (Icc l r) := by
    rw [← horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
    exact hU.continuousOn_capRoof
  have houter (s t : ℝ) (hs : l ≤ s) (hst : s ≤ t) (ht : t ≤ r) :
      (∫ x in s..t, capRoof V x) = (∫ x in s..t, capRoof U x) + (t - s) * ε := by
    calc
      (∫ x in s..t, capRoof V x) = ∫ x in s..t, capRoof U x + ε := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hst] at hx
        apply hU.capRoof_verticalExtrusion hε
        rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
        exact ⟨hs.trans hx.1, hx.2.trans ht⟩
      _ = (∫ x in s..t, capRoof U x) + (t - s) * ε := by
        rw [intervalIntegral.integral_add
          ((hcU.mono (Icc_subset_Icc hs ht)).intervalIntegrable_of_Icc hst)
          intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul]
  have hbarrierU := hU.continuous_partialBarrier_pi_div_two
  have hbarrierV := hV.continuous_partialBarrier_pi_div_two
  have hstrict : (∫ x in a..b, partialBarrier V (Real.pi / 2) x) <
      ∫ x in a..b, partialBarrier U (Real.pi / 2) x + ε := by
    apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      hab hbarrierV.continuousOn (hbarrierU.add continuous_const).continuousOn
    · intro x _
      exact hU.partialBarrier_verticalExtrusion_le hε (by linarith [Real.pi_pos]) le_rfl x
    · refine ⟨x₀, hx₀, ?_⟩
      exact hsmall.trans_le (le_add_of_nonneg_left (partialBarrier_nonneg U _ x₀))
  rw [intervalIntegral.integral_add (hbarrierU.intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul] at hstrict
  rw [hU.capScore_eq_intervalSpatialScore, hV.capScore_eq_intervalSpatialScore,
    hleft, hright]
  change (∫ x in l..a, capRoof U x) + (∫ x in b..r, capRoof U x) -
      (∫ x in a..b, partialBarrier U (Real.pi / 2) x) <
    (∫ x in l..a, capRoof V x) + (∫ x in b..r, capRoof V x) -
      (∫ x in a..b, partialBarrier V (Real.pi / 2) x)
  rw [houter l a le_rfl hla.le (hab.le.trans hbr.le),
    houter b r (hla.le.trans hab.le) hbr.le le_rfl]
  have hlength : (a - l) * ε + (r - b) * ε = (b - a) * ε := by
    dsimp [a, b]
    ring
  linarith

/-- Equal-score extrusion to an actual translated reference cap has height
zero. This uses the zero reference niche at a middle endpoint, not a
general claim that extrusion is strictly score improving. -/
theorem IsDownwardCap.verticalExtrusion_eq_reference_of_score_eq
    {U : Set Plane} (hU : IsDownwardCap U) {ε c : ℝ} (hε : 0 ≤ ε)
    (hheight : ∀ p ∈ U, p.2 + ε ≤ 1)
    (href : verticalExtrusion U ε = AmbidextrousSofa.horizontalTranslate Reference.referenceCap c)
    (hscore : capScore U (Real.pi / 2) =
      capScore (verticalExtrusion U ε) (Real.pi / 2)) :
    ε = 0 ∧ U = AmbidextrousSofa.horizontalTranslate Reference.referenceCap c := by
  have hproj := hU.horizontalProjection_verticalExtrusion hε
  have hleft : horizontalLeft U = horizontalLeft Reference.referenceCap + c := by
    have h : horizontalLeft (verticalExtrusion U ε) = horizontalLeft U := congrArg sInf hproj
    rw [href, horizontalLeft_horizontalTranslate Reference.isDownwardCap_referenceCap] at h
    exact h.symm
  have hright : horizontalRight U = horizontalRight Reference.referenceCap + c := by
    have h : horizontalRight (verticalExtrusion U ε) = horizontalRight U := congrArg sSup hproj
    rw [href, horizontalRight_horizontalTranslate Reference.isDownwardCap_referenceCap] at h
    exact h.symm
  have hwidth : 0 < capWidth U := by
    unfold capWidth
    rw [hleft, hright, Reference.horizontalLeft_referenceCap,
      Reference.horizontalRight_referenceCap]
    linarith [Reference.A_pos]
  have hpoint : Reference.topLeft + c ∈
      middleHalfInterval (horizontalLeft U) (horizontalRight U) := by
    rw [hleft, hright, middleHalfInterval_add, Reference.middleHalfInterval_referenceCap]
    exact ⟨Reference.topLeft, ⟨le_rfl, Reference.topLeft_lt_topRight.le⟩, rfl⟩
  have hzero : partialBarrier (verticalExtrusion U ε) (Real.pi / 2)
      (Reference.topLeft + c) = 0 := by
    rw [href, partialBarrier_horizontalTranslate Reference.isDownwardCap_referenceCap,
      add_sub_cancel_right, Reference.isDownwardCap_referenceCap.partialBarrier_pi_div_two,
      Reference.sweptNiche_referenceCap]
    exact Reference.referenceNiche_eq_zero_of_le_topLeft le_rfl
  have hεzero : ε = 0 := by
    apply le_antisymm _ hε
    by_contra h
    have hpos : 0 < ε := lt_of_not_ge h
    have hstrict := hU.capScore_lt_verticalExtrusion_of_middle_barrier_lt hε hheight
      hwidth hpoint (by rwa [hzero])
    linarith
  refine ⟨hεzero, ?_⟩
  simpa only [hεzero, hU.verticalExtrusion_zero] using href

/-- If the middle chord has roof one on the entire middle window, clipping
has removed no actual cap point. Exterior roofs agree by the chord lemma;
the original unit-strip ceiling forces agreement on the middle as well. -/
theorem IsDownwardCap.eq_middleChordCap_of_middle_roof_one {U : Set Plane}
    (hU : IsDownwardCap U) (hwidth : 0 < capWidth U)
    (hroof : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof (middleChordCap U) x = 1) : U = middleChordCap U := by
  have hV := hU.isDownwardCap_middleChordCap hwidth
  have hproj := hU.horizontalProjection_middleChordCap hwidth
  obtain ⟨ha, hb, hab⟩ := hU.middleChord_endpoints hwidth
  apply hU.eq_of_projection_eq_of_capRoof_eq hV hproj.symm
  funext x
  by_cases hx : x ∈ horizontalProjection U
  · by_cases hmiddle : x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U)
    · rw [hroof x hmiddle]
      apply le_antisymm (capRoof_le_one hU.isCompact hU.inStrip x)
      have hmono := hV.capRoof_mono hU (capCut_subset _ _) x
      rwa [hroof x hmiddle] at hmono
    · exact (hU.capRoof_chordCap_outside ha hb hab hx hmiddle).symm
  · rw [capRoof_eq_zero_of_not_mem hx, capRoof_eq_zero_of_not_mem]
    rwa [hproj]

/-- The literal reference inverse for any original full-score equality cap.
The only reference-identification input concerns the actual canonicalized
cap. No universal bound or optimizer-selection certificate is assumed. -/
theorem IsDownwardCap.eq_reference_of_heightSaturation_middleChordCap_eq
    {U : Set Plane} (hU : IsDownwardCap U) (hwidth : 0 < capWidth U) {c : ℝ}
    (hscore : capScore U (Real.pi / 2) = M / 2)
    (href : heightSaturation (middleChordCap U) =
      AmbidextrousSofa.horizontalTranslate Reference.referenceCap c) :
    U = AmbidextrousSofa.horizontalTranslate Reference.referenceCap c := by
  let V := middleChordCap U
  have hV : IsDownwardCap V := hU.isDownwardCap_middleChordCap hwidth
  have hα0 : 0 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hcanonical : capScore (heightSaturation V) (Real.pi / 2) = M / 2 := by
    rw [href, capScore_horizontalTranslate Reference.isDownwardCap_referenceCap,
      Reference.capScore_referenceCap]
  have hbefore := hU.capScore_le_middleChordCap hwidth hα0 le_rfl
  have hafter := hV.capScore_le_heightSaturation hα0 le_rfl
  have hsame : capScore V (Real.pi / 2) = capScore (heightSaturation V) (Real.pi / 2) := by
    rw [hscore] at hbefore
    rw [hcanonical]
    exact le_antisymm (hcanonical ▸ hafter) hbefore
  obtain ⟨hε, hVref⟩ := hV.verticalExtrusion_eq_reference_of_score_eq
    (sub_nonneg.mpr hV.capHeight_le_one)
    (fun p hp => by linarith [hV.snd_le_capHeight hp]) href hsame
  have hproj : horizontalProjection V = horizontalProjection U :=
    hU.horizontalProjection_middleChordCap hwidth
  have hleft : horizontalLeft U = horizontalLeft Reference.referenceCap + c := by
    have h : horizontalLeft V = horizontalLeft U := congrArg sInf hproj
    rw [hVref, horizontalLeft_horizontalTranslate Reference.isDownwardCap_referenceCap] at h
    exact h.symm
  have hright : horizontalRight U = horizontalRight Reference.referenceCap + c := by
    have h : horizontalRight V = horizontalRight U := congrArg sSup hproj
    rw [hVref, horizontalRight_horizontalTranslate Reference.isDownwardCap_referenceCap] at h
    exact h.symm
  have hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof (middleChordCap U) x = 1 := by
    intro x hx
    rw [hleft, hright, middleHalfInterval_add, Reference.middleHalfInterval_referenceCap] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    change capRoof V (y + c) = 1
    rw [hVref, capRoof_horizontalTranslate, add_sub_cancel_right]
    exact Reference.capRoof_referenceCap_eq_one hy
  exact (hU.eq_middleChordCap_of_middle_roof_one hwidth hmiddle).trans hVref

end AmbidextrousSofa
