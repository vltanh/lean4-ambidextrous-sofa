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
  refine Subset.antisymm (fun p hp => ?_) (hU.subset_verticalExtrusion le_rfl)
  obtain ⟨hp0, q, hq, hqx, hpy⟩ := (mem_verticalExtrusion_iff U 0 p).mp hp
  simpa only [hqx, Prod.mk.eta] using
    hU.downward q hq p.2 hp0 (by simpa only [add_zero] using hpy)

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
  have hV := hU.isDownwardCap_verticalExtrusion hε hheight
  have hproj := hU.horizontalProjection_verticalExtrusion hε
  have hIcc := hU.horizontalProjection_eq_Icc
  have hcU := hU.continuousOn_capRoof_Icc
  set l := horizontalLeft U
  set r := horizontalRight U
  have hlr : l < r := sub_pos.mp hwidth
  have houter (s t : ℝ) (hs : l ≤ s) (hst : s ≤ t) (ht : t ≤ r) :
      (∫ x in s..t, capRoof (verticalExtrusion U ε) x) =
        (∫ x in s..t, capRoof U x) + (t - s) * ε := by
    rw [intervalIntegral.integral_congr (g := fun x => capRoof U x + ε) fun x hx =>
        hU.capRoof_verticalExtrusion hε (hIcc ▸ Icc_subset_Icc hs ht (uIcc_of_le hst ▸ hx)),
      intervalIntegral.integral_add ((hcU.mono (Icc_subset_Icc hs ht)).intervalIntegrable_of_Icc
        hst) intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul]
  have hbU := hU.continuous_partialBarrier_pi_div_two
  have hstrict : (∫ x in (l + (r - l) / 4)..(r - (r - l) / 4),
      partialBarrier (verticalExtrusion U ε) (Real.pi / 2) x) <
        ∫ x in (l + (r - l) / 4)..(r - (r - l) / 4), partialBarrier U (Real.pi / 2) x + ε :=
    intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt (by linarith)
    hV.continuous_partialBarrier_pi_div_two.continuousOn (hbU.add continuous_const).continuousOn
    (fun x _ => hU.partialBarrier_verticalExtrusion_le hε (by positivity) le_rfl x)
    ⟨x₀, hx₀, hsmall.trans_le (le_add_of_nonneg_left (partialBarrier_nonneg U _ x₀))⟩
  rw [intervalIntegral.integral_add (hbU.intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul] at hstrict
  rw [hU.capScore_eq_intervalSpatialScore, hV.capScore_eq_intervalSpatialScore,
    show horizontalLeft (verticalExtrusion U ε) = l from congrArg sInf hproj,
    show horizontalRight (verticalExtrusion U ε) = r from congrArg sSup hproj,
    intervalSpatialScore, intervalSpatialScore, houter l _ le_rfl (by linarith) (by linarith),
    houter _ r (by linarith) (by linarith) le_rfl]
  linarith

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
  refine hU.eq_of_projection_eq_of_capRoof_eq hV hproj.symm (funext fun x => ?_)
  by_cases hx : x ∈ horizontalProjection U
  · by_cases hmiddle : x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U)
    · have hmono := hV.capRoof_mono hU (capCut_subset _ _) x
      rw [hroof x hmiddle] at hmono ⊢
      exact le_antisymm (capRoof_le_one hU.isCompact hU.inStrip x) hmono
    · exact (hU.capRoof_chordCap_outside ha hb hab hx hmiddle).symm
  · rw [capRoof_eq_zero_of_not_mem hx, capRoof_eq_zero_of_not_mem (hproj ▸ hx)]

/-- The literal reference inverse for any original full-score equality cap.
The only reference-identification input concerns the actual canonicalized
cap. No universal bound or optimizer-selection certificate is assumed. -/
theorem IsDownwardCap.eq_reference_of_heightSaturation_middleChordCap_eq
    {U : Set Plane} (hU : IsDownwardCap U) (hwidth : 0 < capWidth U) {c : ℝ}
    (hscore : capScore U (Real.pi / 2) = M / 2)
    (href : heightSaturation (middleChordCap U) =
      AmbidextrousSofa.horizontalTranslate Reference.referenceCap c) :
    U = AmbidextrousSofa.horizontalTranslate Reference.referenceCap c := by
  have hR := Reference.isDownwardCap_referenceCap
  set V := middleChordCap U
  have hV : IsDownwardCap V := hU.isDownwardCap_middleChordCap hwidth
  have hε : 0 ≤ 1 - capHeight V := sub_nonneg.mpr hV.capHeight_le_one
  have hheight (p) (hp : p ∈ V) : p.2 + (1 - capHeight V) ≤ 1 := by
    linarith [hV.snd_le_capHeight hp]
  -- The three caps `U`, `V` and the saturation of `V` share their projection.
  have hprojV : horizontalProjection V = horizontalProjection U :=
    hU.horizontalProjection_middleChordCap hwidth
  have hproj : horizontalProjection U = horizontalProjection
      (AmbidextrousSofa.horizontalTranslate Reference.referenceCap c) := by
    rw [← href, heightSaturation, hV.horizontalProjection_verticalExtrusion hε, hprojV]
  have hlV : horizontalLeft V = horizontalLeft U := congrArg sInf hprojV
  have hrV : horizontalRight V = horizontalRight U := congrArg sSup hprojV
  have hmid : middleHalfInterval (horizontalLeft U) (horizontalRight U) =
      (fun x => x + c) '' Reference.topInterval := by
    rw [show horizontalLeft U = _ from
        (congrArg sInf hproj).trans (horizontalLeft_horizontalTranslate hR c),
      show horizontalRight U = _ from
        (congrArg sSup hproj).trans (horizontalRight_horizontalTranslate hR c),
      middleHalfInterval_add, Reference.middleHalfInterval_referenceCap]
  -- Both canonicalization steps keep the score `M / 2`.
  have hsame : capScore V (Real.pi / 2) = capScore (heightSaturation V) (Real.pi / 2) := by
    have hbefore := hU.capScore_le_middleChordCap hwidth (by positivity) le_rfl
    have hafter := hV.capScore_le_heightSaturation (by positivity) le_rfl
    rw [href, capScore_horizontalTranslate hR, Reference.capScore_referenceCap] at hafter ⊢
    exact le_antisymm hafter (hscore ▸ hbefore)
  -- An extrusion of positive height would increase the score.
  have hx₀ : Reference.topLeft + c ∈ middleHalfInterval (horizontalLeft V) (horizontalRight V) := by
    rw [hlV, hrV, hmid]
    exact ⟨_, ⟨le_rfl, Reference.topLeft_lt_topRight.le⟩, rfl⟩
  have hzero : 1 - capHeight V = 0 := by
    refine hε.antisymm' (not_lt.mp fun hpos =>
      (hV.capScore_lt_verticalExtrusion_of_middle_barrier_lt hε hheight
        (by rw [capWidth, hlV, hrV]; exact hwidth) hx₀ ?_).ne hsame)
    rw [← heightSaturation, href, partialBarrier_horizontalTranslate hR, add_sub_cancel_right,
      hR.partialBarrier_pi_div_two, Reference.sweptNiche_referenceCap,
      Reference.referenceNiche_eq_zero_of_le_topLeft le_rfl]
    exact hpos
  have hVref : V = AmbidextrousSofa.horizontalTranslate Reference.referenceCap c := by
    rwa [heightSaturation, hzero, hV.verticalExtrusion_zero] at href
  refine (hU.eq_middleChordCap_of_middle_roof_one hwidth fun x hx => ?_).trans hVref
  obtain ⟨y, hy, rfl⟩ := hmid ▸ hx
  change capRoof V (y + c) = 1
  rw [hVref, capRoof_horizontalTranslate, add_sub_cancel_right]
  exact Reference.capRoof_referenceCap_eq_one hy

end AmbidextrousSofa
