module

public import AmbidextrousSofa.Analysis.HorizontalRigidity
public import AmbidextrousSofa.Analysis.InverseCanonicalization

@[expose] public section

/-!
# Concrete canonicalization and its inverse at the reference

The canonical cap here is the literal middle-chord cut followed by height
saturation. Its projection, affine middle, height, and maximality are
proved for that exact set, so classifying it applies to every prescribed
original maximum. The previously proved extrusion and chord inverse
then recovers the original cap from its own canonicalization.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

def fullCanonicalCap (U : Set Plane) : Set Plane := heightSaturation (middleChordCap U)

theorem IsDownwardCap.fullCanonicalCap_data {U : Set Plane} (hU : IsDownwardCap U)
    (hwidth : 0 < capWidth U) :
    IsDownwardCap (fullCanonicalCap U) ∧
      horizontalProjection (fullCanonicalCap U) = horizontalProjection U ∧
      capHeight (fullCanonicalCap U) = 1 ∧
      ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft (fullCanonicalCap U))
        (horizontalRight (fullCanonicalCap U)), capRoof (fullCanonicalCap U) x = m * x + c := by
  let V := middleChordCap U
  let a := horizontalLeft U + capWidth U / 4
  let b := horizontalRight U - capWidth U / 4
  let m := (capRoof U b - capRoof U a) / (b - a)
  have hV : IsDownwardCap V := hU.isDownwardCap_middleChordCap hwidth
  have hproj : horizontalProjection V = horizontalProjection U :=
    hU.horizontalProjection_middleChordCap hwidth
  have hCproj : horizontalProjection (fullCanonicalCap U) = horizontalProjection U :=
    hV.horizontalProjection_heightSaturation.trans hproj
  have hleft : horizontalLeft (fullCanonicalCap U) = horizontalLeft U := congrArg sInf hCproj
  have hright : horizontalRight (fullCanonicalCap U) = horizontalRight U := congrArg sSup hCproj
  obtain ⟨ha, hb, hab⟩ := hU.middleChord_endpoints hwidth
  refine ⟨hV.isDownwardCap_heightSaturation, hCproj, hV.capHeight_heightSaturation,
    m, capRoof U a - m * a + (1 - capHeight V), ?_⟩
  intro x hx
  rw [hleft, hright] at hx
  have hxU : x ∈ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
    exact middleHalfInterval_subset
      (horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact) hx
  have hxV : x ∈ horizontalProjection V := by rwa [hproj]
  change capRoof (heightSaturation V) x = _
  rw [heightSaturation,
    hV.capRoof_verticalExtrusion (sub_nonneg.mpr hV.capHeight_le_one) hxV]
  have hchord : capRoof V x = roofChord (capRoof U) a b x :=
    hU.capRoof_chordCap_inside ha hb hab hx
  rw [hchord]
  dsimp [roofChord, m]
  ring

theorem IsDownwardCap.capScore_le_fullCanonicalCap {U : Set Plane}
    (hU : IsDownwardCap U) (hwidth : 0 < capWidth U) {α : ℝ}
    (hα0 : 0 < α) (hαL : α ≤ Real.pi / 2) :
    capScore U α ≤ capScore (fullCanonicalCap U) α :=
  (hU.capScore_le_middleChordCap hwidth hα0 hαL).trans
    ((hU.isDownwardCap_middleChordCap hwidth).capScore_le_heightSaturation hα0 hαL)

theorem IsFullCapMaximizer.fullCanonicalCap {U : Set Plane} (hU : IsFullCapMaximizer U) :
    IsFullCapMaximizer (AmbidextrousSofa.fullCanonicalCap U) := by
  have hwidth : 0 < capWidth U := lt_trans (by norm_num) hU.two_lt_width
  exact hU.of_score_le (hU.isCap.fullCanonicalCap_data hwidth).1
    (hU.isCap.capScore_le_fullCanonicalCap hwidth (by linarith only [Real.pi_pos]) le_rfl)

theorem IsFullCapMaximizer.capScore_fullCanonicalCap {U : Set Plane} (hU : IsFullCapMaximizer U) :
    capScore (AmbidextrousSofa.fullCanonicalCap U) (Real.pi / 2) = capScore U (Real.pi / 2) := by
  have hwidth : 0 < capWidth U := lt_trans (by norm_num) hU.two_lt_width
  exact le_antisymm (hU.2 _ hU.fullCanonicalCap.isCap)
    (hU.isCap.capScore_le_fullCanonicalCap hwidth (by linarith only [Real.pi_pos]) le_rfl)

/-- Classification of this exact canonical cap recovers the prescribed
original maximum. Its original score is derived from maximality. -/
theorem IsFullCapMaximizer.eq_reference_of_fullCanonicalCap_eq
    {U : Set Plane} (hU : IsFullCapMaximizer U) {b : ℝ}
    (href : AmbidextrousSofa.fullCanonicalCap U = AmbidextrousSofa.horizontalTranslate Reference.referenceCap b) :
    U = AmbidextrousSofa.horizontalTranslate Reference.referenceCap b := by
  have hwidth : 0 < capWidth U := lt_trans (by norm_num) hU.two_lt_width
  have hscore : capScore U (Real.pi / 2) = M / 2 := by
    rw [← hU.capScore_fullCanonicalCap, href,
      capScore_horizontalTranslate Reference.isDownwardCap_referenceCap,
      Reference.capScore_referenceCap]
  exact hU.isCap.eq_reference_of_heightSaturation_middleChordCap_eq hwidth hscore href

/-- Once the actual canonical middle is horizontal, the completed
horizontal rigidity and the literal inverse recover the original cap.
The geometric horizontal-middle premise remains explicit here. -/
theorem IsFullCapMaximizer.eq_reference_translate_of_fullCanonicalCap_horizontal
    {U : Set Plane} (hU : IsFullCapMaximizer U)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft (AmbidextrousSofa.fullCanonicalCap U))
      (horizontalRight (AmbidextrousSofa.fullCanonicalCap U)), capRoof (AmbidextrousSofa.fullCanonicalCap U) x = 1) :
    ∃ b : ℝ, U = AmbidextrousSofa.horizontalTranslate Reference.referenceCap b := by
  have hwidth : 0 < capWidth U := lt_trans (by norm_num) hU.two_lt_width
  have hheight := (hU.isCap.fullCanonicalCap_data hwidth).2.2.1
  obtain ⟨b, hb⟩ := hU.fullCanonicalCap.eq_reference_translate_of_horizontal hheight hmiddle
  exact ⟨b, hU.eq_reference_of_fullCanonicalCap_eq hb⟩

end AmbidextrousSofa
