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
  let a := horizontalLeft U + capWidth U / 4
  let b := horizontalRight U - capWidth U / 4
  let m := (capRoof U b - capRoof U a) / (b - a)
  have hV := hU.isDownwardCap_middleChordCap hwidth
  have hproj := hU.horizontalProjection_middleChordCap hwidth
  have hCproj := hV.horizontalProjection_heightSaturation.trans hproj
  obtain ⟨ha, hb, hab⟩ := hU.middleChord_endpoints hwidth
  refine ⟨hV.isDownwardCap_heightSaturation, hCproj, hV.capHeight_heightSaturation,
    m, capRoof U a - m * a + (1 - capHeight (middleChordCap U)), fun x hx => ?_⟩
  rw [horizontalLeft, horizontalRight, fullCanonicalCap, hCproj] at hx
  rw [fullCanonicalCap, heightSaturation, hV.capRoof_verticalExtrusion
    (sub_nonneg.mpr hV.capHeight_le_one)
    (hproj ▸ (convex_horizontalProjection hU.convex).ordConnected.out ha hb hx),
    middleChordCap, hU.capRoof_chordCap_inside ha hb hab hx]
  dsimp [roofChord, m]
  ring

theorem IsDownwardCap.capScore_le_fullCanonicalCap {U : Set Plane}
    (hU : IsDownwardCap U) (hwidth : 0 < capWidth U) :
    capScore U (Real.pi / 2) ≤ capScore (fullCanonicalCap U) (Real.pi / 2) :=
  (hU.capScore_le_middleChordCap hwidth (by positivity) le_rfl).trans
    ((hU.isDownwardCap_middleChordCap hwidth).capScore_le_heightSaturation (by positivity) le_rfl)

theorem IsFullCapMaximizer.fullCanonicalCap {U : Set Plane} (hU : IsFullCapMaximizer U) :
    IsFullCapMaximizer (AmbidextrousSofa.fullCanonicalCap U) :=
  have hwidth := two_pos.trans hU.two_lt_width
  hU.of_score_le (hU.isCap.fullCanonicalCap_data hwidth).1
    (hU.isCap.capScore_le_fullCanonicalCap hwidth)

/-- Once the actual canonical middle is horizontal, the completed
horizontal rigidity and the literal inverse recover the original cap.
The geometric horizontal-middle premise remains explicit here. -/
theorem IsFullCapMaximizer.eq_reference_translate_of_fullCanonicalCap_horizontal
    {U : Set Plane} (hU : IsFullCapMaximizer U)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft (AmbidextrousSofa.fullCanonicalCap U))
      (horizontalRight (AmbidextrousSofa.fullCanonicalCap U)), capRoof (AmbidextrousSofa.fullCanonicalCap U) x = 1) :
    ∃ b : ℝ, U = AmbidextrousSofa.horizontalTranslate Reference.referenceCap b := by
  have hwidth := two_pos.trans hU.two_lt_width
  obtain ⟨b, hb⟩ := hU.fullCanonicalCap.eq_reference_translate_of_horizontal
    (hU.isCap.fullCanonicalCap_data hwidth).2.2.1 hmiddle
  refine ⟨b, hU.isCap.eq_reference_of_heightSaturation_middleChordCap_eq hwidth ?_ hb⟩
  rw [← le_antisymm (hU.2 _ hU.fullCanonicalCap.isCap)
      (hU.isCap.capScore_le_fullCanonicalCap hwidth), hb,
    capScore_horizontalTranslate Reference.isDownwardCap_referenceCap,
    Reference.capScore_referenceCap]

end AmbidextrousSofa
