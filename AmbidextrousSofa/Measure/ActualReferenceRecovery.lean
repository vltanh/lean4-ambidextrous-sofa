import AmbidextrousSofa.Analysis.CapNormalization
import AmbidextrousSofa.Measure.CapAssembly
import AmbidextrousSofa.Reference.Regularity
import AmbidextrousSofa.Reference.Value

/-!
# Literal recovery from the two original reference caps

Both caps are formed from the original hull. Their common horizontal
projection forces their reference translations to coincide. Their
intersection recovers that original hull, and the original angular
constraints place the body inside the same translated reference sofa.
Finite equal area and the independently proved regular closedness of the
reference then recover the entire original compact set, including its
boundary. No canonical replacement is substituted for that set.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem hullCaps_reference_translations_eq {S : Set Plane} (hstrip : S ⊆ unitStrip)
    {a b : ℝ}
    (hU : upperHullCap S = horizontalTranslate Reference.referenceCap a)
    (hV : reflectedHullCap S = horizontalTranslate Reference.referenceCap b) : a = b := by
  have hright := congrArg sSup (hullCaps_same_horizontalProjection hstrip)
  change horizontalRight (upperHullCap S) = horizontalRight (reflectedHullCap S) at hright
  rw [hU, hV, horizontalRight_horizontalTranslate Reference.isDownwardCap_referenceCap,
    horizontalRight_horizontalTranslate Reference.isDownwardCap_referenceCap] at hright
  linarith only [hright]

/-- Equality of both actual caps determines the actual hull, with no
compression or independent cap replacement. -/
theorem actualHull_eq_reference_translate_of_hullCaps_eq
    {S : Set Plane} (hstrip : S ⊆ unitStrip) {b : ℝ}
    (hU : upperHullCap S = horizontalTranslate Reference.referenceCap b)
    (hV : reflectedHullCap S = horizontalTranslate Reference.referenceCap b) :
    actualHull S = horizontalTranslate Reference.referenceHull b := by
  rw [actualHull_eq_inter_hullCaps hstrip, hU, hV, Reference.referenceHull_eq_inter_caps]
  ext p
  simp only [mem_inter_iff, mem_horizontalTranslate_iff, mem_image_reflect, reflect]

/-- The two whole-quarter passage constraints cut the original set down
to the actual reference sofa inside the already identified original hull. -/
theorem subset_referenceSofa_translate_of_hullCaps_eq
    {S : Set Plane} (hstrip : S ⊆ unitStrip) {b : ℝ}
    (hU : upperHullCap S = horizontalTranslate Reference.referenceCap b)
    (hV : reflectedHullCap S = horizontalTranslate Reference.referenceCap b)
    (hα : AngularConstraints S (upperHullCap S) (Real.pi / 2))
    (hγ : AngularConstraints (reflect '' S) (reflectedHullCap S) (Real.pi / 2)) :
    S ⊆ horizontalTranslate Reference.referenceSofa b := by
  have hHull := actualHull_eq_reference_translate_of_hullCaps_eq hstrip hU hV
  intro p hp
  rw [mem_horizontalTranslate_iff]
  have hK := subset_actualHull S hp
  rw [hHull, mem_horizontalTranslate_iff] at hK
  have hnU := hα.partialBarrier_le hstrip hp
  have hnV := hγ.partialBarrier_le (image_reflect_subset_unitStrip hstrip)
    (mem_image_of_mem reflect hp)
  rw [hU, partialBarrier_horizontalTranslate Reference.isDownwardCap_referenceCap,
    Reference.isDownwardCap_referenceCap.partialBarrier_pi_div_two,
    Reference.sweptNiche_referenceCap] at hnU
  rw [hV, partialBarrier_horizontalTranslate Reference.isDownwardCap_referenceCap,
    Reference.isDownwardCap_referenceCap.partialBarrier_pi_div_two,
    Reference.sweptNiche_referenceCap] at hnV
  exact ⟨hK, hnU, hnV⟩

/-- Equal area upgrades reference containment to literal compact-set
equality. Regular closedness is used for the larger reference set. -/
theorem eq_referenceSofa_translate_of_subset_of_volumeReal_eq
    {S : Set Plane} (hS : IsCompact S) {b : ℝ}
    (hsub : S ⊆ horizontalTranslate Reference.referenceSofa b)
    (harea : volume.real S = M) : S = horizontalTranslate Reference.referenceSofa b := by
  let T := horizontalTranslate S (-b)
  have hT : IsCompact T := hS.image (by fun_prop)
  have hTsub : T ⊆ Reference.referenceSofa := by
    rintro p ⟨q, hq, rfl⟩
    have hq' := hsub hq
    rw [mem_horizontalTranslate_iff] at hq'
    change (q.1 + -b, q.2 + 0) ∈ Reference.referenceSofa
    simpa only [add_zero, sub_eq_add_neg] using hq'
  have hTarea : volume.real T = M := by
    simpa only [T, horizontalTranslate, Measure.real, volume_image_translate] using harea
  have hmeasure : volume T = volume Reference.referenceSofa := by
    calc
      _ = ENNReal.ofReal (volume.real T) := (ENNReal.ofReal_toReal hT.measure_ne_top).symm
      _ = ENNReal.ofReal M := congrArg ENNReal.ofReal hTarea
      _ = _ := Reference.volume_referenceSofa.symm
  have heq := eq_of_subset_of_measure_eq_of_isCompact_regularClosed volume hT.isClosed
    Reference.isCompact_referenceSofa Reference.closure_interior_referenceSofa hTsub hmeasure
  have hinv := congrArg (fun R : Set Plane => horizontalTranslate R b) heq
  simpa only [T, horizontalTranslate_add, neg_add_cancel, horizontalTranslate_zero] using hinv

/-- This recovers the original compact body from classification of its
own two caps. The two translations are aligned by their actual common
projection, rather than assumed equal. -/
theorem eq_referenceSofa_translate_of_actual_caps
    {S : Set Plane} (hS : IsCompact S) (hstrip : S ⊆ unitStrip)
    (hα : AngularConstraints S (upperHullCap S) (Real.pi / 2))
    (hγ : AngularConstraints (reflect '' S) (reflectedHullCap S) (Real.pi / 2))
    (hU : ∃ a : ℝ, upperHullCap S = horizontalTranslate Reference.referenceCap a)
    (hV : ∃ b : ℝ, reflectedHullCap S = horizontalTranslate Reference.referenceCap b)
    (harea : volume.real S = M) :
    ∃ b : ℝ, actualHull S = horizontalTranslate Reference.referenceHull b ∧
      S = horizontalTranslate Reference.referenceSofa b := by
  obtain ⟨a, ha⟩ := hU
  obtain ⟨b, hb⟩ := hV
  have hab := hullCaps_reference_translations_eq hstrip ha hb
  subst b
  exact ⟨a, actualHull_eq_reference_translate_of_hullCaps_eq hstrip ha hb,
    eq_referenceSofa_translate_of_subset_of_volumeReal_eq hS
      (subset_referenceSofa_translate_of_hullCaps_eq hstrip ha hb hα hγ) harea⟩

/-- The exact physical deficit transfers equality of the original body
to both of its original scalar caps and to both nonnegative geometric
losses, once their individual scalar ceilings have been established. -/
theorem actual_cap_equality_deficits
    {S : Set Plane} (hS : IsCompact S) (hconn : IsConnected S) (hstrip : S ⊆ unitStrip)
    {α γ : ℝ}
    (hα : AngularConstraints S (upperHullCap S) α)
    (hγ : AngularConstraints (reflect '' S) (reflectedHullCap S) γ)
    (hU : capScore (upperHullCap S) α ≤ M / 2)
    (hV : capScore (reflectedHullCap S) γ ≤ M / 2)
    (harea : volume.real S = M) :
    capScore (upperHullCap S) α = M / 2 ∧
      capScore (reflectedHullCap S) γ = M / 2 ∧
      actualPartitionDefect S α γ = 0 ∧
      volume.real (actualCapEnvelope S α γ \ S) = 0 := by
  have hidentity := actual_cap_four_term_deficit M hS hconn hstrip hα hγ
  rw [harea] at hidentity
  have hpartition := actualPartitionDefect_nonneg S α γ
  have hmissing : 0 ≤ volume.real (actualCapEnvelope S α γ \ S) := ENNReal.toReal_nonneg
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith only [hidentity, hpartition, hmissing, hU, hV]

end AmbidextrousSofa
