module

public import AmbidextrousSofa.Analysis.CapNormalization
public import AmbidextrousSofa.Measure.CapAssembly
public import AmbidextrousSofa.Reference.Regularity
public import AmbidextrousSofa.Reference.Value

@[expose] public section

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

/-- Equal area upgrades reference containment to literal compact-set
equality. Regular closedness is used for the larger reference set. -/
theorem eq_referenceSofa_translate_of_subset_of_volumeReal_eq
    {S : Set Plane} (hS : IsCompact S) {b : ℝ}
    (hsub : S ⊆ horizontalTranslate Reference.referenceSofa b)
    (harea : volume.real S = M) : S = horizontalTranslate Reference.referenceSofa b := by
  have hT : horizontalTranslate S (-b) ⊆ Reference.referenceSofa := fun p hp => by
    simpa [mem_horizontalTranslate_iff] using hsub ((mem_horizontalTranslate_iff _ _ _).1 hp)
  have heq := eq_of_subset_of_measure_eq_of_isCompact_regularClosed volume
    (S := horizontalTranslate S (-b)) (hS.image (by fun_prop)).isClosed
    Reference.isCompact_referenceSofa Reference.closure_interior_referenceSofa hT (by
      rw [horizontalTranslate, volume_image_translate, Reference.volume_referenceSofa, ← harea,
        ofReal_measureReal hS.measure_ne_top])
  rw [← heq, horizontalTranslate_add, neg_add_cancel, horizontalTranslate_zero]

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
  obtain rfl : a = b := by
    have h : horizontalRight (upperHullCap S) = horizontalRight (reflectedHullCap S) :=
      congrArg sSup (hullCaps_same_horizontalProjection hstrip)
    simpa [ha, hb, horizontalRight_horizontalTranslate Reference.isDownwardCap_referenceCap] using h
  -- Equality of both actual caps determines the actual hull.
  have hHull : actualHull S = horizontalTranslate Reference.referenceHull a := by
    rw [actualHull_eq_inter_hullCaps hstrip, ha, hb, Reference.referenceHull_eq_inter_caps]
    ext p
    simp only [mem_inter_iff, mem_horizontalTranslate_iff, mem_image_reflect, reflect]
  -- The two whole-quarter passage constraints cut the body down to the reference sofa.
  refine ⟨a, hHull, eq_referenceSofa_translate_of_subset_of_volumeReal_eq hS (fun p hp => ?_) harea⟩
  have hK := hHull ▸ subset_actualHull S hp
  have hnU := hα.partialBarrier_le hstrip hp
  have hnV := hγ.partialBarrier_le (image_reflect_subset_unitStrip hstrip)
    (mem_image_of_mem reflect hp)
  simp only [ha, hb, partialBarrier_horizontalTranslate Reference.isDownwardCap_referenceCap,
    Reference.isDownwardCap_referenceCap.partialBarrier_pi_div_two,
    Reference.sweptNiche_referenceCap] at hnU hnV
  exact (mem_horizontalTranslate_iff _ _ _).2 ⟨(mem_horizontalTranslate_iff _ _ _).1 hK, hnU, hnV⟩

/-- The exact physical deficit transfers equality of the original body
to both of its original scalar caps and to both nonnegative geometric
losses, once their individual scalar ceilings have been established. -/
theorem actual_cap_equality_deficits
    {S : Set Plane} (hS : IsCompact S) (hconn : IsConnected S) (hstrip : S ⊆ unitStrip) {α γ : ℝ}
    (hα : AngularConstraints S (upperHullCap S) α)
    (hγ : AngularConstraints (reflect '' S) (reflectedHullCap S) γ)
    (hU : capScore (upperHullCap S) α ≤ M / 2)
    (hV : capScore (reflectedHullCap S) γ ≤ M / 2)
    (harea : volume.real S = M) :
    capScore (upperHullCap S) α = M / 2 ∧
      capScore (reflectedHullCap S) γ = M / 2 ∧
      actualPartitionDefect S α γ = 0 ∧
      volume.real (actualCapEnvelope S α γ \ S) = 0 := by
  have h := actual_cap_four_term_deficit M hS hconn hstrip hα hγ
  have h0 := actualPartitionDefect_nonneg S α γ
  have h1 : 0 ≤ volume.real (actualCapEnvelope S α γ \ S) := measureReal_nonneg
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

end AmbidextrousSofa
