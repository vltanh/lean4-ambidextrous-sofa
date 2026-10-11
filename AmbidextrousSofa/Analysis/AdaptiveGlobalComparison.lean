module

public import AmbidextrousSofa.Analysis.AdaptiveGlobalScalar
public import AmbidextrousSofa.Analysis.AdaptiveGlobalValue
public import AmbidextrousSofa.Analysis.AdaptiveTranslation
public import AmbidextrousSofa.Reference.Value

@[expose] public section

/-!
# Global adaptive comparison at every competitive width

The finite stationary family covers all widths from `4/5` to its tail
endpoint by the intermediate value theorem. The explicit tail covers every
larger width. Fixed-trace coercivity compares an arbitrary C1 pair to the
appropriate member. The scalar comparison is strict away from the reference
angle; fixed-trace equality then identifies the actual support functions.

The width restriction is geometric: a set in a unit strip has area at most
twice its half-width, and the reference area exceeds `8/5`.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa.Analysis

/-- A genuine global comparison for all C1 profiles at every competitive
width, with its equality case. There is no optimizer-existence or optimality
hypothesis. -/
theorem adaptiveFunctional_sub_width_le_half_M_of_four_fifths_le
    {u : QuarterPair} {a : ℝ} (hu : u.WidthTraces a) (ha : 4 / 5 ≤ a) :
    adaptiveFunctional u - a ≤ M / 2 ∧
      (adaptiveFunctional u - a = M / 2 → a = 4 / 3 * Reference.A) := by
  by_cases htail : a ≤ familyWidth 0
  · obtain ⟨b, hb, rfl⟩ := exists_familyWidth ha htail
    have hcomp := adaptiveFunctional_le_family_of_widthTraces hb hu
    have hvalue := familyPair_score hb
    have hscalar := familyScore_le_half_M hb
    refine ⟨by linarith, fun heq => ?_⟩
    rw [(familyScore_eq_half_M_iff hb).1 (by linarith), familyWidth_beta]
  · rw [familyWidth_zero, mul_div_assoc', le_div_iff₀ sin_tailAngle0_pos] at htail
    have h := adaptiveFunctional_sub_width_lt_half_M_of_tail (by linarith) hu
    exact ⟨h.le, fun heq => absurd heq h.ne⟩

def centeredReferencePair : QuarterPair :=
  Reference.referencePair.horizontalTranslate (-Reference.k)

theorem centeredReferencePair_widthTraces :
    centeredReferencePair.WidthTraces (4 / 3 * Reference.A) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [centeredReferencePair, QuarterPair.horizontalTranslate, Reference.referencePair,
      Reference.referenceF_zero, Reference.referenceG_zero,
      Reference.referenceF_pi_div_two, Reference.referenceG_pi_div_two,
      Real.cos_zero, Real.sin_zero, Real.cos_pi_div_two, Real.sin_pi_div_two] <;>
    unfold Reference.k <;> ring

theorem adaptiveFunctional_centeredReferencePair :
    adaptiveFunctional centeredReferencePair = M / 2 + 4 / 3 * Reference.A := by
  rw [centeredReferencePair,
    adaptiveFunctional_horizontalTranslate_of_topTraces Reference.referencePair (-Reference.k)
      Reference.referenceF_pi_div_two Reference.referenceG_zero,
    Reference.adaptiveFunctional_reference_eq_M_add_width]
  ring

/-- Centering removes the artificial common-endpoint requirement. The
only width assumption is the explicit, geometrically available `8/5`. -/
theorem adaptiveFunctional_sub_halfWidth_le_half_M (u : QuarterPair)
    (hfL : u.f (Real.pi / 2) = 1) (hg0 : u.g 0 = 1)
    (hwidth : 8 / 5 ≤ u.f 0 + u.g (Real.pi / 2)) :
    adaptiveFunctional u - (u.f 0 + u.g (Real.pi / 2)) / 2 ≤ M / 2 := by
  have h := (adaptiveFunctional_sub_width_le_half_M_of_four_fifths_le
    (u.widthTraces_centered hfL hg0) (by linarith)).1
  rwa [adaptiveFunctional_horizontalTranslate_of_topTraces u _ hfL hg0] at h

/-- Equality forces the reference width. Fixed-width equality with the family member at the
scalar maximum then determines both actual support coordinates up to their one horizontal
translation mode. The parameter is extracted from the endpoint values, rather than postulated
as an equality certificate. -/
theorem eqOn_reference_translate_of_adaptiveFunctional_eq (u : QuarterPair)
    (hfL : u.f (Real.pi / 2) = 1) (hg0 : u.g 0 = 1)
    (hwidth : 8 / 5 ≤ u.f 0 + u.g (Real.pi / 2))
    (heq : adaptiveFunctional u - (u.f 0 + u.g (Real.pi / 2)) / 2 = M / 2) :
    u.f 0 + u.g (Real.pi / 2) = 8 / 3 * Reference.A ∧
      ∃ b : ℝ,
        EqOn u.f (fun t => Reference.referenceF t + b * Real.cos t)
          (Icc (0 : ℝ) (Real.pi / 2)) ∧
        EqOn u.g (fun t => Reference.referenceG t - b * Real.sin t)
          (Icc (0 : ℝ) (Real.pi / 2)) := by
  have hv := u.widthTraces_centered hfL hg0
  have hcenter := adaptiveFunctional_horizontalTranslate_of_topTraces u
    ((u.g (Real.pi / 2) - u.f 0) / 2) hfL hg0
  have ha := (adaptiveFunctional_sub_width_le_half_M_of_four_fifths_le hv (by linarith)).2
    (by rwa [hcenter])
  rw [ha] at hv
  have hβ := beta_mem_family_interval
  have hvalue := familyPair_score hβ
  rw [familyWidth_beta, familyScore_beta] at hvalue
  have key {v : QuarterPair} (hv : v.WidthTraces (4 / 3 * Reference.A))
      (hge : M / 2 + 4 / 3 * Reference.A ≤ adaptiveFunctional v) :=
    eqOn_of_stationary_of_sameTraces_of_ge (familyPair_stationary hβ)
      (QuarterPair.sameTraces_of_widthTraces hv (familyWidth_beta ▸ familyPair_widthTraces hβ))
      (by linarith)
  obtain ⟨h1, h2⟩ := key hv (by linarith)
  obtain ⟨h3, h4⟩ := key centeredReferencePair_widthTraces
    adaptiveFunctional_centeredReferencePair.ge
  simp only [EqOn, QuarterPair.horizontalTranslate, centeredReferencePair,
    Reference.referencePair] at h1 h2 h3 h4
  exact ⟨by linarith, -Reference.k - (u.g (Real.pi / 2) - u.f 0) / 2,
    fun t ht => by linarith [h1 ht, h3 ht], fun t ht => by linarith [h2 ht, h4 ht]⟩

end AmbidextrousSofa.Analysis
