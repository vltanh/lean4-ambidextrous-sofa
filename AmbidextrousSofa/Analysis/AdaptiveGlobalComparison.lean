module

public import AmbidextrousSofa.Analysis.AdaptiveGlobalScalar
public import AmbidextrousSofa.Analysis.AdaptiveGlobalValue
public import AmbidextrousSofa.Analysis.AdaptiveTranslation

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

theorem adaptiveFunctional_sub_width_lt_half_M_of_familyWidth_zero_le
    {u : QuarterPair} {a : ℝ} (hu : u.WidthTraces a) (ha : familyWidth 0 ≤ a) :
    adaptiveFunctional u - a < M / 2 := by
  let r := a / Real.cos tailAngle0
  have hrc : r * Real.cos tailAngle0 = a :=
    div_mul_cancel₀ a (ne_of_gt cos_tailAngle0_pos)
  have hthreshold : familyWidth 0 * Real.sin tailAngle0 = 2 / 3 * Real.cos tailAngle0 := by
    rw [familyWidth_zero]
    field_simp [ne_of_gt sin_tailAngle0_pos]
    <;> ring
  have hmul := mul_le_mul_of_nonneg_right ha sin_tailAngle0_pos.le
  have hr : 2 / 3 ≤ r * Real.sin tailAngle0 := by
    apply (mul_le_mul_iff_left₀ cos_tailAngle0_pos).mp
    have heq : (r * Real.sin tailAngle0) * Real.cos tailAngle0 =
        a * Real.sin tailAngle0 := by
      calc
        _ = (r * Real.cos tailAngle0) * Real.sin tailAngle0 := by ring
        _ = _ := by rw [hrc]
    rw [heq]
    nlinarith [hthreshold]
  have htrace : u.WidthTraces (r * Real.cos tailAngle0) := by simpa only [hrc] using hu
  have h := adaptiveFunctional_sub_width_lt_half_M_of_tail hr htrace
  simpa only [hrc] using h

/-- A genuine global comparison for all C1 profiles at every competitive
width. There is no optimizer-existence or optimality hypothesis. -/
theorem adaptiveFunctional_sub_width_le_half_M_of_four_fifths_le
    {u : QuarterPair} {a : ℝ} (hu : u.WidthTraces a) (ha : 4 / 5 ≤ a) :
    adaptiveFunctional u - a ≤ M / 2 := by
  by_cases htail : a ≤ familyWidth 0
  · obtain ⟨b, hb, hwidth⟩ := exists_familyWidth ha htail
    have htrace : u.WidthTraces (familyWidth b) := by simpa only [hwidth] using hu
    have hcomp := adaptiveFunctional_le_family_of_widthTraces hb htrace
    have hvalue := familyPair_score hb
    have hscalar := familyScore_le_half_M hb
    nlinarith [hwidth]
  · exact (adaptiveFunctional_sub_width_lt_half_M_of_familyWidth_zero_le hu
      (lt_of_not_ge htail).le).le

theorem width_eq_reference_of_adaptiveFunctional_eq
    {u : QuarterPair} {a : ℝ} (hu : u.WidthTraces a) (ha : 4 / 5 ≤ a)
    (heq : adaptiveFunctional u - a = M / 2) : a = 4 / 3 * Reference.A := by
  by_cases htail : a ≤ familyWidth 0
  · obtain ⟨b, hb, hwidth⟩ := exists_familyWidth ha htail
    have htrace : u.WidthTraces (familyWidth b) := by simpa only [hwidth] using hu
    have hcomp := adaptiveFunctional_le_family_of_widthTraces hb htrace
    have hvalue := familyPair_score hb
    have hscalar := familyScore_le_half_M hb
    have hs : familyScore b = M / 2 := by nlinarith [hwidth]
    have hbexact := (familyScore_eq_half_M_iff hb).1 hs
    rw [hbexact, familyWidth_beta] at hwidth
    exact hwidth.symm
  · have hlt := adaptiveFunctional_sub_width_lt_half_M_of_familyWidth_zero_le hu
      (lt_of_not_ge htail).le
    linarith

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

/-- The family member at the unique scalar maximum is the actual centered
reference, by equality in the already proved fixed-width comparison. -/
theorem familyPair_beta_eqOn_centeredReference :
    EqOn (familyPair beta beta_mem_family_interval).f centeredReferencePair.f
      (Icc (0 : ℝ) (Real.pi / 2)) ∧
    EqOn (familyPair beta beta_mem_family_interval).g centeredReferencePair.g
      (Icc (0 : ℝ) (Real.pi / 2)) := by
  have htrace : centeredReferencePair.WidthTraces (familyWidth beta) := by
    simpa only [familyWidth_beta] using centeredReferencePair_widthTraces
  have hvalue := familyPair_score beta_mem_family_interval
  rw [familyWidth_beta, familyScore_beta] at hvalue
  have hge : adaptiveFunctional (familyPair beta beta_mem_family_interval) ≤
      adaptiveFunctional centeredReferencePair := by
    rw [adaptiveFunctional_centeredReferencePair]
    linarith
  have h := eqOn_of_stationary_of_sameTraces_of_ge
    (familyPair_stationary beta_mem_family_interval)
    (QuarterPair.sameTraces_of_widthTraces htrace (familyPair_widthTraces beta_mem_family_interval)) hge
  exact ⟨fun _ ht => (h.1 ht).symm, fun _ ht => (h.2 ht).symm⟩

theorem eqOn_centeredReference_of_adaptiveFunctional_eq
    {u : QuarterPair} {a : ℝ} (hu : u.WidthTraces a) (ha : 4 / 5 ≤ a)
    (heq : adaptiveFunctional u - a = M / 2) :
    a = 4 / 3 * Reference.A ∧
      EqOn u.f centeredReferencePair.f (Icc (0 : ℝ) (Real.pi / 2)) ∧
      EqOn u.g centeredReferencePair.g (Icc (0 : ℝ) (Real.pi / 2)) := by
  have hwidth := width_eq_reference_of_adaptiveFunctional_eq hu ha heq
  have htrace : u.WidthTraces (familyWidth beta) := by
    simpa only [familyWidth_beta, hwidth] using hu
  have hvalue := familyPair_score beta_mem_family_interval
  rw [familyWidth_beta, familyScore_beta] at hvalue
  have hge : adaptiveFunctional (familyPair beta beta_mem_family_interval) ≤ adaptiveFunctional u := by
    rw [hwidth] at heq
    linarith
  have h := eqOn_of_stationary_of_sameTraces_of_ge
    (familyPair_stationary beta_mem_family_interval)
    (QuarterPair.sameTraces_of_widthTraces htrace (familyPair_widthTraces beta_mem_family_interval)) hge
  exact ⟨hwidth,
    fun _ ht => (h.1 ht).trans (familyPair_beta_eqOn_centeredReference.1 ht),
    fun _ ht => (h.2 ht).trans (familyPair_beta_eqOn_centeredReference.2 ht)⟩

/-- Centering removes the artificial common-endpoint requirement. The
only width assumption is the explicit, geometrically available `8/5`. -/
theorem adaptiveFunctional_sub_halfWidth_le_half_M (u : QuarterPair)
    (hfL : u.f (Real.pi / 2) = 1) (hg0 : u.g 0 = 1)
    (hwidth : 8 / 5 ≤ u.f 0 + u.g (Real.pi / 2)) :
    adaptiveFunctional u - (u.f 0 + u.g (Real.pi / 2)) / 2 ≤ M / 2 := by
  have h := adaptiveFunctional_sub_width_le_half_M_of_four_fifths_le
    (u.widthTraces_centered hfL hg0) (by linarith :
      4 / 5 ≤ (u.f 0 + u.g (Real.pi / 2)) / 2)
  rwa [adaptiveFunctional_horizontalTranslate_of_topTraces u _ hfL hg0] at h

/-- Equality determines both actual support coordinates up to their one
horizontal translation mode. The parameter is extracted from the endpoint
values, rather than postulated as an equality certificate. -/
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
  let d := (u.g (Real.pi / 2) - u.f 0) / 2
  have hc : adaptiveFunctional (u.horizontalTranslate d) -
      (u.f 0 + u.g (Real.pi / 2)) / 2 = M / 2 := by
    rw [adaptiveFunctional_horizontalTranslate_of_topTraces u d hfL hg0]
    exact heq
  have h := eqOn_centeredReference_of_adaptiveFunctional_eq
    (u.widthTraces_centered hfL hg0)
    (by linarith : 4 / 5 ≤ (u.f 0 + u.g (Real.pi / 2)) / 2) hc
  refine ⟨by linarith [h.1], -Reference.k - d, ?_, ?_⟩
  · intro t ht
    have hf := h.2.1 ht
    change u.f t + d * Real.cos t = Reference.referenceF t + (-Reference.k) * Real.cos t at hf
    nlinarith
  · intro t ht
    have hg := h.2.2 ht
    change u.g t - d * Real.sin t = Reference.referenceG t - (-Reference.k) * Real.sin t at hg
    nlinarith

end AmbidextrousSofa.Analysis
