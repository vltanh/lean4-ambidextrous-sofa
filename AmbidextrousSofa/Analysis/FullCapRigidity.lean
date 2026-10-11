module

public import AmbidextrousSofa.Analysis.TiltedCapExclusion
public import AmbidextrousSofa.Analysis.CanonicalTiltParameters
public import AmbidextrousSofa.Analysis.FullCapRecovery

@[expose] public section

/-!
# Full-cap rigidity for each prescribed maximum

The actual positive-tilt exclusion forces a centered affine middle to
have nonpositive slope. Applying it to the horizontal reflection forces
the slope to vanish. Translation gives the same statement for a
prescribed uncentered cap. Its literal middle-chord and height
canonicalization is therefore horizontal, and the proved inverse
canonicalization recovers the original set as a reference translate.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem IsFullCapMaximizer.centered_affine_middle_slope_eq_zero
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C m c : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) : m = 0 := by
  refine le_antisymm (not_lt.mp fun hm => hU.false_of_positive_tilt hl hr hheight hm haffine)
    (not_lt.mp fun hm => hU.horizontalMirror.false_of_positive_tilt (C := C) (c := c)
      (by rw [horizontalLeft_horizontalMirror hU.isCap, hr]; ring)
      (by rw [horizontalRight_horizontalMirror hU.isCap, hl]; ring)
      (by rw [capHeight_horizontalMirror, hheight]) (neg_pos.mpr hm) fun x hx => ?_)
  rw [horizontalLeft_horizontalMirror hU.isCap, horizontalRight_horizontalMirror hU.isCap] at hx
  rw [capRoof_horizontalMirror, haffine (-x) ?_]
  · ring
  · simp only [middleHalfInterval, mem_Icc] at hx ⊢
    constructor <;> linarith only [hx.1, hx.2]

/-- The slope belongs to the prescribed affine middle of this actual
maximum; no replacement of the original cap is needed here. -/
theorem IsFullCapMaximizer.affine_middle_slope_eq_zero
    {U : Set Plane} (hU : IsFullCapMaximizer U) {m c : ℝ}
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) : m = 0 :=
  hU.centeredCap.centered_affine_middle_slope_eq_zero (C := capWidth U / 4)
    (by rw [horizontalLeft_centeredCap hU.isCap]; ring)
    (by rw [horizontalRight_centeredCap hU.isCap]; ring)
    (by rw [capHeight_centeredCap hU.isCap, hheight])
    (hU.isCap.affine_middle_horizontalTranslate haffine _)

/-- Classification of every original full maximum, before middle or
height replacement. The translation is the only remaining freedom. -/
theorem IsFullCapMaximizer.eq_reference_translate
    {U : Set Plane} (hU : IsFullCapMaximizer U) :
    ∃ b : ℝ, U = AmbidextrousSofa.horizontalTranslate Reference.referenceCap b := by
  have hV := hU.fullCanonicalCap
  obtain ⟨-, -, hheight, m, c, haffine⟩ :=
    hU.isCap.fullCanonicalCap_data (two_pos.trans hU.two_lt_width)
  obtain rfl := hV.affine_middle_slope_eq_zero hheight haffine
  have hlr := horizontalLeft_le_horizontalRight hV.isCap.nonempty hV.isCap.isCompact
  have hright := hV.middle_right_eq_one_of_affine_nonneg hheight le_rfl haffine
  rw [haffine _ ⟨by linarith only [hlr], le_rfl⟩, zero_mul, zero_add] at hright
  exact hU.eq_reference_translate_of_fullCanonicalCap_horizontal fun x hx => by
    rw [haffine x hx, zero_mul, zero_add, hright]

theorem IsFullCapMaximizer.capScore_eq_half_M
    {U : Set Plane} (hU : IsFullCapMaximizer U) :
    capScore U (Real.pi / 2) = M / 2 := by
  obtain ⟨b, hb⟩ := hU.eq_reference_translate
  rw [hb, capScore_horizontalTranslate Reference.isDownwardCap_referenceCap,
    Reference.capScore_referenceCap]

end AmbidextrousSofa
