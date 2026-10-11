module

public import AmbidextrousSofa.Analysis.TerminalExtension
public import AmbidextrousSofa.Analysis.PartialRegularDomain

@[expose] public section

/-!
# The terminal facet bound for a prescribed proper maximizer

An overlong facet permits one angle increase with exactly the same cap
and barrier. At the new fixed angle the old terminal normal is a regular
interior normal, so the curvature of that same cap has no atom there.
The unchanged positive facet contradicts this regularity. No largest
terminal angle is selected in this argument.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

/-- TB1: the short-facet bound follows from the actual new-angle
regularity of the unchanged cap, rather than from angle maximality. -/
theorem IsJointCapMaximizer.terminalFaceWidth_le_reserve_of_corner_lt_of_tail_regime
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hcorner : (attachedCorner U α).1 < terminalFirstRightAbscissa U α) :
    terminalFaceWidth U α ≤ terminalTailReserve U α := by
  have hH := (hU.terminalTailPoint_bounds_of_tail_regime hregime hproper hheight haffine).2.1
  by_contra hnot
  obtain ⟨β, hβ, hmax, -⟩ := hU.exists_same_cap_angle_extension_of_overlong_facet hproper
    haffine hH hcorner (not_le.mp hnot)
  have hzero := hmax.sigmaAt_eq_zero_on_regular_proper_domain hβ.2 haffine (t := α)
    ⟨⟨⟨hU.angle_pos, by linarith [Real.pi_pos]⟩,
      by simp [hproper.ne, (hregime.terminal_lt_affineNormal hproper).ne]⟩, hβ.1.ne⟩
  have hwidth : terminalFaceWidth U α = 0 := by
    rw [hU.isCap.terminalFaceWidth_eq_curvature_atom,
      show (upperCurvature U {α}).toReal = 0 from hzero, zero_mul]
  linarith [(hU.isCap.terminalTailInset_bounds hU.angle_pos hproper hH).2.2.1]

end AmbidextrousSofa
