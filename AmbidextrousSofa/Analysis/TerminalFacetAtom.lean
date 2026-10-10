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

theorem IsJointCapMaximizer.faceWidth_eq_zero_at_regular_visited_normal
    {U : Set Plane} {β m c t : ℝ} (hU : IsJointCapMaximizer U β)
    (hproper : β < Real.pi / 2)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (ht : t ∈ Ioo 0 β) (hmiddle : t ≠ affineNormalAngle m) :
    terminalFaceWidth U t = 0 := by
  have hregular : t ∈ regularProperCurvatureDomain β m := by
    refine ⟨?_, ht.2.ne⟩
    refine ⟨⟨ht.1, by linarith only [ht.2, hproper, Real.pi_pos]⟩, ?_⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨(ht.2.trans hproper).ne, hmiddle⟩
  have hzero := hU.sigmaAt_eq_zero_on_regular_proper_domain hproper haffine hregular
  rw [hU.isCap.terminalFaceWidth_eq_curvature_atom]
  change MovingSofaOptimality.sigmaAt U t * Real.sin t = 0
  rw [hzero, zero_mul]

/-- TB1: the short-facet bound follows from the actual new-angle
regularity of the unchanged cap, rather than from angle maximality. -/
theorem IsJointCapMaximizer.terminalFaceWidth_le_reserve_of_regular_terminal
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hproper : α < Real.pi / 2)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hmiddle : α ≠ affineNormalAngle m)
    (hH : Real.sin α < (terminalTailPoint U α).2)
    (hcorner : (attachedCorner U α).1 < terminalFirstRightAbscissa U α) :
    terminalFaceWidth U α ≤ terminalTailReserve U α := by
  by_contra hnot
  have hfacet : terminalTailReserve U α < terminalFaceWidth U α := lt_of_not_ge hnot
  obtain ⟨β, hβ, hmax, _hbarrier⟩ :=
    hU.exists_same_cap_angle_extension_of_overlong_facet hproper haffine hH hcorner hfacet
  have hzero := hmax.faceWidth_eq_zero_at_regular_visited_normal hβ.2 haffine
    ⟨hU.angle_pos, hβ.1⟩ hmiddle
  have hreserve := (hU.isCap.terminalTailInset_bounds hU.angle_pos hproper hH).2.2.1
  rw [hzero] at hfacet
  exact (not_lt_of_ge hreserve.le) hfacet

theorem IsJointCapMaximizer.terminalFaceWidth_le_reserve_of_corner_lt_of_tail_regime
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hcorner : (attachedCorner U α).1 < terminalFirstRightAbscissa U α) :
    terminalFaceWidth U α ≤ terminalTailReserve U α :=
  hU.terminalFaceWidth_le_reserve_of_regular_terminal hproper haffine
    (hregime.terminal_lt_affineNormal hproper).ne
    (hU.terminalTailPoint_bounds_of_tail_regime hregime hproper hheight haffine).2.1 hcorner

end AmbidextrousSofa
