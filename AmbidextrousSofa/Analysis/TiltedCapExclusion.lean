module

public import AmbidextrousSofa.Analysis.FirstUnitOccupationClosure
public import AmbidextrousSofa.Analysis.JointCommonOccupation
public import AmbidextrousSofa.Analysis.CanonicalTiltParameters
public import AmbidextrousSofa.Analysis.TiltedUnitSelection

@[expose] public section

/-!
# Exclusion of an actual positive tilted full maximum

The first-unit density, the common joint source, and the phase data are
all selected from the prescribed cap. Its literal common source law
then supplies the already proved first-unit geometric contradiction.
The public theorem assumes only a centered height-one full maximum
with a positive affine middle slope. The common occupation, its contact
saturation, and both source equations are derived from that same cap.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

theorem IsFullCapMaximizer.false_of_positive_tilt
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C m c : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1) (hm : 0 < m)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) : False := by
  obtain ⟨hC0, hC1, hh0, hh1, hsmall, hlow, hhigh⟩ :=
    hU.centered_positive_tilt_parameters hl hr hheight hm haffine
  obtain ⟨ρ, hρ, hsharp, hρK, heq, hunit⟩ := hU.exists_tilted_first_unit_density
    hl hr hC0 hC1 hh0 hh1 hheight haffine hhigh hlow
  have hρ0 (t : ℝ) := (hsharp t).1
  have hκ (t : ℝ) := (hsharp t).2
  obtain ⟨α, η, hphase⟩ := fullTiltedSupportQuarterPair_exists_strict_sign_phases
    hU hm.le haffine hρ hρ0 hρK heq hl hr hC0 hC1.le hh0 hh1 hm hsmall hheight hlow hhigh hκ hunit
  obtain ⟨xlo, xhi, hleft, hright, hbox, ⟨J⟩⟩ := hU.exists_jointSourceLimit
  obtain ⟨b, δ, χ, hδm, hcoeff, hbalance, hfirstFlag, hvisible, hsecondShadow⟩ :=
    J.exists_common_source_occupation_of_phases hU hl hr hC0 hm hheight haffine
      hlow hhigh hh0 hρ hρ0 hρK heq hunit hbox hleft hright hphase
  exact fullTiltedSupportQuarterPair_false_of_common_occupation
    hU hm.le haffine hρ hρ0 hρK heq hl hr hC0 hC1.le hh0 hh1 hm hsmall
      hheight hlow hhigh hκ hunit hδm hcoeff hbalance hfirstFlag hvisible hsecondShadow

end AmbidextrousSofa
