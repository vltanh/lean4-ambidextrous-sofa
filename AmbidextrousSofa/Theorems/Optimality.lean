module

public import AmbidextrousSofa.Analysis.SharpCapBound
public import AmbidextrousSofa.Analysis.SharpCapEquality
public import AmbidextrousSofa.Measure.ReferenceOrbit
public import AmbidextrousSofa.Geometry.MotionReduction

@[expose] public section

/-!
# Optimality and equality in the original ambidextrous domain

Both effective angles and both caps are constructed from the original
independent passages. The universal scalar cap bound therefore bounds
the area of every original body. At equality the physical four-term
deficit forces each original cap to attain its own sharp value. Their
individual classifications force full angles and aligned reference
caps. The original compact set is then recovered from those exact caps,
and the initial rigid normalization is inverted explicitly. All
quantified cap bounds and occupation laws are discharged internally.

Each angle is either a quarter turn that its passage reaches, or the final
angle of its passage, below `π/2`. At equality both angles are full, so each
of the two passages that witness a sofa of area `M` turns the body through a
quarter turn (`quarter_turns_of_volumeReal_eq_M`).
-/

open Set MeasureTheory

namespace AmbidextrousSofa

/-- Every compact connected body with the two original independent
passages has area at most the displayed reference value. -/
theorem IsAmbidextrous.volumeReal_le_M
    {S : Set Plane} (hS : IsAmbidextrous S) : volume.real S ≤ M := by
  rcases hS.original_domain_score_reduction with hsmall |
      ⟨θ, v, α, γ, hT, hstrip, -, hα, hγ, hU, hV, hbound⟩
  · exact hsmall.trans sqrt_two_lt_M.le
  · have hcapU := isDownwardCap_upperHullCap hT.nonempty hT.isCompact hstrip
    have hcapV := isDownwardCap_reflectedHullCap hT.nonempty hT.isCompact hstrip
    linarith only [hbound, hcapU.capScore_le_half_M ⟨hα.le, hU.angle_le⟩,
      hcapV.capScore_le_half_M ⟨hγ.le, hV.angle_le⟩]

/-- At area `M` both caps of a normalized body attain the score `M/2`, so both
angles are the full quarter turn and both caps are translates of Romik's cap. -/
theorem actual_caps_eq_reference_of_volumeReal_eq
    {T : Set Plane} (hT : IsCompact T) (hconn : IsConnected T) (hstrip : T ⊆ unitStrip)
    {α γ : ℝ} (hα : Real.pi / 4 < α) (hγ : Real.pi / 4 < γ)
    (hU : AngularConstraints T (upperHullCap T) α)
    (hV : AngularConstraints (reflect '' T) (reflectedHullCap T) γ)
    (harea : volume.real T = M) :
    (α = Real.pi / 2 ∧ ∃ a : ℝ, upperHullCap T = horizontalTranslate Reference.referenceCap a) ∧
      γ = Real.pi / 2 ∧
        ∃ b : ℝ, reflectedHullCap T = horizontalTranslate Reference.referenceCap b := by
  have hcapU := isDownwardCap_upperHullCap hconn.nonempty hT hstrip
  have hcapV := isDownwardCap_reflectedHullCap hconn.nonempty hT hstrip
  have hαmem : α ∈ Icc (Real.pi / 4) (Real.pi / 2) := ⟨hα.le, hU.angle_le⟩
  have hγmem : γ ∈ Icc (Real.pi / 4) (Real.pi / 2) := ⟨hγ.le, hV.angle_le⟩
  obtain ⟨hscoreU, hscoreV, -, -⟩ := actual_cap_equality_deficits hT hconn hstrip hU hV
    (hcapU.capScore_le_half_M hαmem) (hcapV.capScore_le_half_M hγmem) harea
  exact ⟨(hcapU.capScore_eq_half_M_iff hαmem).mp hscoreU,
    (hcapV.capScore_eq_half_M_iff hγmem).mp hscoreV⟩

/-- Equal area classifies this same original body, including its
boundary, as a rotation and translation of the actual reference sofa. -/
theorem IsAmbidextrous.eq_rigidImage_referenceSofa_of_volumeReal_eq
    {S : Set Plane} (hS : IsAmbidextrous S) (harea : volume.real S = M) :
    ∃ (θ : ℝ) (v : Plane), S = rigidMap θ v '' Reference.referenceSofa := by
  obtain ⟨θ, v, α, γ, hT, hstrip, hvolume, hα, hγ, hU, hV⟩ :=
    hS.exists_normalized_angularConstraints (harea ▸ sqrt_two_lt_M)
  have hTarea : volume.real (rigidMap θ v '' S) = M := hvolume.trans harea
  obtain ⟨⟨rfl, hrefU⟩, rfl, hrefV⟩ := actual_caps_eq_reference_of_volumeReal_eq
    hT.isCompact hT.isConnected hstrip hα hγ hU hV hTarea
  obtain ⟨b, -, hbody⟩ := eq_referenceSofa_translate_of_actual_caps
    hT.isCompact hstrip hU hV hrefU hrefV hTarea
  exact ⟨-θ, rotate (-θ) ((b, 0) - v), eq_rigidImage_of_normalized_horizontalTranslate hbody⟩

/-- In an ambidextrous sofa of area `M`, each of the two passages that witness it
turns the body through a full quarter turn at some time: clockwise in the lower
hallway, which turns right, and counterclockwise in the upper hallway, which
turns left. The hypotheses are those of `IsAmbidextrous` with the two passages
made explicit, so this holds for every pair of passages that witness the sofa. -/
theorem quarter_turns_of_volumeReal_eq_M
    {S : Set Plane} (hS : IsCompact S) (hconn : IsConnected S)
    {lower upper : RigidMotionPath} (horient : SameInitialOrientation lower upper)
    (hlower : Passage S lowerHall incomingArm lowerOutgoingArm lower)
    (hupper : Passage S upperHall incomingArm upperOutgoingArm upper)
    (harea : volume.real S = M) :
    (∃ t ∈ motionInterval, lower.angle t = lower.angle 0 - Real.pi / 2) ∧
      ∃ t ∈ motionInterval, upper.angle t = upper.angle 0 + Real.pi / 2 := by
  obtain ⟨θ, v, α, γ, hT, hstrip, hvolume, hα, hγ, hU, hV, hαr, hγr⟩ :=
    exists_normalized_angularConstraints_of_passages hS hconn horient hlower hupper
      (harea ▸ sqrt_two_lt_M)
  -- both angles are the quarter turn, so neither passage ends below it
  obtain ⟨⟨rfl, -⟩, rfl, -⟩ := actual_caps_eq_reference_of_volumeReal_eq
    hT.isCompact hT.isConnected hstrip hα hγ hU hV (hvolume.trans harea)
  exact ⟨(hαr.resolve_right fun h => h.2.false).2, (hγr.resolve_right fun h => h.2.false).2⟩

theorem IsAmbidextrous.volumeReal_eq_M_iff
    {S : Set Plane} (hS : IsAmbidextrous S) :
    volume.real S = M ↔ ∃ (θ : ℝ) (v : Plane),
      S = rigidMap θ v '' Reference.referenceSofa :=
  ⟨hS.eq_rigidImage_referenceSofa_of_volumeReal_eq,
    fun ⟨θ, v, h⟩ => h ▸ Reference.volumeReal_rigidImage_referenceSofa θ v⟩

/-- The displayed value is an attained greatest element of the area
set of the original ambidextrous domain. -/
theorem isGreatest_ambidextrous_areas :
    IsGreatest {a : ℝ | ∃ S : Set Plane, IsAmbidextrous S ∧ volume.real S = a} M :=
  ⟨⟨Reference.referenceSofa, Reference.isAmbidextrous_referenceSofa,
    Reference.volumeReal_referenceSofa⟩, fun _ ⟨_, hS, h⟩ => h ▸ hS.volumeReal_le_M⟩

end AmbidextrousSofa
