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
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

/-- Every compact connected body with the two original independent
passages has area at most the displayed reference value. -/
theorem IsAmbidextrous.volumeReal_le_M
    {S : Set Plane} (hS : IsAmbidextrous S) : volume.real S ≤ M := by
  rcases hS.original_domain_score_reduction with hsmall |
      ⟨θ, v, α, γ, hT, hstrip, _harea, hα, hγ, hU, hV, hbound⟩
  · exact hsmall.trans sqrt_two_lt_M.le
  · have hcapU := isDownwardCap_upperHullCap hT.nonempty hT.isCompact hstrip
    have hcapV := isDownwardCap_reflectedHullCap hT.nonempty hT.isCompact hstrip
    have hscoreU := hcapU.capScore_le_half_M ⟨hα.le, hU.angle_le⟩
    have hscoreV := hcapV.capScore_le_half_M ⟨hγ.le, hV.angle_le⟩
    linarith only [hbound, hscoreU, hscoreV]

/-- Equal area classifies this same original body, including its
boundary, as a rotation and translation of the actual reference sofa. -/
theorem IsAmbidextrous.eq_rigidImage_referenceSofa_of_volumeReal_eq
    {S : Set Plane} (hS : IsAmbidextrous S) (harea : volume.real S = M) :
    ∃ (θ : ℝ) (v : Plane), S = rigidMap θ v '' Reference.referenceSofa := by
  have hlarge : Real.sqrt 2 < volume.real S := by
    rw [harea]
    exact sqrt_two_lt_M
  obtain ⟨θ, v, α, γ, hT, hstrip, hvolume, hα, hγ, hU, hV⟩ :=
    hS.exists_normalized_angularConstraints hlarge
  have hTarea : volume.real (rigidMap θ v '' S) = M := hvolume.trans harea
  have hcapU := isDownwardCap_upperHullCap hT.nonempty hT.isCompact hstrip
  have hcapV := isDownwardCap_reflectedHullCap hT.nonempty hT.isCompact hstrip
  have hαmem : α ∈ Icc (Real.pi / 4) (Real.pi / 2) := ⟨hα.le, hU.angle_le⟩
  have hγmem : γ ∈ Icc (Real.pi / 4) (Real.pi / 2) := ⟨hγ.le, hV.angle_le⟩
  obtain ⟨hscoreU, hscoreV, _hpartition, _hmissing⟩ :=
    actual_cap_equality_deficits hT.isCompact hT.isConnected hstrip hU hV
      (hcapU.capScore_le_half_M hαmem) (hcapV.capScore_le_half_M hγmem) hTarea
  obtain ⟨hαfull, hrefU⟩ := (hcapU.capScore_eq_half_M_iff hαmem).mp hscoreU
  obtain ⟨hγfull, hrefV⟩ := (hcapV.capScore_eq_half_M_iff hγmem).mp hscoreV
  have hUfull : AngularConstraints (rigidMap θ v '' S)
      (upperHullCap (rigidMap θ v '' S)) (Real.pi / 2) := by
    simpa only [hαfull] using hU
  have hVfull : AngularConstraints (reflect '' (rigidMap θ v '' S))
      (reflectedHullCap (rigidMap θ v '' S)) (Real.pi / 2) := by
    simpa only [hγfull] using hV
  obtain ⟨b, _hHull, hbody⟩ := eq_referenceSofa_translate_of_actual_caps
    hT.isCompact hstrip hUfull hVfull hrefU hrefV hTarea
  exact ⟨-θ, rotate (-θ) ((b, 0) - v),
    eq_rigidImage_of_normalized_horizontalTranslate hbody⟩

theorem IsAmbidextrous.volumeReal_eq_M_iff
    {S : Set Plane} (hS : IsAmbidextrous S) :
    volume.real S = M ↔ ∃ (θ : ℝ) (v : Plane),
      S = rigidMap θ v '' Reference.referenceSofa := by
  constructor
  · exact hS.eq_rigidImage_referenceSofa_of_volumeReal_eq
  · rintro ⟨θ, v, rfl⟩
    exact Reference.volumeReal_rigidImage_referenceSofa θ v

/-- The displayed value is an attained greatest element of the area
set of the original ambidextrous domain. -/
theorem isGreatest_ambidextrous_areas :
    IsGreatest {a : ℝ | ∃ S : Set Plane, IsAmbidextrous S ∧ volume.real S = a} M := by
  constructor
  · exact ⟨Reference.referenceSofa, Reference.isAmbidextrous_referenceSofa,
      Reference.volumeReal_referenceSofa⟩
  · rintro a ⟨S, hS, rfl⟩
    exact hS.volumeReal_le_M

end AmbidextrousSofa
