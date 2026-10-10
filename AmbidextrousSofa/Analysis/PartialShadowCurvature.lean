module

public import AmbidextrousSofa.Analysis.PartialShadowSecants
public import AmbidextrousSofa.Analysis.PartialAtomIntervalLimit

@[expose] public section

/-!
# The actual proper same-sign curvature laws

The selected polygons and their moving neighboring-wall margins belong
to the original proper maximizer. Summation keeps every unsampled atom
and both vanishing errors. Lebesgue differentiation then gives the
zero and half-density bounds in the two same-sign quadrants. The actual
terminal normal is excluded from the regular domain throughout.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

/-- Both support directions avoid the actual exceptional normals. -/
def regularProperCornerDomain (α m : ℝ) : Set ℝ :=
  Ioo (0 : ℝ) (Real.pi / 2) ∩ (regularProperCurvatureDomain α m ∩
    (fun t : ℝ => t + Real.pi / 2) ⁻¹' regularProperCurvatureDomain α m)

theorem isOpen_regularProperCornerDomain (α m : ℝ) :
    IsOpen (regularProperCornerDomain α m) := by
  have hreg := isOpen_regularProperCurvatureDomain α m
  exact isOpen_Ioo.inter (hreg.inter (hreg.preimage (continuous_id.add_const (Real.pi / 2))))

namespace PartialGrid

variable {α : TerminalAngle} {hαL : (α : ℝ) < Real.pi / 2}

theorem curvature_local_shadow_bound
    {target : Set Plane} {U : ℕ → Set Plane}
    {boxLeft boxRight R m c t ε : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    {ρ : ℝ → ℝ}
    (hTarget : IsDownwardCap target)
    (hU : ∀ n, IsSelectedPolygon target α hαL boxLeft boxRight (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hbox : ∀ n, U n ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hwidth : 0 < capWidth target)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
      capRoof target x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s)
    (heq : (upperCurvature target).restrict (regularProperCurvatureDomain α m) =
      (volume.restrict (regularProperCurvatureDomain α m)).withDensity
        (fun s => ENNReal.ofReal (ρ s)))
    (positive : Bool) (ht : t ∈ regularProperCurvatureDomain α m)
    (hpaired : sourceQuarterAngle t ∈ regularProperCornerDomain α m)
    (hmargin : 0 < sameSignVelocityMargin positive target (sourceQuarterAngle t))
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ d : ℝ, 0 < d → d < δ →
      (upperCurvature target).real (Ioc t (t + d)) ≤
        (sameSignCoefficient positive t + ε) * d := by
  have htop := (mem_regularCurvatureDomain_iff.mp ht.1).2.2.1
  have hfirst := sigmaAt_eq_zero_of_density hρ hρ0 heq hpaired.2.1
  have hsecond := sigmaAt_eq_zero_of_density hρ hρ0 heq hpaired.2.2
  obtain ⟨δ₀, hδ₀, hfinite⟩ := eventually_shadow_atoms_le hTarget hU hHausdorff hlevel hc
    (isCompact_Icc.prod isCompact_Icc) hbox positive htop hfirst hsecond hmargin hε
  obtain ⟨a, b, htIoo, hIoo⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    ((isOpen_regularProperCurvatureDomain α m).mem_nhds ht)
  let δ := min δ₀ (b - t)
  have hδ : 0 < δ := lt_min hδ₀ (sub_pos.mpr htIoo.2)
  have hδ₀' : δ ≤ δ₀ := min_le_left _ _
  have hδb : δ ≤ b - t := min_le_right _ _
  refine ⟨δ, hδ, ?_⟩
  intro d hd hdδ
  have hreg : Icc t (t + d) ⊆ regularProperCurvatureDomain α m := by
    intro s hs
    apply hIoo
    exact ⟨htIoo.1.trans_le hs.1, by linarith only [hs.2, hdδ, hδb]⟩
  have hbound := curvature_Ioc_le_of_eventual_sampled_atom_bound
    hTarget hU hHausdorff hlevel hc hrate hbox hwidth haffine
    (show 0 ≤ sameSignCoefficient positive t + ε from
      add_nonneg (sameSignCoefficient_nonneg positive t) hε.le)
    (show t ≤ t + d by linarith only [hd]) hreg
    (sigmaAt_eq_zero_of_density hρ hρ0 heq ht)
    (sigmaAt_eq_zero_of_density hρ hρ0 heq (hreg ⟨by linarith only [hd], le_rfl⟩)) (by
      filter_upwards [hfinite] with n hn
      intro j hj
      apply hn j
      apply abs_lt.mpr
      constructor <;> linarith only [hj.1, hj.2, hdδ, hδ₀', hδ₀])
  simpa only [add_sub_cancel_left] using hbound

end PartialGrid

/-- The actual proper maximum supplies its own selected sequence. The
density premise is only the literal curvature representation already
constructed on its regular domain. -/
theorem IsJointCapMaximizer.ae_proper_density_same_sign_bound
    {K : Set Plane} {α m c C : ℝ} (hK : IsJointCapMaximizer K α)
    (hproper : α < Real.pi / 2) {ρ : ℝ → ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft K) (horizontalRight K),
      capRoof K x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (heq : (upperCurvature K).restrict (regularProperCurvatureDomain α m) =
      (volume.restrict (regularProperCurvatureDomain α m)).withDensity
        (fun t => ENNReal.ofReal (ρ t)))
    (positive : Bool) :
    ∀ᵐ t : ℝ ∂volume, t ∈ regularProperCurvatureDomain α m →
      sourceQuarterAngle t ∈ regularProperCornerDomain α m →
        0 < sameSignVelocityMargin positive K (sourceQuarterAngle t) →
          ρ t ≤ sameSignCoefficient positive t := by
  let R := |horizontalLeft K| + |horizontalRight K| + 1
  let β : TerminalAngle := ⟨α, hK.angle_mem⟩
  have hR : 0 ≤ R := by positivity
  have hbox : K ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1 := by
    apply subset_symmetricBox_of_horizontalBox
    intro p hp
    refine ⟨?_, hK.isCap.inStrip hp⟩
    rw [← horizontalProjection_eq_Icc hK.isCap.nonempty hK.isCap.isCompact hK.isCap.convex]
    exact ⟨p, hp, rfl⟩
  obtain ⟨level, coefficient, U, hlevel, hc, hrate, hU, _, hHausdorff⟩ :=
    PartialGrid.exists_selected_sequence β hproper hK
      (by linarith only [hR] : -R ≤ R) hbox
  have hlevelTop : Tendsto level atTop atTop := tendsto_atTop_mono hlevel tendsto_id
  have hwidth : 0 < capWidth K := by linarith only [hK.width_bounds.1, one_lt_M]
  have h := ae_density_le_of_conditional_local_bound
    (isOpen_regularProperCurvatureDomain α m) hρ hρ0 hρC heq
    (P := fun t => sourceQuarterAngle t ∈ regularProperCornerDomain α m ∧
      0 < sameSignVelocityMargin positive K (sourceQuarterAngle t))
    (f := sameSignCoefficient positive) (by
      intro t ht hP ε hε
      exact PartialGrid.curvature_local_shadow_bound hK.isCap hU hHausdorff hlevelTop
        (fun n => (hc n).le) hrate (fun n => (hU n).inBox) hwidth haffine hρ hρ0 heq
        positive ht hP.1 hP.2 hε)
  filter_upwards [h] with t ht hregular hpaired hmargin
  exact ht hregular ⟨hpaired, hmargin⟩

/-- In the convention `p = -secondCornerVelocity` and
`q = firstCornerVelocity`, these are the `++` and `--` source laws.
Both densities represent curvature of the original proper cap. -/
theorem IsJointCapMaximizer.ae_proper_curvature_same_sign_quadrants
    {K : Set Plane} {α m c C : ℝ} (hK : IsJointCapMaximizer K α)
    (hproper : α < Real.pi / 2) {ρ : ℝ → ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft K) (horizontalRight K),
      capRoof K x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (heq : (upperCurvature K).restrict (regularProperCurvatureDomain α m) =
      (volume.restrict (regularProperCurvatureDomain α m)).withDensity
        (fun t => ENNReal.ofReal (ρ t))) :
    ∀ᵐ t ∂volume.restrict (regularProperCornerDomain α m),
      (0 < firstCornerVelocity K t ∧ secondCornerVelocity K t < 0 →
        ρ t = 0 ∧ ρ (t + Real.pi / 2) ≤ 1 / 2) ∧
      (firstCornerVelocity K t < 0 ∧ 0 < secondCornerVelocity K t →
        ρ (t + Real.pi / 2) = 0 ∧ ρ t ≤ 1 / 2) := by
  have hp := hK.ae_proper_density_same_sign_bound hproper haffine hρ hρ0 hρC heq true
  have hn := hK.ae_proper_density_same_sign_bound hproper haffine hρ hρ0 hρC heq false
  have hpShift := (measurePreserving_add_right volume (Real.pi / 2)).quasiMeasurePreserving.ae hp
  have hnShift := (measurePreserving_add_right volume (Real.pi / 2)).quasiMeasurePreserving.ae hn
  filter_upwards [ae_restrict_mem (isOpen_regularProperCornerDomain α m).measurableSet,
    ae_restrict_of_ae hp, ae_restrict_of_ae hn,
    ae_restrict_of_ae hpShift, ae_restrict_of_ae hnShift] with t ht hp hn hpShift hnShift
  have hbase : sourceQuarterAngle t = t := by
    simp only [sourceQuarterAngle, if_pos ht.1.2]
  have hnot : ¬ t + Real.pi / 2 < Real.pi / 2 := by linarith only [ht.1.1]
  have hshift : sourceQuarterAngle (t + Real.pi / 2) = t := by
    simp only [sourceQuarterAngle, if_neg hnot, add_sub_cancel_right]
  have hpBase := hp ht.2.1 (hbase.symm ▸ ht)
  have hnBase := hn ht.2.1 (hbase.symm ▸ ht)
  have hpComp := hpShift ht.2.2 (hshift.symm ▸ ht)
  have hnComp := hnShift ht.2.2 (hshift.symm ▸ ht)
  constructor
  · rintro ⟨hq, hr⟩
    have hm : 0 < sameSignVelocityMargin true K t := by
      simpa [sameSignVelocityMargin] using lt_min (neg_pos.mpr hr) hq
    have hfirst : ρ t ≤ 0 := by
      simpa [sameSignCoefficient, ht.1.2] using hpBase (hbase.symm ▸ hm)
    have hsecond : ρ (t + Real.pi / 2) ≤ 1 / 2 := by
      simpa [sameSignCoefficient, hnot] using hpComp (hshift.symm ▸ hm)
    exact ⟨le_antisymm hfirst (hρ0 t), hsecond⟩
  · rintro ⟨hq, hr⟩
    have hm : 0 < sameSignVelocityMargin false K t := by
      simpa [sameSignVelocityMargin] using lt_min hr (neg_pos.mpr hq)
    have hfirst : ρ t ≤ 1 / 2 := by
      simpa [sameSignCoefficient, ht.1.2] using hnBase (hbase.symm ▸ hm)
    have hsecond : ρ (t + Real.pi / 2) ≤ 0 := by
      simpa [sameSignCoefficient, hnot] using hnComp (hshift.symm ▸ hm)
    exact ⟨le_antisymm hsecond (hρ0 _), hfirst⟩

end AmbidextrousSofa
