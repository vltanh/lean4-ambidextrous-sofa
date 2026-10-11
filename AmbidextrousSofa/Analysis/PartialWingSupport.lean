module

public import AmbidextrousSofa.Analysis.PartialNegativeCornerCurvature
public import AmbidextrousSofa.Analysis.PartialWidthBounds
public import AmbidextrousSofa.Analysis.TiltedWingSupport

@[expose] public section

/-!
# The actual two used support arcs of a proper maximum

Same-cap completion places the negative middle normal beyond the
terminal angle. In the other middle orientations that normal is at or
beyond the top. Consequently the entire first used open arc has the
proved density, and the literal left companion cut supplies the second
arc. The positive-tilt initial surrogate interval has both actual
densities zero; its first density vanishes because its original corner
is below the floor.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem ProperTailRegime.first_arc_subset_regular {U : Set Plane} {α m : ℝ}
    (hregime : ProperTailRegime U α m) (hproper : α < Real.pi / 2) :
    Ioo (0 : ℝ) α ⊆ regularProperCurvatureDomain α m := fun t ht =>
  ⟨mem_regularCurvatureDomain_iff.mpr ⟨ht.1, by linarith [ht.2, Real.pi_pos],
    (ht.2.trans hproper).ne, (affineNormal_coefficient_pos_before ht.1.le
      (ht.2.trans (hregime.terminal_lt_affineNormal hproper))).ne'⟩, ht.2.ne⟩

theorem regularCompanionDomain_subset_regularProperCurvatureDomain
    {α m : ℝ} (hproper : α < Real.pi / 2) :
    regularCompanionDomain m ⊆ regularProperCurvatureDomain α m := fun _ ht =>
  ⟨regularCompanionDomain_subset_regularCurvatureDomain m ht, (hproper.trans ht.1.1).ne'⟩

theorem ProperTailRegime.first_density_of_regular {U : Set Plane} {α m : ℝ} {ρ : ℝ → ℝ}
    (hregime : ProperTailRegime U α m) (hproper : α < Real.pi / 2)
    (heq : (upperCurvature U).restrict (regularProperCurvatureDomain α m) =
      (volume.restrict (regularProperCurvatureDomain α m)).withDensity
        (fun t => ENNReal.ofReal (ρ t))) :
    (upperCurvature U).restrict (Ioo (0 : ℝ) α) =
      (volume.restrict (Ioo (0 : ℝ) α)).withDensity (fun t => ENNReal.ofReal (ρ t)) :=
  restrict_withDensity_of_subset heq measurableSet_Ioo (hregime.first_arc_subset_regular hproper)

theorem IsJointCapMaximizer.proper_leftCompanion_density_of_regular
    {U : Set Plane} {α m c : ℝ} {ρ : ℝ → ℝ} (hU : IsJointCapMaximizer U α)
    (hproper : α < Real.pi / 2)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (heq : (upperCurvature U).restrict (regularProperCurvatureDomain α m) =
      (volume.restrict (regularProperCurvatureDomain α m)).withDensity
        (fun t => ENNReal.ofReal (ρ t))) :
    (upperCurvature (leftCompanionCap U (horizontalLeft U + capWidth U / 4))).restrict
        (Ioo (Real.pi / 2) Real.pi) =
      (volume.restrict (Ioo (Real.pi / 2) Real.pi)).withDensity
        (fun t => ENNReal.ofReal (leftCompanionWingDensity m ρ t)) :=
  hU.leftCompanion_density_of_regular_companion haffine
    (restrict_withDensity_of_subset heq (measurableSet_regularCompanionDomain m)
      (regularCompanionDomain_subset_regularProperCurvatureDomain hproper))

theorem IsJointCapMaximizer.proper_first_wing_initial_curvature_zero
    {U : Set Plane} {α C m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1) (hm : 0 ≤ m)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    upperCurvature U (Ioo (0 : ℝ) (Real.arctan m)) = 0 := by
  have hb :=
    hU.centered_proper_half_width_bounds hproper (hl.trans (neg_mul _ _)) hr hheight haffine
  have haff := (centered_quarter_points hl hr).2.2 ▸ haffine
  have hhigh : capRoof U C = 1 := by
    rw [← hU.middle_right_eq_one_of_affine_nonneg hheight hm haffine, capWidth, hl, hr]
    congr 1; ring
  -- The proper width and tilt bounds give the smallness needed for the positive-tilt interval.
  have hsmall : C + m < 1 := by
    have hmC : m = (1 - capRoof U (-C)) / (2 * C) := by
      rw [eq_div_iff (by linarith)]
      linarith [haff (-C) ⟨le_rfl, by linarith⟩, haff C ⟨by linarith, le_rfl⟩]
    exact hmC ▸ canonical_width_add_slope_lt_one (by linarith) (by linarith)
      (by simpa only [show -(2 * C) / 2 = -C by ring] using hb.2.2 hm)
  have hmα : Real.arctan m < α := by
    simpa [affineNormalAngle] using hU.middle_normal_lt_terminal_companion haffine
  refine le_antisymm ((measure_mono fun t ht => ?_).trans_eq
    (hU.upperCurvature_proper_negative_corners_eq_zero hproper haffine)) zero_le
  have htL := ht.2.trans (Real.arctan_lt_pi_div_two m)
  refine ⟨⟨firstQuarter_subset_regularCurvatureDomain_of_nonneg hm ⟨ht.1, htL⟩,
    (ht.2.trans hmα).ne⟩, ?_⟩
  simpa only [sourceCornerHeight, sourceQuarterAngle, htL, ↓reduceIte] using
    hU.isCap.attachedCorner_neg_before_positive_affine hl hr (by linarith) hsmall haff hhigh ht

end AmbidextrousSofa
