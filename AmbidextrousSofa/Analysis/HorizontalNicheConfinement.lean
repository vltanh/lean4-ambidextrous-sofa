module

public import AmbidextrousSofa.Analysis.HorizontalUnitCurvature
public import AmbidextrousSofa.Measure.GraphIntegral

@[expose] public section

/-!
# Actual endpoint order and horizontal niche confinement

Unit curvature orders both tangency abscissae from their true axis
and top endpoints. The width gap separates the two tangencies and
excludes reverse corners. The wall derivatives then show that every
positive niche point lies strictly between the two middle endpoints.
The spatial score is consequently ready for the actual signed-roof
area calculation.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem IsFullCapMaximizer.corner_velocity_pos_or_pos_of_unit_density
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {C t : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρC : ∀ x, ρ x ≤ C)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (hunit : ∀ᵐ u ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      ρ u ≤ 1 ∧ ρ (u + Real.pi / 2) ≤ 1)
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < firstCornerVelocity U t ∨ 0 < secondCornerVelocity U t := by
  have hsub := regularCornerDomain_zero.ge
  -- the first tangency starts at the right axis, the second one ends at the left axis
  have hB : horizontalRight U - 1 ≤ (firstTangency U t).1 := by
    have hm := (hU.isCap.firstTangency_monotoneOn_open_of_unit_density hρ hρ0 hρC heq hsub
      (hunit.mono fun _ h => h.1)).1
    refine le_of_tendsto hU.isCap.firstTangency_tendsto_zero_right.fst_nhds ?_
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (isOpen_Iio.mem_nhds ht.1)]
      with u hu0 hut using hm ⟨hu0, hut.trans ht.2⟩ ht hut.le
  have hD : (secondTangency U t).1 ≤ horizontalLeft U + 1 := by
    have hm := (hU.isCap.secondTangency_monotoneOn_open_of_unit_density hρ hρ0 hρC heq hsub
      (hunit.mono fun _ h => h.2)).1
    refine ge_of_tendsto hU.isCap.secondTangency_tendsto_pi_div_two_left.fst_nhds ?_
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds ht.2)]
      with u huL htu using hm ht ⟨ht.1.trans htu, huL⟩ htu.le
  have hw := hU.two_lt_width
  rw [capWidth] at hw
  have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
  by_contra! h
  simp only [firstTangency, secondTangency] at hB hD
  linarith [mul_nonpos_of_nonpos_of_nonneg h.1 hc.le, mul_nonpos_of_nonpos_of_nonneg h.2 hs.le]

theorem IsDownwardCap.capScore_eq_volume_sub_middle_niche_of_horizontal
    {U : Set Plane} (hU : IsDownwardCap U)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1) :
    capScore U (Real.pi / 2) = volume.real U - capWidth U / 2 -
      ∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U),
        sweptNiche U (Real.pi / 2) x := by
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  have hroof : (∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x) =
      capWidth U / 2 := by
    rw [setIntegral_congr_fun (measurableSet_middleHalfInterval _ _) hmiddle, setIntegral_const,
      smul_eq_mul, mul_one, volumeReal_middleHalfInterval hlr]
    rfl
  rw [hU.capScore_pi_div_two,
    setIntegral_sdiff (measurableSet_middleHalfInterval _ _)
      (hU.integrableOn_capRoof_Icc _ _) (middleHalfInterval_subset hlr),
    ← hU.volumeReal_eq_integral_capRoof, hroof]

end AmbidextrousSofa
