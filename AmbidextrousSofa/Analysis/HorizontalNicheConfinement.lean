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

theorem IsFullCapMaximizer.firstTangency_from_right_axis
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {C t : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρC : ∀ x, ρ x ≤ C)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (hfirst : ∀ᵐ u ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ u ≤ 1)
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    horizontalRight U - 1 ≤ (firstTangency U t).1 ∧
      (firstTangency U t).2 ≤ capRoof U (horizontalRight U) := by
  have hsub : Ioo (0 : ℝ) (Real.pi / 2) ⊆ regularCornerDomain 0 := by
    rw [regularCornerDomain_zero]
  have hm := hU.isCap.firstTangency_monotoneOn_open_of_unit_density
    hρ hρ0 hρC heq hsub hfirst
  have hlim := hU.isCap.firstTangency_tendsto_zero_right
  have horder : ∀ᶠ u in 𝓝[>] (0 : ℝ),
      (firstTangency U u).1 ≤ (firstTangency U t).1 ∧
        (firstTangency U t).2 ≤ (firstTangency U u).2 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (isOpen_Iio.mem_nhds ht.1)] with u hu0 hut
    have hu : u ∈ Ioo (0 : ℝ) (Real.pi / 2) := ⟨hu0, hut.trans ht.2⟩
    exact ⟨hm.1 hu ht hut.le, hm.2 hu ht hut.le⟩
  exact ⟨le_of_tendsto hlim.fst_nhds (horder.mono (fun _ h => h.1)),
    ge_of_tendsto hlim.snd_nhds (horder.mono (fun _ h => h.2))⟩

theorem IsFullCapMaximizer.secondTangency_before_left_axis
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {C t : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρC : ∀ x, ρ x ≤ C)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (hcompanion : ∀ᵐ u ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ (u + Real.pi / 2) ≤ 1)
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    (secondTangency U t).1 ≤ horizontalLeft U + 1 ∧
      (secondTangency U t).2 ≤ capRoof U (horizontalLeft U) := by
  have hsub : Ioo (0 : ℝ) (Real.pi / 2) ⊆ regularCornerDomain 0 := by
    rw [regularCornerDomain_zero]
  have hm := hU.isCap.secondTangency_monotoneOn_open_of_unit_density
    hρ hρ0 hρC heq hsub hcompanion
  have hlim := hU.isCap.secondTangency_tendsto_pi_div_two_left
  have horder : ∀ᶠ u in 𝓝[<] (Real.pi / 2),
      (secondTangency U t).1 ≤ (secondTangency U u).1 ∧
        (secondTangency U t).2 ≤ (secondTangency U u).2 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds ht.2)] with u huL htu
    have hu : u ∈ Ioo (0 : ℝ) (Real.pi / 2) := ⟨ht.1.trans htu, huL⟩
    exact ⟨hm.1 ht hu htu.le, hm.2 ht hu htu.le⟩
  exact ⟨ge_of_tendsto hlim.fst_nhds (horder.mono (fun _ h => h.1)),
    ge_of_tendsto hlim.snd_nhds (horder.mono (fun _ h => h.2))⟩

theorem IsFullCapMaximizer.tangency_horizontal_gap_pos_of_unit_density
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {C t : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρC : ∀ x, ρ x ≤ C)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (hunit : ∀ᵐ u ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      ρ u ≤ 1 ∧ ρ (u + Real.pi / 2) ≤ 1)
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < (firstTangency U t).1 - (secondTangency U t).1 := by
  have hB := hU.firstTangency_from_right_axis hρ hρ0 hρC heq
    (hunit.mono (fun _ h => h.1)) ht
  have hD := hU.secondTangency_before_left_axis hρ hρ0 hρC heq
    (hunit.mono (fun _ h => h.2)) ht
  have hw := hU.two_lt_width
  unfold capWidth at hw
  linarith [hB.1, hD.1]

theorem IsFullCapMaximizer.corner_velocity_pos_or_pos_of_unit_density
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {C t : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρC : ∀ x, ρ x ≤ C)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (hunit : ∀ᵐ u ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      ρ u ≤ 1 ∧ ρ (u + Real.pi / 2) ≤ 1)
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < firstCornerVelocity U t ∨ 0 < secondCornerVelocity U t := by
  have hgap := hU.tangency_horizontal_gap_pos_of_unit_density hρ hρ0 hρC heq hunit ht
  have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
  by_cases hq : 0 < firstCornerVelocity U t
  · exact Or.inl hq
  · right
    by_contra hr
    have hqc := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hq) hc.le
    have hrs := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hr) hs.le
    dsimp only [firstTangency, secondTangency, Prod.fst_add, Prod.fst_sub, Prod.fst] at hgap
    linarith

theorem IsDownwardCap.capScore_eq_volume_sub_middle_niche_of_horizontal
    {U : Set Plane} (hU : IsDownwardCap U)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1) :
    capScore U (Real.pi / 2) = volume.real U - capWidth U / 2 -
      ∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U),
        sweptNiche U (Real.pi / 2) x := by
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  have hroof : (∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x) =
      capWidth U / 2 := by
    calc
      _ = ∫ _x in middleHalfInterval (horizontalLeft U) (horizontalRight U), (1 : ℝ) :=
        setIntegral_congr_fun (measurableSet_middleHalfInterval _ _) hmiddle
      _ = capWidth U / 2 := by
        rw [setIntegral_const, smul_eq_mul, mul_one, volumeReal_middleHalfInterval hlr]
        rfl
  rw [hU.capScore_pi_div_two,
    setIntegral_sdiff (measurableSet_middleHalfInterval _ _)
      (hU.integrableOn_capRoof_Icc _ _) (middleHalfInterval_subset hlr),
    ← hU.volumeReal_eq_integral_capRoof, hroof]

end AmbidextrousSofa
