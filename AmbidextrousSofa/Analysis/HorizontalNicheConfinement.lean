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
  exact ⟨le_of_tendsto hlim.fst (horder.mono (fun _ h => h.1)),
    ge_of_tendsto hlim.snd (horder.mono (fun _ h => h.2))⟩

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
  exact ⟨ge_of_tendsto hlim.fst (horder.mono (fun _ h => h.1)),
    ge_of_tendsto hlim.snd (horder.mono (fun _ h => h.2))⟩

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

theorem IsFullCapMaximizer.firstWall_nonpos_right_of_middle_of_unit_density
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {C t x : ℝ}
    (hheight : capHeight U = 1)
    (hmiddle : ∀ y ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U y = 1)
    (hρ : Measurable ρ) (hρ0 : ∀ u, 0 ≤ ρ u) (hρC : ∀ u, ρ u ≤ C)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun u => ENNReal.ofReal (ρ u)))
    (hfirst : ∀ᵐ u ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ u ≤ 1)
    (hx : horizontalRight U - capWidth U / 4 ≤ x)
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) : firstWall U t x ≤ 0 := by
  have hf : Continuous (fun s => support U (unitNormal s)) :=
    (continuous_support hU.isCap.isCompact).comp continuous_unitNormal
  have hn : Continuous (fun s => support U (unitNormal s) - 1 - x * Real.cos s) :=
    (hf.sub_const 1).sub (Real.continuous_cos.const_mul x)
  have hcont : ContinuousAt (fun s => firstWall U s x) (Real.pi / 2) :=
    hn.continuousAt.div Real.continuous_sin.continuousAt (by simp)
  have hz : firstWall U (Real.pi / 2) x = 0 := by
    simp only [firstWall, unitNormal, Real.cos_pi_div_two, Real.sin_pi_div_two,
      mul_zero, sub_zero, div_one]
    change capHeight U - 1 = 0
    rw [hheight, sub_self]
  have hlim := hcont.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[<] (Real.pi / 2) ≤ 𝓝 (Real.pi / 2))
  rw [hz] at hlim
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds ht.2)] with b hb htb
  have hsub : Icc t b ⊆ Ioo (0 : ℝ) (Real.pi / 2) :=
    fun u hu => ⟨ht.1.trans_le hu.1, hu.2.trans_lt hb⟩
  apply endpoint_le_of_hasDerivAt_nonneg htb.le
    (fun u hu => (hU.isCap.hasDerivAt_walls_on_regularCornerDomain hρ hρ0 hρC heq
      (by simpa only [regularCornerDomain_zero] using hsub hu) x).1)
  intro u hu
  have hB := hU.firstTangency_before_top_endpoint hheight hmiddle hρ hρ0 hρC heq
    (by norm_num : (0 : ℝ) ≤ 0) hfirst (hsub (Ioo_subset_Icc_self hu))
  exact div_nonneg (sub_nonneg.mpr (hB.1.trans hx)) (sq_nonneg _)

theorem IsFullCapMaximizer.secondWall_nonpos_left_of_middle_of_unit_density
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {C t x : ℝ}
    (hheight : capHeight U = 1)
    (hmiddle : ∀ y ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U y = 1)
    (hρ : Measurable ρ) (hρ0 : ∀ u, 0 ≤ ρ u) (hρC : ∀ u, ρ u ≤ C)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun u => ENNReal.ofReal (ρ u)))
    (hcompanion : ∀ᵐ u ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ (u + Real.pi / 2) ≤ 1)
    (hx : x ≤ horizontalLeft U + capWidth U / 4)
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) : secondWall U t x ≤ 0 := by
  have hg : Continuous (fun s => support U (companionNormal s)) :=
    (continuous_support hU.isCap.isCompact).comp continuous_companionNormal
  have hn : Continuous (fun s => support U (companionNormal s) - 1 + x * Real.sin s) :=
    (hg.sub_const 1).add (Real.continuous_sin.const_mul x)
  have hcont : ContinuousAt (fun s => secondWall U s x) 0 :=
    hn.continuousAt.div Real.continuous_cos.continuousAt (by simp)
  have hz : secondWall U 0 x = 0 := by
    simp only [secondWall, companionNormal, Real.cos_zero, Real.sin_zero, neg_zero,
      mul_zero, add_zero, div_one]
    change capHeight U - 1 = 0
    rw [hheight, sub_self]
  have hlim := hcont.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  rw [hz] at hlim
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (isOpen_Iio.mem_nhds ht.1)] with a ha hat
  have hsub : Icc a t ⊆ Ioo (0 : ℝ) (Real.pi / 2) :=
    fun u hu => ⟨ha.trans_le hu.1, hu.2.trans_lt ht.2⟩
  apply endpoint_le_of_hasDerivAt_nonpos hat.le
    (fun u hu => (hU.isCap.hasDerivAt_walls_on_regularCornerDomain hρ hρ0 hρC heq
      (by simpa only [regularCornerDomain_zero] using hsub hu) x).2)
  intro u hu
  have hD := hU.secondTangency_from_top_endpoint hheight hmiddle hρ hρ0 hρC heq
    hcompanion (hsub (Ioo_subset_Icc_self hu))
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hx.trans hD.1)) (sq_nonneg _)

theorem IsFullCapMaximizer.sweptNiche_eq_zero_outside_middle_of_unit_density
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {C x : ℝ}
    (hheight : capHeight U = 1)
    (hmiddle : ∀ y ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U y = 1)
    (hρ : Measurable ρ) (hρ0 : ∀ u, 0 ≤ ρ u) (hρC : ∀ u, ρ u ≤ C)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun u => ENNReal.ofReal (ρ u)))
    (hunit : ∀ᵐ u ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      ρ u ≤ 1 ∧ ρ (u + Real.pi / 2) ≤ 1)
    (hx : x ≤ horizontalLeft U + capWidth U / 4 ∨ horizontalRight U - capWidth U / 4 ≤ x) :
    sweptNiche U (Real.pi / 2) x = 0 := by
  apply le_antisymm _ (sweptNiche_nonneg _ _ _)
  apply sweptNiche_le_of_forall (by linarith [Real.pi_pos]) le_rfl
  intro t ht
  rcases hx with hx | hx
  · exact (min_le_right _ _).trans
      (hU.secondWall_nonpos_left_of_middle_of_unit_density hheight hmiddle hρ hρ0 hρC heq
        (hunit.mono (fun _ h => h.2)) hx ht)
  · exact (min_le_left _ _).trans
      (hU.firstWall_nonpos_right_of_middle_of_unit_density hheight hmiddle hρ hρ0 hρC heq
        (hunit.mono (fun _ h => h.1)) hx ht)

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
