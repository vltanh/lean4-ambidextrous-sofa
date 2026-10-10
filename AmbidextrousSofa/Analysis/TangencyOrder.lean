import AmbidextrousSofa.Analysis.TangencyEndpoints
import AmbidextrousSofa.Analysis.RegularTangency

/-!
# Order and floor bounds for the actual unit-curvature tangency

The companion tangency starts at the actual left endpoint of the top
facet. Unit companion curvature makes both coordinates nondecreasing.
Its tangent also stays above the direction at the beginning of every
regular interval. Consequently each strictly advanced abscissa has
strictly positive height, even if the initial height is zero.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem IsDownwardCap.secondTangency_cross_monotone_of_unit_density
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {C a b : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hab : a ≤ b) (hquarter : Icc a b ⊆ Ioo (0 : ℝ) (Real.pi / 2))
    (hbase : Icc a b ⊆ S) (hshift : Icc (a + Real.pi / 2) (b + Real.pi / 2) ⊆ S)
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo a b), ρ (t + Real.pi / 2) ≤ 1) :
    MonotoneOn (fun t => Real.cos a * (secondTangency U t).2 -
      Real.sin a * (secondTangency U t).1) (Icc a b) := by
  have hac := hU.absolutelyContinuousOnInterval_tangency_coordinates_of_density
    hρ hρ0 hρC heq hab hbase hshift
  have hd := hU.ae_hasDerivAt_tangency_coordinates_of_density
    hρ hρ0 hρC heq hab hbase hshift
  apply absolutelyContinuousOnInterval_monotoneOn_of_ae_hasDerivAt_nonneg
    ((hac.2.2.2.const_mul (Real.cos a)).sub (hac.2.2.1.const_mul (Real.sin a))) hab
  filter_upwards [ae_restrict_mem measurableSet_Ioo, hd, hunit] with t ht hdt hu
  have hderiv := (hdt.2.2.2.const_mul (Real.cos a)).sub (hdt.2.2.1.const_mul (Real.sin a))
  have hformula : Real.cos a * ((1 - ρ (t + Real.pi / 2)) * Real.sin t) -
      Real.sin a * ((1 - ρ (t + Real.pi / 2)) * Real.cos t) =
        (1 - ρ (t + Real.pi / 2)) * Real.sin (t - a) := by
    rw [Real.sin_sub]
    ring
  rw [hformula] at hderiv
  refine ⟨hderiv, mul_nonneg (sub_nonneg.mpr hu) ?_⟩
  apply Real.sin_nonneg_of_mem_Icc
  have haq := hquarter (left_mem_Icc.mpr hab)
  have htq := hquarter (Ioo_subset_Icc_self ht)
  constructor <;> linarith [ht.1, haq.1, htq.2, Real.pi_pos]

theorem IsDownwardCap.secondTangency_snd_pos_of_fst_gt
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {C a b : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hab : a ≤ b) (hquarter : Icc a b ⊆ Ioo (0 : ℝ) (Real.pi / 2))
    (hbase : Icc a b ⊆ S) (hshift : Icc (a + Real.pi / 2) (b + Real.pi / 2) ⊆ S)
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo a b), ρ (t + Real.pi / 2) ≤ 1)
    (hfloor : 0 ≤ (secondTangency U a).2)
    (hmove : (secondTangency U a).1 < (secondTangency U b).1) :
    0 < (secondTangency U b).2 := by
  have hm := hU.secondTangency_cross_monotone_of_unit_density hρ hρ0 hρC heq hab
    hquarter hbase hshift hunit (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
  have haq := hquarter (left_mem_Icc.mpr hab)
  have hs := Real.sin_pos_of_pos_of_lt_pi haq.1 (by linarith [haq.2, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [haq.1, Real.pi_pos], haq.2⟩
  by_contra hnot
  have hnonpos := mul_nonpos_of_nonneg_of_nonpos hc.le (le_of_not_gt hnot)
  have hnonneg := mul_nonneg hc.le hfloor
  have hstrict := mul_pos hs (sub_pos.mpr hmove)
  nlinarith

theorem IsFullCapMaximizer.secondTangency_from_top_endpoint
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {C t : ℝ}
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1)
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρC : ∀ x, ρ x ≤ C)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (hcompanion : ∀ᵐ u ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ (u + Real.pi / 2) ≤ 1)
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    horizontalLeft U + capWidth U / 4 ≤ (secondTangency U t).1 ∧ 0 ≤ (secondTangency U t).2 := by
  have hsub : Ioo (0 : ℝ) (Real.pi / 2) ⊆ regularCornerDomain 0 := by
    intro u hu
    simpa only [regularCornerDomain_zero] using hu
  have hm := hU.isCap.secondTangency_monotoneOn_open_of_unit_density
    hρ hρ0 hρC heq hsub hcompanion
  have hlim := hU.secondTangency_tendsto_zero_right hheight hmiddle
  have horder : ∀ᶠ u in 𝓝[>] (0 : ℝ),
      (secondTangency U u).1 ≤ (secondTangency U t).1 ∧
        (secondTangency U u).2 ≤ (secondTangency U t).2 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (isOpen_Iio.mem_nhds ht.1)] with u hu0 hut
    have hu : u ∈ Ioo (0 : ℝ) (Real.pi / 2) := ⟨hu0, hut.trans ht.2⟩
    exact ⟨hm.1 hu ht hut.le, hm.2 hu ht hut.le⟩
  exact ⟨le_of_tendsto hlim.fst (horder.mono (fun _ h => h.1)),
    le_of_tendsto hlim.snd (horder.mono (fun _ h => h.2))⟩

theorem IsFullCapMaximizer.firstTangency_before_top_endpoint
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {C b₀ t : ℝ}
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1)
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρC : ∀ x, ρ x ≤ C)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (hb₀ : 0 ≤ b₀)
    (hfuture : ∀ᵐ u ∂volume.restrict (Ioo b₀ (Real.pi / 2)), ρ u ≤ 1)
    (ht : t ∈ Ioo b₀ (Real.pi / 2)) :
    (firstTangency U t).1 ≤ horizontalRight U - capWidth U / 4 ∧ 0 ≤ (firstTangency U t).2 := by
  have hsub : Ioo b₀ (Real.pi / 2) ⊆ regularCornerDomain 0 := by
    intro u hu
    have huq : u ∈ Ioo (0 : ℝ) (Real.pi / 2) := ⟨hb₀.trans_lt hu.1, hu.2⟩
    simpa only [regularCornerDomain_zero] using huq
  have hm := hU.isCap.firstTangency_monotoneOn_open_of_unit_density
    hρ hρ0 hρC heq hsub hfuture
  have hlim := hU.firstTangency_tendsto_pi_div_two_left hheight hmiddle
  have horder : ∀ᶠ u in 𝓝[<] (Real.pi / 2),
      (firstTangency U t).1 ≤ (firstTangency U u).1 ∧
        (firstTangency U u).2 ≤ (firstTangency U t).2 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds ht.2)] with u huL htu
    have hu : u ∈ Ioo b₀ (Real.pi / 2) := ⟨ht.1.trans htu, huL⟩
    exact ⟨hm.1 ht hu htu.le, hm.2 ht hu htu.le⟩
  exact ⟨le_of_tendsto_of_tendsto tendsto_const_nhds hlim.fst (horder.mono (fun _ h => h.1)),
    le_of_tendsto hlim.snd (horder.mono (fun _ h => h.2))⟩

theorem IsFullCapMaximizer.visible_corner_middle_and_height
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {C b₀ t : ℝ}
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1)
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρC : ∀ x, ρ x ≤ C)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (hb₀ : 0 ≤ b₀)
    (hcompanion : ∀ᵐ u ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ (u + Real.pi / 2) ≤ 1)
    (hfuture : ∀ᵐ u ∂volume.restrict (Ioo b₀ (Real.pi / 2)), ρ u ≤ 1)
    (ht : t ∈ Ioo b₀ (Real.pi / 2))
    (hq : 0 < firstCornerVelocity U t) (hr : 0 < secondCornerVelocity U t) :
    horizontalLeft U + capWidth U / 4 ≤ (secondTangency U t).1 ∧
      (attachedCorner U t).1 ≤ horizontalRight U - capWidth U / 4 ∧
        0 < (attachedCorner U t).2 := by
  have htq : t ∈ Ioo (0 : ℝ) (Real.pi / 2) := ⟨hb₀.trans_lt ht.1, ht.2⟩
  have hD := hU.secondTangency_from_top_endpoint hheight hmiddle hρ hρ0 hρC heq hcompanion htq
  have hB := hU.firstTangency_before_top_endpoint hheight hmiddle hρ hρ0 hρC heq hb₀ hfuture ht
  have hs := Real.sin_pos_of_pos_of_lt_pi htq.1 (by linarith [htq.2, Real.pi_pos])
  refine ⟨hD.1, ?_, ?_⟩
  · have hbr : (attachedCorner U t).1 ≤ (firstTangency U t).1 := by
      dsimp only [firstTangency]
      nlinarith [mul_pos hr hs]
    exact hbr.trans hB.1
  · have hfloor := hD.2
    dsimp only [secondTangency] at hfloor
    nlinarith [mul_pos hq hs]

end AmbidextrousSofa
