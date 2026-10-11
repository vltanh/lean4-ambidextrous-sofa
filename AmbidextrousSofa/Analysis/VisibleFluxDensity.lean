module

public import AmbidextrousSofa.Analysis.VisibleGraphFlux
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

@[expose] public section

/-!
# The actual companion density lower bound on visible positive corners

A flux bound by curvature masses is differentiated at almost every
Lebesgue point of the bounded curvature density: the charged interval
mass divided by its width tends to the density, while the transverse
masses tend to zero. Applied to the two physical graph projections, after
the finite source limit has been proved, this gives
`1 + secondCornerVelocity ≤ 2 * companion density`.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

/-- Differentiation of a flux bound at almost every `x`, a Lebesgue point
of the bounded density `ρ` of `μ` on `S`. If every small increment
`G (t + h) - G t` is at most the mass of `(x, x + h]` plus `h` times the
masses of `(x, x + h]` and `(y, y + h]`, then `G' ≤ ρ x`: the first mass
divided by `h` tends to `ρ x`, while the other two tend to zero. -/
theorem ae_le_density_of_increment_le {μ : Measure ℝ} {ρ : ℝ → ℝ} {S : Set ℝ} {C : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ z, 0 ≤ ρ z) (hρC : ∀ z, ρ z ≤ C)
    (heq : μ.restrict S = (volume.restrict S).withDensity (fun z => ENNReal.ofReal (ρ z))) :
    ∀ᵐ x, ∀ (G : ℝ → ℝ) (G' t y : ℝ), HasDerivAt G G' t →
      (∀ᶠ h in 𝓝[>] 0, Ioc x (x + h) ⊆ S ∧ Ioc y (y + h) ⊆ S ∧ G (t + h) - G t ≤
        μ.real (Ioc x (x + h)) + h * (μ.real (Ioc x (x + h)) + μ.real (Ioc y (y + h)))) →
      G' ≤ ρ x := by
  have hlocal : LocallyIntegrable ρ volume := (locallyIntegrable_const C).mono
    hρ.aestronglyMeasurable (.of_forall fun z => abs_le_abs_of_nonneg (hρ0 z) (hρC z))
  -- On `(z, z + h] ⊆ S` the mass is an increment of the continuous primitive of `ρ`.
  have hmass {z h : ℝ} (hh : 0 < h) (hsub : Ioc z (z + h) ⊆ S) :
      μ.real (Ioc z (z + h)) = ∫ w in z..z + h, ρ w :=
    (measureReal_eq_integral_of_restrict_withDensity hρ hρ0 heq measurableSet_Ioc hsub).trans
      (intervalIntegral.integral_of_le (le_add_of_nonneg_right hh.le)).symm
  have hzero (z : ℝ) : Tendsto (fun h => ∫ w in z..z + h, ρ w) (𝓝[>] 0) (𝓝 0) :=
    (((intervalIntegral.continuous_primitive (intervalIntegrable_bounded_real_density hρ hρ0 hρC)
      z).comp (continuous_const_add z)).tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hlocal] with x hx G G' t y hG hbound
  have hslope := (hx x).tendsto_slope_zero_right
  simp only [intervalIntegral.integral_same, sub_zero, smul_eq_mul] at hslope
  have hlim := hslope.add ((hzero x).add (hzero y))
  rw [add_zero, add_zero] at hlim
  refine le_of_tendsto_of_tendsto hG.tendsto_slope_zero_right hlim ?_
  filter_upwards [hbound, self_mem_nhdsWithin] with h ⟨hx', hy', hb⟩ (hh : 0 < h)
  rw [hmass hh hx', hmass hh hy'] at hb
  rw [smul_eq_mul, inv_mul_le_iff₀ hh, mul_add, ← mul_assoc, mul_inv_cancel₀ hh.ne', one_mul]
  exact hb

/-- The actual horizontal top endpoints discharge the height and middle
containment of both visible graph pieces. Zero-height tangency pieces
are included through the proved angular order inequality. -/
theorem IsFullCapMaximizer.ae_companion_density_ge_of_unit_companion_and_future
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {C b₀ : ℝ}
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1)
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρC : ∀ x, ρ x ≤ C)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (hb₀ : 0 ≤ b₀)
    (hcompanion : ∀ᵐ u ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ (u + Real.pi / 2) ≤ 1)
    (hfuture : ∀ᵐ u ∂volume.restrict (Ioo b₀ (Real.pi / 2)), ρ u ≤ 1) :
    ∀ᵐ t ∂volume.restrict (Ioo b₀ (Real.pi / 2)),
      0 < firstCornerVelocity U t → 0 < secondCornerVelocity U t →
        1 + secondCornerVelocity U t ≤ 2 * ρ (t + Real.pi / 2) := by
  -- Almost every `t` is a point of differentiability of the second tangency, and `t + π / 2`
  -- is a Lebesgue point of `ρ`.
  have hTang := hU.isCap.ae_hasDerivAt_tangency_coordinates_on_regularCornerDomain
    hρ hρ0 hρC heq
  rw [regularCornerDomain_zero] at hTang
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_left hb₀) hTang,
    ae_restrict_of_ae ((measurePreserving_add_right volume (Real.pi / 2)).quasiMeasurePreserving.ae
      (ae_le_density_of_increment_le hρ hρ0 hρC heq))] with t ht hT hL hq hr
  obtain ⟨hleft, hright, hcy⟩ := hU.visible_corner_middle_and_height hheight hmiddle hρ hρ0 hρC
    heq hb₀ hcompanion hfuture ht hq hr
  have htreg := regularCornerDomain_zero.ge (Ioo_subset_Ioo_left hb₀ ht)
  have hvelocity := hU.isCap.continuousAt_cornerVelocities_on_regularCornerDomain
    hρ hρ0 hρC heq htreg
  have hcorner := hU.isCap.hasDerivAt_corner_coordinates_on_regularCornerDomain
    hρ hρ0 hρC heq htreg
  -- On a neighborhood `(a, b)` of `t` all the localization hypotheses of the graph flux hold.
  obtain ⟨a, b, htI, hIP⟩ := mem_nhds_iff_exists_Ioo_subset.mp (Filter.Eventually.and
    (isOpen_Ioo.mem_nhds ht) ((hvelocity.1.tendsto.eventually (lt_mem_nhds hq)).and
      ((hvelocity.2.tendsto.eventually (lt_mem_nhds hr)).and
        (hcorner.2.continuousAt.tendsto.eventually (lt_mem_nhds hcy)))))
  -- Differentiate the graph flux bound on `[t, t + h]`.
  have key := hL _ _ t t (((hT.2.2.1.const_mul (Real.cos t)).add
    (hT.2.2.2.const_mul (Real.sin t))).sub
      ((hcorner.1.const_mul (Real.cos t)).add (hcorner.2.const_mul (Real.sin t)))) ?_
  · simp only [cornerVelocityX, cornerVelocityY] at key
    linarith [congrArg ((1 - ρ (t + Real.pi / 2)) * ·) (Real.sin_sq_add_cos_sq t),
      congrArg (secondCornerVelocity U t * ·) (Real.sin_sq_add_cos_sq t)]
  filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 htI.2)] with h hh
  have hn : Icc t (t + h) ⊆ Ioo a b := Icc_subset_Ioo htI.1 (by linarith [hh.2])
  obtain ⟨h₁, h₂⟩ := regularCornerDomain_interval_directions fun u hu =>
    regularCornerDomain_zero.ge (Ioo_subset_Ioo_left hb₀ (hIP (hn hu)).1)
  have hflux := hU.visible_tangency_corner_flux hheight hmiddle hρ hρ0 hρC heq hb₀
    hcompanion hfuture (lt_add_of_pos_right t hh.1) (left_mem_Icc.2 (le_add_of_nonneg_right hh.1.le))
    (fun u hu => (hIP (hn hu)).1) (fun u hu => (hIP (hn hu)).2.1) (fun u hu => (hIP (hn hu)).2.2.1)
    (fun u hu => (hU.secondTangency_from_top_endpoint hheight hmiddle hρ hρ0 hρC heq hcompanion
      (Ioo_subset_Ioo_left hb₀ (hIP (hn hu)).1)).2)
    (fun u hu => (hIP (hn hu)).2.2.2) hleft hright
  rw [add_right_comm t h, add_sub_cancel_left] at hflux
  rw [add_right_comm t h] at h₂
  exact ⟨Ioc_subset_Icc_self.trans h₂, Ioc_subset_Icc_self.trans h₁,
    by simp only [Pi.add_apply, Pi.sub_apply]; linarith⟩

end AmbidextrousSofa
