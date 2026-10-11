module

public import AmbidextrousSofa.Analysis.CornerEndpointEnergy

@[expose] public section

/-!
# The actual companion-quarter endpoint energy

The companion energy uses the original cap and its literal density.
Its derivative has the terminal-time sign, so the left axis limit
controls it without transporting curvature through a reflected body.
The same-sign law includes the clipping level through the established
almost-everywhere derivative formula.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

/-- An absolutely continuous function whose derivative is nonnegative almost everywhere
above a height stays below that height before a terminal time at which it is below it. -/
theorem absolutelyContinuousOnInterval_le_of_ae_deriv_nonneg_above
    {f : ℝ → ℝ} {a b H : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (hab : a ≤ b) (hterminal : f b ≤ H)
    (hd : ∀ᵐ t ∂volume.restrict (Ioo a b), H < f t → 0 ≤ deriv f t)
    {x : ℝ} (hx : x ∈ Icc a b) : f x ≤ H := by
  have hg := (absolutelyContinuousOnInterval_max_const hf H).mono (by
    rw [uIcc_of_le hx.2, uIcc_of_le hab]
    exact Icc_subset_Icc hx.1 le_rfl)
  have hgd : ∀ᵐ t ∂volume.restrict (Icc x b), 0 ≤ deriv (fun s => max (f s) H) t := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_left hx.1) hd,
      ae_restrict_of_ae (ae_hasDerivAt_max_const hf H)] with t ht hdt hmt
    rw [(hmt (by rw [uIcc_of_le hab]; exact ⟨hx.1.trans ht.1.le, ht.2.le⟩)).deriv]
    split_ifs with hpos
    exacts [hdt hpos, le_rfl]
  have h := intervalIntegral.integral_nonneg_of_ae_restrict hx.2 hgd
  rw [hg.integral_deriv_eq_sub, max_eq_right hterminal] at h
  linarith [le_max_left (f x) H]

theorem clippedCornerEnergy_le_max_terminal
    {p q u v : ℝ → ℝ} {a b : ℝ}
    (hp : AbsolutelyContinuousOnInterval p a b)
    (hq : AbsolutelyContinuousOnInterval q a b) (hab : a ≤ b)
    (hode : ∀ᵐ t ∂volume.restrict (Ioo a b),
      HasDerivAt p (1 + q t - u t) t ∧ HasDerivAt q (1 - p t - v t) t)
    (hbound : ∀ᵐ t ∂volume.restrict (Ioo a b), p t ≤ 1 ∧ -1 ≤ q t)
    (hκ : ∀ᵐ t ∂volume.restrict (Ioo a b), v t ≤ sourceKappa (p t))
    (hshadow : ∀ᵐ t ∂volume.restrict (Ioo a b),
      0 < p t → 0 < q t → u t = 0 ∧ v t ≤ 1 / 2)
    {t : ℝ} (ht : t ∈ Icc a b) :
    clippedCornerEnergy p q t ≤ max (17 / 4) (clippedCornerEnergy p q b) := by
  refine absolutelyContinuousOnInterval_le_of_ae_deriv_nonneg_above
    (absolutelyContinuousOnInterval_clippedCornerEnergy hp hq) hab (le_max_right _ _) ?_ ht
  -- The reversed system is the forward one with `2 + 2 q - u` and `2 - 2 p - v`.
  filter_upwards [ae_hasDerivAt_clippedCornerEnergy (u := fun t => 2 + 2 * q t - u t)
      (v := fun t => 2 - 2 * p t - v t) hp hab
      (hode.mono fun t h => ⟨h.1.congr_deriv (by ring), h.2.congr_deriv (by ring)⟩),
    hbound, hκ, hshadow] with x hd hb hk hs hE
  have h := clippedCornerEnergy_derivative_nonpos_above hb.1 hb.2 hk hs
    ((le_max_left _ _).trans_lt hE)
  rw [hd.deriv]
  split_ifs at h ⊢ <;> linarith

def actualCompanionEnergy (U : Set Plane) : ℝ → ℝ :=
  clippedCornerEnergy (fun t => -firstCornerVelocity U t) (secondCornerVelocity U)

theorem IsFullCapMaximizer.actualCompanionEnergy_le_max_terminal_on_interval
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {C m c a b t : ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρC : ∀ x, ρ x ≤ C)
    (hκ : ∀ x, ρ x ≤ sourceKappa (upperCornerVelocity U x))
    (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
      (volume.restrict (regularCurvatureDomain m)).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (hab : a ≤ b) (hsub : Icc a b ⊆ regularCornerDomain m) (ht : t ∈ Icc a b) :
    actualCompanionEnergy U t ≤ max (17 / 4) (actualCompanionEnergy U b) := by
  have hdir := regularCornerDomain_interval_directions hsub
  have hac := hU.isCap.absolutelyContinuousOnInterval_cornerVelocities_of_density
    hρ hρ0 hρC heq hab hdir.1 hdir.2
  refine clippedCornerEnergy_le_max_terminal (p := fun x => -firstCornerVelocity U x)
    (u := fun x => ρ (x + Real.pi / 2)) (v := ρ) hac.1.neg hac.2 hab ?_
    (Eventually.of_forall fun x => ⟨by linarith [hU.isCap.firstCornerVelocity_ge_neg_one x],
      by linarith [hU.isCap.neg_secondCornerVelocity_le_one x]⟩) ?_ ?_ ht
  · filter_upwards [hU.isCap.ae_hasDerivAt_cornerVelocities_of_density
      hρ hρ0 hρC heq hab hdir.1 hdir.2] with x hd
    exact ⟨hd.1.neg.congr_deriv (by ring), hd.2.congr_deriv (by ring)⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simpa only [sourceKappa_neg] using
      (upperCorner_density_bounds_on_quarter hκ (hsub (Ioo_subset_Icc_self hx)).1).1
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Icc_self.trans hsub)
      (hU.ae_curvature_same_sign_quadrants haffine hρ hρ0 hρC heq)] with x hx hp hq
    exact hx.2 ⟨by linarith, hq⟩

theorem IsFullCapMaximizer.actualCompanionEnergy_tendsto_pi_div_two_left
    {U : Set Plane} (hU : IsFullCapMaximizer U) (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1) :
    Tendsto (actualCompanionEnergy U) (𝓝[<] (Real.pi / 2))
      (𝓝 ((capRoof U (horizontalLeft U) - 1 / 2) ^ 2 + (3 * capWidth U / 4) ^ 2)) := by
  have hvel := hU.cornerVelocities_tendsto_pi_div_two_left hheight hmiddle
  have hE := (((hvel.fst_nhds.neg.max (tendsto_const_nhds (x := (0 : ℝ)))).sub_const
    (1 / 2)).pow 2).add ((hvel.snd_nhds.add_const 1).pow 2)
  change Tendsto (actualCompanionEnergy U) _ _ at hE
  have heL : 0 ≤ capRoof U (horizontalLeft U) :=
    capRoof_nonneg hU.isCap.isCompact (fun p hp => (hU.isCap.inStrip hp).1) _
  have hwidth : horizontalRight U - capWidth U / 4 - horizontalLeft U - 1 + 1 =
      3 * capWidth U / 4 := by
    rw [capWidth]
    ring
  simpa only [neg_neg, max_eq_left heL, hwidth] using hE

theorem IsFullCapMaximizer.actualCompanionEnergy_le_of_endpoint_criterion
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {C t : ℝ}
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1)
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρC : ∀ x, ρ x ≤ C)
    (hκ : ∀ x, ρ x ≤ sourceKappa (upperCornerVelocity U x))
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (henergy : (3 * capWidth U / 4) ^ 2 ≤
      4 + capRoof U (horizontalLeft U) * (1 - capRoof U (horizontalLeft U)))
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) : actualCompanionEnergy U t ≤ 17 / 4 := by
  have heL : (capRoof U (horizontalLeft U) - 1 / 2) ^ 2 + (3 * capWidth U / 4) ^ 2 ≤ 17 / 4 := by
    linear_combination henergy
  refine (ge_of_tendsto ((tendsto_const_nhds (x := (17 / 4 : ℝ))).max
    (hU.actualCompanionEnergy_tendsto_pi_div_two_left hheight hmiddle)) ?_).trans
    (max_le le_rfl heL)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds ht.2).filter_mono nhdsWithin_le_nhds] with b hb htb
  exact hU.actualCompanionEnergy_le_max_terminal_on_interval (m := 0) (c := 1)
    (by simpa only [zero_mul, zero_add] using hmiddle) hρ hρ0 hρC hκ heq htb.le
    (by rw [regularCornerDomain_zero]; exact fun x hx => ⟨ht.1.trans_le hx.1, hx.2.trans_lt hb⟩)
    ⟨le_rfl, htb.le⟩

/-- The actual left endpoint criterion supplies the companion quarter;
the already proved visibility and crossing argument supplies the first.
The two conclusions concern the same literal density of the same cap. -/
theorem IsFullCapMaximizer.ae_both_density_le_one_of_left_endpoint_criterion
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {C : ℝ}
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1)
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρC : ∀ x, ρ x ≤ C)
    (hκ : ∀ x, ρ x ≤ sourceKappa (upperCornerVelocity U x))
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (henergy : (3 * capWidth U / 4) ^ 2 ≤
      4 + capRoof U (horizontalLeft U) * (1 - capRoof U (horizontalLeft U))) :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      ρ t ≤ 1 ∧ ρ (t + Real.pi / 2) ≤ 1 := by
  have hshadow := hU.ae_curvature_same_sign_quadrants (m := 0) (c := 1)
    (by simpa only [zero_mul, zero_add] using hmiddle) hρ hρ0 hρC heq
  rw [regularCornerDomain_zero] at hshadow
  have hcompanion : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      ρ (t + Real.pi / 2) ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hshadow] with t ht hs
    exact curvature_le_one_of_clippedCornerEnergy (p := -firstCornerVelocity U t)
      (by linarith [hU.isCap.neg_secondCornerVelocity_le_one t])
      (upperCorner_density_bounds_on_quarter hκ ht).2 (fun hp hq => (hs.2 ⟨by linarith, hq⟩).1)
      (hU.actualCompanionEnergy_le_of_endpoint_criterion hheight hmiddle hρ hρ0 hρC hκ heq
        henergy ht)
  exact (hU.ae_first_density_le_one_of_unit_companion hheight hmiddle hρ hρ0 hρC hκ heq
    hcompanion).and hcompanion

end AmbidextrousSofa
