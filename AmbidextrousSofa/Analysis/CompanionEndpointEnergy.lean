module

public import AmbidextrousSofa.Analysis.CornerEndpointEnergy

@[expose] public section

/-!
# The actual companion-quarter endpoint energy

The companion energy uses the original cap and its literal density.
Its derivative has the terminal-time sign; reversing time turns the
initial energy bound into a terminal one, so the left axis limit
controls it without transporting curvature through a reflected body.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

/-- The time reversal `t ↦ a + b - t` of
`clippedCornerEnergy_le_max_of_zero_source_alternative`: for the terminal-time system the
clipped energy stays below the larger of `17/4` and its terminal value. -/
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
  have hrev {P : ℝ → Prop} (h : ∀ᵐ t ∂volume.restrict (Ioo a b), P t) :
      ∀ᵐ s ∂volume.restrict (Ioo a b), P (a + b - s) := by
    simpa only [add_sub_cancel_right, add_sub_cancel_left] using
      ae_restrict_Ioo_comp_const_sub (c := a + b) h
  have hac {f : ℝ → ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
      AbsolutelyContinuousOnInterval (fun s => f (a + b - s)) a b := by
    simpa only [add_sub_cancel_right, add_sub_cancel_left] using
      absolutelyContinuousOnInterval_comp_const_sub hf hab (a + b)
  have h := clippedCornerEnergy_le_max_of_zero_source_alternative (u := fun s => u (a + b - s))
    (v := fun s => v (a + b - s)) (hac hp) (hac hq) hab
    ((hrev hode).mono fun s h => ⟨(h.1.comp_const_sub (a + b) s).congr_deriv (by ring),
      (h.2.comp_const_sub (a + b) s).congr_deriv (by ring)⟩)
    ((hrev hbound).mono fun _ h => h.2) (hrev hκ) (hrev hshadow)
    ((hrev hbound).mono fun _ h => .inl h.1) (t := a + b - t)
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  simpa only [clippedCornerEnergy, add_sub_cancel_left, sub_sub_cancel] using h

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
