module

public import AmbidextrousSofa.Analysis.CornerPropagation

@[expose] public section

/-!
# The actual endpoint energy bound

The clipped energy is bounded by the larger of its true endpoint limit
and `17/4`. Passing to the endpoint uses the established one-sided
support limits. In particular, equality at the threshold does not need
an interior starting point with strictly smaller energy.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem clippedCornerEnergy_le_max_initial
    {p q u v : ℝ → ℝ} {a b : ℝ}
    (hp : AbsolutelyContinuousOnInterval p a b)
    (hq : AbsolutelyContinuousOnInterval q a b) (hab : a ≤ b)
    (hode : ∀ᵐ t ∂volume.restrict (Ioo a b),
      HasDerivAt p (u t - 1 - q t) t ∧ HasDerivAt q (v t - 1 + p t) t)
    (hbound : ∀ᵐ t ∂volume.restrict (Ioo a b), p t ≤ 1 ∧ -1 ≤ q t)
    (hκ : ∀ᵐ t ∂volume.restrict (Ioo a b), v t ≤ sourceKappa (p t))
    (hshadow : ∀ᵐ t ∂volume.restrict (Ioo a b),
      0 < p t → 0 < q t → u t = 0 ∧ v t ≤ 1 / 2)
    {t : ℝ} (ht : t ∈ Icc a b) :
    clippedCornerEnergy p q t ≤ max (17 / 4) (clippedCornerEnergy p q a) := by
  apply absolutelyContinuousOnInterval_le_of_ae_deriv_nonpos_above
    (absolutelyContinuousOnInterval_clippedCornerEnergy hp hq) hab (le_max_right _ _) _ ht
  filter_upwards [ae_hasDerivAt_clippedCornerEnergy hp hab hode, hbound, hκ, hshadow]
    with x hd hb hk hs
  intro hE
  rw [hd.deriv]
  exact clippedCornerEnergy_derivative_nonpos_above hb.1 hb.2 hk hs
    ((le_max_left _ _).trans_lt hE)

theorem IsFullCapMaximizer.actualCornerEnergy_le_max_initial_on_interval
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {C m c a b t : ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρC : ∀ x, ρ x ≤ C)
    (hκ : ∀ x, ρ x ≤ sourceKappa (upperCornerVelocity U x))
    (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
      (volume.restrict (regularCurvatureDomain m)).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (hab : a ≤ b) (hsub : Icc a b ⊆ regularCornerDomain m) (ht : t ∈ Icc a b) :
    actualCornerEnergy U t ≤ max (17 / 4) (actualCornerEnergy U a) := by
  have hdir := regularCornerDomain_interval_directions hsub
  have hac := hU.isCap.absolutelyContinuousOnInterval_cornerVelocities_of_density
    hρ hρ0 hρC heq hab hdir.1 hdir.2
  have hode : ∀ᵐ x ∂volume.restrict (Ioo a b),
      HasDerivAt (fun y => -secondCornerVelocity U y)
        (ρ x - 1 - firstCornerVelocity U x) x ∧
      HasDerivAt (firstCornerVelocity U)
        (ρ (x + Real.pi / 2) - 1 + -secondCornerVelocity U x) x := by
    filter_upwards [hU.isCap.ae_hasDerivAt_cornerVelocities_of_density
      hρ hρ0 hρC heq hab hdir.1 hdir.2] with x hd
    exact ⟨hd.2.neg.congr_deriv (by ring), hd.1.congr_deriv (by ring)⟩
  have hb : ∀ᵐ x ∂volume.restrict (Ioo a b),
      -secondCornerVelocity U x ≤ 1 ∧ -1 ≤ firstCornerVelocity U x :=
    Eventually.of_forall (fun x => ⟨hU.isCap.neg_secondCornerVelocity_le_one x,
      hU.isCap.firstCornerVelocity_ge_neg_one x⟩)
  have hk : ∀ᵐ x ∂volume.restrict (Ioo a b),
      ρ (x + Real.pi / 2) ≤ sourceKappa (-secondCornerVelocity U x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simpa only [sourceKappa_neg] using
      (upperCorner_density_bounds_on_quarter hκ (hsub (Ioo_subset_Icc_self hx)).1).2
  have hs : ∀ᵐ x ∂volume.restrict (Ioo a b),
      0 < -secondCornerVelocity U x → 0 < firstCornerVelocity U x →
        ρ x = 0 ∧ ρ (x + Real.pi / 2) ≤ 1 / 2 := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Icc_self.trans hsub)
      (hU.ae_curvature_same_sign_quadrants haffine hρ hρ0 hρC heq)] with x hx
    intro hp hq
    exact hx.1 ⟨hq, by linarith⟩
  exact clippedCornerEnergy_le_max_initial hac.2.neg hac.1 hab hode hb hk hs ht

theorem IsFullCapMaximizer.actualCornerEnergy_tendsto_zero_right
    {U : Set Plane} (hU : IsFullCapMaximizer U) (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1) :
    Tendsto (actualCornerEnergy U) (𝓝[>] (0 : ℝ))
      (𝓝 ((capRoof U (horizontalRight U) - 1 / 2) ^ 2 + (3 * capWidth U / 4) ^ 2)) := by
  have hvel := hU.cornerVelocities_tendsto_zero_right hheight hmiddle
  have hE := (((hvel.snd.neg.max tendsto_const_nhds).sub_const (1 / 2)).pow 2).add
    ((hvel.fst.add_const 1).pow 2)
  change Tendsto (actualCornerEnergy U) _ _ at hE
  have heR : 0 ≤ capRoof U (horizontalRight U) :=
    capRoof_nonneg hU.isCap.isCompact (fun p hp => (hU.isCap.inStrip hp).1) _
  have hwidth : horizontalRight U - 1 - (horizontalLeft U + capWidth U / 4) + 1 =
      3 * capWidth U / 4 := by unfold capWidth; ring
  simpa only [neg_neg, max_eq_left heR, hwidth] using hE

/-- A pointwise bound from the actual axis limit, valid throughout the
open quarter, including parameters after any number of sign changes. -/
theorem IsFullCapMaximizer.actualCornerEnergy_le_max_of_endpoint
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {C t : ℝ}
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1)
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρC : ∀ x, ρ x ≤ C)
    (hκ : ∀ x, ρ x ≤ sourceKappa (upperCornerVelocity U x))
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    actualCornerEnergy U t ≤
      max (17 / 4) ((capRoof U (horizontalRight U) - 1 / 2) ^ 2 + (3 * capWidth U / 4) ^ 2) := by
  have hlim := (tendsto_const_nhds (x := (17 / 4 : ℝ))).max
    (hU.actualCornerEnergy_tendsto_zero_right hheight hmiddle)
  apply ge_of_tendsto hlim
  have hlt : ∀ᶠ a in 𝓝[>] (0 : ℝ), a < t :=
    (eventually_lt_nhds ht.1).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hlt] with a ha hat
  have hsub : Icc a t ⊆ regularCornerDomain 0 := by
    rw [regularCornerDomain_zero]
    exact fun x hx => ⟨ha.trans_le hx.1, hx.2.trans_lt ht.2⟩
  exact hU.actualCornerEnergy_le_max_initial_on_interval (m := 0) (c := 1)
    (by simpa only [zero_mul, zero_add] using hmiddle)
    hρ hρ0 hρC hκ heq hat.le hsub ⟨hat.le, le_rfl⟩

theorem IsFullCapMaximizer.actualCornerEnergy_le_of_endpoint_criterion
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {C t : ℝ}
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1)
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρC : ∀ x, ρ x ≤ C)
    (hκ : ∀ x, ρ x ≤ sourceKappa (upperCornerVelocity U x))
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (henergy : (3 * capWidth U / 4) ^ 2 ≤
      4 + capRoof U (horizontalRight U) * (1 - capRoof U (horizontalRight U)))
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) : actualCornerEnergy U t ≤ 17 / 4 := by
  have he := hU.actualCornerEnergy_le_max_of_endpoint hheight hmiddle hρ hρ0 hρC hκ heq ht
  have he0 : (capRoof U (horizontalRight U) - 1 / 2) ^ 2 + (3 * capWidth U / 4) ^ 2 ≤ 17 / 4 := by
    nlinarith
  simpa only [max_eq_left he0] using he

theorem IsFullCapMaximizer.ae_first_density_le_one_of_endpoint_criterion
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {C : ℝ}
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1)
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρC : ∀ x, ρ x ≤ C)
    (hκ : ∀ x, ρ x ≤ sourceKappa (upperCornerVelocity U x))
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (henergy : (3 * capWidth U / 4) ^ 2 ≤
      4 + capRoof U (horizontalRight U) * (1 - capRoof U (horizontalRight U))) :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ t ≤ 1 := by
  apply ae_restrict_of_local_intervals isOpen_Ioo
  intro t ht
  obtain ⟨a, ha0, hat⟩ := exists_between ht.1
  obtain ⟨b, htb, hbL⟩ := exists_between ht.2
  have ha : a ∈ Ioo (0 : ℝ) (Real.pi / 2) := ⟨ha0, hat.trans ht.2⟩
  have hfuture := hU.ae_density_le_one_after_cornerEnergy hmiddle hρ hρ0 hρC hκ heq ha
    (hU.actualCornerEnergy_le_of_endpoint_criterion hheight hmiddle hρ hρ0 hρC hκ heq henergy ha)
  exact ⟨a, b, ⟨hat, htb⟩, ae_restrict_of_ae_restrict_of_subset
    (Ioo_subset_Ioo le_rfl hbL.le) hfuture⟩

end AmbidextrousSofa
