import AmbidextrousSofa.Analysis.CornerEndpointEnergy

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

theorem absolutelyContinuousOnInterval_le_terminal_of_ae_deriv_nonneg
    {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (hab : a ≤ b)
    (hd : ∀ᵐ t ∂volume.restrict (Ioo a b), 0 ≤ deriv f t)
    {x : ℝ} (hx : x ∈ Icc a b) : f x ≤ f b := by
  have hxb : AbsolutelyContinuousOnInterval f x b := hf.mono (by
    rw [uIcc_of_le hx.2, uIcc_of_le hab]
    exact Icc_subset_Icc hx.1 le_rfl)
  have hdcc : ∀ᵐ t ∂volume.restrict (Icc a b), 0 ≤ deriv f t := by
    rwa [← restrict_Ioo_eq_restrict_Icc]
  have hdx : ∀ᵐ t ∂volume.restrict (Icc x b), 0 ≤ deriv f t :=
    ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc hx.1 le_rfl) hdcc
  have hnonneg := intervalIntegral.integral_nonneg_of_ae_restrict hx.2 hdx
  rw [hxb.integral_deriv_eq_sub] at hnonneg
  linarith

theorem absolutelyContinuousOnInterval_le_of_ae_deriv_nonneg_above
    {f : ℝ → ℝ} {a b H : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (hab : a ≤ b) (hterminal : f b ≤ H)
    (hd : ∀ᵐ t ∂volume.restrict (Ioo a b), H < f t → 0 ≤ deriv f t)
    {x : ℝ} (hx : x ∈ Icc a b) : f x ≤ H := by
  have hg := absolutelyContinuousOnInterval_max_const hf H
  have hgd : ∀ᵐ t ∂volume.restrict (Ioo a b),
      0 ≤ deriv (fun s => max (f s) H) t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hd,
      ae_restrict_of_ae (ae_hasDerivAt_max_const hf H)] with t ht hdt hmt
    have htmem : t ∈ uIcc a b := by
      rw [uIcc_of_le hab]
      exact Ioo_subset_Icc_self ht
    rw [(hmt htmem).deriv]
    split_ifs with hpos
    · exact hdt hpos
    · exact le_rfl
  have hle := absolutelyContinuousOnInterval_le_terminal_of_ae_deriv_nonneg hg hab hgd hx
  rw [max_eq_right hterminal] at hle
  exact (le_max_left (f x) H).trans hle

theorem ae_hasDerivAt_clippedCornerEnergy_reverse
    {p q u v : ℝ → ℝ} {a b : ℝ}
    (hp : AbsolutelyContinuousOnInterval p a b) (hab : a ≤ b)
    (hode : ∀ᵐ t ∂volume.restrict (Ioo a b),
      HasDerivAt p (1 + q t - u t) t ∧ HasDerivAt q (1 - p t - v t) t) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      HasDerivAt (clippedCornerEnergy p q)
        (2 * (max (p t) 0 - 1 / 2) *
            (if 0 < p t then 1 + q t - u t else 0) +
          2 * (q t + 1) * (1 - p t - v t)) t := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo, hode,
    ae_restrict_of_ae (ae_hasDerivAt_max_const hp 0)] with t ht hd hclip
  have htmem : t ∈ uIcc a b := by
    rw [uIcc_of_le hab]
    exact Ioo_subset_Icc_self ht
  have hclip' : HasDerivAt (fun s => max (p s) 0)
      (if 0 < p t then 1 + q t - u t else 0) t := by
    simpa only [hd.1.deriv] using hclip htmem
  have he := ((hclip'.sub_const (1 / 2)).pow 2).add ((hd.2.add_const 1).pow 2)
  change HasDerivAt (clippedCornerEnergy p q) _ t at he
  apply he.congr_deriv
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]

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
  apply absolutelyContinuousOnInterval_le_of_ae_deriv_nonneg_above
    (absolutelyContinuousOnInterval_clippedCornerEnergy hp hq) hab (le_max_right _ _) _ ht
  filter_upwards [ae_hasDerivAt_clippedCornerEnergy_reverse hp hab hode,
    hbound, hκ, hshadow] with x hd hb hk hs
  intro hE
  rw [hd.deriv]
  have hnonpos := clippedCornerEnergy_derivative_nonpos_above hb.1 hb.2 hk hs
    ((le_max_left _ _).trans_lt hE)
  by_cases hpos : 0 < p x
  · simp only [if_pos hpos] at hnonpos ⊢
    nlinarith
  · simp only [if_neg hpos] at hnonpos ⊢
    nlinarith

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
  have hode : ∀ᵐ x ∂volume.restrict (Ioo a b),
      HasDerivAt (fun y => -firstCornerVelocity U y)
        (1 + secondCornerVelocity U x - ρ (x + Real.pi / 2)) x ∧
      HasDerivAt (secondCornerVelocity U)
        (1 - -firstCornerVelocity U x - ρ x) x := by
    filter_upwards [hU.isCap.ae_hasDerivAt_cornerVelocities_of_density
      hρ hρ0 hρC heq hab hdir.1 hdir.2] with x hd
    exact ⟨hd.1.neg.congr_deriv (by ring), hd.2.congr_deriv (by ring)⟩
  have hb : ∀ᵐ x ∂volume.restrict (Ioo a b),
      -firstCornerVelocity U x ≤ 1 ∧ -1 ≤ secondCornerVelocity U x := by
    apply Eventually.of_forall
    intro x
    constructor
    · linarith [hU.isCap.firstCornerVelocity_ge_neg_one x]
    · linarith [hU.isCap.neg_secondCornerVelocity_le_one x]
  have hk : ∀ᵐ x ∂volume.restrict (Ioo a b),
      ρ x ≤ sourceKappa (-firstCornerVelocity U x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simpa only [sourceKappa_neg] using
      (upperCorner_density_bounds_on_quarter hκ (hsub (Ioo_subset_Icc_self hx)).1).1
  have hs : ∀ᵐ x ∂volume.restrict (Ioo a b),
      0 < -firstCornerVelocity U x → 0 < secondCornerVelocity U x →
        ρ (x + Real.pi / 2) = 0 ∧ ρ x ≤ 1 / 2 := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Icc_self.trans hsub)
      (hU.ae_curvature_same_sign_quadrants haffine hρ hρ0 hρC heq)] with x hx
    intro hp hq
    exact hx.2 ⟨by linarith, hq⟩
  exact clippedCornerEnergy_le_max_terminal hac.1.neg hac.2 hab hode hb hk hs ht

theorem IsFullCapMaximizer.actualCompanionEnergy_tendsto_pi_div_two_left
    {U : Set Plane} (hU : IsFullCapMaximizer U) (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1) :
    Tendsto (actualCompanionEnergy U) (𝓝[<] (Real.pi / 2))
      (𝓝 ((capRoof U (horizontalLeft U) - 1 / 2) ^ 2 + (3 * capWidth U / 4) ^ 2)) := by
  have hvel := hU.cornerVelocities_tendsto_pi_div_two_left hheight hmiddle
  have hE := (((hvel.fst.neg.max tendsto_const_nhds).sub_const (1 / 2)).pow 2).add
    ((hvel.snd.add_const 1).pow 2)
  change Tendsto (actualCompanionEnergy U) _ _ at hE
  have heL : 0 ≤ capRoof U (horizontalLeft U) :=
    capRoof_nonneg hU.isCap.isCompact (fun p hp => (hU.isCap.inStrip hp).1) _
  have hwidth : horizontalRight U - capWidth U / 4 - horizontalLeft U - 1 + 1 =
      3 * capWidth U / 4 := by unfold capWidth; ring
  simpa only [neg_neg, max_eq_left heL, hwidth] using hE

theorem IsFullCapMaximizer.actualCompanionEnergy_le_max_of_endpoint
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {C t : ℝ}
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1)
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρC : ∀ x, ρ x ≤ C)
    (hκ : ∀ x, ρ x ≤ sourceKappa (upperCornerVelocity U x))
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    actualCompanionEnergy U t ≤
      max (17 / 4) ((capRoof U (horizontalLeft U) - 1 / 2) ^ 2 + (3 * capWidth U / 4) ^ 2) := by
  have hlim := (tendsto_const_nhds (x := (17 / 4 : ℝ))).max
    (hU.actualCompanionEnergy_tendsto_pi_div_two_left hheight hmiddle)
  apply ge_of_tendsto hlim
  have hlt : ∀ᶠ b in 𝓝[<] (Real.pi / 2), t < b :=
    (eventually_gt_nhds ht.2).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hlt] with b hb htb
  have hsub : Icc t b ⊆ regularCornerDomain 0 := by
    rw [regularCornerDomain_zero]
    exact fun x hx => ⟨ht.1.trans_le hx.1, hx.2.trans_lt hb⟩
  exact hU.actualCompanionEnergy_le_max_terminal_on_interval (m := 0) (c := 1)
    (by simpa only [zero_mul, zero_add] using hmiddle)
    hρ hρ0 hρC hκ heq htb.le hsub ⟨le_rfl, htb.le⟩

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
  have he := hU.actualCompanionEnergy_le_max_of_endpoint hheight hmiddle hρ hρ0 hρC hκ heq ht
  have heL : (capRoof U (horizontalLeft U) - 1 / 2) ^ 2 + (3 * capWidth U / 4) ^ 2 ≤ 17 / 4 := by
    nlinarith
  simpa only [max_eq_left heL] using he

theorem IsFullCapMaximizer.ae_companion_density_le_one_of_endpoint_criterion
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {C : ℝ}
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1)
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρC : ∀ x, ρ x ≤ C)
    (hκ : ∀ x, ρ x ≤ sourceKappa (upperCornerVelocity U x))
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (henergy : (3 * capWidth U / 4) ^ 2 ≤
      4 + capRoof U (horizontalLeft U) * (1 - capRoof U (horizontalLeft U))) :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ (t + Real.pi / 2) ≤ 1 := by
  have hshadow := hU.ae_curvature_same_sign_quadrants (m := 0) (c := 1)
    (by simpa only [zero_mul, zero_add] using hmiddle) hρ hρ0 hρC heq
  rw [regularCornerDomain_zero] at hshadow
  filter_upwards [ae_restrict_mem measurableSet_Ioo, hshadow] with t ht hs
  have hr : -1 ≤ secondCornerVelocity U t := by
    linarith [hU.isCap.neg_secondCornerVelocity_le_one t]
  have hE := hU.actualCompanionEnergy_le_of_endpoint_criterion
    hheight hmiddle hρ hρ0 hρC hκ heq henergy ht
  exact curvature_le_one_of_clippedCornerEnergy (p := -firstCornerVelocity U t) hr
    (upperCorner_density_bounds_on_quarter hκ ht).2
    (fun hp hq => (hs.2 ⟨by linarith, hq⟩).1) hE

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
  have hcompanion := hU.ae_companion_density_le_one_of_endpoint_criterion
    hheight hmiddle hρ hρ0 hρC hκ heq henergy
  have hfirst := hU.ae_first_density_le_one_of_unit_companion
    hheight hmiddle hρ hρ0 hρC hκ heq hcompanion
  filter_upwards [hfirst, hcompanion] with t hf hc
  exact ⟨hf, hc⟩

end AmbidextrousSofa
