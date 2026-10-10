module

public import AmbidextrousSofa.Analysis.FirstSourceFlux
public import AmbidextrousSofa.Analysis.TiltedInitialCircle
public import AmbidextrousSofa.Analysis.VisibleFluxDensity

@[expose] public section

/-!
# Actual first-source density from visible graph pieces

The exact finite first-family flux is differentiated at genuine
Lebesgue points of the cap's curvature density. Core contact gives
`q ≤ u`; adding the disjoint charged first-tangency piece gives
`1 + q ≤ 2u`. All support and tangent derivatives used in the final
statements are supplied by the actual support pair itself.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem hasDerivAt_innerCornerPoint_coordinates
    {f fD g gD : ℝ → ℝ} {t : ℝ}
    (hf : HasDerivAt f (fD t) t) (hg : HasDerivAt g (gD t) t) :
    HasDerivAt (fun s => (innerCornerPoint f g s).1)
        (supportP fD g t * Real.cos t - supportQ gD f t * Real.sin t) t ∧
      HasDerivAt (fun s => (innerCornerPoint f g s).2)
        (supportP fD g t * Real.sin t + supportQ gD f t * Real.cos t) t := by
  constructor
  · have h := ((hf.sub_const 1).mul (Real.hasDerivAt_cos t)).sub
      ((hg.sub_const 1).mul (Real.hasDerivAt_sin t))
    change HasDerivAt (fun s => (innerCornerPoint f g s).1) _ t at h
    exact h.congr_deriv (by dsimp only [supportP, supportQ]; ring)
  · have h := ((hf.sub_const 1).mul (Real.hasDerivAt_sin t)).add
      ((hg.sub_const 1).mul (Real.hasDerivAt_cos t))
    change HasDerivAt (fun s => (innerCornerPoint f g s).2) _ t at h
    exact h.congr_deriv (by dsimp only [supportP, supportQ]; ring)

/-- Differentiation of a local physical projection inequality. The
transverse error vanishes because both literal curvature interval masses
tend to zero. -/
theorem first_density_ge_of_projection_increments
    {U : Set Plane} {ρ G : ℝ → ℝ} {K m a b t A : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρK : ∀ x, ρ x ≤ K)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
      (volume.restrict (regularCurvatureDomain m)).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (hregular : Ioo a b ⊆ regularCornerDomain m) (ht : t ∈ Ioo a b)
    (hG : HasDerivAt G A t)
    (hLebesgue : HasDerivAt (fun y => ∫ x in t..y, ρ x) (ρ t) t)
    (hflux : ∀ d : ℝ, 0 < d → t + d < b →
      G (t + d) - G t ≤ (upperCurvature U).real (Ioc t (t + d)) +
        d * ((upperCurvature U).real (Ioc t (t + d)) +
          (upperCurvature U).real (Ioc (t + Real.pi / 2) (t + Real.pi / 2 + d)))) :
    A ≤ ρ t := by
  let d := AngularGrid.selectionRate
  have hd : Tendsto d atTop (𝓝 0) := AngularGrid.selectionRate_tendsto
  have hdpos : ∀ n, 0 < d n := AngularGrid.selectionRate_pos
  have hsmall : ∀ᶠ n in atTop, t + d n < b := by
    filter_upwards [hd.eventually (Iio_mem_nhds (sub_pos.mpr ht.2))] with n hn
    linarith
  have hbase : ∀ᶠ n in atTop, Ioc t (t + d n) ⊆ regularCurvatureDomain m := by
    filter_upwards [hsmall] with n hn x hx
    exact (hregular ⟨ht.1.trans hx.1, hx.2.trans_lt hn⟩).2.1
  have hshift : ∀ᶠ n in atTop,
      Ioc (t + Real.pi / 2) (t + Real.pi / 2 + d n) ⊆ regularCurvatureDomain m := by
    filter_upwards [hsmall] with n hn x hx
    have hx' : x - Real.pi / 2 ∈ Ioo a b := by
      constructor <;> linarith [ht.1, hx.1, hx.2]
    simpa only [mem_preimage, sub_add_cancel] using (hregular hx').2.2
  have hmass0 := measureReal_Ioc_increment_tendsto_zero_of_density
    hρ hρ0 hρK heq hd hdpos hbase
  have hshift0 := measureReal_Ioc_increment_tendsto_zero_of_density
    hρ hρ0 hρK heq hd hdpos hshift
  have hquot := measureReal_Ioc_increment_div_tendsto_of_density
    hρ hρ0 heq hLebesgue hd hdpos hbase
  have hGlim := HasDerivAt.forward_increment_div_tendsto hG hd hdpos
  have hbound : ∀ᶠ n in atTop,
      (G (t + d n) - G t) / d n ≤
        (upperCurvature U).real (Ioc t (t + d n)) / d n +
          ((upperCurvature U).real (Ioc t (t + d n)) +
            (upperCurvature U).real (Ioc (t + Real.pi / 2) (t + Real.pi / 2 + d n))) := by
    filter_upwards [hsmall] with n hn
    have h := div_le_div_of_nonneg_right (hflux (d n) (hdpos n) hn) (hdpos n).le
    simpa only [add_div, mul_div_cancel_left₀ _ (hdpos n).ne'] using h
  exact le_of_tendsto_of_tendsto hGlim
    (by simpa only [add_zero, zero_add] using hquot.add (hmass0.add hshift0)) hbound

section ActualPair

variable {U : Set Plane} (hU : IsFullCapMaximizer U)
  {m c : ℝ} {ρ : ℝ → ℝ} {K : ℝ} (hm : 0 ≤ m)
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
    capRoof U x = m * x + c)
  (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
  (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))

local notation "F" => fullTiltedSupportQuarterPair hU hm haffine hρ hρ0 hρK heq
set_option quotPrecheck false in
local notation "B" => firstTangentPoint (F).f (F).fD
set_option quotPrecheck false in
local notation "Z" => innerCornerPoint (F).f (F).g
set_option quotPrecheck false in
local notation "p" => supportP (F).fD (F).g
set_option quotPrecheck false in
local notation "q" => supportQ (F).gD (F).f

theorem fullTiltedSupportQuarterPair_ae_first_density_ge_core
    {a b : ℝ} (hheight : capHeight U = 1)
    (hregular : Ioo a b ⊆ regularCornerDomain m)
    (hpieces : ∀ s t : ℝ, a < s → s < t → t < b →
      FirstSourceCorePiece hU.isCap Z s t) :
    ∀ᵐ t ∂volume.restrict (Ioo a b), q t ≤ ρ t := by
  have hlocal : LocallyIntegrable ρ volume := by
    apply locallyIntegrable_iff.mpr
    intro S hS
    apply IntegrableOn.of_bound hS.measure_lt_top hρ.aestronglyMeasurable K
    exact Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hρ0 x)]
      exact hρK x)
  have hD := ae_restrict_of_ae_restrict_of_subset
    (fun t ht => (hregular ht).1)
    (fullTiltedSupportQuarterPair_ae_derivatives hU hm haffine hρ hρ0 hρK heq)
  filter_upwards [ae_restrict_mem measurableSet_Ioo, hD,
    ae_restrict_of_ae (LocallyIntegrable.ae_hasDerivAt_integral hlocal)] with t ht hd hLeb
  have hZ := hasDerivAt_innerCornerPoint_coordinates hd.1 hd.2.1
  let G : ℝ → ℝ := fun s => Real.cos t * (Z s).2 - Real.sin t * (Z s).1
  have hG : HasDerivAt G (q t) t := by
    have h := (hZ.2.const_mul (Real.cos t)).sub (hZ.1.const_mul (Real.sin t))
    change HasDerivAt G _ t at h
    apply h.congr_deriv
    have hcircle := congrArg (fun r : ℝ => q t * r) (Real.sin_sq_add_cos_sq t)
    nlinarith only [hcircle]
  apply first_density_ge_of_projection_increments hρ hρ0 hρK heq hregular ht hG (hLeb t)
  intro d hd0 hdb
  have hsub : Icc t (t + d) ⊆ regularCornerDomain m := by
    intro s hs
    exact hregular ⟨ht.1.trans_le hs.1, hs.2.trans_lt hdb⟩
  have hdirs := regularCornerDomain_interval_directions hsub
  have hflux := hU.first_source_flux_of_core_piece hheight haffine
    (show t ∈ Icc t (t + d) from ⟨le_rfl, by linarith only [hd0]⟩)
    hdirs.1 hdirs.2 (hpieces t (t + d) ht.1 (by linarith only [hd0]) hdb)
  have hcomm : t + d + Real.pi / 2 = t + Real.pi / 2 + d := by ring
  rw [hcomm] at hflux
  simp only [add_sub_cancel_left] at hflux
  convert hflux using 1 <;> dsimp only [G] <;> ring

theorem fullTiltedSupportQuarterPair_ae_first_density_ge_charged
    {a b : ℝ} (hheight : capHeight U = 1)
    (hregular : Ioo a b ⊆ regularCornerDomain m)
    (hpieces : ∀ s t : ℝ, a < s → s < t → t < b →
      FirstSourceChargedPieces hU.isCap B Z s t) :
    ∀ᵐ t ∂volume.restrict (Ioo a b), 1 + q t ≤ 2 * ρ t := by
  have hlocal : LocallyIntegrable ρ volume := by
    apply locallyIntegrable_iff.mpr
    intro S hS
    apply IntegrableOn.of_bound hS.measure_lt_top hρ.aestronglyMeasurable K
    exact Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hρ0 x)]
      exact hρK x)
  have hD := ae_restrict_of_ae_restrict_of_subset
    (fun t ht => (hregular ht).1)
    (fullTiltedSupportQuarterPair_ae_derivatives hU hm haffine hρ hρ0 hρK heq)
  have hT := ae_restrict_of_ae_restrict_of_subset
    (fun t ht => (hregular ht).1)
    (fullTiltedSupportQuarterPair_tangent_calculus hU hm haffine hρ hρ0 hρK heq).2.2.2.2
  filter_upwards [ae_restrict_mem measurableSet_Ioo, hD, hT,
    ae_restrict_of_ae (LocallyIntegrable.ae_hasDerivAt_integral hlocal)] with t ht hd hT hLeb
  have hZ := hasDerivAt_innerCornerPoint_coordinates hd.1 hd.2.1
  let G : ℝ → ℝ := fun s =>
    (Real.cos t * (Z s).2 - Real.sin t * (Z s).1) +
      (Real.sin t * (B s).1 - Real.cos t * (B s).2)
  have hG : HasDerivAt G (q t + 1 - ρ t) t := by
    have h := ((hZ.2.const_mul (Real.cos t)).sub (hZ.1.const_mul (Real.sin t))).add
      ((hT.1.const_mul (Real.sin t)).sub (hT.2.1.const_mul (Real.cos t)))
    change HasDerivAt G _ t at h
    apply h.congr_deriv
    have hcircleq := congrArg (fun r : ℝ => q t * r) (Real.sin_sq_add_cos_sq t)
    have hcircleu := congrArg (fun r : ℝ => (1 - ρ t) * r) (Real.sin_sq_add_cos_sq t)
    nlinarith only [hcircleq, hcircleu]
  have hbound : q t + 1 - ρ t ≤ ρ t := by
    apply first_density_ge_of_projection_increments hρ hρ0 hρK heq hregular ht hG (hLeb t)
    intro d hd0 hdb
    have hsub : Icc t (t + d) ⊆ regularCornerDomain m := by
      intro s hs
      exact hregular ⟨ht.1.trans_le hs.1, hs.2.trans_lt hdb⟩
    have hdirs := regularCornerDomain_interval_directions hsub
    have hflux := hU.first_source_flux_of_charged_pieces hheight haffine
      (show t ∈ Icc t (t + d) from ⟨le_rfl, by linarith only [hd0]⟩)
      hdirs.1 hdirs.2 (hpieces t (t + d) ht.1 (by linarith only [hd0]) hdb)
    have hcomm : t + d + Real.pi / 2 = t + Real.pi / 2 + d := by ring
    rw [hcomm] at hflux
    simp only [add_sub_cancel_left] at hflux
    convert hflux using 1 <;> dsimp only [G] <;> ring
  linarith only [hbound]

end ActualPair
end AmbidextrousSofa
