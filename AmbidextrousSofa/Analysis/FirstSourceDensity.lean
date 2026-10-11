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

section ActualPair

variable {U : Set Plane} (hU : IsFullCapMaximizer U)
  {m c : ℝ} {ρ : ℝ → ℝ} {K : ℝ} (hm : 0 ≤ m)
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
    capRoof U x = m * x + c)
  (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
  (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))

local notation "F" => fullTiltedSupportQuarterPair hU hm haffine hρ hρ0 hρK heq
set_option quotPrecheck false
local notation "B" => firstTangentPoint (F).f (F).fD
local notation "Z" => innerCornerPoint (F).f (F).g
local notation "q" => supportQ (F).gD (F).f

/-- Differentiation of a local physical projection inequality, whose
projection is the corner term plus an extra term `E`, at Lebesgue points
of the density. The transverse error vanishes because both literal
curvature interval masses tend to zero. -/
theorem fullTiltedSupportQuarterPair_ae_first_density_ge_of_flux {a b : ℝ}
    {E : ℝ → ℝ → ℝ} {A : ℝ → ℝ} (hregular : Ioo a b ⊆ regularCornerDomain m)
    (hE : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt (E t) (A t) t)
    (hflux : ∀ s t : ℝ, a < s → s < t → t < b → Icc s t ⊆ regularCurvatureDomain m →
      Icc (s + Real.pi / 2) (t + Real.pi / 2) ⊆ regularCurvatureDomain m →
      Real.cos s * ((Z t).2 - (Z s).2) - Real.sin s * ((Z t).1 - (Z s).1) + (E s t - E s s) ≤
        (upperCurvature U).real (Ioc s t) + (t - s) * ((upperCurvature U).real (Ioc s t) +
          (upperCurvature U).real (Ioc (s + Real.pi / 2) (t + Real.pi / 2)))) :
    ∀ᵐ t ∂volume.restrict (Ioo a b), q t + A t ≤ ρ t := by
  have hlocal : LocallyIntegrable ρ volume := (locallyIntegrable_const K).mono
    hρ.aestronglyMeasurable (.of_forall fun x => abs_le_abs_of_nonneg (hρ0 x) (hρK x))
  filter_upwards [ae_restrict_mem measurableSet_Ioo, hE,
    ae_restrict_of_ae_restrict_of_subset (fun t ht => (hregular ht).1)
      (fullTiltedSupportQuarterPair_ae_derivatives hU hm haffine hρ hρ0 hρK heq),
    ae_restrict_of_ae (LocallyIntegrable.ae_hasDerivAt_integral hlocal)] with t ht hE hd hLeb
  have hZ₁ := ((hd.1.sub_const 1).mul (Real.hasDerivAt_cos t)).sub
    ((hd.2.1.sub_const 1).mul (Real.hasDerivAt_sin t))
  have hZ₂ := ((hd.1.sub_const 1).mul (Real.hasDerivAt_sin t)).add
    ((hd.2.1.sub_const 1).mul (Real.hasDerivAt_cos t))
  have hG : HasDerivAt (fun s => Real.cos t * (Z s).2 - Real.sin t * (Z s).1 + E t s)
      (q t + A t) t :=
    (((hZ₂.const_mul _).sub (hZ₁.const_mul _)).add hE).congr_deriv (by
      unfold supportQ
      linear_combination ((F).gD t + (F).f t - 1) * Real.sin_sq_add_cos_sq t)
  let d := AngularGrid.selectionRate
  have hd : Tendsto d atTop (𝓝 0) := AngularGrid.selectionRate_tendsto
  have hdpos : ∀ n, 0 < d n := AngularGrid.selectionRate_pos
  have hsmall : ∀ᶠ n in atTop, t + d n < b ∧
      Icc t (t + d n) ⊆ regularCurvatureDomain m ∧
      Icc (t + Real.pi / 2) (t + d n + Real.pi / 2) ⊆ regularCurvatureDomain m := by
    filter_upwards [hd.eventually_lt_const (sub_pos.mpr ht.2)] with n hn
    exact ⟨by linarith only [hn], regularCornerDomain_interval_directions
      fun x hx => hregular ⟨ht.1.trans_le hx.1, by linarith only [hx.2, hn]⟩⟩
  have hbase : ∀ᶠ n in atTop, Ioc t (t + d n) ⊆ regularCurvatureDomain m :=
    hsmall.mono fun n hn => Ioc_subset_Icc_self.trans hn.2.1
  have hshift : ∀ᶠ n in atTop,
      Ioc (t + Real.pi / 2) (t + Real.pi / 2 + d n) ⊆ regularCurvatureDomain m :=
    hsmall.mono fun n hn => by rw [add_right_comm]; exact Ioc_subset_Icc_self.trans hn.2.2
  have hlim := (measureReal_Ioc_increment_div_tendsto_of_density hρ hρ0 heq (hLeb t) hd hdpos
    hbase).add ((measureReal_Ioc_increment_tendsto_zero_of_density hρ hρ0 hρK heq hd hdpos
      hbase).add
        (measureReal_Ioc_increment_tendsto_zero_of_density hρ hρ0 hρK heq hd hdpos hshift))
  rw [add_zero, add_zero] at hlim
  refine le_of_tendsto_of_tendsto (HasDerivAt.forward_increment_div_tendsto hG hd hdpos) hlim ?_
  filter_upwards [hsmall] with n hn
  have h := hflux t (t + d n) ht.1 (lt_add_of_pos_right t (hdpos n)) hn.1 hn.2.1 hn.2.2
  rw [add_right_comm, add_sub_cancel_left] at h
  rw [div_add' _ _ _ (hdpos n).ne', div_le_div_iff_of_pos_right (hdpos n)]
  linarith only [h]

theorem fullTiltedSupportQuarterPair_ae_first_density_ge_core
    {a b : ℝ} (hheight : capHeight U = 1)
    (hregular : Ioo a b ⊆ regularCornerDomain m)
    (hpieces : ∀ s t : ℝ, a < s → s < t → t < b →
      FirstSourceCorePiece hU.isCap Z s t) :
    ∀ᵐ t ∂volume.restrict (Ioo a b), q t ≤ ρ t := by
  simpa only [add_zero] using fullTiltedSupportQuarterPair_ae_first_density_ge_of_flux
    hU hm haffine hρ hρ0 hρK heq (E := fun _ _ => 0) hregular
    (.of_forall fun t => hasDerivAt_const t 0) fun s t has hst htb h₁ h₂ => by
      linarith only [hU.first_source_flux_of_core_piece hheight haffine ⟨le_rfl, hst.le⟩
        h₁ h₂ (hpieces s t has hst htb)]

theorem fullTiltedSupportQuarterPair_ae_first_density_ge_charged
    {a b : ℝ} (hheight : capHeight U = 1)
    (hregular : Ioo a b ⊆ regularCornerDomain m)
    (hpieces : ∀ s t : ℝ, a < s → s < t → t < b →
      FirstSourceChargedPieces hU.isCap B Z s t) :
    ∀ᵐ t ∂volume.restrict (Ioo a b), 1 + q t ≤ 2 * ρ t := by
  have hT := ae_restrict_of_ae_restrict_of_subset (fun t ht => (hregular ht).1)
    (fullTiltedSupportQuarterPair_tangent_calculus hU hm haffine hρ hρ0 hρK heq).2.2.2.2
  filter_upwards [fullTiltedSupportQuarterPair_ae_first_density_ge_of_flux
    hU hm haffine hρ hρ0 hρK heq (E := fun θ s => Real.sin θ * (B s).1 - Real.cos θ * (B s).2)
    (A := fun t => 1 - ρ t) hregular
    (hT.mono fun t ht => ((ht.1.const_mul _).sub (ht.2.1.const_mul _)).congr_deriv
      (by linear_combination (1 - ρ t) * Real.sin_sq_add_cos_sq t))
    fun s t has hst htb h₁ h₂ => by
      linarith only [hU.first_source_flux_of_charged_pieces hheight haffine ⟨le_rfl, hst.le⟩
        h₁ h₂ (hpieces s t has hst htb)]] with t ht
  linarith only [ht]

end ActualPair
end AmbidextrousSofa
