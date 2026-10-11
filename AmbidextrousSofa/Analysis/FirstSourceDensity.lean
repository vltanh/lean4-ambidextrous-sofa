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
  filter_upwards [ae_restrict_mem measurableSet_Ioo, hE,
    ae_restrict_of_ae_restrict_of_subset (fun t ht => (hregular ht).1)
      (fullTiltedSupportQuarterPair_ae_derivatives hU hm haffine hρ hρ0 hρK heq),
    ae_restrict_of_ae (ae_le_density_of_increment_le hρ hρ0 hρK heq)] with t ht hE hd hLeb
  have hZ₁ := ((hd.1.sub_const 1).mul (Real.hasDerivAt_cos t)).sub
    ((hd.2.1.sub_const 1).mul (Real.hasDerivAt_sin t))
  have hZ₂ := ((hd.1.sub_const 1).mul (Real.hasDerivAt_sin t)).add
    ((hd.2.1.sub_const 1).mul (Real.hasDerivAt_cos t))
  have hG : HasDerivAt (fun s => Real.cos t * (Z s).2 - Real.sin t * (Z s).1 + E t s)
      (q t + A t) t :=
    (((hZ₂.const_mul _).sub (hZ₁.const_mul _)).add hE).congr_deriv (by
      unfold supportQ
      linear_combination ((F).gD t + (F).f t - 1) * Real.sin_sq_add_cos_sq t)
  refine hLeb _ _ t (t + Real.pi / 2) hG ?_
  filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 ht.2)] with h hh
  have hI : Icc t (t + h) ⊆ regularCornerDomain m := fun x hx =>
    hregular ⟨ht.1.trans_le hx.1, by linarith [hx.2, hh.2]⟩
  obtain ⟨h₁, h₂⟩ := regularCornerDomain_interval_directions hI
  have := hflux t (t + h) ht.1 (lt_add_of_pos_right t hh.1) (by linarith [hh.2]) h₁ h₂
  rw [add_right_comm t h, add_sub_cancel_left] at this
  rw [add_right_comm t h] at h₂
  exact ⟨Ioc_subset_Icc_self.trans h₁, Ioc_subset_Icc_self.trans h₂, by linarith⟩

theorem fullTiltedSupportQuarterPair_ae_first_density_ge_core
    {a b : ℝ} (hheight : capHeight U = 1)
    (hregular : Ioo a b ⊆ regularCornerDomain m)
    (hpieces : ∀ s t : ℝ, a < s → s < t → t < b →
      FirstSourceCorePiece hU.isCap Z s t) :
    ∀ᵐ t ∂volume.restrict (Ioo a b), q t ≤ ρ t := by
  simpa only [add_zero] using fullTiltedSupportQuarterPair_ae_first_density_ge_of_flux
    hU hm haffine hρ hρ0 hρK heq (E := fun _ _ => 0) hregular
    (.of_forall fun t => hasDerivAt_const t 0) fun s t has hst htb h₁ h₂ => by
      -- A core chord alone is a charged pair whose tangent piece is collapsed at `Z s`.
      have H := hpieces s t has hst htb
      have := hU.first_source_flux_of_charged_pieces hheight haffine ⟨le_rfl, hst.le⟩ h₁ h₂
        (show FirstSourceChargedPieces hU.isCap (fun _ => Z s) Z s t from
          ⟨H, le_rfl, le_rfl, H.middle_right, H.contact_s, H.contact_s,
            fun x hx => (hx.1.trans hx.2).false.elim, fun x hx => (hx.1.trans hx.2).false.elim⟩)
      simp only [sub_self, mul_zero, add_zero] at this
      linarith only [this]

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
