import AmbidextrousSofa.Analysis.ProperExcessScalar
import AmbidextrousSofa.Analysis.ProperReflectedEntry

/-!
# The actual reflected proper-wing excess envelopes

The regular arc starts after the literal terminal impulse. Its deadline
is the maximum of the unused gap and the first-zero root, followed by
the quadratic decay length. The exact scalar bounds control both terms
of that maximum. The actual affine cutoff is then spliced to the proved
zero-source region, with its single endpoint discarded only as a
Lebesgue null set.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

theorem ae_Ioo_splice_real {P : ℝ → Prop} {a b c : ℝ}
    (hleft : ∀ᵐ t ∂volume.restrict (Ioo a b), P t)
    (hright : ∀ᵐ t ∂volume.restrict (Ioo b c), P t) :
    ∀ᵐ t ∂volume.restrict (Ioo a c), P t := by
  have hne : ∀ᵐ t : ℝ ∂volume, t ≠ b := by
    apply ae_iff.mpr
    simpa only [not_not] using (measure_singleton b : volume ({b} : Set ℝ) = 0)
  have hL := (ae_restrict_iff' measurableSet_Ioo).mp hleft
  have hR := (ae_restrict_iff' measurableSet_Ioo).mp hright
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hL,
    ae_restrict_of_ae hR, ae_restrict_of_ae hne] with t ht hL hR hne
  by_cases htb : t < b
  · exact hL ⟨ht.1, htb⟩
  · exact hR ⟨lt_of_le_of_ne (le_of_not_gt htb) hne.symm, ht.2⟩

namespace CornerArcDynamics

variable {p q u v : ℝ → ℝ} {a b : ℝ}

theorem ae_linear_excess_of_proper_roots
    (D : CornerArcDynamics p q u v a b) {d e δ B : ℝ}
    (hfirst : ∀ t ∈ Icc a b, p t ≤ 1)
    (hpa : 0 < p a → p a ≤ e - d * a + a ^ 2 / 2)
    (hqa : 0 < p a → d - 1 - a ≤ q a)
    (hd0 : 199 / 100 ≤ d) (hd1 : d ≤ 2311 / 1000)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 30)
    (had : a ≤ d) (hZ : 4 < d ^ 2 - e * (1 - e) + δ)
    (henergy : clippedCornerEnergy p q a ≤ d ^ 2 - e * (1 - e) + 1 / 4 + δ)
    (hstop : Analysis.properExcessEnd d e δ ≤ B)
    (hgap : a + Analysis.properDecayLength d e δ ≤ B) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      max (u t - 1) 0 ≤ (19 / 25 : ℝ) * max (B - t) 0 := by
  obtain ⟨hx, hy, hz⟩ := Analysis.properExcess_roots_bounds hd0 hd1 he0 he1 hδ0 hδ1
  let T := max a (Analysis.properFirstZeroTime d e)
  let ell := Analysis.properDecayLength d e δ
  have hS : 2 < Analysis.properEnergyRoot d e δ := by
    by_contra hnot
    have hp := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hnot))
      (show 0 ≤ 2 + Analysis.properEnergyRoot d e δ by linarith only [hy.1])
    nlinarith only [hp, hy.2.2, hZ]
  have hell0 : 0 ≤ ell := by
    dsimp only [ell, Analysis.properDecayLength]
    by_contra hnot
    have hp := mul_pos
      (show 0 < 1 - Analysis.properDecayRoot d e δ by linarith only [lt_of_not_ge hnot])
      (show 0 < 1 + Analysis.properDecayRoot d e δ by linarith only [hz.1])
    nlinarith only [hp, hz.2.2, hS]
  have hell : ell < 13 / 25 :=
    Analysis.properDecayLength_lt_fifty_two_hundredths hd0 hd1 he0 he1 hδ0 hδ1
  have hτd : Analysis.properFirstZeroTime d e ≤ d := by
    unfold Analysis.properFirstZeroTime
    linarith only [hx.1]
  have hTd : T ≤ d := max_le had hτd
  have hτT : Analysis.properFirstZeroTime d e ≤ T := le_max_right _ _
  have hquad := Analysis.properFirstZeroTime_quadratic
    (d := d) (e := e) (by rw [← hx.2.2]; exact sq_nonneg _)
  have hcross : e ≤ d * T - T ^ 2 / 2 := by
    have hp := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hτT)
      (show T + Analysis.properFirstZeroTime d e - 2 * d ≤ 0 by
        linarith only [hTd, hτd])
    nlinarith only [hp, hquad]
  have hphi : 2 + ell / 2 + ell ^ 2 / 4 = Analysis.properEnergyRoot d e δ := by
    dsimp only [ell, Analysis.properDecayLength]
    nlinarith only [hz.2.2]
  have henergy' : clippedCornerEnergy p q a ≤ 1 / 4 + (2 + ell / 2 + ell ^ 2 / 4) ^ 2 := by
    rw [hphi, hy.2.2]
    linarith only [henergy]
  have hdeadline : T + ell ≤ B := by
    dsimp only [T]
    rcases le_total a (Analysis.properFirstZeroTime d e) with h | h
    · rw [max_eq_right h]
      exact hstop
    · rw [max_eq_left h]
      exact hgap
  have h := D.ae_linear_excess_of_quadratic_deadline hfirst hpa hqa
    (show a ≤ T from le_max_left _ _) hcross hell0 (by linarith only [hell]) henergy'
  filter_upwards [h] with t ht
  calc
    max (u t - 1) 0 ≤ (ell + 1) / 2 * max (T + ell - t) 0 := ht
    _ ≤ (ell + 1) / 2 * max (B - t) 0 :=
      mul_le_mul_of_nonneg_left (max_le_max (by linarith only [hdeadline]) le_rfl)
        (by linarith only [hell0])
    _ ≤ (19 / 25 : ℝ) * max (B - t) 0 :=
      mul_le_mul_of_nonneg_right (by linarith only [hell]) (le_max_right _ _)

/-- Below threshold there is no excess. Above threshold the actual
energy forces the lower width needed for the exact root comparison. -/
theorem ae_linear_excess_of_proper_scalar_bounds
    (D : CornerArcDynamics p q u v a b) {d e δ B ellMax : ℝ}
    (hfirst : ∀ t ∈ Icc a b, p t ≤ 1)
    (hpa : 0 < p a → p a ≤ e - d * a + a ^ 2 / 2)
    (hqa : 0 < p a → d - 1 - a ≤ q a)
    (hd0 : 3 / 2 < d) (hd1 : d ≤ 2311 / 1000)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 30)
    (had : a ≤ d)
    (henergy : clippedCornerEnergy p q a ≤ d ^ 2 - e * (1 - e) + 1 / 4 + δ)
    (hstop : 199 / 100 ≤ d → Analysis.properExcessEnd d e δ ≤ B)
    (hdecay : 199 / 100 ≤ d → Analysis.properDecayLength d e δ ≤ ellMax)
    (hgap : a + ellMax ≤ B) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      max (u t - 1) 0 ≤ (19 / 25 : ℝ) * max (B - t) 0 := by
  by_cases hZ : d ^ 2 - e * (1 - e) + δ ≤ 4
  · have hunit := D.ae_unit_of_initial_energy (by linarith only [henergy, hZ])
    filter_upwards [hunit] with t ht
    rw [max_eq_right (sub_nonpos.mpr ht)]
    exact mul_nonneg (by norm_num) (le_max_right _ _)
  · have hlarge : 199 / 100 ≤ d := by
      by_contra hnot
      have hsmall := lt_of_not_ge hnot
      have hp := mul_nonneg (sub_nonneg.mpr hsmall.le)
        (show 0 ≤ 199 / 100 + d by linarith only [hd0])
      have hprod := mul_nonneg he0 (sub_nonneg.mpr he1)
      nlinarith only [hp, hprod, hδ1, lt_of_not_ge hZ]
    exact D.ae_linear_excess_of_proper_roots hfirst hpa hqa hlarge hd1 he0 he1 hδ0 hδ1
      had (lt_of_not_ge hZ) henergy (hstop hlarge)
      (by linarith only [hgap, hdecay hlarge])

end CornerArcDynamics

theorem IsJointCapMaximizer.properReflected_ae_near_full_excess_bound_of_tail_regime
    {U : Set Plane} {α C m c K : ℝ} {ρ : ℝ → ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (hsharp : ∀ t, ρ t ≤ sourceKappa (upperCornerVelocity U t))
    (heq : (upperCurvature U).restrict (regularProperCurvatureDomain α m) =
      (volume.restrict (regularProperCurvatureDomain α m)).withDensity
        (fun t => ENNReal.ofReal (ρ t))) (hκ : terminalSlope α ≤ 1 / 8) :
    ∀ᵐ r ∂volume.restrict (Ioo (Real.pi / 2 - α) (Real.pi / 2)),
      max (properReflectedFirstDensity m ρ r - 1) 0 ≤
        (19 / 25 : ℝ) * max (73 / 100 - r) 0 := by
  have D := hU.properReflected_cornerArcDynamics_of_tail_regime hregime hproper hl hr hheight haffine
    hρ hρ0 hρK hsharp heq
  have hparams := hU.centered_terminal_reflected_near_full_parameters_of_tail_regime
    hregime hproper hl hr hheight haffine hκ
  have hgap := (terminal_near_full_bounds hU.angle_pos hproper hκ).2.2.1
  have harms := hU.properReflected_arm_bounds_of_tail_regime hregime hproper hheight haffine hρ hρ0 hρK heq
  have hentry := hU.properReflected_entry_quadratic_of_tail_regime
    hregime hproper hl hr hheight haffine hρ hρ0 hρK heq
  have henergy := hU.properReflected_initial_energy_lt_near_full_payment_of_tail_regime
    hregime hproper hl hr hheight haffine hρ hρ0 hρK heq hκ
  have hactive := D.ae_linear_excess_of_proper_scalar_bounds
    (δ := (1 / 480 : ℝ)) (B := (73 / 100 : ℝ)) (ellMax := (43 / 100 : ℝ))
    (fun t ht => (harms t ht).1) (fun hp => (hentry hp).1) (fun hp => (hentry hp).2)
    hparams.1 (by linarith only [hparams.2.1]) hparams.2.2.1
    (by linarith only [hparams.2.2.2]) (by norm_num) (by norm_num)
    (by linarith only [hgap, hparams.1]) henergy.le
    (fun hd => (Analysis.properExcessEnd_lt_near_full hd hparams.2.1.le
      hparams.2.2.1 hparams.2.2.2.le (by norm_num) le_rfl).le)
    (fun hd => (Analysis.properDecayLength_lt_near_full hd hparams.2.1.le
      hparams.2.2.1 (by linarith only [hparams.2.2.2]) (by norm_num) le_rfl).le)
    (by linarith only [hgap])
  have hzero := hU.properReflected_densities_zero_after_active
    hproper hl hr hheight haffine hρ hρ0 heq
  apply ae_Ioo_splice_real hactive
  filter_upwards [hzero] with r hr
  rw [hr.1]
  simp only [zero_sub, max_eq_right (by norm_num : (-1 : ℝ) ≤ 0)]
  exact mul_nonneg (by norm_num) (le_max_right _ _)

theorem IsJointCapMaximizer.properReflected_ae_near_full_excess_bound
    {U : Set Plane} {α C m c K : ℝ} {ρ : ℝ → ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (hsharp : ∀ t, ρ t ≤ sourceKappa (upperCornerVelocity U t))
    (heq : (upperCurvature U).restrict (regularProperCurvatureDomain α m) =
      (volume.restrict (regularProperCurvatureDomain α m)).withDensity
        (fun t => ENNReal.ofReal (ρ t))) (hκ : terminalSlope α ≤ 1 / 8) :
    ∀ᵐ r ∂volume.restrict (Ioo (Real.pi / 2 - α) (Real.pi / 2)),
      max (properReflectedFirstDensity m ρ r - 1) 0 ≤
        (19 / 25 : ℝ) * max (73 / 100 - r) 0 := by
  exact IsJointCapMaximizer.properReflected_ae_near_full_excess_bound_of_tail_regime hU
    (hU.properTailRegime_of_largest hLargest hproper hheight haffine) hproper hl hr hheight haffine
    hρ hρ0 hρK hsharp heq hκ

theorem IsJointCapMaximizer.properReflected_ae_excess_bound_of_tail_regime
    {U : Set Plane} {α C m c K : ℝ} {ρ : ℝ → ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (hsharp : ∀ t, ρ t ≤ sourceKappa (upperCornerVelocity U t))
    (heq : (upperCurvature U).restrict (regularProperCurvatureDomain α m) =
      (volume.restrict (regularProperCurvatureDomain α m)).withDensity
        (fun t => ENNReal.ofReal (ρ t))) :
    ∀ᵐ r ∂volume.restrict (Ioo (Real.pi / 2 - α) (Real.pi / 2)),
      max (properReflectedFirstDensity m ρ r - 1) 0 ≤
        (19 / 25 : ℝ) * max (91 / 100 - r) 0 := by
  have D := hU.properReflected_cornerArcDynamics_of_tail_regime hregime hproper hl hr hheight haffine
    hρ hρ0 hρK hsharp heq
  have hparams := hU.centered_terminal_reflected_parameters_of_tail_regime hregime hproper hl hr hheight haffine
  have hd1 : terminalReflectedSpan U α ≤ 2311 / 1000 := by
    rcases hparams.2.2 with h | h <;> linarith only [h.2.1]
  have he1 : terminalReflectedHeight U α ≤ 1 := by
    rcases hparams.2.2 with h | h <;> linarith only [h.2.2]
  have hgap : Real.pi / 2 - α < 3 / 8 := by
    rw [terminal_gap_eq_arctan_slope hU.angle_pos hproper]
    exact (Real.arctan_lt_self (terminalSlope_pos hU.angle_pos hproper)).trans
      (hU.proper_terminalSlope_lt_three_eighths hproper)
  have harms := hU.properReflected_arm_bounds_of_tail_regime hregime hproper hheight haffine hρ hρ0 hρK heq
  have hentry := hU.properReflected_entry_quadratic_of_tail_regime
    hregime hproper hl hr hheight haffine hρ hρ0 hρK heq
  have henergy := hU.properReflected_initial_energy_lt_payment_of_tail_regime
    hregime hproper hl hr hheight haffine hρ hρ0 hρK heq
  have hstop (hd : 199 / 100 ≤ terminalReflectedSpan U α) :
      Analysis.properExcessEnd (terminalReflectedSpan U α) (terminalReflectedHeight U α)
        (1 / 30) ≤ 91 / 100 := by
    rcases hparams.2.2 with h | h
    · exact (Analysis.properExcessEnd_lt_negative_middle hd h.2.1.le hparams.2.1 h.2.2.le
        (by norm_num) le_rfl).le.trans (by norm_num)
    · exact (Analysis.properExcessEnd_lt_nonnegative_middle hd h.2.1.le hparams.2.1 h.2.2.le
        (by norm_num) le_rfl).le
  have hactive := D.ae_linear_excess_of_proper_scalar_bounds
    (δ := (1 / 30 : ℝ)) (B := (91 / 100 : ℝ)) (ellMax := (13 / 25 : ℝ))
    (fun t ht => (harms t ht).1) (fun hp => (hentry hp).1) (fun hp => (hentry hp).2)
    hparams.1 hd1 hparams.2.1 he1 (by norm_num) le_rfl
    (by linarith only [hgap, hparams.1]) henergy.le hstop
    (fun hd => (Analysis.properDecayLength_lt_fifty_two_hundredths
      hd hd1 hparams.2.1 he1 (by norm_num) le_rfl).le)
    (by linarith only [hgap])
  have hzero := hU.properReflected_densities_zero_after_active
    hproper hl hr hheight haffine hρ hρ0 heq
  apply ae_Ioo_splice_real hactive
  filter_upwards [hzero] with r hr
  rw [hr.1]
  simp only [zero_sub, max_eq_right (by norm_num : (-1 : ℝ) ≤ 0)]
  exact mul_nonneg (by norm_num) (le_max_right _ _)

theorem IsJointCapMaximizer.properReflected_ae_excess_bound
    {U : Set Plane} {α C m c K : ℝ} {ρ : ℝ → ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (hsharp : ∀ t, ρ t ≤ sourceKappa (upperCornerVelocity U t))
    (heq : (upperCurvature U).restrict (regularProperCurvatureDomain α m) =
      (volume.restrict (regularProperCurvatureDomain α m)).withDensity
        (fun t => ENNReal.ofReal (ρ t))) :
    ∀ᵐ r ∂volume.restrict (Ioo (Real.pi / 2 - α) (Real.pi / 2)),
      max (properReflectedFirstDensity m ρ r - 1) 0 ≤
        (19 / 25 : ℝ) * max (91 / 100 - r) 0 := by
  exact IsJointCapMaximizer.properReflected_ae_excess_bound_of_tail_regime hU
    (hU.properTailRegime_of_largest hLargest hproper hheight haffine) hproper hl hr hheight haffine
    hρ hρ0 hρK hsharp heq

end AmbidextrousSofa
