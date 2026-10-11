module

public import AmbidextrousSofa.Analysis.ProperExcessScalar
public import AmbidextrousSofa.Analysis.ProperReflectedEntry

@[expose] public section

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

open Analysis

theorem ae_Ioo_splice_real {P : ℝ → Prop} {a b c : ℝ}
    (hleft : ∀ᵐ t ∂volume.restrict (Ioo a b), P t)
    (hright : ∀ᵐ t ∂volume.restrict (Ioo b c), P t) :
    ∀ᵐ t ∂volume.restrict (Ioo a c), P t :=
  ae_restrict_of_ae_restrict_of_subset (fun t ht => (le_or_gt t b).imp (⟨ht.1, ·⟩) (⟨·, ht.2⟩))
    ((ae_restrict_union_iff _ _ _).2 ⟨(ae_restrict_congr_set Ioo_ae_eq_Ioc).1 hleft, hright⟩)

namespace CornerArcDynamics

variable {p q u v : ℝ → ℝ} {a b : ℝ}

/-- Below threshold there is no excess. Above threshold the actual
energy forces the lower width needed for the exact root comparison. The
bound on the active arc `(a, b)` extends to `(a, c)` when `u` vanishes on `(b, c)`. -/
theorem ae_linear_excess_of_proper_scalar_bounds
    (D : CornerArcDynamics p q u v a b) {c d e δ B ellMax : ℝ}
    (hfirst : ∀ t ∈ Icc a b, p t ≤ 1)
    (hpa : 0 < p a → p a ≤ e - d * a + a ^ 2 / 2)
    (hqa : 0 < p a → d - 1 - a ≤ q a)
    (hzero : ∀ᵐ t ∂volume.restrict (Ioo b c), u t = 0)
    (hd0 : 3 / 2 < d) (hd1 : d ≤ 2311 / 1000)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 30)
    (had : a ≤ d)
    (henergy : clippedCornerEnergy p q a ≤ d ^ 2 - e * (1 - e) + 1 / 4 + δ)
    (hstop : 199 / 100 ≤ d → properExcessEnd d e δ ≤ B)
    (hdecay : 199 / 100 ≤ d → properDecayLength d e δ ≤ ellMax)
    (hgap : a + ellMax ≤ B) :
    ∀ᵐ t ∂volume.restrict (Ioo a c),
      max (u t - 1) 0 ≤ (19 / 25 : ℝ) * max (B - t) 0 := by
  have hunit (t : ℝ) (ht : u t ≤ 1) : max (u t - 1) 0 ≤ (19 / 25 : ℝ) * max (B - t) 0 := by
    rw [max_eq_right (sub_nonpos.2 ht)]
    exact mul_nonneg (by norm_num) (le_max_right _ _)
  refine ae_Ioo_splice_real ?_ (hzero.mono fun t ht => hunit t (ht.trans_le zero_le_one))
  by_cases hZ : d ^ 2 - e * (1 - e) + δ ≤ 4
  · exact (D.ae_unit_of_initial_energy (by linarith)).mono hunit
  have hd : 199 / 100 ≤ d := (pow_le_pow_iff_left₀ (by norm_num) (by linarith) two_ne_zero).1
    (by linarith [mul_nonneg he0 (sub_nonneg.2 he1)])
  obtain ⟨⟨-, -, hx2⟩, ⟨-, -, hy2⟩, ⟨-, -, hz2⟩⟩ := properExcess_roots_bounds hd hd1 he0 he1 hδ0 hδ1
  have hY : 2 < properEnergyRoot d e δ := (Real.lt_sqrt (by norm_num)).2 (by linarith)
  have hell0 : 0 ≤ properDecayLength d e δ := sub_nonneg.2 (Real.le_sqrt_of_sq_le (by linarith))
  have hell := properDecayLength_lt_fifty_two_hundredths hd hd1 he0 he1 hδ0 hδ1
  have hτ : properFirstZeroTime d e ≤ d := sub_le_self _ (Real.sqrt_nonneg _)
  have hquad := properFirstZeroTime_quadratic (hx2 ▸ sq_nonneg _)
  -- The first zero `τ` and the quadratic deadline `max a τ + ell` of the excess.
  set τ := properFirstZeroTime d e
  set ell := properDecayLength d e δ
  have henergy' : clippedCornerEnergy p q a ≤ 1 / 4 + (2 + ell / 2 + ell ^ 2 / 4) ^ 2 := by
    rw [show 2 + ell / 2 + ell ^ 2 / 4 = properEnergyRoot d e δ by
      simp only [ell, properDecayLength]; linear_combination hz2 / 4, hy2]
    linarith
  have hcross : e ≤ d * max a τ - max a τ ^ 2 / 2 := by
    linarith [mul_nonneg (sub_nonneg.2 (le_max_right a τ))
      (by linarith [max_le had hτ] : 0 ≤ 2 * d - max a τ - τ)]
  have hdeadline : max a τ + ell ≤ B :=
    (max_add_add_right a τ ell).symm.trans_le (max_le (by linarith [hdecay hd]) (hstop hd))
  filter_upwards [D.ae_linear_excess_of_quadratic_deadline hfirst hpa hqa (le_max_left a τ) hcross
    hell0 (by linarith) henergy'] with t ht
  exact ht.trans (mul_le_mul (by linarith) (max_le_max (by linarith) le_rfl) (le_max_right _ _)
    (by norm_num))

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
  obtain ⟨hd0, hd1, he0, he1⟩ := hU.centered_terminal_reflected_near_full_parameters_of_tail_regime
    hregime hproper hl hr hheight haffine hκ
  have hgap := (terminal_near_full_bounds hU.angle_pos hproper hκ).2.2.1
  have harms := hU.properReflected_arm_bounds_of_tail_regime hregime hproper hheight haffine hρ
    hρ0 hρK heq
  have hentry := hU.properReflected_entry_quadratic_of_tail_regime hregime hproper hl hr hheight
    haffine hρ hρ0 hρK heq
  exact (hU.properReflected_cornerArcDynamics_of_tail_regime hregime hproper hl hr hheight haffine
    hρ hρ0 hρK hsharp heq).ae_linear_excess_of_proper_scalar_bounds (δ := 1 / 480)
    (ellMax := 43 / 100) (fun t ht => (harms t ht).1) (fun hp => (hentry hp).1)
    (fun hp => (hentry hp).2) ((hU.properReflected_densities_zero_after_active hproper hl hr
      hheight haffine hρ hρ0 heq).mono fun _ h => h.1) hd0 (by linarith) he0 (by linarith)
    (by norm_num) (by norm_num) (by linarith)
    (hU.properReflected_initial_energy_lt_near_full_payment_of_tail_regime hregime hproper hl hr
      hheight haffine hρ hρ0 hρK heq hκ).le
    (fun hd => (properExcessEnd_lt_near_full hd hd1.le he0 he1.le (by norm_num) le_rfl).le)
    (fun hd => (properDecayLength_lt_near_full hd hd1.le he0 (by linarith) (by norm_num)
      le_rfl).le) (by linarith)

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
  obtain ⟨hd0, he0, hcase⟩ := hU.centered_terminal_reflected_parameters_of_tail_regime hregime
    hproper hl hr hheight haffine
  have hd1 : terminalReflectedSpan U α ≤ 2311 / 1000 := by rcases hcase with h | h <;> linarith
  have he1 : terminalReflectedHeight U α ≤ 1 := by rcases hcase with h | h <;> linarith
  have hgap : Real.pi / 2 - α < 3 / 8 := by
    rw [terminal_gap_eq_arctan_slope hU.angle_pos hproper]
    exact (Real.arctan_lt_self (terminalSlope_pos hU.angle_pos hproper)).trans
      (hU.proper_terminalSlope_lt_three_eighths hproper)
  have harms := hU.properReflected_arm_bounds_of_tail_regime hregime hproper hheight haffine hρ
    hρ0 hρK heq
  have hentry := hU.properReflected_entry_quadratic_of_tail_regime hregime hproper hl hr hheight
    haffine hρ hρ0 hρK heq
  exact (hU.properReflected_cornerArcDynamics_of_tail_regime hregime hproper hl hr hheight haffine
    hρ hρ0 hρK hsharp heq).ae_linear_excess_of_proper_scalar_bounds (δ := 1 / 30)
    (ellMax := 13 / 25) (fun t ht => (harms t ht).1) (fun hp => (hentry hp).1)
    (fun hp => (hentry hp).2) ((hU.properReflected_densities_zero_after_active hproper hl hr
      hheight haffine hρ hρ0 heq).mono fun _ h => h.1) hd0 hd1 he0 he1 (by norm_num) le_rfl
    (by linarith) (hU.properReflected_initial_energy_lt_payment_of_tail_regime hregime hproper hl
      hr hheight haffine hρ hρ0 hρK heq).le
    (fun hd => by
      rcases hcase with h | h
      · exact (properExcessEnd_lt_negative_middle hd h.2.1.le he0 h.2.2.le (by norm_num)
          le_rfl).le.trans (by norm_num)
      · exact (properExcessEnd_lt_nonnegative_middle hd h.2.1.le he0 h.2.2.le (by norm_num)
          le_rfl).le)
    (fun hd => (properDecayLength_lt_fifty_two_hundredths hd hd1 he0 he1 (by norm_num)
      le_rfl).le) (by linarith)

end AmbidextrousSofa
