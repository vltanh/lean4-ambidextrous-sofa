module

public import AmbidextrousSofa.Analysis.PartialReflectedSupport
public import AmbidextrousSofa.Analysis.TerminalThreeSupports
public import AmbidextrousSofa.Analysis.TerminalCorner
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

/-!
# The actual terminal impulse and its exact energy payment

The impulse is the whole curvature atom at the first terminal normal.
Its upper bound follows from the actual facet reserve. The exact change
of the same-sign energy is a quadratic in that atom; its maximum on the
proved atom interval has a useful cancellation in the terminal inset.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem terminalInset_mul_cos {α : ℝ} (hα0 : 0 < α) (hαL : α < Real.pi / 2) :
    terminalInset α * Real.cos α = 1 - Real.sin α := by
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith only [hα0, Real.pi_pos], hαL⟩
  exact div_mul_cancel₀ _ hc.ne'

theorem terminalInset_mul_one_add_sin {α : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2) :
    terminalInset α * (1 + Real.sin α) = Real.cos α := by
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith only [hα0, Real.pi_pos], hαL⟩
  unfold terminalInset
  field_simp [hc.ne']
  nlinarith only [Real.sin_sq_add_cos_sq α]

theorem terminalInset_sq_mul_one_add_sin {α : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2) :
    terminalInset α ^ 2 * (1 + Real.sin α) = 1 - Real.sin α := by
  calc
    _ = terminalInset α * (terminalInset α * (1 + Real.sin α)) := by ring
    _ = terminalInset α * Real.cos α := by rw [terminalInset_mul_one_add_sin hα0 hαL]
    _ = 1 - Real.sin α := terminalInset_mul_cos hα0 hαL

theorem terminalInset_lt_one {α : ℝ} (hα0 : 0 < α) (hαL : α < Real.pi / 2) :
    terminalInset α < 1 := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hα0 (by linarith only [hαL, Real.pi_pos])
  have hk := terminalInset_pos hα0 hαL
  have hrel := terminalInset_mul_one_add_sin hα0 hαL
  nlinarith only [hrel, mul_pos hk hs, Real.cos_le_one α]

theorem terminalSlope_mul_one_sub_inset_sq {α : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2) :
    terminalSlope α * (1 - terminalInset α ^ 2) = 2 * terminalInset α := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hα0 (by linarith only [hαL, Real.pi_pos])
  have hκ : terminalSlope α * Real.sin α = Real.cos α := div_mul_cancel₀ _ hs.ne'
  have hkc := terminalInset_mul_cos hα0 hαL
  have hks := terminalInset_mul_one_add_sin hα0 hαL
  have hsqc : terminalInset α ^ 2 * Real.cos α = terminalInset α * (1 - Real.sin α) := by
    calc
      _ = terminalInset α * (terminalInset α * Real.cos α) := by ring
      _ = terminalInset α * (1 - Real.sin α) := by rw [hkc]
  apply (mul_right_cancel₀ hs.ne')
  calc
    terminalSlope α * (1 - terminalInset α ^ 2) * Real.sin α =
        (1 - terminalInset α ^ 2) * (terminalSlope α * Real.sin α) := by ring
    _ = (1 - terminalInset α ^ 2) * Real.cos α := by rw [hκ]
    _ = 2 * terminalInset α * Real.sin α := by nlinarith only [hks, hsqc]

theorem terminalInset_lt_half_slope {α : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2) :
    terminalInset α < terminalSlope α / 2 := by
  have hκ := terminalSlope_pos hα0 hαL
  have hk := terminalInset_pos hα0 hαL
  have hrel := terminalSlope_mul_one_sub_inset_sq hα0 hαL
  nlinarith only [hrel, mul_pos hκ (sq_pos_of_pos hk)]

theorem terminalInset_lt_two_elevenths_of_slope_le {α : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2) (hκ : terminalSlope α ≤ 3 / 8) :
    terminalInset α < 2 / 11 := by
  have hk0 := terminalInset_pos hα0 hαL
  have hk1 := terminalInset_lt_one hα0 hαL
  have hden : 0 ≤ 1 - terminalInset α ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hk1.le)
      (show 0 ≤ 1 + terminalInset α by linarith only [hk0])]
  have hmul := mul_le_mul_of_nonneg_right hκ hden
  rw [terminalSlope_mul_one_sub_inset_sq hα0 hαL] at hmul
  by_contra hnot
  have hlow := le_of_not_gt hnot
  have hsq := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 2 / 11) hk0.le).mpr hlow
  nlinarith only [hmul, hlow, hsq]

theorem terminal_gap_eq_arctan_slope {α : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2) :
    Real.pi / 2 - α = Real.arctan (terminalSlope α) := by
  have h := Real.arctan_tan
    (x := Real.pi / 2 - α) (by linarith only [hαL, Real.pi_pos])
    (by linarith only [hα0])
  rw [Real.tan_eq_sin_div_cos, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub] at h
  exact h.symm

theorem terminal_near_full_bounds {α : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2) (hκ : terminalSlope α ≤ 1 / 8) :
    124 / 125 < Real.sin α ∧ Real.cos α < 1 / 8 ∧
      Real.pi / 2 - α < 1 / 8 ∧ terminalInset α < 1 / 16 := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hα0 (by linarith only [hαL, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith only [hα0, Real.pi_pos], hαL⟩
  have hs1 : Real.sin α < 1 := by
    nlinarith only [Real.sin_sq_add_cos_sq α, Real.sin_le_one α, sq_pos_of_pos hc]
  have hcs : Real.cos α ≤ Real.sin α / 8 := by
    have h := (div_le_iff₀ hs).mp hκ
    change Real.cos α ≤ (1 / 8) * Real.sin α at h
    linarith only [h]
  have hsin : 124 / 125 < Real.sin α := by
    by_contra hnot
    have hsle := le_of_not_gt hnot
    have hsquare := mul_nonneg (sub_nonneg.mpr hsle)
      (show 0 ≤ 124 / 125 + Real.sin α by linarith only [hs])
    have hcsquare := mul_nonneg (sub_nonneg.mpr hcs)
      (show 0 ≤ Real.sin α / 8 + Real.cos α by positivity)
    nlinarith only [hsquare, hcsquare, Real.sin_sq_add_cos_sq α]
  have hgap : Real.pi / 2 - α < 1 / 8 := by
    rw [terminal_gap_eq_arctan_slope hα0 hαL]
    exact (Real.arctan_lt_self (terminalSlope_pos hα0 hαL)).trans_le hκ
  exact ⟨hsin, by linarith only [hcs, hs1], hgap,
    by linarith only [terminalInset_lt_half_slope hα0 hαL, hκ]⟩

theorem IsJointCapMaximizer.proper_terminalSlope_lt_three_eighths
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α)
    (hproper : α < Real.pi / 2) : terminalSlope α < 3 / 8 := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hU.angle_pos (by linarith only [hproper, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith only [hU.angle_pos, Real.pi_pos], hproper⟩
  have ht := Real.strictMonoOn_tan (Real.arctan_mem_Ioo (8 / 3))
    (show α ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨by linarith only [hU.angle_pos, Real.pi_pos], hproper⟩)
    hU.terminal_angle_gt_arctan_eight_thirds
  rw [Real.tan_arctan, Real.tan_eq_sin_div_cos] at ht
  have hsc := (lt_div_iff₀ hc).mp ht
  apply (div_lt_iff₀ hs).mpr
  linarith only [hsc]

/-- The actual whole terminal curvature atom is bounded by the small
universal inset, using the proved terminal facet reserve. -/
theorem IsJointCapMaximizer.terminal_curvature_atom_le_inset_of_tail_regime
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    0 ≤ MovingSofaOptimality.sigmaAt U α ∧ MovingSofaOptimality.sigmaAt U α ≤ terminalInset α := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hU.angle_pos (by linarith only [hproper, Real.pi_pos])
  have hmass := hU.terminal_curvature_atom_le_reserve_div_sin_of_tail_regime hregime hproper hheight haffine
  have hH := (hU.terminalTailPoint_bounds_of_tail_regime hregime hproper hheight haffine).2.1
  obtain ⟨_, _, _, hreserve, _⟩ := hU.isCap.terminalTailInset_bounds hU.angle_pos hproper hH
  have hdiv : terminalTailReserve U α / Real.sin α ≤ Real.cos α / (1 + Real.sin α) := by
    apply (div_le_iff₀ hs).mpr
    exact hreserve.trans_eq (by ring)
  have hk : terminalInset α = Real.cos α / (1 + Real.sin α) :=
    (eq_div_iff (show 1 + Real.sin α ≠ 0 by linarith only [hs])).mpr
      (terminalInset_mul_one_add_sin hU.angle_pos hproper)
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  change MovingSofaOptimality.sigmaAt U α ≤ terminalTailReserve U α / Real.sin α at hmass
  exact (hmass.trans hdiv).trans_eq hk.symm

theorem IsJointCapMaximizer.terminal_curvature_atom_le_inset
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    0 ≤ MovingSofaOptimality.sigmaAt U α ∧ MovingSofaOptimality.sigmaAt U α ≤ terminalInset α := by
  exact IsJointCapMaximizer.terminal_curvature_atom_le_inset_of_tail_regime hU
    (hU.properTailRegime_of_largest hLargest hproper hheight haffine) hproper hheight haffine

namespace Analysis

def terminalImpulseEnergyChange (d e α j : ℝ) : ℝ :=
  (1 - e) * (1 - Real.sin α) - d * Real.cos α +
    2 * j * (d * Real.sin α - (1 - e) * Real.cos α) + j ^ 2

theorem initialFloorCircle_impulse_energy (d e α j : ℝ) :
    initialFloorEnergy (initialFloorCircleP d (e - 1) (Real.pi / 2 - α))
      (initialFloorCircleQ d (e - 1) (Real.pi / 2 - α) + j) =
        d ^ 2 - e * (1 - e) + 1 / 4 + terminalImpulseEnergyChange d e α j := by
  have h := initialFloorCircle_energy d (e - 1) (Real.pi / 2 - α)
  simp only [initialFloorCircleP, initialFloorCircleQ, Real.cos_pi_div_two_sub,
    Real.sin_pi_div_two_sub] at h ⊢
  unfold initialFloorEnergy terminalImpulseEnergyChange at *
  nlinarith only [h]

theorem terminalImpulseEnergyChange_le_at_inset {d e α j : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2)
    (hj0 : 0 ≤ j) (hjk : j ≤ terminalInset α)
    (hQ : 0 ≤ d * Real.sin α - (1 - e) * Real.cos α) :
    terminalImpulseEnergyChange d e α j ≤
      terminalImpulseEnergyChange d e α (terminalInset α) := by
  have hj := mul_le_mul_of_nonneg_right hjk hQ
  have hsq := (sq_le_sq₀ hj0 (terminalInset_pos hα0 hαL).le).mpr hjk
  unfold terminalImpulseEnergyChange
  nlinarith only [hj, hsq]

theorem terminalImpulseEnergyChange_at_inset {d e α : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2) :
    terminalImpulseEnergyChange d e α (terminalInset α) =
      terminalInset α ^ 2 * (e - (1 - e) * Real.sin α - d * Real.cos α) := by
  have hkc := terminalInset_mul_cos hα0 hαL
  have hks := terminalInset_mul_one_add_sin hα0 hαL
  have hk2 := terminalInset_sq_mul_one_add_sin hα0 hαL
  have htail : 2 * terminalInset α * Real.sin α - Real.cos α =
      -terminalInset α ^ 2 * Real.cos α := by
    calc
      _ = terminalInset α * (Real.sin α - 1) := by nlinarith only [hks]
      _ = -terminalInset α * (1 - Real.sin α) := by ring
      _ = -terminalInset α * (terminalInset α * Real.cos α) := by rw [hkc]
      _ = -terminalInset α ^ 2 * Real.cos α := by ring
  calc
    terminalImpulseEnergyChange d e α (terminalInset α) =
        -(1 - e) * (1 - Real.sin α) + terminalInset α ^ 2 +
          d * (2 * terminalInset α * Real.sin α - Real.cos α) := by
      unfold terminalImpulseEnergyChange
      linear_combination -2 * (1 - e) * hkc
    _ = terminalInset α ^ 2 * (e - (1 - e) * Real.sin α - d * Real.cos α) := by
      rw [htail, ← hk2]
      ring

theorem terminalImpulseEnergyChange_le_inset_sq {d e α j : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2) (hd : 0 ≤ d) (he : e ≤ 1)
    (hj0 : 0 ≤ j) (hjk : j ≤ terminalInset α)
    (hQ : 0 ≤ d * Real.sin α - (1 - e) * Real.cos α) :
    terminalImpulseEnergyChange d e α j ≤ terminalInset α ^ 2 := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hα0 (by linarith only [hαL, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith only [hα0, Real.pi_pos], hαL⟩
  have hbracket : e - (1 - e) * Real.sin α - d * Real.cos α ≤ 1 := by
    nlinarith only [he, mul_nonneg (sub_nonneg.mpr he) hs.le, mul_nonneg hd hc.le]
  have h := terminalImpulseEnergyChange_le_at_inset hα0 hαL hj0 hjk hQ
  rw [terminalImpulseEnergyChange_at_inset hα0 hαL] at h
  exact h.trans (by simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hbracket (sq_nonneg (terminalInset α)))

theorem terminalImpulseEnergyChange_lt_one_four_hundred_eightieth {d e α j : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2) (hκ : terminalSlope α ≤ 1 / 8)
    (hd : 0 ≤ d) (he : e ≤ 19 / 25)
    (hj0 : 0 ≤ j) (hjk : j ≤ terminalInset α)
    (hQ : 0 ≤ d * Real.sin α - (1 - e) * Real.cos α) :
    terminalImpulseEnergyChange d e α j < 1 / 480 := by
  obtain ⟨hs, _hcsmall, _hgap, hk⟩ := terminal_near_full_bounds hα0 hαL hκ
  have hs0 := Real.sin_pos_of_pos_of_lt_pi hα0 (by linarith only [hαL, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith only [hα0, Real.pi_pos], hαL⟩
  have hbracket : e - (1 - e) * Real.sin α - d * Real.cos α < 53 / 100 := by
    have hp := mul_nonneg (sub_nonneg.mpr he)
      (show 0 ≤ 1 + Real.sin α by linarith only [hs0])
    nlinarith only [hp, hs, mul_nonneg hd hc.le]
  have hk0 := terminalInset_pos hα0 hαL
  have h := terminalImpulseEnergyChange_le_at_inset hα0 hαL hj0 hjk hQ
  rw [terminalImpulseEnergyChange_at_inset hα0 hαL] at h
  have hstrict := h.trans_lt (mul_lt_mul_of_pos_left hbracket (sq_pos_of_pos hk0))
  have hsq := (sq_lt_sq₀ hk0.le (by norm_num : (0 : ℝ) ≤ 1 / 16)).mpr hk
  nlinarith only [hstrict, hsq]

theorem terminalImpulseEnergyChange_lt_one_thirtieth {d e α j : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2) (hκ : terminalSlope α ≤ 3 / 8)
    (hd : 0 ≤ d) (he : e ≤ 1)
    (hj0 : 0 ≤ j) (hjk : j ≤ terminalInset α)
    (hQ : 0 ≤ d * Real.sin α - (1 - e) * Real.cos α) :
    terminalImpulseEnergyChange d e α j < 1 / 30 := by
  have h := terminalImpulseEnergyChange_le_inset_sq hα0 hαL hd he hj0 hjk hQ
  have hk := terminalInset_lt_two_elevenths_of_slope_le hα0 hαL hκ
  have hsq := (sq_lt_sq₀ (terminalInset_pos hα0 hαL).le
    (by norm_num : (0 : ℝ) ≤ 2 / 11)).mpr hk
  nlinarith only [h, hsq]

end Analysis

theorem IsJointCapMaximizer.properReflected_initial_energy_of_tail_regime
    {U : Set Plane} {α m c K : ℝ} {ρ : ℝ → ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (heq : (upperCurvature U).restrict (regularProperCurvatureDomain α m) =
      (volume.restrict (regularProperCurvatureDomain α m)).withDensity
        (fun t => ENNReal.ofReal (ρ t))) :
    Analysis.initialFloorEnergy (properReflectedP U m ρ (Real.pi / 2 - α))
      (properReflectedQ U m ρ (Real.pi / 2 - α)) =
        terminalReflectedSpan U α ^ 2 -
          terminalReflectedHeight U α * (1 - terminalReflectedHeight U α) + 1 / 4 +
          Analysis.terminalImpulseEnergyChange (terminalReflectedSpan U α)
            (terminalReflectedHeight U α) α (MovingSofaOptimality.sigmaAt U α) := by
  have h := hU.properReflected_terminal_impulse_of_tail_regime hregime hproper hheight haffine hρ hρ0 hρK heq
  rw [h.1, h.2]
  exact Analysis.initialFloorCircle_impulse_energy _ _ _ _

theorem IsJointCapMaximizer.properReflected_initial_energy
    {U : Set Plane} {α m c K : ℝ} {ρ : ℝ → ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (heq : (upperCurvature U).restrict (regularProperCurvatureDomain α m) =
      (volume.restrict (regularProperCurvatureDomain α m)).withDensity
        (fun t => ENNReal.ofReal (ρ t))) :
    Analysis.initialFloorEnergy (properReflectedP U m ρ (Real.pi / 2 - α))
      (properReflectedQ U m ρ (Real.pi / 2 - α)) =
        terminalReflectedSpan U α ^ 2 -
          terminalReflectedHeight U α * (1 - terminalReflectedHeight U α) + 1 / 4 +
          Analysis.terminalImpulseEnergyChange (terminalReflectedSpan U α)
            (terminalReflectedHeight U α) α (MovingSofaOptimality.sigmaAt U α) := by
  exact IsJointCapMaximizer.properReflected_initial_energy_of_tail_regime hU
    (hU.properTailRegime_of_largest hLargest hproper hheight haffine) hproper hheight haffine hρ hρ0
    hρK heq

end AmbidextrousSofa
