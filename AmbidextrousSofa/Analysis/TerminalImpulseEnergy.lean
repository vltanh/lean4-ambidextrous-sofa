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
    terminalInset α * Real.cos α = 1 - Real.sin α :=
  div_mul_cancel₀ _ (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hαL⟩).ne'

theorem terminalInset_mul_one_add_sin {α : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2) :
    terminalInset α * (1 + Real.sin α) = Real.cos α := by
  rw [terminalInset, div_mul_eq_mul_div,
    div_eq_iff (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hαL⟩).ne']
  linear_combination -Real.sin_sq_add_cos_sq α

theorem terminalSlope_mul_one_sub_inset_sq {α : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2) :
    terminalSlope α * (1 - terminalInset α ^ 2) = 2 * terminalInset α := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hα0 (by linarith [Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hαL⟩
  unfold terminalSlope terminalInset
  field_simp
  linear_combination Real.sin_sq_add_cos_sq α

theorem terminalInset_lt_two_elevenths_of_slope_le {α : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2) (hκ : terminalSlope α ≤ 3 / 8) :
    terminalInset α < 2 / 11 := by
  have hk0 := terminalInset_pos hα0 hαL
  have hk1 : terminalInset α < 1 := by
    nlinarith [terminalInset_mul_one_add_sin hα0 hαL, Real.cos_le_one α,
      Real.sin_pos_of_pos_of_lt_pi hα0 (by linarith [Real.pi_pos])]
  have hmul := mul_le_mul_of_nonneg_right hκ (by nlinarith : (0 : ℝ) ≤ 1 - terminalInset α ^ 2)
  rw [terminalSlope_mul_one_sub_inset_sq hα0 hαL] at hmul
  nlinarith

theorem terminal_gap_eq_arctan_slope {α : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2) :
    Real.pi / 2 - α = Real.arctan (terminalSlope α) := by
  rw [terminalSlope, ← Real.cos_pi_div_two_sub α, ← Real.sin_pi_div_two_sub α,
    ← Real.tan_eq_sin_div_cos, Real.arctan_tan (by linarith) (by linarith [Real.pi_pos])]

theorem terminal_near_full_bounds {α : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2) (hκ : terminalSlope α ≤ 1 / 8) :
    124 / 125 < Real.sin α ∧ Real.cos α < 1 / 8 ∧
      Real.pi / 2 - α < 1 / 8 ∧ terminalInset α < 1 / 16 := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hα0 (by linarith [Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hαL⟩
  have hs1 : Real.sin α < 1 := (Real.sin_lt_sin_of_lt_of_le_pi_div_two
    (by linarith [Real.pi_pos]) le_rfl hαL).trans_eq Real.sin_pi_div_two
  have hcs : Real.cos α ≤ Real.sin α / 8 := by
    rw [terminalSlope, div_le_iff₀ hs] at hκ
    linarith
  refine ⟨by nlinarith [Real.sin_sq_add_cos_sq α], by linarith, ?_, ?_⟩
  · rw [terminal_gap_eq_arctan_slope hα0 hαL]
    exact (Real.arctan_lt_self (terminalSlope_pos hα0 hαL)).trans_le hκ
  · linarith [terminalSlope_mul_one_sub_inset_sq hα0 hαL,
      mul_pos (terminalSlope_pos hα0 hαL) (pow_pos (terminalInset_pos hα0 hαL) 2)]

theorem IsJointCapMaximizer.proper_terminalSlope_lt_three_eighths
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α)
    (hproper : α < Real.pi / 2) : terminalSlope α < 3 / 8 := by
  rw [← Real.arctan_strictMono.lt_iff_lt, ← terminal_gap_eq_arctan_slope hU.angle_pos hproper,
    show (3 / 8 : ℝ) = (8 / 3)⁻¹ by norm_num, Real.arctan_inv_of_pos (by norm_num)]
  linarith [hU.terminal_angle_gt_arctan_eight_thirds]

/-- The actual whole terminal curvature atom is bounded by the small
universal inset, using the proved terminal facet reserve. -/
theorem IsJointCapMaximizer.terminal_curvature_atom_le_inset_of_tail_regime
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    0 ≤ MovingSofaOptimality.sigmaAt U α ∧ MovingSofaOptimality.sigmaAt U α ≤ terminalInset α := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hU.angle_pos (by linarith [Real.pi_pos])
  have hH := (hU.terminalTailPoint_bounds_of_tail_regime hregime hproper hheight haffine).2.1
  have hreserve := (hU.isCap.terminalTailInset_bounds hU.angle_pos hproper hH).2.2.2.1
  refine ⟨ENNReal.toReal_nonneg, (hU.terminal_curvature_atom_le_reserve_div_sin_of_tail_regime
    hregime hproper hheight haffine).trans ?_⟩
  rw [div_le_iff₀ hs]
  exact hreserve.trans_eq (by rw [← terminalInset_mul_one_add_sin hU.angle_pos hproper]; field_simp)

namespace Analysis

def terminalImpulseEnergyChange (d e α j : ℝ) : ℝ :=
  (1 - e) * (1 - Real.sin α) - d * Real.cos α +
    2 * j * (d * Real.sin α - (1 - e) * Real.cos α) + j ^ 2

theorem initialFloorCircle_impulse_energy (d e α j : ℝ) :
    initialFloorEnergy (initialFloorCircleP d (e - 1) (Real.pi / 2 - α))
      (initialFloorCircleQ d (e - 1) (Real.pi / 2 - α) + j) =
        d ^ 2 - e * (1 - e) + 1 / 4 + terminalImpulseEnergyChange d e α j := by
  have h := initialFloorCircle_energy d (e - 1) (Real.pi / 2 - α)
  simp only [initialFloorEnergy, initialFloorCircleP, initialFloorCircleQ, Real.cos_pi_div_two_sub,
    Real.sin_pi_div_two_sub, terminalImpulseEnergyChange] at h ⊢
  linear_combination h

/-- On the proved atom interval the energy change is at most its value at the inset. -/
theorem terminalImpulseEnergyChange_le_inset {d e α j : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2)
    (hj0 : 0 ≤ j) (hjk : j ≤ terminalInset α)
    (hQ : 0 ≤ d * Real.sin α - (1 - e) * Real.cos α) :
    terminalImpulseEnergyChange d e α j ≤
      terminalInset α ^ 2 * (e - (1 - e) * Real.sin α - d * Real.cos α) := by
  unfold terminalImpulseEnergyChange
  linear_combination 2 * mul_le_mul_of_nonneg_right hjk hQ + pow_le_pow_left₀ hj0 hjk 2 +
    ((1 - e) * terminalInset α + d) * terminalInset_mul_one_add_sin hα0 hαL +
    (d * terminalInset α - (1 - e)) * terminalInset_mul_cos hα0 hαL

theorem terminalImpulseEnergyChange_lt_one_four_hundred_eightieth {d e α j : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2) (hκ : terminalSlope α ≤ 1 / 8)
    (hd : 0 ≤ d) (he : e ≤ 19 / 25)
    (hj0 : 0 ≤ j) (hjk : j ≤ terminalInset α)
    (hQ : 0 ≤ d * Real.sin α - (1 - e) * Real.cos α) :
    terminalImpulseEnergyChange d e α j < 1 / 480 := by
  obtain ⟨hs, -, -, hk⟩ := terminal_near_full_bounds hα0 hαL hκ
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hαL⟩
  have hbracket : e - (1 - e) * Real.sin α - d * Real.cos α ≤ 53 / 100 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr he) (show 0 ≤ 1 + Real.sin α by linarith),
      mul_nonneg hd hc.le]
  nlinarith [terminalImpulseEnergyChange_le_inset hα0 hαL hj0 hjk hQ,
    mul_le_mul_of_nonneg_left hbracket (sq_nonneg (terminalInset α)), terminalInset_pos hα0 hαL]

theorem terminalImpulseEnergyChange_lt_one_thirtieth {d e α j : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2) (hκ : terminalSlope α ≤ 3 / 8)
    (hd : 0 ≤ d) (he : e ≤ 1)
    (hj0 : 0 ≤ j) (hjk : j ≤ terminalInset α)
    (hQ : 0 ≤ d * Real.sin α - (1 - e) * Real.cos α) :
    terminalImpulseEnergyChange d e α j < 1 / 30 := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hα0 (by linarith [Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hαL⟩
  have hbracket : e - (1 - e) * Real.sin α - d * Real.cos α ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr he) hs.le, mul_nonneg hd hc.le]
  nlinarith [terminalImpulseEnergyChange_le_inset hα0 hαL hj0 hjk hQ,
    mul_le_mul_of_nonneg_left hbracket (sq_nonneg (terminalInset α)), terminalInset_pos hα0 hαL,
    terminalInset_lt_two_elevenths_of_slope_le hα0 hαL hκ]

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
  obtain ⟨hP, hQ⟩ := hU.properReflected_terminal_impulse_of_tail_regime hregime hproper hheight
    haffine hρ hρ0 hρK heq
  rw [hP, hQ, Analysis.initialFloorCircle_impulse_energy]

end AmbidextrousSofa
