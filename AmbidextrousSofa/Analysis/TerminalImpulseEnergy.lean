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
  div_mul_cancel₀ _ (sin_cos_pos_of_mem_quarter ⟨hα0, hαL⟩).2.ne'

theorem terminalInset_mul_one_add_sin {α : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2) :
    terminalInset α * (1 + Real.sin α) = Real.cos α := by
  rw [terminalInset, div_mul_eq_mul_div, div_eq_iff (sin_cos_pos_of_mem_quarter ⟨hα0, hαL⟩).2.ne']
  linear_combination -Real.sin_sq_add_cos_sq α

theorem terminalSlope_mul_one_sub_inset_sq {α : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2) :
    terminalSlope α * (1 - terminalInset α ^ 2) = 2 * terminalInset α := by
  obtain ⟨hs, hc⟩ := sin_cos_pos_of_mem_quarter ⟨hα0, hαL⟩
  unfold terminalSlope terminalInset
  field_simp
  linear_combination Real.sin_sq_add_cos_sq α

theorem terminalInset_le_half_slope {α : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2) : terminalInset α ≤ terminalSlope α / 2 := by
  linarith only [terminalSlope_mul_one_sub_inset_sq hα0 hαL,
    mul_nonneg (terminalSlope_pos hα0 hαL).le (sq_nonneg (terminalInset α))]

theorem terminal_height_loss_le_half_slope_sq {α : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2) : 1 - Real.sin α ≤ terminalSlope α ^ 2 / 2 := by
  obtain ⟨hs, -⟩ := sin_cos_pos_of_mem_quarter ⟨hα0, hαL⟩
  have hcs : terminalSlope α * Real.sin α = Real.cos α := div_mul_cancel₀ _ hs.ne'
  have hcs2 : terminalSlope α ^ 2 * Real.sin α ^ 2 = Real.cos α ^ 2 := by rw [← mul_pow, hcs]
  have hid : Real.sin α ^ 2 * (terminalSlope α ^ 2 - 2 * (1 - Real.sin α)) =
      (1 - Real.sin α) ^ 2 * (1 + 2 * Real.sin α) := by
    linear_combination hcs2 + Real.sin_sq_add_cos_sq α
  have hfactor : 0 ≤ Real.sin α ^ 2 * (terminalSlope α ^ 2 - 2 * (1 - Real.sin α)) := by
    rw [hid]
    exact mul_nonneg (sq_nonneg _) (by linarith only [hs])
  have hnonneg : 0 ≤ terminalSlope α ^ 2 - 2 * (1 - Real.sin α) :=
    le_of_mul_le_mul_left (by simpa using hfactor) (sq_pos_of_pos hs)
  linarith only [hnonneg]

theorem terminalSlope_mul_tailInset (U : Set Plane) {α : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2) :
    terminalSlope α * terminalTailInset U α = terminalSlope α * terminalInset α +
      (1 - (terminalTailPoint U α).2) := by
  obtain ⟨hs, hc⟩ := sin_cos_pos_of_mem_quarter ⟨hα0, hαL⟩
  unfold terminalSlope terminalTailInset terminalInset
  field_simp
  ring

theorem terminal_gap_eq_arctan_slope {α : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2) :
    Real.pi / 2 - α = Real.arctan (terminalSlope α) := by
  rw [terminalSlope, ← Real.cos_pi_div_two_sub α, ← Real.sin_pi_div_two_sub α,
    ← Real.tan_eq_sin_div_cos, Real.arctan_tan (by linarith) (by linarith [Real.pi_pos])]

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
  have hs := (sin_cos_pos_of_mem_quarter ⟨hU.angle_pos, hproper⟩).1
  have hH := (hU.terminalTailPoint_bounds_of_tail_regime hregime hproper hheight haffine).2.1
  have hreserve := (hU.isCap.terminalTailInset_bounds hU.angle_pos hproper hH).2.2.2.1
  have hwidth := hU.terminalFaceWidth_le_reserve_of_tail_regime hregime hproper hheight haffine
  rw [hU.isCap.terminalFaceWidth_eq_curvature_atom] at hwidth
  refine ⟨ENNReal.toReal_nonneg, le_of_mul_le_mul_right ((hwidth.trans hreserve).trans_eq ?_) hs⟩
  rw [← terminalInset_mul_one_add_sin hU.angle_pos hproper]
  field_simp

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

/-- The whole atom costs less than the square of the geometric inset. -/
theorem terminalImpulseEnergyChange_lt_inset_sq {d e α j : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2) (hd : 0 < d) (he : e ≤ 1)
    (hj0 : 0 ≤ j) (hjk : j ≤ terminalInset α)
    (hQ : 0 ≤ d * Real.sin α - (1 - e) * Real.cos α) :
    terminalImpulseEnergyChange d e α j < terminalInset α ^ 2 := by
  obtain ⟨hs, hc⟩ := sin_cos_pos_of_mem_quarter ⟨hα0, hαL⟩
  have hbracket : e - (1 - e) * Real.sin α - d * Real.cos α < 1 := by
    linarith only [mul_nonneg (sub_nonneg.2 he) (by linarith only [hs] : 0 ≤ 1 + Real.sin α), mul_pos hd hc]
  exact (terminalImpulseEnergyChange_le_inset hα0 hαL hj0 hjk hQ).trans_lt
    (by nlinarith only [mul_pos (sq_pos_of_pos (terminalInset_pos hα0 hαL)) (sub_pos.2 hbracket)])

end Analysis

theorem IsJointCapMaximizer.properReflected_initial_energy_of_tail_regime
    {U : Set Plane} {α m c K : ℝ} {ρ : ℝ → ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m) (hproper : α < Real.pi / 2)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (heq : (upperCurvature U).restrict (regularProperCurvatureDomain α m) =
      (volume.restrict (regularProperCurvatureDomain α m)).withDensity
        (fun t => ENNReal.ofReal (ρ t))) :
    Analysis.initialFloorEnergy (properReflectedP U m ρ (Real.pi / 2 - α))
      (properReflectedQ U ρ (Real.pi / 2 - α)) =
        terminalReflectedSpan U α ^ 2 -
          terminalReflectedHeight U α * (1 - terminalReflectedHeight U α) + 1 / 4 +
          Analysis.terminalImpulseEnergyChange (terminalReflectedSpan U α)
            (terminalReflectedHeight U α) α (MovingSofaOptimality.sigmaAt U α) := by
  obtain ⟨hP, hQ⟩ := hU.properReflected_terminal_impulse_of_tail_regime hregime hproper haffine
    hρ hρ0 hρK heq
  rw [hP, hQ, Analysis.initialFloorCircle_impulse_energy]

end AmbidextrousSofa
