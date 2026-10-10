import AmbidextrousSofa.Analysis.ExactEstimates
import AmbidextrousSofa.Analysis.TerminalWallBound
import AmbidextrousSofa.Analysis.JointCapMaximum

/-!
# Exact exclusion of low terminal angles

The actual outgoing-wall estimate reduces the cap score to a function
of sine and cosine. On `π/4 ≤ α ≤ arctan (5/4)`, its cotangent lies in
`[4/5,1]`. A squared inequality and a factored quadratic give the exact
upper bound `(33 + 5 * sqrt 41) / 80`; no derivative estimate or numerical
search is used.

A rational cut below the actual defining cubic root gives `41/50 < M/2`.
Consequently every actual joint cap maximizer has terminal angle strictly
above `arctan (5/4)`. The remaining terminal angles are not settled here.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

/-- The reciprocal-sine and cotangent relation gives the exact scalar
endpoint bound throughout the relevant cotangent interval. -/
theorem terminal_cotangent_scalar_bound {a s : ℝ}
    (ha0 : 4 / 5 ≤ a) (ha1 : a ≤ 1) (hs0 : 0 ≤ s)
    (hs2 : s ^ 2 = 1 + a ^ 2) :
    (1 + s) ^ 2 / (8 * a) ≤ (33 + 5 * Real.sqrt 41) / 80 := by
  have ha : 0 < a := by linarith
  have hr0 := Real.sqrt_nonneg (41 : ℝ)
  have hr2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 41)
  have ha2 : 16 / 25 ≤ a ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ a - 4 / 5 by linarith)
      (show 0 ≤ a + 4 / 5 by linarith)]
  have hroot : 4 * s ≤ a * Real.sqrt 41 := by
    apply (sq_le_sq₀ (by positivity : 0 ≤ 4 * s)
      (mul_nonneg ha.le hr0)).mp
    simp only [mul_pow, hs2, hr2]
    nlinarith
  have hquadratic : 10 * a ^ 2 + 20 ≤ 33 * a := by
    nlinarith [mul_nonneg (show 0 ≤ 5 * a - 4 by linarith)
      (show 0 ≤ 5 - 2 * a by linarith)]
  apply (div_le_iff₀ (by positivity : 0 < 8 * a)).2
  nlinarith

/-- PD's exact angle bound is proved from the real sine and cosine
values, rather than assumed through an auxiliary parameter. -/
theorem terminal_bound_le_arctan_five_fourths {α : ℝ}
    (hα0 : Real.pi / 4 ≤ α) (hα1 : α ≤ Real.arctan (5 / 4)) :
    (1 + 1 / Real.sin α) ^ 2 / (8 * (Real.cos α / Real.sin α)) ≤
      (33 + 5 * Real.sqrt 41) / 80 := by
  have hαpos : 0 < α := by linarith [Real.pi_pos]
  have hαL : α < Real.pi / 2 :=
    hα1.trans_lt (Real.arctan_lt_pi_div_two (5 / 4))
  have hαmem : α ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], hαL⟩
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hαpos
    (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo hαmem
  have htan0 : 1 ≤ Real.tan α := by
    have h := Real.strictMonoOn_tan.monotoneOn
      (show Real.pi / 4 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) from
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
      hαmem hα0
    simpa only [Real.tan_pi_div_four] using h
  have htan1 : Real.tan α ≤ 5 / 4 := by
    have h := Real.strictMonoOn_tan.monotoneOn hαmem
      (Real.arctan_mem_Ioo (5 / 4)) hα1
    simpa only [Real.tan_arctan] using h
  rw [Real.tan_eq_sin_div_cos] at htan0 htan1
  have hsc0 := (le_div_iff₀ hc).1 htan0
  have hsc1 := (div_le_iff₀ hc).1 htan1
  have ha0 : 4 / 5 ≤ Real.cos α / Real.sin α := by
    apply (le_div_iff₀ hs).2
    linarith
  have ha1 : Real.cos α / Real.sin α ≤ 1 := by
    apply (div_le_iff₀ hs).2
    linarith
  have hs2 : (1 / Real.sin α) ^ 2 = 1 + (Real.cos α / Real.sin α) ^ 2 := by
    calc
      _ = 1 / Real.sin α ^ 2 := by rw [div_pow, one_pow]
      _ = (Real.sin α ^ 2 + Real.cos α ^ 2) / Real.sin α ^ 2 := by
        rw [Real.sin_sq_add_cos_sq]
      _ = _ := by
        rw [add_div, div_self (pow_ne_zero 2 (ne_of_gt hs)), div_pow]
  exact terminal_cotangent_scalar_bound ha0 ha1 (by positivity) hs2

theorem terminal_exact_bound_lt_rational :
    (33 + 5 * Real.sqrt 41) / 80 < (1301 / 1600 : ℝ) := by
  have hs : Real.sqrt (41 : ℝ) < 641 / 100 :=
    (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
  linarith

/-- The reference margin comes from the defining cubic and a proved
arctangent lower bound. -/
theorem forty_one_fiftieths_lt_half_M : (41 / 50 : ℝ) < M / 2 := by
  have hY : (19 / 64 : ℝ) < Y := by
    apply (cubic_strictMono.lt_iff_lt).mp
    rw [Y_cubic]
    norm_num [cubic]
  have hbeta : Y - Y ^ 3 / 3 ≤ beta := self_sub_cube_div_three_le_arctan Y_pos.le
  have hYsq := mul_pos (sub_pos.mpr hY)
    (show 0 < Y + 19 / 64 by linarith [Y_pos])
  unfold M
  nlinarith [Y_equation]

theorem terminal_exact_bound_lt_half_M :
    (33 + 5 * Real.sqrt 41) / 80 < M / 2 := by
  calc
    _ < (1301 / 1600 : ℝ) := terminal_exact_bound_lt_rational
    _ < (41 / 50 : ℝ) := by norm_num
    _ < M / 2 := forty_one_fiftieths_lt_half_M

theorem terminal_bound_lt_half_M {α : ℝ}
    (hα0 : Real.pi / 4 ≤ α) (hα1 : α ≤ Real.arctan (5 / 4)) :
    (1 + 1 / Real.sin α) ^ 2 / (8 * (Real.cos α / Real.sin α)) < M / 2 :=
  (terminal_bound_le_arctan_five_fourths hα0 hα1).trans_lt
    terminal_exact_bound_lt_half_M

/-- The exact terminal-angle cut applies to every actual downward cap. -/
theorem IsDownwardCap.capScore_lt_half_M_of_low_terminal_angle
    {U : Set Plane} (hU : IsDownwardCap U) {α : ℝ}
    (hα0 : Real.pi / 4 ≤ α) (hα1 : α ≤ Real.arctan (5 / 4)) :
    capScore U α < M / 2 := by
  have hαpos : 0 < α := by linarith [Real.pi_pos]
  have hαL : α < Real.pi / 2 :=
    hα1.trans_lt (Real.arctan_lt_pi_div_two (5 / 4))
  exact (hU.capScore_le_terminal_bound hαpos hαL).trans_lt
    (terminal_bound_lt_half_M hα0 hα1)

theorem IsJointCapMaximizer.terminal_angle_gt_arctan_five_fourths
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α) :
    Real.arctan (5 / 4) < α := by
  by_contra h
  have hscore := hU.isCap.capScore_lt_half_M_of_low_terminal_angle
    hU.angle_mem.1 (le_of_not_gt h)
  exact (not_lt_of_ge hU.reference_le) hscore

end AmbidextrousSofa
