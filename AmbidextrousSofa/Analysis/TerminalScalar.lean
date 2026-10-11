module

public import AmbidextrousSofa.Analysis.ExactEstimates
public import AmbidextrousSofa.Analysis.TerminalWallBound
public import AmbidextrousSofa.Analysis.JointCapMaximum

@[expose] public section

/-!
# Exact exclusion of low terminal angles

The actual outgoing-wall estimate reduces the cap score to a function
of sine and cosine. On `π/4 ≤ α ≤ arctan (5/4)`, its cotangent lies in
`[4/5,1]`. A squared inequality and a factored quadratic give the exact
upper bound `(33 + 5 * sqrt 41) / 80`; no derivative estimate or numerical
search is used.

A rational cut below the actual defining cubic root gives `41/50 < M/2`.
Consequently every actual joint cap maximizer has terminal angle strictly
above `arctan (5/4)`.
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
  have hr2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 41)
  have hroot : 4 * s ≤ a * Real.sqrt 41 := by
    refine (sq_le_sq₀ (by positivity) (by positivity)).mp ?_
    rw [mul_pow, mul_pow, hs2, hr2]
    nlinarith
  rw [div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg (show 0 ≤ 5 * a - 4 by linarith) (show 0 ≤ 5 - 2 * a by linarith)]

/-- The exact bound on the terminal-wall estimate for `π/4 ≤ α ≤ arctan (5/4)`, from the sine and
cosine of `α`. -/
theorem terminal_bound_le_arctan_five_fourths {α : ℝ}
    (hα0 : Real.pi / 4 ≤ α) (hα1 : α ≤ Real.arctan (5 / 4)) :
    (1 + 1 / Real.sin α) ^ 2 / (8 * (Real.cos α / Real.sin α)) ≤
      (33 + 5 * Real.sqrt 41) / 80 := by
  have hαL : α < Real.pi / 2 := hα1.trans_lt (Real.arctan_lt_pi_div_two (5 / 4))
  have hαmem : α ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith [Real.pi_pos], hαL⟩
  obtain ⟨hs, hc⟩ := sin_cos_pos_of_mem_quarter ⟨by linarith [Real.pi_pos], hαL⟩
  have htan0 : 1 ≤ Real.tan α := by
    simpa only [Real.tan_pi_div_four] using Real.strictMonoOn_tan.monotoneOn
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ hαmem hα0
  have htan1 : Real.tan α ≤ 5 / 4 := by
    simpa only [Real.tan_arctan] using
      Real.strictMonoOn_tan.monotoneOn hαmem (Real.arctan_mem_Ioo (5 / 4)) hα1
  rw [Real.tan_eq_sin_div_cos, le_div_iff₀ hc] at htan0
  rw [Real.tan_eq_sin_div_cos, div_le_iff₀ hc] at htan1
  refine terminal_cotangent_scalar_bound ((le_div_iff₀ hs).2 (by linarith))
    ((div_le_iff₀ hs).2 (by linarith)) (by positivity) ?_
  field_simp
  linarith [Real.sin_sq_add_cos_sq α]

theorem terminal_exact_bound_lt_rational :
    (33 + 5 * Real.sqrt 41) / 80 < (1301 / 1600 : ℝ) := by
  have hs : Real.sqrt (41 : ℝ) < 641 / 100 :=
    (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
  linarith

/-- The exact terminal-angle cut applies to every actual downward cap, so
the reference score excludes the low terminal angles. -/
theorem IsJointCapMaximizer.terminal_angle_gt_arctan_five_fourths
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α) :
    Real.arctan (5 / 4) < α := by
  by_contra! h
  linarith [hU.reference_le, terminal_exact_bound_lt_rational, forty_one_fiftieths_lt_half_M,
    hU.isCap.capScore_le_terminal_bound hU.angle_pos (h.trans_lt (Real.arctan_lt_pi_div_two _)),
    terminal_bound_le_arctan_five_fourths hU.angle_mem.1 h]

end AmbidextrousSofa
