module

public import AmbidextrousSofa.Analysis.AdaptiveGlobalBoundary
public import AmbidextrousSofa.Analysis.ExactEstimates

@[expose] public section

/-!
# The width boundary and the explicit large-width branch

The fully active trigonometric family satisfies the actual Euler equations.
Fixed-trace coercivity therefore bounds every unrestricted C1 competitor at
its widths. Its value is computed by elementary integration, and the branch
lies strictly below half the reference value. The disk pair at the width
boundary is also defined here.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa.Analysis

theorem QuarterPair.sameTraces_of_widthTraces {u v : QuarterPair} {a : ℝ}
    (hu : u.WidthTraces a) (hv : v.WidthTraces a) : u.SameTraces v :=
  ⟨hu.1.trans hv.1.symm, hu.2.1.trans hv.2.1.symm, hu.2.2.1.trans hv.2.2.1.symm,
    hu.2.2.2.trans hv.2.2.2.symm⟩

def diskPair : QuarterPair where
  f := fun t => 1 / 2 + Real.sin t / 2
  g := fun t => 1 / 2 + Real.cos t / 2
  fD := fun t => Real.cos t / 2
  gD := fun t => -Real.sin t / 2
  continuous_f := by fun_prop
  continuous_g := by fun_prop
  continuous_fD := by fun_prop
  continuous_gD := by fun_prop
  hasDeriv_f := fun t _ => (((Real.hasDerivAt_sin t).div_const 2).const_add (1 / 2)).hasDerivWithinAt
  hasDeriv_g := fun t _ => (((Real.hasDerivAt_cos t).div_const 2).const_add (1 / 2)).hasDerivWithinAt

def tailAngle0 : ℝ := Real.pi / 8

def tailPhase (t : ℝ) : ℝ := t / 2 + tailAngle0

def tailCoefficient (r : ℝ) : ℝ := 1 - r * Real.sin tailAngle0

theorem sin_tailAngle0_pos : 0 < Real.sin tailAngle0 := by
  unfold tailAngle0
  exact Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])

theorem cos_tailAngle0_pos : 0 < Real.cos tailAngle0 := by
  unfold tailAngle0
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

theorem tailPhase_zero : tailPhase 0 = tailAngle0 := by simp [tailPhase]

theorem tailPhase_pi_div_two : tailPhase (Real.pi / 2) = Real.pi / 2 - tailAngle0 := by
  unfold tailPhase tailAngle0; ring

theorem hasDerivAt_tailPhase (t : ℝ) : HasDerivAt tailPhase (1 / 2) t :=
  ((hasDerivAt_id t).div_const 2).add_const tailAngle0

/-- A division-free rational lower bound for tan(pi/8). -/
theorem two_cos_tailAngle0_lt_five_sin :
    2 * Real.cos tailAngle0 < 5 * Real.sin tailAngle0 := by
  have hangle : tailAngle0 + tailAngle0 = Real.pi / 4 := by unfold tailAngle0; ring
  have hc := Real.cos_add tailAngle0 tailAngle0
  have hs := Real.sin_add tailAngle0 tailAngle0
  simp only [hangle, Real.cos_pi_div_four, Real.sin_pi_div_four] at hc hs
  nlinarith [sin_tailAngle0_pos, cos_tailAngle0_pos]

def tailPair (r : ℝ) : QuarterPair where
  f t := r * Real.cos (tailPhase t) + tailCoefficient r * Real.sin t
  g t := r * Real.sin (tailPhase t) + tailCoefficient r * Real.cos t
  fD t := -(r / 2) * Real.sin (tailPhase t) + tailCoefficient r * Real.cos t
  gD t := r / 2 * Real.cos (tailPhase t) - tailCoefficient r * Real.sin t
  continuous_f := by unfold tailPhase; fun_prop
  continuous_g := by unfold tailPhase; fun_prop
  continuous_fD := by unfold tailPhase; fun_prop
  continuous_gD := by unfold tailPhase; fun_prop
  hasDeriv_f t _ := ((((hasDerivAt_tailPhase t).cos).const_mul r).add
    ((Real.hasDerivAt_sin t).const_mul _)).hasDerivWithinAt.congr_deriv (by ring)
  hasDeriv_g t _ := ((((hasDerivAt_tailPhase t).sin).const_mul r).add
    ((Real.hasDerivAt_cos t).const_mul _)).hasDerivWithinAt.congr_deriv (by ring)

theorem tailPair_widthTraces (r : ℝ) :
    (tailPair r).WidthTraces (r * Real.cos tailAngle0) := by
  simp only [QuarterPair.WidthTraces, tailPair, tailPhase_zero, tailPhase_pi_div_two,
    Real.sin_zero, Real.cos_zero, Real.sin_pi_div_two, Real.cos_pi_div_two,
    Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub, tailCoefficient]
  refine ⟨by ring, by ring, by ring, by ring⟩

theorem tailPair_momentum_signs {r t : ℝ} (hr : 2 / 3 ≤ r * Real.sin tailAngle0)
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    (tailPair r).p t ≤ 0 ∧ 0 ≤ (tailPair r).q t := by
  have hr0 : 0 ≤ r := (pos_of_mul_pos_left (by linarith) sin_tailAngle0_pos.le).le
  have h : Real.sin tailAngle0 ≤ Real.sin (tailPhase t) ∧
      Real.sin tailAngle0 ≤ Real.cos (tailPhase t) := by
    rw [← Real.sin_pi_div_two_sub (tailPhase t)]
    constructor <;> apply Real.sin_le_sin_of_le_of_le_pi_div_two <;>
      simp only [tailPhase, tailAngle0] <;> linarith [ht.1, ht.2, Real.pi_pos]
  simp only [QuarterPair.p, QuarterPair.q, tailPair]
  constructor <;> linarith [mul_le_mul_of_nonneg_left h.1 hr0, mul_le_mul_of_nonneg_left h.2 hr0]

theorem tailPair_fluxF {r t : ℝ} (hr : 2 / 3 ≤ r * Real.sin tailAngle0)
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    (tailPair r).fluxF t = 3 / 2 * r * Real.sin (tailPhase t) -
      3 / 2 * tailCoefficient r * Real.cos t - 1 / 2 := by
  rw [QuarterPair.fluxF, min_eq_left (tailPair_momentum_signs hr ht).1]
  simp only [QuarterPair.p, tailPair]; ring

theorem tailPair_fluxG {r t : ℝ} (hr : 2 / 3 ≤ r * Real.sin tailAngle0)
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    (tailPair r).fluxG t = -(3 / 2) * r * Real.cos (tailPhase t) +
      3 / 2 * tailCoefficient r * Real.sin t + 1 / 2 := by
  rw [QuarterPair.fluxG, max_eq_left (tailPair_momentum_signs hr ht).2]
  simp only [QuarterPair.q, tailPair]; ring

theorem tailPair_eulerF {r t : ℝ} (hr : 2 / 3 ≤ r * Real.sin tailAngle0)
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivWithinAt (tailPair r).fluxF ((tailPair r).forceF t) (Ioi t) t := by
  have h := (((hasDerivAt_tailPhase t).sin.const_mul (3 / 2 * r)).sub
    ((Real.hasDerivAt_cos t).const_mul (3 / 2 * tailCoefficient r))).sub_const (1 / 2)
  refine ((h.congr_of_eventuallyEq <| Filter.eventuallyEq_of_mem (Ioo_mem_nhds ht.1 ht.2)
    fun s hs => tailPair_fluxF hr (Ioo_subset_Icc_self hs)).congr_deriv ?_).hasDerivWithinAt
  rw [QuarterPair.forceF, max_eq_left (tailPair_momentum_signs hr (Ioo_subset_Icc_self ht)).2]
  simp only [QuarterPair.q, tailPair]; ring

theorem tailPair_eulerG {r t : ℝ} (hr : 2 / 3 ≤ r * Real.sin tailAngle0)
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivWithinAt (tailPair r).fluxG ((tailPair r).forceG t) (Ioi t) t := by
  have h := (((hasDerivAt_tailPhase t).cos.const_mul (-(3 / 2) * r)).add
    ((Real.hasDerivAt_sin t).const_mul (3 / 2 * tailCoefficient r))).add_const (1 / 2)
  refine ((h.congr_of_eventuallyEq <| Filter.eventuallyEq_of_mem (Ioo_mem_nhds ht.1 ht.2)
    fun s hs => tailPair_fluxG hr (Ioo_subset_Icc_self hs)).congr_deriv ?_).hasDerivWithinAt
  rw [QuarterPair.forceG, min_eq_left (tailPair_momentum_signs hr (Ioo_subset_Icc_self ht)).1]
  simp only [QuarterPair.p, tailPair]; ring

/-- With both contacts active, twice the functional minus the self-variation
integrates to a boundary term. -/
theorem two_mul_adaptiveFunctional_sub_of_active {u : QuarterPair}
    (h : ∀ t ∈ Icc (0 : ℝ) (Real.pi / 2), u.p t ≤ 0 ∧ 0 ≤ u.q t) :
    2 * adaptiveFunctional u - adaptiveFirstVariation u u =
      (u.g (Real.pi / 2) - u.f (Real.pi / 2)) / 2 - (u.g 0 - u.f 0) / 2 := by
  have hL : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  rw [← intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
      (f := fun t => (u.g t - u.f t) / 2) hL ((u.continuous_g.sub u.continuous_f).div_const 2)
      (fun t ht => ((u.hasDeriv_g t ht).sub (u.hasDeriv_f t ht)).div_const 2)
      (((u.continuous_gD.sub u.continuous_fD).div_const 2).intervalIntegrable_of_Icc hL),
    adaptiveFunctional, adaptiveFirstVariation, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub
      (((continuousOn_adaptiveDensity u).intervalIntegrable_of_Icc hL).const_mul 2)
      ((continuousOn_adaptiveLinearDensity u u).intervalIntegrable_of_Icc hL)]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hL] at ht
  simp only [adaptiveDensity, adaptiveLinearDensity, min_eq_left (h t ht).1,
    max_eq_left (h t ht).2]
  unfold QuarterPair.p QuarterPair.q; ring

/-- The exact value of the actual stationary large-width family. -/
theorem adaptiveFunctional_tailPair {r : ℝ} (hr : 2 / 3 ≤ r * Real.sin tailAngle0) :
    adaptiveFunctional (tailPair r) = 4 * r * Real.cos tailAngle0 - 1 -
      3 * r ^ 2 * Real.sin tailAngle0 * Real.cos tailAngle0 := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (Real.pi / 2) := ⟨le_rfl, by positivity⟩
  have hL : Real.pi / 2 ∈ Icc (0 : ℝ) (Real.pi / 2) := ⟨by positivity, le_rfl⟩
  have h := two_mul_adaptiveFunctional_sub_of_active fun _ => tailPair_momentum_signs hr
  obtain ⟨hf0, hg0, hfL, hgL⟩ := tailPair_widthTraces r
  rw [adaptiveFirstVariation_eq_boundary _ _ (fun _ => tailPair_eulerF hr)
    (fun _ => tailPair_eulerG hr), tailPair_fluxF hr hL, tailPair_fluxG hr hL,
    tailPair_fluxF hr h0, tailPair_fluxG hr h0, hf0, hg0, hfL, hgL] at h
  simp only [tailPhase_zero, tailPhase_pi_div_two, tailCoefficient, Real.sin_pi_div_two_sub,
    Real.cos_pi_div_two_sub, Real.sin_zero, Real.cos_zero, Real.sin_pi_div_two,
    Real.cos_pi_div_two] at h
  linear_combination h / 2

/-- A whole large-width branch is excluded by its explicit stationary
optimizer, without assuming an optimizer exists at other widths. -/
theorem adaptiveFunctional_sub_width_lt_half_M_of_tail
    {u : QuarterPair} {r : ℝ} (hr : 2 / 3 ≤ r * Real.sin tailAngle0)
    (hu : u.WidthTraces (r * Real.cos tailAngle0)) :
    adaptiveFunctional u - r * Real.cos tailAngle0 < M / 2 := by
  have h := adaptiveFunctional_le_of_stationary
    ((tailPair r).stationary_of_euler (fun _ => tailPair_eulerF hr) (fun _ => tailPair_eulerG hr))
    (QuarterPair.sameTraces_of_widthTraces hu (tailPair_widthTraces r))
  have hx : r * Real.sin tailAngle0 - (r * Real.sin tailAngle0) ^ 2 ≤ 2 / 9 := by nlinarith
  have hscore : 3 * r * Real.cos tailAngle0 - 1 -
      3 * r ^ 2 * Real.sin tailAngle0 * Real.cos tailAngle0 < 2 / 3 := by
    nlinarith [sin_tailAngle0_pos, mul_le_mul_of_nonneg_left hx cos_tailAngle0_pos.le,
      two_cos_tailAngle0_lt_five_sin]
  linarith [adaptiveFunctional_tailPair hr, eight_fifths_lt_M]

end AmbidextrousSofa.Analysis
