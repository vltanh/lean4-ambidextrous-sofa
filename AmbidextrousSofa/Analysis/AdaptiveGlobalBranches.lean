module

public import AmbidextrousSofa.Analysis.AdaptiveGlobalBoundary
public import AmbidextrousSofa.Analysis.ExactEstimates

@[expose] public section

/-!
# The width boundary and the explicit large-width branch

The disk and the fully active trigonometric family satisfy the actual Euler
equations. Fixed-trace coercivity therefore bounds every unrestricted C1
competitor at their widths. Their values are computed by elementary
integration, and both branches lie strictly below half the reference value.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology

namespace AmbidextrousSofa.Analysis

theorem QuarterPair.sameTraces_of_widthTraces {u v : QuarterPair} {a : ℝ}
    (hu : u.WidthTraces a) (hv : v.WidthTraces a) : u.SameTraces v := by
  rcases hu with ⟨hu0, hug0, huL, hugL⟩
  rcases hv with ⟨hv0, hvg0, hvL, hvgL⟩
  exact ⟨hu0.trans hv0.symm, hug0.trans hvg0.symm,
    huL.trans hvL.symm, hugL.trans hvgL.symm⟩

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

theorem diskPair_widthTraces : diskPair.WidthTraces (1 / 2) := by
  norm_num [QuarterPair.WidthTraces, diskPair]

theorem diskPair_p (t : ℝ) : diskPair.p t = 1 / 2 := by
  unfold QuarterPair.p diskPair
  ring

theorem diskPair_q (t : ℝ) : diskPair.q t = -1 / 2 := by
  unfold QuarterPair.q diskPair
  ring

theorem diskPair_fluxF (t : ℝ) : diskPair.fluxF t = 1 / 4 - 3 / 4 * Real.cos t := by
  norm_num [QuarterPair.fluxF, diskPair_p, diskPair] <;> ring

theorem diskPair_fluxG (t : ℝ) : diskPair.fluxG t = 3 / 4 * Real.sin t - 1 / 4 := by
  norm_num [QuarterPair.fluxG, diskPair_q, diskPair] <;> ring

theorem diskPair_forceF (t : ℝ) : diskPair.forceF t = 3 / 4 * Real.sin t := by
  norm_num [QuarterPair.forceF, diskPair_q, diskPair] <;> ring

theorem diskPair_forceG (t : ℝ) : diskPair.forceG t = 3 / 4 * Real.cos t := by
  norm_num [QuarterPair.forceG, diskPair_p, diskPair] <;> ring

theorem diskPair_eulerF (t : ℝ) :
    HasDerivWithinAt diskPair.fluxF (diskPair.forceF t) (Ioi t) t := by
  have h : HasDerivAt (fun s => 1 / 4 - 3 / 4 * Real.cos s) (diskPair.forceF t) t := by
    apply (((Real.hasDerivAt_cos t).const_mul (3 / 4)).const_sub (1 / 4)).congr_deriv
    rw [diskPair_forceF]
    ring
  exact h.hasDerivWithinAt.congr (fun s _ => diskPair_fluxF s) (diskPair_fluxF t)

theorem diskPair_eulerG (t : ℝ) :
    HasDerivWithinAt diskPair.fluxG (diskPair.forceG t) (Ioi t) t := by
  have h : HasDerivAt (fun s => 3 / 4 * Real.sin s - 1 / 4) (diskPair.forceG t) t := by
    apply (((Real.hasDerivAt_sin t).const_mul (3 / 4)).sub_const (1 / 4)).congr_deriv
    rw [diskPair_forceG]
  exact h.hasDerivWithinAt.congr (fun s _ => diskPair_fluxG s) (diskPair_fluxG t)

theorem diskPair_stationary : diskPair.Stationary :=
  diskPair.stationary_of_euler (fun t _ => diskPair_eulerF t) (fun t _ => diskPair_eulerG t)

theorem adaptiveDensity_diskPair (t : ℝ) :
    adaptiveDensity diskPair t = 1 / 2 + (Real.sin t + Real.cos t) / 8 := by
  unfold adaptiveDensity
  rw [diskPair_p, diskPair_q]
  norm_num [diskPair] <;> ring

theorem adaptiveFunctional_diskPair : adaptiveFunctional diskPair = Real.pi / 4 + 1 / 4 := by
  let P : ℝ → ℝ := fun t => t / 2 + (-Real.cos t + Real.sin t) / 8
  have hL : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hftc : (∫ t in (0 : ℝ)..(Real.pi / 2), adaptiveDensity diskPair t) =
      P (Real.pi / 2) - P 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hL (by dsimp [P]; fun_prop)
    · intro t _
      rw [adaptiveDensity_diskPair]
      apply (((hasDerivAt_id t).div_const 2).add
        (((Real.hasDerivAt_cos t).neg.add (Real.hasDerivAt_sin t)).div_const 8)).congr_deriv
      ring
    · exact ContinuousOn.intervalIntegrable_of_Icc hL (continuousOn_adaptiveDensity diskPair)
  change (∫ t in (0 : ℝ)..(Real.pi / 2), adaptiveDensity diskPair t) = _
  rw [hftc]
  dsimp [P]
  simp only [Real.sin_zero, Real.cos_zero, Real.sin_pi_div_two, Real.cos_pi_div_two]
  ring

/-- The width boundary is strictly suboptimal even among unrestricted C1
profiles with those traces. This is an actual fixed-width comparison. -/
theorem adaptiveFunctional_sub_width_lt_half_M_at_half {u : QuarterPair}
    (hu : u.WidthTraces (1 / 2)) : adaptiveFunctional u - 1 / 2 < M / 2 := by
  have h := adaptiveFunctional_le_of_stationary diskPair_stationary
    (QuarterPair.sameTraces_of_widthTraces hu diskPair_widthTraces)
  rw [adaptiveFunctional_diskPair] at h
  linarith [Real.pi_lt_four, eight_fifths_lt_M]

def tailAngle0 : ℝ := Real.pi / 8

def tailPhase (t : ℝ) : ℝ := t / 2 + tailAngle0

def tailCoefficient (r : ℝ) : ℝ := 1 - r * Real.sin tailAngle0

theorem tailAngle0_pos : 0 < tailAngle0 := by unfold tailAngle0; linarith [Real.pi_pos]

theorem tailAngle0_lt_pi_div_two : tailAngle0 < Real.pi / 2 := by
  unfold tailAngle0
  linarith [Real.pi_pos]

theorem sin_tailAngle0_pos : 0 < Real.sin tailAngle0 :=
  Real.sin_pos_of_pos_of_lt_pi tailAngle0_pos
    (by linarith [tailAngle0_lt_pi_div_two, Real.pi_pos])

theorem cos_tailAngle0_pos : 0 < Real.cos tailAngle0 :=
  Real.cos_pos_of_mem_Ioo
    ⟨by linarith [tailAngle0_pos, Real.pi_pos], tailAngle0_lt_pi_div_two⟩

theorem tailPhase_zero : tailPhase 0 = tailAngle0 := by unfold tailPhase; ring

theorem tailPhase_pi_div_two : tailPhase (Real.pi / 2) = Real.pi / 2 - tailAngle0 := by
  unfold tailPhase tailAngle0
  ring

theorem hasDerivAt_tailPhase (t : ℝ) : HasDerivAt tailPhase (1 / 2) t :=
  ((hasDerivAt_id t).div_const 2).add_const tailAngle0

/-- A division-free rational lower bound for tan(pi/8). -/
theorem two_cos_tailAngle0_lt_five_sin :
    2 * Real.cos tailAngle0 < 5 * Real.sin tailAngle0 := by
  have hangle : tailAngle0 + tailAngle0 = Real.pi / 4 := by unfold tailAngle0; ring
  have hc := Real.cos_add tailAngle0 tailAngle0
  have hs := Real.sin_add tailAngle0 tailAngle0
  rw [hangle, Real.cos_pi_div_four] at hc
  rw [hangle, Real.sin_pi_div_four] at hs
  by_contra h
  have hle : 5 * Real.sin tailAngle0 ≤ 2 * Real.cos tailAngle0 := le_of_not_gt h
  have hprod := mul_nonneg (sub_nonneg.mpr hle)
    (add_nonneg (mul_nonneg (by norm_num) cos_tailAngle0_pos.le)
      (mul_nonneg (by norm_num) sin_tailAngle0_pos.le))
  have hcross := mul_nonneg (sub_nonneg.mpr hle) cos_tailAngle0_pos.le
  nlinarith [mul_self_pos.mpr (ne_of_gt cos_tailAngle0_pos)]

def tailPair (r : ℝ) : QuarterPair where
  f := fun t => r * Real.cos (tailPhase t) + tailCoefficient r * Real.sin t
  g := fun t => r * Real.sin (tailPhase t) + tailCoefficient r * Real.cos t
  fD := fun t => -(r / 2) * Real.sin (tailPhase t) + tailCoefficient r * Real.cos t
  gD := fun t => r / 2 * Real.cos (tailPhase t) - tailCoefficient r * Real.sin t
  continuous_f := by unfold tailPhase; fun_prop
  continuous_g := by unfold tailPhase; fun_prop
  continuous_fD := by unfold tailPhase; fun_prop
  continuous_gD := by unfold tailPhase; fun_prop
  hasDeriv_f := by
    intro t _
    apply ((((hasDerivAt_tailPhase t).cos).const_mul r).add
      ((Real.hasDerivAt_sin t).const_mul (tailCoefficient r))).hasDerivWithinAt.congr_deriv
    ring
  hasDeriv_g := by
    intro t _
    apply ((((hasDerivAt_tailPhase t).sin).const_mul r).add
      ((Real.hasDerivAt_cos t).const_mul (tailCoefficient r))).hasDerivWithinAt.congr_deriv
    ring

theorem tailPair_widthTraces (r : ℝ) :
    (tailPair r).WidthTraces (r * Real.cos tailAngle0) := by
  simp only [QuarterPair.WidthTraces, tailPair, tailPhase_zero, tailPhase_pi_div_two,
    Real.sin_zero, Real.cos_zero, Real.sin_pi_div_two, Real.cos_pi_div_two,
    Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub, tailCoefficient]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

theorem tailPair_p (r t : ℝ) : (tailPair r).p t = 1 - 3 / 2 * r * Real.sin (tailPhase t) := by
  unfold QuarterPair.p tailPair
  ring

theorem tailPair_q (r t : ℝ) : (tailPair r).q t = 3 / 2 * r * Real.cos (tailPhase t) - 1 := by
  unfold QuarterPair.q tailPair
  ring

theorem tailPair_momentum_signs {r t : ℝ} (hr : 2 / 3 ≤ r * Real.sin tailAngle0)
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    (tailPair r).p t ≤ 0 ∧ 0 ≤ (tailPair r).q t := by
  have hrpos : 0 < r := pos_of_mul_pos_left
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2 / 3) hr) sin_tailAngle0_pos.le
  have hs : Real.sin tailAngle0 ≤ Real.sin (tailPhase t) := by
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · linarith [tailAngle0_pos, Real.pi_pos]
    · unfold tailPhase tailAngle0
      linarith [ht.2, Real.pi_pos]
    · unfold tailPhase
      linarith [ht.1]
  have hc : Real.sin tailAngle0 ≤ Real.cos (tailPhase t) := by
    rw [← Real.sin_pi_div_two_sub]
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · linarith [tailAngle0_pos, Real.pi_pos]
    · unfold tailPhase tailAngle0
      linarith [ht.1, Real.pi_pos]
    · unfold tailPhase tailAngle0
      linarith [ht.2]
  have hps := mul_le_mul_of_nonneg_left hs hrpos.le
  have hqs := mul_le_mul_of_nonneg_left hc hrpos.le
  rw [tailPair_p, tailPair_q]
  constructor <;> nlinarith

theorem tailPair_fluxF {r t : ℝ} (hr : 2 / 3 ≤ r * Real.sin tailAngle0)
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    (tailPair r).fluxF t = 3 / 2 * r * Real.sin (tailPhase t) -
      3 / 2 * tailCoefficient r * Real.cos t - 1 / 2 := by
  unfold QuarterPair.fluxF
  rw [min_eq_left (tailPair_momentum_signs hr ht).1, tailPair_p]
  unfold tailPair
  ring

theorem tailPair_fluxG {r t : ℝ} (hr : 2 / 3 ≤ r * Real.sin tailAngle0)
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    (tailPair r).fluxG t = -(3 / 2) * r * Real.cos (tailPhase t) +
      3 / 2 * tailCoefficient r * Real.sin t + 1 / 2 := by
  unfold QuarterPair.fluxG
  rw [max_eq_left (tailPair_momentum_signs hr ht).2, tailPair_q]
  unfold tailPair
  ring

theorem tailPair_forceF {r t : ℝ} (hr : 2 / 3 ≤ r * Real.sin tailAngle0)
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    (tailPair r).forceF t = 3 / 4 * r * Real.cos (tailPhase t) +
      3 / 2 * tailCoefficient r * Real.sin t := by
  unfold QuarterPair.forceF
  rw [max_eq_left (tailPair_momentum_signs hr ht).2, tailPair_q]
  unfold tailPair
  ring

theorem tailPair_forceG {r t : ℝ} (hr : 2 / 3 ≤ r * Real.sin tailAngle0)
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    (tailPair r).forceG t = 3 / 4 * r * Real.sin (tailPhase t) +
      3 / 2 * tailCoefficient r * Real.cos t := by
  unfold QuarterPair.forceG
  rw [min_eq_left (tailPair_momentum_signs hr ht).1, tailPair_p]
  unfold tailPair
  ring

theorem tailPair_eulerF {r t : ℝ} (hr : 2 / 3 ≤ r * Real.sin tailAngle0)
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivWithinAt (tailPair r).fluxF ((tailPair r).forceF t) (Ioi t) t := by
  have h := (((((hasDerivAt_tailPhase t).sin).const_mul (3 / 2 * r)).sub
    ((Real.hasDerivAt_cos t).const_mul (3 / 2 * tailCoefficient r))).sub_const (1 / 2))
  have hd : 3 / 2 * r * (Real.cos (tailPhase t) * (1 / 2)) -
      3 / 2 * tailCoefficient r * -Real.sin t = (tailPair r).forceF t := by
    rw [tailPair_forceF hr ⟨ht.1.le, ht.2.le⟩]
    ring
  apply (h.congr_deriv hd).hasDerivWithinAt.congr_of_eventuallyEq
  · filter_upwards [(Ioo_mem_nhds ht.1 ht.2).filter_mono nhdsWithin_le_nhds] with s hs
    exact tailPair_fluxF hr ⟨hs.1.le, hs.2.le⟩
  · exact tailPair_fluxF hr ⟨ht.1.le, ht.2.le⟩

theorem tailPair_eulerG {r t : ℝ} (hr : 2 / 3 ≤ r * Real.sin tailAngle0)
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivWithinAt (tailPair r).fluxG ((tailPair r).forceG t) (Ioi t) t := by
  have h := (((((hasDerivAt_tailPhase t).cos).const_mul (-(3 / 2) * r)).add
    ((Real.hasDerivAt_sin t).const_mul (3 / 2 * tailCoefficient r))).add_const (1 / 2))
  have hd : -(3 / 2) * r * (-Real.sin (tailPhase t) * (1 / 2)) +
      3 / 2 * tailCoefficient r * Real.cos t = (tailPair r).forceG t := by
    rw [tailPair_forceG hr ⟨ht.1.le, ht.2.le⟩]
    ring
  apply (h.congr_deriv hd).hasDerivWithinAt.congr_of_eventuallyEq
  · filter_upwards [(Ioo_mem_nhds ht.1 ht.2).filter_mono nhdsWithin_le_nhds] with s hs
    exact tailPair_fluxG hr ⟨hs.1.le, hs.2.le⟩
  · exact tailPair_fluxG hr ⟨ht.1.le, ht.2.le⟩

theorem tailPair_stationary {r : ℝ} (hr : 2 / 3 ≤ r * Real.sin tailAngle0) :
    (tailPair r).Stationary :=
  (tailPair r).stationary_of_euler (fun _ ht => tailPair_eulerF hr ht)
    (fun _ ht => tailPair_eulerG hr ht)

theorem twice_density_sub_self_of_active (u : QuarterPair) (t : ℝ)
    (hp : u.p t ≤ 0) (hq : 0 ≤ u.q t) :
    2 * adaptiveDensity u t - adaptiveLinearDensity u u t = (u.gD t - u.fD t) / 2 := by
  unfold adaptiveDensity adaptiveLinearDensity
  rw [min_eq_left hp, max_eq_left hq]
  unfold QuarterPair.p QuarterPair.q
  ring

theorem tailPair_self_variation {r : ℝ} (hr : 2 / 3 ≤ r * Real.sin tailAngle0) :
    adaptiveFirstVariation (tailPair r) (tailPair r) =
      7 * r * Real.cos tailAngle0 - 1 -
        6 * r ^ 2 * Real.sin tailAngle0 * Real.cos tailAngle0 := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hL : Real.pi / 2 ∈ Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], le_rfl⟩
  rw [adaptiveFirstVariation_eq_boundary (tailPair r) (tailPair r)
    (fun _ ht => tailPair_eulerF hr ht) (fun _ ht => tailPair_eulerG hr ht),
    tailPair_fluxF hr hL, tailPair_fluxG hr hL, tailPair_fluxF hr h0, tailPair_fluxG hr h0]
  simp only [tailPair, tailPhase_zero, tailPhase_pi_div_two, tailCoefficient,
    Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub, Real.sin_zero, Real.cos_zero,
    Real.sin_pi_div_two, Real.cos_pi_div_two]
  ring

/-- The exact value of the actual stationary large-width family. -/
theorem adaptiveFunctional_tailPair {r : ℝ} (hr : 2 / 3 ≤ r * Real.sin tailAngle0) :
    adaptiveFunctional (tailPair r) = 4 * r * Real.cos tailAngle0 - 1 -
      3 * r ^ 2 * Real.sin tailAngle0 * Real.cos tailAngle0 := by
  let u := tailPair r
  have hL : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hd := ContinuousOn.intervalIntegrable_of_Icc hL (continuousOn_adaptiveDensity u)
  have hv := ContinuousOn.intervalIntegrable_of_Icc hL (continuousOn_adaptiveLinearDensity u u)
  have hftc : (∫ t in (0 : ℝ)..(Real.pi / 2), (u.gD t - u.fD t) / 2) =
      r * Real.cos tailAngle0 - 1 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hL
      ((u.continuous_g.sub u.continuous_f).div_const 2)
      (fun t ht => ((u.hasDeriv_g t ht).sub (u.hasDeriv_f t ht)).div_const 2)
      (ContinuousOn.intervalIntegrable_of_Icc hL
        ((u.continuous_gD.sub u.continuous_fD).div_const 2))
    rcases tailPair_widthTraces r with ⟨hf0, hg0, hfL, hgL⟩
    change _ = ((tailPair r).g (Real.pi / 2) - (tailPair r).f (Real.pi / 2)) / 2 -
      ((tailPair r).g 0 - (tailPair r).f 0) / 2 at h
    rw [hf0, hg0, hfL, hgL] at h
    dsimp [u]
    linarith
  have hsplit : 2 * adaptiveFunctional u - adaptiveFirstVariation u u =
      r * Real.cos tailAngle0 - 1 := by
    unfold adaptiveFunctional adaptiveFirstVariation
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (hd.const_mul 2) hv]
    calc
      _ = ∫ t in (0 : ℝ)..(Real.pi / 2), (u.gD t - u.fD t) / 2 := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hL] at ht
        exact twice_density_sub_self_of_active u t
          (tailPair_momentum_signs hr ht).1 (tailPair_momentum_signs hr ht).2
      _ = _ := hftc
  have hself := tailPair_self_variation hr
  dsimp [u] at hsplit
  nlinarith

theorem tailPair_score_lt_two_thirds {r : ℝ} (hr : 2 / 3 ≤ r * Real.sin tailAngle0) :
    adaptiveFunctional (tailPair r) - r * Real.cos tailAngle0 < 2 / 3 := by
  have hpar : r * Real.sin tailAngle0 - (r * Real.sin tailAngle0) ^ 2 ≤ 2 / 9 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hr)
      (show 0 ≤ r * Real.sin tailAngle0 - 1 / 3 by linarith)
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hpar
    (mul_nonneg (by norm_num) cos_tailAngle0_pos.le)
  rw [adaptiveFunctional_tailPair hr]
  apply (mul_lt_mul_iff_left₀ sin_tailAngle0_pos).mp
  nlinarith [two_cos_tailAngle0_lt_five_sin]

/-- A whole large-width branch is excluded by its explicit stationary
optimizer, without assuming an optimizer exists at other widths. -/
theorem adaptiveFunctional_sub_width_lt_half_M_of_tail
    {u : QuarterPair} {r : ℝ} (hr : 2 / 3 ≤ r * Real.sin tailAngle0)
    (hu : u.WidthTraces (r * Real.cos tailAngle0)) :
    adaptiveFunctional u - r * Real.cos tailAngle0 < M / 2 := by
  have h := adaptiveFunctional_le_of_stationary (tailPair_stationary hr)
    (QuarterPair.sameTraces_of_widthTraces hu (tailPair_widthTraces r))
  linarith [tailPair_score_lt_two_thirds hr, eight_fifths_lt_M]

/-- Half-width at least two lies wholly in the explicit, strictly
suboptimal tail. Thus only a compact interval of widths can compete. -/
theorem adaptiveFunctional_sub_width_lt_half_M_of_two_le
    {u : QuarterPair} {a : ℝ} (hu : u.WidthTraces a) (ha : 2 ≤ a) :
    adaptiveFunctional u - a < M / 2 := by
  let r := a / Real.cos tailAngle0
  have hrpos : 0 < r := div_pos (by linarith) cos_tailAngle0_pos
  have hrc : r * Real.cos tailAngle0 = a :=
    div_mul_cancel₀ a (ne_of_gt cos_tailAngle0_pos)
  have hmul := mul_lt_mul_of_pos_left two_cos_tailAngle0_lt_five_sin hrpos
  have hr : 2 / 3 ≤ r * Real.sin tailAngle0 := by nlinarith [hrc]
  have htrace : u.WidthTraces (r * Real.cos tailAngle0) := by rwa [hrc]
  have h := adaptiveFunctional_sub_width_lt_half_M_of_tail hr htrace
  rwa [hrc] at h

end AmbidextrousSofa.Analysis
