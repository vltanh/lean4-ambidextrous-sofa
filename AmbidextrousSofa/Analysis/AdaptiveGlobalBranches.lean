module

public import AmbidextrousSofa.Analysis.AdaptiveGlobalBoundary
public import AmbidextrousSofa.Analysis.ExactEstimates

@[expose] public section

/-!
# The fully active phase and the explicit large-width branch

Where both contacts are active, the value density is the derivative of the
half difference of the two supports. A symmetric pair whose first support is
`R cos (t / 2 + π / 8) + S sin t` on `[c, π/2 - c]` has both contacts active
there once `2/3 ≤ R sin (c / 2 + π / 8)`, and its first flux is an explicit
trigonometric polynomial whose derivative is the force.

The pairs of this form on the whole quarter make up the large-width branch.
They satisfy the Euler equations, so fixed-trace coercivity bounds every
unrestricted C1 competitor at their widths. Their value is computed by
elementary integration, and the branch lies strictly below half the
reference value.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa.Analysis

/-- With both contacts active, the value density is the derivative of `(g - f) / 2`. -/
theorem integral_remainder_of_active {u : QuarterPair} {a c : ℝ} (ha : 0 ≤ a) (hac : a ≤ c)
    (hc : c ≤ Real.pi / 2) (h : ∀ t ∈ Icc a c, u.p t ≤ 0 ∧ 0 ≤ u.q t) :
    ∫ t in a..c, 2 * adaptiveDensity u t - adaptiveLinearDensity u u t =
      (u.g c - u.f c) / 2 - (u.g a - u.f a) / 2 := by
  have hsub : Icc a c ⊆ Icc 0 (Real.pi / 2) := Icc_subset_Icc ha hc
  rw [intervalIntegral.integral_congr (g := fun t => (u.gD t - u.fD t) / 2) fun t ht => by
    rw [uIcc_of_le hac] at ht
    simp only [adaptiveDensity, adaptiveLinearDensity, min_eq_left (h t ht).1,
      max_eq_left (h t ht).2]
    unfold QuarterPair.p QuarterPair.q; ring]
  have hi {t : ℝ} (ht : t ∈ Ioo a c) : t ∈ Ioo 0 (Real.pi / 2) :=
    ⟨ha.trans_lt ht.1, ht.2.trans_le hc⟩
  exact intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hac
    (((u.continuous_g.mono hsub).sub (u.continuous_f.mono hsub)).div_const 2)
    (fun t ht => ((u.hasDeriv_g t (hi ht)).sub (u.hasDeriv_f t (hi ht))).div_const 2)
    ((((u.continuous_gD.sub u.continuous_fD).div_const 2).mono hsub).intervalIntegrable_of_Icc hac)

def tailAngle0 : ℝ := Real.pi / 8

def tailPhase (t : ℝ) : ℝ := t / 2 + tailAngle0

theorem sin_tailAngle0_pos : 0 < Real.sin tailAngle0 := by
  unfold tailAngle0
  exact Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])

theorem cos_tailAngle0_pos : 0 < Real.cos tailAngle0 := by
  unfold tailAngle0
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

theorem tailPhase_zero : tailPhase 0 = tailAngle0 := by simp [tailPhase]

theorem tailPhase_pi_div_two : tailPhase (Real.pi / 2) = Real.pi / 2 - tailAngle0 := by
  unfold tailPhase tailAngle0; ring

theorem tailPhase_reflection (t : ℝ) :
    tailPhase (Real.pi / 2 - t) = Real.pi / 2 - tailPhase t := by
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

/-- The first support of a fully active phase with radius `R`. -/
def activeF (R S t : ℝ) : ℝ := R * Real.cos (tailPhase t) + S * Real.sin t

def activeFD (R S t : ℝ) : ℝ := -(R / 2) * Real.sin (tailPhase t) + S * Real.cos t

/-- The first flux of a fully active phase, and its derivative, the force. -/
def activeFlux (R S t : ℝ) : ℝ :=
  3 / 2 * R * Real.sin (tailPhase t) - 3 / 2 * S * Real.cos t - 1 / 2

def activeForce (R S t : ℝ) : ℝ := 3 / 4 * R * Real.cos (tailPhase t) + 3 / 2 * S * Real.sin t

theorem hasDerivAt_activeF (R S t : ℝ) : HasDerivAt (activeF R S) (activeFD R S t) t :=
  (((hasDerivAt_tailPhase t).cos.const_mul R).add ((Real.hasDerivAt_sin t).const_mul S)).congr_deriv
    (by unfold activeFD; ring)

theorem continuous_activeFD (R S : ℝ) : Continuous (activeFD R S) := by
  unfold activeFD tailPhase; fun_prop

theorem hasDerivAt_activeFlux (R S t : ℝ) : HasDerivAt (activeFlux R S) (activeForce R S t) t :=
  ((((hasDerivAt_tailPhase t).sin.const_mul _).sub ((Real.hasDerivAt_cos t).const_mul _)).sub_const
    _).congr_deriv (by unfold activeForce; ring)

/-- A symmetric pair given by a fully active phase on `[c, π/2 - c]` has both contacts active
there, and its first flux and force are those of the phase. -/
theorem symmetricPair_active {F FD : ℝ → ℝ} {hF : ∀ t, HasDerivAt F (FD t) t}
    {hFD : Continuous FD} {R S c s : ℝ} (hc : 0 ≤ c) (hR : 2 / 3 ≤ R * Real.sin (tailPhase c))
    (hFc : ∀ t ∈ Icc c (Real.pi / 2 - c), F t = activeF R S t ∧ FD t = activeFD R S t)
    (hs : s ∈ Icc c (Real.pi / 2 - c)) :
    ((symmetricPair F FD hF hFD).p s ≤ 0 ∧ 0 ≤ (symmetricPair F FD hF hFD).q s) ∧
      (symmetricPair F FD hF hFD).fluxF s = activeFlux R S s ∧
      (symmetricPair F FD hF hFD).forceF s = activeForce R S s := by
  obtain ⟨h1, h2⟩ := hFc s hs
  obtain ⟨h3, h4⟩ := hFc (Real.pi / 2 - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hsin : Real.sin (tailPhase c) ≤ Real.sin (tailPhase s) ∧
      Real.sin (tailPhase c) ≤ Real.cos (tailPhase s) := by
    rw [← Real.sin_pi_div_two_sub (tailPhase s)]
    constructor <;> apply Real.sin_le_sin_of_le_of_le_pi_div_two <;>
      simp only [tailPhase, tailAngle0] <;> linarith [hs.1, hs.2, Real.pi_pos]
  have hR0 : 0 ≤ R := (pos_of_mul_pos_left (by linarith) (Real.sin_nonneg_of_nonneg_of_le_pi
    (x := tailPhase c) (by unfold tailPhase tailAngle0; positivity)
    (by unfold tailPhase tailAngle0; linarith [hs.1, hs.2, Real.pi_pos]))).le
  have hsign : (symmetricPair F FD hF hFD).p s ≤ 0 ∧ 0 ≤ (symmetricPair F FD hF hFD).q s := by
    simp only [QuarterPair.p, QuarterPair.q, symmetricPair, h1, h2, h3, h4, activeF, activeFD,
      tailPhase_reflection, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hsin.1 hR0,
      mul_le_mul_of_nonneg_left hsin.2 hR0]
  refine ⟨hsign, ?_⟩
  simp only [QuarterPair.fluxF, QuarterPair.forceF, min_eq_left hsign.1, max_eq_left hsign.2]
  simp only [QuarterPair.p, QuarterPair.q, symmetricPair, h1, h2, h3, h4, activeF, activeFD,
    activeFlux, activeForce, tailPhase_reflection, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
  constructor <;> ring

def tailCoefficient (r : ℝ) : ℝ := 1 - r * Real.sin tailAngle0

/-- The symmetric pair that is fully active with radius `r` on the whole quarter. -/
abbrev tailPair (r : ℝ) : QuarterPair :=
  symmetricPair (activeF r (tailCoefficient r)) (activeFD r (tailCoefficient r))
    (hasDerivAt_activeF _ _) (continuous_activeFD _ _)

theorem tailPair_widthTraces (r : ℝ) : (tailPair r).WidthTraces (r * Real.cos tailAngle0) :=
  symmetricPair_widthTraces (by simp [activeF, tailPhase_zero])
    (by simp [activeF, tailPhase_pi_div_two, tailCoefficient, Real.cos_pi_div_two_sub])

theorem tailPair_active {r s : ℝ} (hr : 2 / 3 ≤ r * Real.sin tailAngle0)
    (hs : s ∈ Icc 0 (Real.pi / 2)) :
    ((tailPair r).p s ≤ 0 ∧ 0 ≤ (tailPair r).q s) ∧
      (tailPair r).fluxF s = activeFlux r (tailCoefficient r) s ∧
      (tailPair r).forceF s = activeForce r (tailCoefficient r) s :=
  symmetricPair_active le_rfl (by rwa [tailPhase_zero]) (fun _ _ => ⟨rfl, rfl⟩)
    (by rwa [sub_zero])

theorem tailPair_euler {r t : ℝ} (hr : 2 / 3 ≤ r * Real.sin tailAngle0)
    (ht : t ∈ Ioo 0 (Real.pi / 2)) :
    HasDerivAt (tailPair r).fluxF ((tailPair r).forceF t) t :=
  ((hasDerivAt_activeFlux _ _ t).congr_of_eventuallyEq (Filter.eventuallyEq_of_mem
    (Icc_mem_nhds ht.1 ht.2) fun _ hs => (tailPair_active hr hs).2.1)).congr_deriv
    (tailPair_active hr (Ioo_subset_Icc_self ht)).2.2.symm

/-- The exact value of the actual stationary large-width family. -/
theorem adaptiveFunctional_tailPair {r : ℝ} (hr : 2 / 3 ≤ r * Real.sin tailAngle0) :
    adaptiveFunctional (tailPair r) = 4 * r * Real.cos tailAngle0 - 1 -
      3 * r ^ 2 * Real.sin tailAngle0 * Real.cos tailAngle0 := by
  have h := two_mul_adaptiveFunctional (tailPair r)
  obtain ⟨hf0, hg0, hfL, hgL⟩ := tailPair_widthTraces r
  rw [integral_remainder_of_active le_rfl (by positivity) le_rfl fun s hs =>
      (tailPair_active hr hs).1, symmetricPair_self_variation fun t ht => tailPair_euler hr ht,
    (tailPair_active hr ⟨le_rfl, by positivity⟩).2.1,
    (tailPair_active hr ⟨by positivity, le_rfl⟩).2.1, hf0, hg0, hfL, hgL] at h
  simp only [activeFlux, activeF, tailPhase_zero, tailPhase_pi_div_two, tailCoefficient,
    Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub, Real.sin_zero, Real.cos_zero,
    Real.cos_pi_div_two, Real.sin_pi_div_two] at h
  linear_combination h / 2

/-- A whole large-width branch is excluded by its explicit stationary
optimizer, without assuming an optimizer exists at other widths. -/
theorem adaptiveFunctional_sub_width_lt_half_M_of_tail {u : QuarterPair} {a : ℝ}
    (ha : 2 * Real.cos tailAngle0 ≤ 3 * a * Real.sin tailAngle0) (hu : u.WidthTraces a) :
    adaptiveFunctional u - a < M / 2 := by
  have hc := cos_tailAngle0_pos
  set r := a / Real.cos tailAngle0
  have har : a = r * Real.cos tailAngle0 := (div_mul_cancel₀ a hc.ne').symm
  have hr : 2 / 3 ≤ r * Real.sin tailAngle0 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]; linarith
  rw [har] at hu ⊢
  have h := adaptiveFunctional_le_of_stationary
    (symmetricPair_stationary fun t ht => tailPair_euler (r := r) hr ht)
    (QuarterPair.sameTraces_of_widthTraces hu (tailPair_widthTraces r))
  have hx : r * Real.sin tailAngle0 - (r * Real.sin tailAngle0) ^ 2 ≤ 2 / 9 := by nlinarith
  have hscore : 3 * r * Real.cos tailAngle0 - 1 -
      3 * r ^ 2 * Real.sin tailAngle0 * Real.cos tailAngle0 < 2 / 3 := by
    nlinarith [sin_tailAngle0_pos, mul_le_mul_of_nonneg_left hx hc.le,
      two_cos_tailAngle0_lt_five_sin]
  linarith [adaptiveFunctional_tailPair hr, eight_fifths_lt_M]

end AmbidextrousSofa.Analysis
