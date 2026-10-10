module

public import AmbidextrousSofa.Reference.Hull

@[expose] public section

/-!
# Realization of the displayed reference support

The boundary points are defined by `h μ + h' ν`. Their scalar projections
have right derivative `(h + h'') sin (φ - t)`. The right-derivative fundamental
theorem of calculus controls these projections even at the two curvature
jumps. The two upper arcs are joined by the actual horizontal top face.
Reflection then supplies the lower half-plane constraints.

This argument constructs attaining points in the existing `referenceHull`;
it does not assume that the prescribed support has already been realized.
-/

noncomputable section

open Set
open scoped Topology

namespace AmbidextrousSofa.Reference

/-- A point with the prescribed normal and tangent coordinates. -/
def supportPoint (h hD : ℝ → ℝ) (t : ℝ) : Plane :=
  (h t * Real.cos t - hD t * Real.sin t,
    h t * Real.sin t + hD t * Real.cos t)

/-- The same construction on the companion quarter. -/
def companionSupportPoint (h hD : ℝ → ℝ) (t : ℝ) : Plane :=
  rotate (Real.pi / 2) (supportPoint h hD t)

/-- Projection of the support point against a fixed target normal. -/
def supportProjection (h hD : ℝ → ℝ) (φ t : ℝ) : ℝ :=
  h t * Real.cos (φ - t) + hD t * Real.sin (φ - t)

theorem coordDot_supportPoint (h hD : ℝ → ℝ) (φ t : ℝ) :
    coordDot (supportPoint h hD t) (unitNormal φ) = supportProjection h hD φ t := by
  simp only [coordDot, supportPoint, unitNormal, supportProjection,
    Real.cos_sub, Real.sin_sub]
  ring

theorem coordDot_companionSupportPoint (h hD : ℝ → ℝ) (φ t : ℝ) :
    coordDot (companionSupportPoint h hD t) (unitNormal φ) =
      supportProjection h hD (φ - Real.pi / 2) t := by
  unfold companionSupportPoint
  rw [coordDot_rotate, rotate_unitNormal]
  rw [show -(Real.pi / 2) + φ = φ - Real.pi / 2 by ring]
  exact coordDot_supportPoint h hD (φ - Real.pi / 2) t

theorem supportProjection_self (h hD : ℝ → ℝ) (t : ℝ) :
    supportProjection h hD t t = h t := by
  simp [supportProjection]

theorem continuous_supportProjection {h hD : ℝ → ℝ}
    (hh : Continuous h) (hhD : Continuous hD) (φ : ℝ) :
    Continuous (supportProjection h hD φ) := by
  unfold supportProjection
  fun_prop

/-- Right derivatives of a continuous join use the right-hand phase at its switch. -/
theorem hasDerivWithinAt_if_le_right (c : ℝ) {f g fD gD : ℝ → ℝ}
    (hf : ∀ x, HasDerivWithinAt f (fD x) (Ioi x) x)
    (hg : ∀ x, HasDerivWithinAt g (gD x) (Ioi x) x)
    (hvalue : f c = g c) (x : ℝ) :
    HasDerivWithinAt (fun y => if y ≤ c then f y else g y)
      (if x < c then fD x else gD x) (Ioi x) x := by
  rcases lt_trichotomy x c with hlt | rfl | hgt
  · rw [if_pos hlt]
    apply (hf x).congr_of_eventuallyEq
    · filter_upwards [(Iio_mem_nhds hlt).filter_mono nhdsWithin_le_nhds] with y hy
      exact if_pos hy.le
    · exact if_pos hlt.le
  · rw [if_neg (lt_irrefl c)]
    apply (hg c).congr
    · intro y hy
      exact if_neg (not_le.mpr hy)
    · simpa only [if_pos le_rfl] using hvalue
  · rw [if_neg (not_lt.mpr hgt.le)]
    apply (hg x).congr
    · intro y hy
      exact if_neg (not_le.mpr (hgt.trans hy))
    · exact if_neg (not_le.mpr hgt)

/-- The coordinate cancellation underlying the support construction. -/
theorem hasDerivWithinAt_supportProjection {h hD : ℝ → ℝ} {hDD φ t : ℝ}
    (hh : HasDerivWithinAt h (hD t) (Ioi t) t)
    (hhD : HasDerivWithinAt hD hDD (Ioi t) t) :
    HasDerivWithinAt (supportProjection h hD φ)
      ((h t + hDD) * Real.sin (φ - t)) (Ioi t) t := by
  have hangle : HasDerivAt (fun x : ℝ => φ - x) (-1) t := by
    simpa using (hasDerivAt_const t φ).sub (hasDerivAt_id t)
  unfold supportProjection
  apply ((hh.mul hangle.cos.hasDerivWithinAt).add
    (hhD.mul hangle.sin.hasDerivWithinAt)).congr_deriv
  ring

/-- The FTC monotonicity consequence requires only right derivatives. -/
theorem le_of_right_derivative_nonneg {f fD : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hfD : ∀ x ∈ Ioo a b, HasDerivWithinAt f (fD x) (Ioi x) x)
    (hnonneg : ∀ x ∈ Ioo a b, 0 ≤ fD x) : f a ≤ f b := by
  have h := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hab hf hfD
    (φ := fun _ : ℝ => 0) (by simp) hnonneg
  simpa only [intervalIntegral.integral_zero, sub_nonneg] using h

theorem le_of_right_derivative_nonpos {f fD : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hfD : ∀ x ∈ Ioo a b, HasDerivWithinAt f (fD x) (Ioi x) x)
    (hnonpos : ∀ x ∈ Ioo a b, fD x ≤ 0) : f b ≤ f a := by
  have h := le_of_right_derivative_nonneg hab hf.neg
    (fun x hx => (hfD x hx).neg) (fun x hx => neg_nonneg.mpr (hnonpos x hx))
  linarith

/-- Projection increases as a nonnegative-curvature arc approaches its normal. -/
theorem supportProjection_le_of_le {h hD hDD : ℝ → ℝ} {a b φ : ℝ}
    (hh : Continuous h) (hhD : Continuous hD)
    (hderiv : ∀ x, HasDerivWithinAt h (hD x) (Ioi x) x)
    (hsecond : ∀ x, HasDerivWithinAt hD (hDD x) (Ioi x) x)
    (hcurv : ∀ x ∈ Icc a b, 0 ≤ h x + hDD x)
    (hab : a ≤ b) (hbφ : b ≤ φ) (hφa : φ - a ≤ Real.pi) :
    supportProjection h hD φ a ≤ supportProjection h hD φ b := by
  apply le_of_right_derivative_nonneg hab
    (continuous_supportProjection hh hhD φ).continuousOn
    (fun x _ => hasDerivWithinAt_supportProjection (hderiv x) (hsecond x))
  intro x hx
  apply mul_nonneg (hcurv x ⟨hx.1.le, hx.2.le⟩)
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.2]) (by linarith [hx.1])

/-- Projection decreases once a nonnegative-curvature arc has passed its normal. -/
theorem supportProjection_le_of_ge {h hD hDD : ℝ → ℝ} {a b φ : ℝ}
    (hh : Continuous h) (hhD : Continuous hD)
    (hderiv : ∀ x, HasDerivWithinAt h (hD x) (Ioi x) x)
    (hsecond : ∀ x, HasDerivWithinAt hD (hDD x) (Ioi x) x)
    (hcurv : ∀ x ∈ Icc a b, 0 ≤ h x + hDD x)
    (hab : a ≤ b) (hφa : φ ≤ a) (hbφ : b - φ ≤ Real.pi) :
    supportProjection h hD φ b ≤ supportProjection h hD φ a := by
  apply le_of_right_derivative_nonpos hab
    (continuous_supportProjection hh hhD φ).continuousOn
    (fun x _ => hasDerivWithinAt_supportProjection (hderiv x) (hsecond x))
  intro x hx
  apply mul_nonpos_of_nonneg_of_nonpos (hcurv x ⟨hx.1.le, hx.2.le⟩)
  have hs : 0 ≤ Real.sin (x - φ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.1]) (by linarith [hx.2])
  have heq : φ - x = -(x - φ) := by ring
  rw [heq, Real.sin_neg]
  exact neg_nonpos.mpr hs

/-- Every point of an arc of angular length at most π lies below its own support data. -/
theorem supportProjection_le_self {h hD hDD : ℝ → ℝ} {a b s t : ℝ}
    (hh : Continuous h) (hhD : Continuous hD)
    (hderiv : ∀ x, HasDerivWithinAt h (hD x) (Ioi x) x)
    (hsecond : ∀ x, HasDerivWithinAt hD (hDD x) (Ioi x) x)
    (hcurv : ∀ x ∈ Icc a b, 0 ≤ h x + hDD x)
    (hwidth : b - a ≤ Real.pi) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    supportProjection h hD t s ≤ h t := by
  rcases le_total s t with hst | hts
  · have h := supportProjection_le_of_le hh hhD hderiv hsecond
      (fun x hx => hcurv x ⟨hs.1.trans hx.1, hx.2.trans ht.2⟩)
      hst le_rfl (by linarith [hs.1, ht.2])
    simpa only [supportProjection_self] using h
  · have h := supportProjection_le_of_ge hh hhD hderiv hsecond
      (fun x hx => hcurv x ⟨ht.1.trans hx.1, hx.2.trans hs.2⟩)
      hts le_rfl (by linarith [ht.1, hs.2])
    simpa only [supportProjection_self] using h

/-- The right second derivative of the first three-phase support. -/
def referenceFSecond (t : ℝ) : ℝ :=
  if t < beta then -Real.cos t - 1 / 2 * Real.sin t
  else if t < lateSwitch then
    -(R / 4) * Real.cos (t / 2 + Real.pi / 8) - k * Real.cos t - 1 / 2 * Real.sin t
  else -(1 - 2 / 3 * A) * Real.cos t - 1 / 2 * Real.sin t

/-- The right second derivative of the companion support. -/
def referenceGSecond (t : ℝ) : ℝ :=
  if t < beta then -(2 * A - 1) * Real.sin t - 1 / 2 * Real.cos t
  else if t < lateSwitch then
    -(R / 4) * Real.sin (t / 2 + Real.pi / 8) + k * Real.sin t - 1 / 2 * Real.cos t
  else -(8 / 3 * A - 1) * Real.sin t - 1 / 2 * Real.cos t

theorem hasDerivWithinAt_referenceFD_right (t : ℝ) :
    HasDerivWithinAt referenceFD (referenceFSecond t) (Ioi t) t := by
  unfold referenceFD referenceFSecond
  apply hasDerivWithinAt_if_le_right beta
    (fun x => (hasDerivAt_fEarlyD x).hasDerivWithinAt)
    (hasDerivWithinAt_if_le_right lateSwitch
      (fun x => (hasDerivAt_fMiddleD x).hasDerivWithinAt)
      (fun x => (hasDerivAt_fLateD x).hasDerivWithinAt) fD_matching_last)
  rw [if_pos (le_of_lt beta_lt_lateSwitch)]
  exact fD_matching_first.symm

theorem hasDerivWithinAt_referenceGD_right (t : ℝ) :
    HasDerivWithinAt referenceGD (referenceGSecond t) (Ioi t) t := by
  unfold referenceGD referenceGSecond
  apply hasDerivWithinAt_if_le_right beta
    (fun x => (hasDerivAt_gEarlyD x).hasDerivWithinAt)
    (hasDerivWithinAt_if_le_right lateSwitch
      (fun x => (hasDerivAt_gMiddleD x).hasDerivWithinAt)
      (fun x => (hasDerivAt_gLateD x).hasDerivWithinAt) gD_matching_last)
  rw [if_pos (le_of_lt beta_lt_lateSwitch)]
  exact gD_matching_first.symm

theorem referenceF_eq_right_phases (t : ℝ) :
    referenceF t = if t < beta then fEarly t
      else if t < lateSwitch then fMiddle t else fLate t := by
  unfold referenceF
  rcases lt_trichotomy t beta with hlt | rfl | hgt
  · rw [if_pos hlt.le, if_pos hlt]
  · rw [if_pos le_rfl, if_neg (lt_irrefl beta), if_pos beta_lt_lateSwitch]
    exact f_matching_first.symm
  · rw [if_neg (not_le.mpr hgt), if_neg (not_lt.mpr hgt.le)]
    rcases lt_trichotomy t lateSwitch with hlt | rfl | hgt
    · rw [if_pos hlt.le, if_pos hlt]
    · rw [if_pos le_rfl, if_neg (lt_irrefl lateSwitch)]
      exact f_matching_last
    · rw [if_neg (not_le.mpr hgt), if_neg (not_lt.mpr hgt.le)]

theorem referenceG_eq_right_phases (t : ℝ) :
    referenceG t = if t < beta then gEarly t
      else if t < lateSwitch then gMiddle t else gLate t := by
  unfold referenceG
  rcases lt_trichotomy t beta with hlt | rfl | hgt
  · rw [if_pos hlt.le, if_pos hlt]
  · rw [if_pos le_rfl, if_neg (lt_irrefl beta), if_pos beta_lt_lateSwitch]
    exact g_matching_first.symm
  · rw [if_neg (not_le.mpr hgt), if_neg (not_lt.mpr hgt.le)]
    rcases lt_trichotomy t lateSwitch with hlt | rfl | hgt
    · rw [if_pos hlt.le, if_pos hlt]
    · rw [if_pos le_rfl, if_neg (lt_irrefl lateSwitch)]
      exact g_matching_last
    · rw [if_neg (not_le.mpr hgt), if_neg (not_lt.mpr hgt.le)]

theorem referenceF_right_curvature_nonneg {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    0 ≤ referenceF t + referenceFSecond t := by
  rw [referenceF_eq_right_phases]
  unfold referenceFSecond
  split_ifs with hearly hmiddle
  · unfold fEarly
    nlinarith
  · have hcos : 0 < Real.cos (t / 2 + Real.pi / 8) := by
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> linarith [ht.1, ht.2, Real.pi_pos]
    unfold fMiddle
    nlinarith [mul_pos R_pos hcos]
  · unfold fLate
    nlinarith

theorem referenceG_right_curvature_nonneg {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    0 ≤ referenceG t + referenceGSecond t := by
  rw [referenceG_eq_right_phases]
  unfold referenceGSecond
  split_ifs with hearly hmiddle
  · unfold gEarly
    nlinarith
  · have hsin : 0 < Real.sin (t / 2 + Real.pi / 8) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · linarith [ht.1, Real.pi_pos]
      · linarith [ht.2, Real.pi_pos]
    unfold gMiddle
    nlinarith [mul_pos R_pos hsin]
  · unfold gLate
    nlinarith

/-- The actual first upper boundary arc. -/
def fBoundary (t : ℝ) : Plane := supportPoint referenceF referenceFD t

/-- The actual second upper boundary arc. -/
def gBoundary (t : ℝ) : Plane := companionSupportPoint referenceG referenceGD t

theorem coordDot_fBoundary (φ t : ℝ) :
    coordDot (fBoundary t) (unitNormal φ) = supportProjection referenceF referenceFD φ t :=
  coordDot_supportPoint referenceF referenceFD φ t

theorem coordDot_gBoundary (φ t : ℝ) :
    coordDot (gBoundary t) (unitNormal φ) =
      supportProjection referenceG referenceGD (φ - Real.pi / 2) t :=
  coordDot_companionSupportPoint referenceG referenceGD φ t

theorem coordDot_fBoundary_self (t : ℝ) :
    coordDot (fBoundary t) (unitNormal t) = referenceF t := by
  rw [coordDot_fBoundary, supportProjection_self]

theorem coordDot_gBoundary_self (t : ℝ) :
    coordDot (gBoundary t) (unitNormal (t + Real.pi / 2)) = referenceG t := by
  rw [coordDot_gBoundary]
  simp only [add_sub_cancel_right, supportProjection_self]

theorem fBoundary_zero : fBoundary 0 = (1, 1 / 2) := by
  simp [fBoundary, supportPoint, referenceF_zero, referenceFD,
    le_of_lt beta_pos, fEarlyD_zero]

theorem fBoundary_pi_div_two :
    fBoundary (Real.pi / 2) = (1 - 2 / 3 * A, 1) := by
  simp [fBoundary, supportPoint, referenceF_pi_div_two, referenceFD,
    not_le.mpr beta_lt_pi_div_two, not_le.mpr lateSwitch_lt_pi_div_two,
    fLateD_pi_div_two] <;> ring

theorem gBoundary_zero : gBoundary 0 = (1 - 2 * A, 1) := by
  simp [gBoundary, companionSupportPoint, supportPoint, rotate, referenceG_zero,
    referenceGD, le_of_lt beta_pos, gEarlyD_zero] <;> ring

theorem gBoundary_pi_div_two :
    gBoundary (Real.pi / 2) = (1 - 8 / 3 * A, 1 / 2) := by
  simp [gBoundary, companionSupportPoint, supportPoint, rotate,
    referenceG_pi_div_two, referenceGD, not_le.mpr beta_lt_pi_div_two,
    not_le.mpr lateSwitch_lt_pi_div_two, gLateD_pi_div_two] <;> ring

theorem fBoundary_below_first_support {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) (Real.pi / 2)) (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    coordDot (fBoundary s) (unitNormal t) ≤ referenceF t := by
  rw [coordDot_fBoundary]
  exact supportProjection_le_self continuous_referenceF continuous_referenceFD
    (fun x => (hasDerivAt_referenceF x).hasDerivWithinAt)
    hasDerivWithinAt_referenceFD_right (fun _ hx => referenceF_right_curvature_nonneg hx)
    (by linarith [Real.pi_pos]) hs ht

theorem gBoundary_below_companion_support {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) (Real.pi / 2)) (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    coordDot (gBoundary s) (unitNormal (t + Real.pi / 2)) ≤ referenceG t := by
  rw [coordDot_gBoundary, add_sub_cancel_right]
  exact supportProjection_le_self continuous_referenceG continuous_referenceGD
    (fun x => (hasDerivAt_referenceG x).hasDerivWithinAt)
    hasDerivWithinAt_referenceGD_right (fun _ hx => referenceG_right_curvature_nonneg hx)
    (by linarith [Real.pi_pos]) hs ht

theorem fBoundary_above_midline {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : 1 / 2 ≤ (fBoundary t).2 := by
  have h := supportProjection_le_of_le continuous_referenceF continuous_referenceFD
    (fun x => (hasDerivAt_referenceF x).hasDerivWithinAt)
    hasDerivWithinAt_referenceFD_right
    (fun x hx => referenceF_right_curvature_nonneg ⟨hx.1, hx.2.trans ht.2⟩)
    ht.1 ht.2 (show Real.pi / 2 - 0 ≤ Real.pi by linarith [Real.pi_pos])
  have hdot : coordDot (fBoundary 0) (unitNormal (Real.pi / 2)) ≤
      coordDot (fBoundary t) (unitNormal (Real.pi / 2)) := by
    simpa only [coordDot_fBoundary] using h
  rw [fBoundary_zero] at hdot
  simpa only [coordDot, unitNormal, Real.cos_pi_div_two, Real.sin_pi_div_two,
    mul_zero, mul_one, zero_add] using hdot

theorem gBoundary_above_midline {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : 1 / 2 ≤ (gBoundary t).2 := by
  have h := supportProjection_le_of_ge continuous_referenceG continuous_referenceGD
    (fun x => (hasDerivAt_referenceG x).hasDerivWithinAt)
    hasDerivWithinAt_referenceGD_right
    (fun x hx => referenceG_right_curvature_nonneg ⟨ht.1.trans hx.1, hx.2⟩)
    ht.2 ht.1 (show Real.pi / 2 - 0 ≤ Real.pi by linarith [Real.pi_pos])
  have hdot : coordDot (gBoundary (Real.pi / 2)) (unitNormal (Real.pi / 2)) ≤
      coordDot (gBoundary t) (unitNormal (Real.pi / 2)) := by
    simpa only [coordDot_gBoundary, sub_self] using h
  rw [gBoundary_pi_div_two] at hdot
  simpa only [coordDot, unitNormal, Real.cos_pi_div_two, Real.sin_pi_div_two,
    mul_zero, mul_one, zero_add] using hdot

theorem fBoundary_below_companion_support {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) (Real.pi / 2)) (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    coordDot (fBoundary s) (unitNormal (t + Real.pi / 2)) ≤ referenceG t := by
  have hmono : coordDot (fBoundary s) (unitNormal (t + Real.pi / 2)) ≤
      coordDot (fBoundary (Real.pi / 2)) (unitNormal (t + Real.pi / 2)) := by
    rw [coordDot_fBoundary, coordDot_fBoundary]
    apply supportProjection_le_of_le continuous_referenceF continuous_referenceFD
      (fun x => (hasDerivAt_referenceF x).hasDerivWithinAt)
      hasDerivWithinAt_referenceFD_right
      (fun x hx => referenceF_right_curvature_nonneg ⟨hs.1.trans hx.1, hx.2⟩)
      hs.2
    · linarith [ht.1]
    · linarith [ht.2, hs.1]
  have hface : coordDot (fBoundary (Real.pi / 2)) (unitNormal (t + Real.pi / 2)) ≤
      coordDot (gBoundary 0) (unitNormal (t + Real.pi / 2)) := by
    rw [fBoundary_pi_div_two, gBoundary_zero]
    simp only [coordDot, unitNormal, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
    have hsin : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht.1
      (by linarith [ht.2, Real.pi_pos])
    nlinarith [mul_nonneg A_pos.le hsin]
  exact hmono.trans (hface.trans (gBoundary_below_companion_support
    ⟨le_rfl, by linarith [Real.pi_pos]⟩ ht))

theorem gBoundary_below_first_support {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) (Real.pi / 2)) (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    coordDot (gBoundary s) (unitNormal t) ≤ referenceF t := by
  have hmono : coordDot (gBoundary s) (unitNormal t) ≤
      coordDot (gBoundary 0) (unitNormal t) := by
    rw [coordDot_gBoundary, coordDot_gBoundary]
    apply supportProjection_le_of_ge continuous_referenceG continuous_referenceGD
      (fun x => (hasDerivAt_referenceG x).hasDerivWithinAt)
      hasDerivWithinAt_referenceGD_right
      (fun x hx => referenceG_right_curvature_nonneg ⟨hx.1, hx.2.trans hs.2⟩)
      hs.1
    · linarith [ht.2]
    · linarith [ht.1, hs.2]
  have hface : coordDot (gBoundary 0) (unitNormal t) ≤
      coordDot (fBoundary (Real.pi / 2)) (unitNormal t) := by
    rw [gBoundary_zero, fBoundary_pi_div_two]
    simp only [coordDot, unitNormal]
    have hcos : 0 ≤ Real.cos t := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
    nlinarith [mul_nonneg A_pos.le hcos]
  exact hmono.trans (hface.trans (fBoundary_below_first_support
    ⟨by linarith [Real.pi_pos], le_rfl⟩ ht))

/-- Reflecting an upper-half point decreases every upward coordinate pairing. -/
theorem coordDot_reflect_le {p v : Plane} (hp : 1 / 2 ≤ p.2) (hv : 0 ≤ v.2) :
    coordDot (reflect p) v ≤ coordDot p v := by
  have hmul := mul_nonneg (show 0 ≤ 2 * p.2 - 1 by linarith) hv
  unfold coordDot reflect
  nlinarith

theorem fBoundary_mem_referenceHull {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : fBoundary t ∈ referenceHull := by
  apply (mem_referenceHull_iff _).mpr
  intro s hs
  have hfirst := fBoundary_below_first_support ht hs
  have hsecond := fBoundary_below_companion_support ht hs
  refine ⟨⟨hfirst, hsecond⟩, ?_, ?_⟩
  · apply (coordDot_reflect_le (fBoundary_above_midline ht) ?_).trans hfirst
    exact Real.sin_nonneg_of_nonneg_of_le_pi hs.1 (by linarith [hs.2, Real.pi_pos])
  · apply (coordDot_reflect_le (fBoundary_above_midline ht) ?_).trans hsecond
    change 0 ≤ Real.sin (s + Real.pi / 2)
    rw [Real.sin_add_pi_div_two]
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [hs.1, Real.pi_pos], hs.2⟩

theorem gBoundary_mem_referenceHull {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : gBoundary t ∈ referenceHull := by
  apply (mem_referenceHull_iff _).mpr
  intro s hs
  have hfirst := gBoundary_below_first_support ht hs
  have hsecond := gBoundary_below_companion_support ht hs
  refine ⟨⟨hfirst, hsecond⟩, ?_, ?_⟩
  · apply (coordDot_reflect_le (gBoundary_above_midline ht) ?_).trans hfirst
    exact Real.sin_nonneg_of_nonneg_of_le_pi hs.1 (by linarith [hs.2, Real.pi_pos])
  · apply (coordDot_reflect_le (gBoundary_above_midline ht) ?_).trans hsecond
    change 0 ≤ Real.sin (s + Real.pi / 2)
    rw [Real.sin_add_pi_div_two]
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [hs.1, Real.pi_pos], hs.2⟩

/-- Every prescribed first-quarter support value is attained in the concrete intersection. -/
theorem angleSupport_referenceHull_eq_f {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    angleSupport referenceHull t = referenceF t := by
  apply le_antisymm (angleSupport_referenceHull_le_f ht)
  rw [← coordDot_fBoundary_self]
  exact coordDot_le_support isCompact_referenceHull (fBoundary_mem_referenceHull ht) _

/-- Every companion-quarter value is attained by the second explicit arc. -/
theorem angleSupport_referenceHull_eq_g {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    angleSupport referenceHull (t + Real.pi / 2) = referenceG t := by
  apply le_antisymm (angleSupport_referenceHull_le_g ht)
  rw [← coordDot_gBoundary_self]
  exact coordDot_le_support isCompact_referenceHull (gBoundary_mem_referenceHull ht) _

theorem angleSupport_referenceCap_eq_f {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    angleSupport referenceCap t = referenceF t := by
  rw [angleSupport_referenceCap
    (Real.sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2, Real.pi_pos]))]
  exact angleSupport_referenceHull_eq_f ht

theorem angleSupport_referenceCap_eq_g {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    angleSupport referenceCap (t + Real.pi / 2) = referenceG t := by
  rw [angleSupport_referenceCap (by
    rw [Real.sin_add_pi_div_two]
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)]
  exact angleSupport_referenceHull_eq_g ht

end AmbidextrousSofa.Reference
