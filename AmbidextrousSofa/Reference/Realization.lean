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
  simp only [coordDot, supportPoint, unitNormal, supportProjection, Real.cos_sub, Real.sin_sub]
  ring

theorem coordDot_companionSupportPoint (h hD : ℝ → ℝ) (φ t : ℝ) :
    coordDot (companionSupportPoint h hD t) (unitNormal φ) =
      supportProjection h hD (φ - Real.pi / 2) t := by
  rw [companionSupportPoint, coordDot_rotate, rotate_unitNormal, neg_add_eq_sub,
    coordDot_supportPoint]

theorem supportProjection_self (h hD : ℝ → ℝ) (t : ℝ) :
    supportProjection h hD t t = h t := by
  simp [supportProjection]

/-- Right derivatives of a continuous join use the right-hand phase at its switch. -/
theorem hasDerivWithinAt_if_le_right (c : ℝ) {f g fD gD : ℝ → ℝ}
    (hf : ∀ x, HasDerivWithinAt f (fD x) (Ioi x) x)
    (hg : ∀ x, HasDerivWithinAt g (gD x) (Ioi x) x)
    (hvalue : f c = g c) (x : ℝ) :
    HasDerivWithinAt (fun y => if y ≤ c then f y else g y)
      (if x < c then fD x else gD x) (Ioi x) x := by
  rcases lt_or_ge x c with hlt | hge
  · rw [ite_eq_left hlt]
    exact (hf x).congr_of_eventuallyEq (((eventually_lt_nhds hlt).mono fun y hy =>
      ite_eq_left hy.le).filter_mono nhdsWithin_le_nhds) (ite_eq_left hlt.le)
  · rw [ite_eq_right (not_lt.mpr hge)]
    refine (hg x).congr (fun y (hy : x < y) => ite_eq_right (not_le.mpr (hge.trans_lt hy))) ?_
    split_ifs with h <;> [rw [le_antisymm h hge, hvalue]; rfl]

/-- The coordinate cancellation underlying the support construction. -/
theorem hasDerivWithinAt_supportProjection {h hD : ℝ → ℝ} {hDD φ t : ℝ}
    (hh : HasDerivWithinAt h (hD t) (Ioi t) t)
    (hhD : HasDerivWithinAt hD hDD (Ioi t) t) :
    HasDerivWithinAt (supportProjection h hD φ)
      ((h t + hDD) * Real.sin (φ - t)) (Ioi t) t := by
  have hangle := (hasDerivAt_id' t).const_sub φ
  exact ((hh.mul hangle.cos.hasDerivWithinAt).add
    (hhD.mul hangle.sin.hasDerivWithinAt)).congr_deriv (by ring)

/-- Projection increases as a nonnegative-curvature arc approaches its normal. -/
theorem supportProjection_le_of_le {h hD hDD : ℝ → ℝ} {a b φ : ℝ}
    (hh : Continuous h) (hhD : Continuous hD)
    (hderiv : ∀ x, HasDerivWithinAt h (hD x) (Ioi x) x)
    (hsecond : ∀ x, HasDerivWithinAt hD (hDD x) (Ioi x) x)
    (hcurv : ∀ x ∈ Icc a b, 0 ≤ h x + hDD x)
    (hab : a ≤ b) (hbφ : b ≤ φ) (hφa : φ - a ≤ Real.pi) :
    supportProjection h hD φ a ≤ supportProjection h hD φ b := by
  -- the FTC monotonicity consequence requires only right derivatives
  simpa only [intervalIntegral.integral_zero, sub_nonneg] using
    intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hab
      (Continuous.continuousOn (by unfold supportProjection; fun_prop))
      (fun x _ => hasDerivWithinAt_supportProjection (hderiv x) (hsecond x)) (φ := fun _ => 0)
      (by simp) fun x hx => mul_nonneg (hcurv x ⟨hx.1.le, hx.2.le⟩)
        (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.2]) (by linarith [hx.1]))

/-- Projection decreases once a nonnegative-curvature arc has passed its normal. -/
theorem supportProjection_le_of_ge {h hD hDD : ℝ → ℝ} {a b φ : ℝ}
    (hh : Continuous h) (hhD : Continuous hD)
    (hderiv : ∀ x, HasDerivWithinAt h (hD x) (Ioi x) x)
    (hsecond : ∀ x, HasDerivWithinAt hD (hDD x) (Ioi x) x)
    (hcurv : ∀ x ∈ Icc a b, 0 ≤ h x + hDD x)
    (hab : a ≤ b) (hφa : φ ≤ a) (hbφ : b - φ ≤ Real.pi) :
    supportProjection h hD φ b ≤ supportProjection h hD φ a := by
  simpa only [intervalIntegral.integral_zero, sub_nonpos] using
    intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hab
      (Continuous.continuousOn (by unfold supportProjection; fun_prop))
      (fun x _ => hasDerivWithinAt_supportProjection (hderiv x) (hsecond x)) (φ := fun _ => 0)
      (by simp) fun x hx => mul_nonpos_of_nonneg_of_nonpos (hcurv x ⟨hx.1.le, hx.2.le⟩)
        (Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith [hx.1]) (by linarith [hx.2]))

/-- Every point of an arc of angular length at most π lies below its own support data. -/
theorem supportProjection_le_self {h hD hDD : ℝ → ℝ} {a b s t : ℝ}
    (hh : Continuous h) (hhD : Continuous hD)
    (hderiv : ∀ x, HasDerivWithinAt h (hD x) (Ioi x) x)
    (hsecond : ∀ x, HasDerivWithinAt hD (hDD x) (Ioi x) x)
    (hcurv : ∀ x ∈ Icc a b, 0 ≤ h x + hDD x)
    (hwidth : b - a ≤ Real.pi) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    supportProjection h hD t s ≤ h t := by
  rw [← supportProjection_self h hD t]
  rcases le_total s t with hst | hts
  · exact supportProjection_le_of_le hh hhD hderiv hsecond
      (fun x hx => hcurv x ⟨hs.1.trans hx.1, hx.2.trans ht.2⟩) hst le_rfl
      (by linarith [hs.1, ht.2])
  · exact supportProjection_le_of_ge hh hhD hderiv hsecond
      (fun x hx => hcurv x ⟨ht.1.trans hx.1, hx.2.trans hs.2⟩) hts le_rfl
      (by linarith [ht.1, hs.2])

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
    HasDerivWithinAt referenceFD (referenceFSecond t) (Ioi t) t :=
  hasDerivWithinAt_if_le_right beta (fun x => (hasDerivAt_fEarlyD x).hasDerivWithinAt)
    (hasDerivWithinAt_if_le_right lateSwitch (fun x => (hasDerivAt_fMiddleD x).hasDerivWithinAt)
      (fun x => (hasDerivAt_fLateD x).hasDerivWithinAt) fD_matching_last)
    (by rw [ite_eq_left beta_lt_lateSwitch.le, fD_matching_first]) t

theorem hasDerivWithinAt_referenceGD_right (t : ℝ) :
    HasDerivWithinAt referenceGD (referenceGSecond t) (Ioi t) t :=
  hasDerivWithinAt_if_le_right beta (fun x => (hasDerivAt_gEarlyD x).hasDerivWithinAt)
    (hasDerivWithinAt_if_le_right lateSwitch (fun x => (hasDerivAt_gMiddleD x).hasDerivWithinAt)
      (fun x => (hasDerivAt_gLateD x).hasDerivWithinAt) gD_matching_last)
    (by rw [ite_eq_left beta_lt_lateSwitch.le, gD_matching_first]) t

theorem referenceF_eq_right_phases (t : ℝ) :
    referenceF t = if t < beta then fEarly t
      else if t < lateSwitch then fMiddle t else fLate t := by
  rcases lt_trichotomy t beta with h | rfl | h
  · simp [referenceF, h, h.le]
  · simp [referenceF, beta_lt_lateSwitch, f_matching_first]
  rcases lt_trichotomy t lateSwitch with h' | rfl | h'
  · simp [referenceF, h.not_ge, h.not_gt, h', h'.le]
  · simp [referenceF, h.not_ge, h.not_gt, f_matching_last]
  · simp [referenceF, h.not_ge, h.not_gt, h'.not_ge, h'.not_gt]

theorem referenceG_eq_right_phases (t : ℝ) :
    referenceG t = if t < beta then gEarly t
      else if t < lateSwitch then gMiddle t else gLate t := by
  rcases lt_trichotomy t beta with h | rfl | h
  · simp [referenceG, h, h.le]
  · simp [referenceG, beta_lt_lateSwitch, g_matching_first]
  rcases lt_trichotomy t lateSwitch with h' | rfl | h'
  · simp [referenceG, h.not_ge, h.not_gt, h', h'.le]
  · simp [referenceG, h.not_ge, h.not_gt, g_matching_last]
  · simp [referenceG, h.not_ge, h.not_gt, h'.not_ge, h'.not_gt]

theorem referenceF_right_curvature_nonneg {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    0 ≤ referenceF t + referenceFSecond t := by
  have hcos : 0 < Real.cos (t / 2 + Real.pi / 8) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2, Real.pi_pos]⟩
  rw [referenceF_eq_right_phases]
  unfold referenceFSecond fEarly fMiddle fLate
  split_ifs <;> linarith [mul_pos R_pos hcos]

theorem referenceG_right_curvature_nonneg {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    0 ≤ referenceG t + referenceGSecond t := by
  have hsin : 0 < Real.sin (t / 2 + Real.pi / 8) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1, Real.pi_pos])
      (by linarith [ht.2, Real.pi_pos])
  rw [referenceG_eq_right_phases]
  unfold referenceGSecond gEarly gMiddle gLate
  split_ifs <;> linarith [mul_pos R_pos hsin]

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
  rw [coordDot_gBoundary, add_sub_cancel_right, supportProjection_self]

theorem fBoundary_pi_div_two :
    fBoundary (Real.pi / 2) = (1 - 2 / 3 * A, 1) := by
  simp [fBoundary, supportPoint, referenceF_pi_div_two, referenceFD,
    not_le.mpr beta_lt_pi_div_two, not_le.mpr lateSwitch_lt_pi_div_two, fLateD_pi_div_two]

theorem gBoundary_zero : gBoundary 0 = (1 - 2 * A, 1) := by
  simp [gBoundary, companionSupportPoint, supportPoint, rotate, referenceG_zero,
    referenceGD, le_of_lt beta_pos, gEarlyD_zero]

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
    (fun x => (hasDerivAt_referenceF x).hasDerivWithinAt) hasDerivWithinAt_referenceFD_right
    (fun x hx => referenceF_right_curvature_nonneg ⟨hx.1, hx.2.trans ht.2⟩)
    ht.1 ht.2 (by linarith [Real.pi_pos])
  rw [← coordDot_fBoundary, ← coordDot_fBoundary, show fBoundary 0 = (1, 1 / 2) by
    simp [fBoundary, supportPoint, referenceF_zero, referenceFD, beta_pos.le, fEarlyD_zero]] at h
  simpa [coordDot, unitNormal] using h

theorem gBoundary_above_midline {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : 1 / 2 ≤ (gBoundary t).2 := by
  have h := supportProjection_le_of_ge continuous_referenceG continuous_referenceGD
    (fun x => (hasDerivAt_referenceG x).hasDerivWithinAt) hasDerivWithinAt_referenceGD_right
    (fun x hx => referenceG_right_curvature_nonneg ⟨ht.1.trans hx.1, hx.2⟩)
    ht.2 ht.1 (by linarith [Real.pi_pos])
  rw [← sub_self (Real.pi / 2), ← coordDot_gBoundary, ← coordDot_gBoundary,
    show gBoundary (Real.pi / 2) = (1 - 8 / 3 * A, 1 / 2) by
      simp [gBoundary, companionSupportPoint, supportPoint, rotate, referenceG_pi_div_two,
        referenceGD, beta_lt_pi_div_two.not_ge, lateSwitch_lt_pi_div_two.not_ge,
        gLateD_pi_div_two]] at h
  simpa [coordDot, unitNormal] using h

theorem fBoundary_below_companion_support {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) (Real.pi / 2)) (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    coordDot (fBoundary s) (unitNormal (t + Real.pi / 2)) ≤ referenceG t := by
  rw [coordDot_fBoundary]
  refine ((supportProjection_le_of_le continuous_referenceF continuous_referenceFD
    (fun x => (hasDerivAt_referenceF x).hasDerivWithinAt) hasDerivWithinAt_referenceFD_right
    (fun x hx => referenceF_right_curvature_nonneg ⟨hs.1.trans hx.1, hx.2⟩) hs.2
    (by linarith [ht.1]) (by linarith [ht.2, hs.1])).trans ?_).trans
    (gBoundary_below_companion_support ⟨le_rfl, by linarith [Real.pi_pos]⟩ ht)
  -- the top face joins the two arcs
  rw [← coordDot_fBoundary, fBoundary_pi_div_two, gBoundary_zero]
  simp only [coordDot, unitNormal, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
  linarith [mul_nonneg A_pos.le
    (Real.sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2, Real.pi_pos]))]

theorem gBoundary_below_first_support {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) (Real.pi / 2)) (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    coordDot (gBoundary s) (unitNormal t) ≤ referenceF t := by
  rw [coordDot_gBoundary]
  refine ((supportProjection_le_of_ge continuous_referenceG continuous_referenceGD
    (fun x => (hasDerivAt_referenceG x).hasDerivWithinAt) hasDerivWithinAt_referenceGD_right
    (fun x hx => referenceG_right_curvature_nonneg ⟨hx.1, hx.2.trans hs.2⟩) hs.1
    (by linarith [ht.2]) (by linarith [ht.1, hs.2])).trans ?_).trans
    (fBoundary_below_first_support ⟨by linarith [Real.pi_pos], le_rfl⟩ ht)
  rw [← coordDot_gBoundary, gBoundary_zero, fBoundary_pi_div_two]
  simp only [coordDot, unitNormal]
  linarith [mul_nonneg A_pos.le
    (Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)]

/-- A point above the midline lies in the hull once it satisfies the upper constraints:
reflection decreases every upward coordinate pairing. -/
private theorem mem_referenceHull_of_upper {p : Plane} (hp : 1 / 2 ≤ p.2)
    (h : ∀ s ∈ Icc (0 : ℝ) (Real.pi / 2), p ∈ upperHalfPlanes s) : p ∈ referenceHull := by
  refine (mem_referenceHull_iff p).2 fun s hs => ⟨h s hs, ?_⟩
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi hs.1 (by linarith [hs.2, Real.pi_pos])
  have hcos := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hs.1, Real.pi_pos], hs.2⟩
  obtain ⟨h1, h2⟩ := h s hs
  simp only [upperHalfPlanes, mem_ofPred_eq, coordDot, reflect, unitNormal,
    Real.cos_add_pi_div_two, Real.sin_add_pi_div_two] at h1 h2 ⊢
  constructor <;> linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * p.2 - 1) hsin,
    mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * p.2 - 1) hcos]

theorem fBoundary_mem_referenceHull {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : fBoundary t ∈ referenceHull :=
  mem_referenceHull_of_upper (fBoundary_above_midline ht) fun _ hs =>
    ⟨fBoundary_below_first_support ht hs, fBoundary_below_companion_support ht hs⟩

theorem gBoundary_mem_referenceHull {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : gBoundary t ∈ referenceHull :=
  mem_referenceHull_of_upper (gBoundary_above_midline ht) fun _ hs =>
    ⟨gBoundary_below_first_support ht hs, gBoundary_below_companion_support ht hs⟩

/-- Every prescribed first-quarter support value is attained in the concrete intersection. -/
theorem angleSupport_referenceHull_eq_f {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    angleSupport referenceHull t = referenceF t :=
  (angleSupport_referenceHull_le_f ht).antisymm <| (coordDot_fBoundary_self t).symm.trans_le
    (coordDot_le_support isCompact_referenceHull (fBoundary_mem_referenceHull ht) _)

/-- Every companion-quarter value is attained by the second explicit arc. -/
theorem angleSupport_referenceHull_eq_g {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    angleSupport referenceHull (t + Real.pi / 2) = referenceG t :=
  (angleSupport_referenceHull_le_g ht).antisymm <| (coordDot_gBoundary_self t).symm.trans_le
    (coordDot_le_support isCompact_referenceHull (gBoundary_mem_referenceHull ht) _)

theorem angleSupport_referenceCap_eq_f {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    angleSupport referenceCap t = referenceF t :=
  (angleSupport_referenceCap (Real.sin_nonneg_of_nonneg_of_le_pi ht.1
    (by linarith [ht.2, Real.pi_pos]))).trans (angleSupport_referenceHull_eq_f ht)

theorem angleSupport_referenceCap_eq_g {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    angleSupport referenceCap (t + Real.pi / 2) = referenceG t :=
  (angleSupport_referenceCap (t := t + Real.pi / 2) (Real.sin_add_pi_div_two t ▸
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)).trans
    (angleSupport_referenceHull_eq_g ht)

end AmbidextrousSofa.Reference
