module

public import AmbidextrousSofa.Reference.Hull

@[expose] public section

/-!
# Realization of the displayed reference support

The boundary points are defined by `h μ + h' ν`. Their scalar projections
have right derivative `(h + h'') sin (φ - t)`. The right-derivative fundamental
theorem of calculus controls these projections even at the two curvature
jumps. The first upper arc meets the companion constraints through the actual
horizontal top face, and reflection supplies the lower half-plane constraints.
The second arc is the mirror image of the first about the center abscissa.

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

/-- Right derivatives of a three-phase join that is continuous at both switches: at each
switch the right-hand phase gives the derivative. -/
theorem hasDerivWithinAt_phases_right {p q r pD qD rD : ℝ → ℝ}
    (hp : ∀ x, HasDerivAt p (pD x) x) (hq : ∀ x, HasDerivAt q (qD x) x)
    (hr : ∀ x, HasDerivAt r (rD x) x) (h₁ : p beta = q beta)
    (h₂ : q lateSwitch = r lateSwitch) (t : ℝ) :
    HasDerivWithinAt (fun t => if t ≤ beta then p t else if t ≤ lateSwitch then q t else r t)
      (if t < beta then pD t else if t < lateSwitch then qD t else rD t) (Ioi t) t := by
  simp only [phases_eq_right h₁ h₂]
  split_ifs with ha hb
  · refine (hp t).hasDerivWithinAt.congr_of_eventuallyEq ?_ (ite_eq_left ha)
    filter_upwards [mem_nhdsWithin_of_mem_nhds (eventually_lt_nhds ha)] with s hs
    rw [ite_eq_left hs]
  · refine (hq t).hasDerivWithinAt.congr_of_eventuallyEq ?_
      (by rw [ite_eq_right ha, ite_eq_left hb])
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (eventually_lt_nhds hb)]
      with s hs hs'
    rw [ite_eq_right fun h => ha (hs.out.trans h), ite_eq_left hs']
  · refine (hr t).hasDerivWithinAt.congr_of_eventuallyEq ?_
      (by rw [ite_eq_right ha, ite_eq_right hb])
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [ite_eq_right fun h => ha (hs.out.trans h), ite_eq_right fun h => hb (hs.out.trans h)]

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

/-- Projection decreases once a nonnegative-curvature arc has passed its normal: it increases
toward the opposite normal `φ + π`. -/
theorem supportProjection_le_of_ge {h hD hDD : ℝ → ℝ} {a b φ : ℝ}
    (hh : Continuous h) (hhD : Continuous hD)
    (hderiv : ∀ x, HasDerivWithinAt h (hD x) (Ioi x) x)
    (hsecond : ∀ x, HasDerivWithinAt hD (hDD x) (Ioi x) x)
    (hcurv : ∀ x ∈ Icc a b, 0 ≤ h x + hDD x)
    (hab : a ≤ b) (hφa : φ ≤ a) (hbφ : b - φ ≤ Real.pi) :
    supportProjection h hD φ b ≤ supportProjection h hD φ a := by
  have key := supportProjection_le_of_le hh hhD hderiv hsecond hcurv hab (φ := φ + Real.pi)
    (by linarith) (by linarith)
  simp only [supportProjection, add_sub_right_comm, Real.cos_add_pi, Real.sin_add_pi] at key ⊢
  linarith

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

theorem hasDerivWithinAt_referenceFD_right :
    ∀ t, HasDerivWithinAt referenceFD (referenceFSecond t) (Ioi t) t := by
  refine hasDerivWithinAt_phases_right (fun x => ?_) (fun x => ?_) (fun x => ?_)
    fD_matching_first fD_matching_last
  · exact ((Real.hasDerivAt_sin x).neg.add
      ((Real.hasDerivAt_cos x).const_mul (1 / 2))).congr_deriv (by ring)
  · exact ((((hasDerivAt_middlePhaseAngle x).sin.const_mul (-(R / 2))).sub
      ((Real.hasDerivAt_sin x).const_mul k)).add
      ((Real.hasDerivAt_cos x).const_mul (1 / 2))).congr_deriv (by ring)
  · exact (((Real.hasDerivAt_sin x).const_mul (-(1 - 2 / 3 * A))).add
      ((Real.hasDerivAt_cos x).const_mul (1 / 2))).congr_deriv (by ring)

theorem hasDerivWithinAt_referenceGD_right :
    ∀ t, HasDerivWithinAt referenceGD (referenceGSecond t) (Ioi t) t := by
  refine hasDerivWithinAt_phases_right (fun x => ?_) (fun x => ?_) (fun x => ?_)
    gD_matching_first gD_matching_last
  · exact (((Real.hasDerivAt_cos x).const_mul (2 * A - 1)).sub
      ((Real.hasDerivAt_sin x).const_mul (1 / 2))).congr_deriv (by ring)
  · exact ((((hasDerivAt_middlePhaseAngle x).cos.const_mul (R / 2)).sub
      ((Real.hasDerivAt_cos x).const_mul k)).sub
      ((Real.hasDerivAt_sin x).const_mul (1 / 2))).congr_deriv (by ring)
  · exact (((Real.hasDerivAt_cos x).const_mul (8 / 3 * A - 1)).sub
      ((Real.hasDerivAt_sin x).const_mul (1 / 2))).congr_deriv (by ring)

/-- The right curvature radius `h + h''` of the first support lies in `[0, 1)`. -/
theorem referenceF_right_curvature (t : ℝ) :
    0 ≤ referenceF t + referenceFSecond t ∧ referenceF t + referenceFSecond t < 1 := by
  rw [referenceF_eq_right_phases, referenceFSecond]
  split_ifs with h₁ h₂
  · simp only [fEarly]; ring_nf; norm_num
  · obtain ⟨h₃, h₄, -⟩ := middlePhase_bounds (not_lt.1 h₁) h₂.le
    simp only [fMiddle]; constructor <;> linarith
  · simp only [fLate]; ring_nf; norm_num

/-- The right curvature radius of the companion support is at most one. -/
theorem referenceG_right_curvature_le_one (t : ℝ) : referenceG t + referenceGSecond t ≤ 1 := by
  rw [referenceG_eq_right_phases, referenceGSecond]
  split_ifs with h₁ h₂
  · simp only [gEarly]; ring_nf; norm_num
  · have := (middlePhase_bounds (not_lt.1 h₁) h₂.le).2.2
    simp only [gMiddle]; linarith
  · simp only [gLate]; ring_nf; norm_num

/-- The actual first upper boundary arc. -/
def fBoundary (t : ℝ) : Plane := supportPoint referenceF referenceFD t

/-- The actual second upper boundary arc. -/
def gBoundary (t : ℝ) : Plane := companionSupportPoint referenceG referenceGD t

theorem coordDot_fBoundary (φ t : ℝ) :
    coordDot (fBoundary t) (unitNormal φ) = supportProjection referenceF referenceFD φ t :=
  coordDot_supportPoint referenceF referenceFD φ t

theorem coordDot_fBoundary_self (t : ℝ) :
    coordDot (fBoundary t) (unitNormal t) = referenceF t := by
  rw [coordDot_fBoundary, supportProjection_self]

theorem coordDot_gBoundary_self (t : ℝ) :
    coordDot (gBoundary t) (unitNormal (t + Real.pi / 2)) = referenceG t := by
  rw [gBoundary, coordDot_companionSupportPoint, add_sub_cancel_right, supportProjection_self]

theorem fBoundary_pi_div_two : fBoundary (Real.pi / 2) = (1 - 2 / 3 * A, 1) := by
  simp [fBoundary, supportPoint, referenceF_pi_div_two, referenceFD_pi_div_two]

/-- Mirroring about the center abscissa exchanges the two half-plane families at
complementary angles. -/
theorem mirror_mem_upperHalfPlanes {p : Plane} {t : ℝ} :
    (2 * k - p.1, p.2) ∈ upperHalfPlanes t ↔ p ∈ upperHalfPlanes (Real.pi / 2 - t) := by
  simp only [upperHalfPlanes, mem_ofPred_eq, coordDot, unitNormal, Real.cos_add_pi_div_two,
    Real.sin_add_pi_div_two, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub,
    referenceF_complement, referenceG_complement]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- The hull is symmetric about the vertical line through its center. -/
theorem mirror_mem_referenceHull (p : Plane) :
    (2 * k - p.1, p.2) ∈ referenceHull ↔ p ∈ referenceHull := by
  have key (q : Plane) (hq : q ∈ referenceHull) : (2 * k - q.1, q.2) ∈ referenceHull := by
    refine (mem_referenceHull_iff _).2 fun t ht => ?_
    obtain ⟨h₁, h₂⟩ := (mem_referenceHull_iff q).1 hq (Real.pi / 2 - t)
      ⟨by linarith [ht.2], by linarith [ht.1]⟩
    exact ⟨mirror_mem_upperHalfPlanes.2 h₁, mirror_mem_upperHalfPlanes.2 h₂⟩
  exact ⟨fun h => by simpa using key _ h, key p⟩

/-- The second arc is the mirror image of the first about the center abscissa `k`. -/
theorem gBoundary_eq_mirror (t : ℝ) :
    gBoundary t = (2 * k - (fBoundary (Real.pi / 2 - t)).1, (fBoundary (Real.pi / 2 - t)).2) := by
  have hG := referenceG_complement (Real.pi / 2 - t)
  have hGD := referenceGD_complement (Real.pi / 2 - t)
  rw [sub_sub_cancel, Real.cos_pi_div_two_sub] at hG
  rw [sub_sub_cancel, Real.sin_pi_div_two_sub] at hGD
  simp only [gBoundary, fBoundary, companionSupportPoint, supportPoint, rotate, hG, hGD,
    Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]
  ext <;> [linear_combination 2 * k * Real.sin_sq_add_cos_sq t; ring]

theorem fBoundary_below_first_support {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) (Real.pi / 2)) (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    coordDot (fBoundary s) (unitNormal t) ≤ referenceF t := by
  rw [coordDot_fBoundary]
  exact supportProjection_le_self continuous_referenceF continuous_referenceFD
    (fun x => (hasDerivAt_referenceF x).hasDerivWithinAt)
    hasDerivWithinAt_referenceFD_right (fun x _ => (referenceF_right_curvature x).1)
    (by linarith [Real.pi_pos]) hs ht

theorem fBoundary_above_midline {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : 1 / 2 ≤ (fBoundary t).2 := by
  have h := supportProjection_le_of_le continuous_referenceF continuous_referenceFD
    (fun x => (hasDerivAt_referenceF x).hasDerivWithinAt) hasDerivWithinAt_referenceFD_right
    (fun x _ => (referenceF_right_curvature x).1) ht.1 ht.2 (by linarith [Real.pi_pos])
  rw [← coordDot_fBoundary, ← coordDot_fBoundary, show fBoundary 0 = (1, 1 / 2) by
    simp [fBoundary, supportPoint, referenceF_zero, referenceFD_zero]] at h
  simpa [coordDot, unitNormal] using h

theorem fBoundary_below_companion_support {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) (Real.pi / 2)) (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    coordDot (fBoundary s) (unitNormal (t + Real.pi / 2)) ≤ referenceG t := by
  -- The arc rises to the right end of the top face, whose mirror image, the left end,
  -- lies below the companion support line.
  have h := fBoundary_below_first_support (s := Real.pi / 2) ⟨by positivity, le_rfl⟩
    (t := Real.pi / 2 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  rw [fBoundary_pi_div_two, referenceF_complement] at h
  rw [coordDot_fBoundary]
  refine (supportProjection_le_of_le continuous_referenceF continuous_referenceFD
    (fun x => (hasDerivAt_referenceF x).hasDerivWithinAt) hasDerivWithinAt_referenceFD_right
    (fun x _ => (referenceF_right_curvature x).1) hs.2 (by linarith [ht.1])
    (by linarith [ht.2, hs.1])).trans ?_
  rw [← coordDot_fBoundary, fBoundary_pi_div_two]
  simp only [coordDot, unitNormal, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two,
    Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub, k] at h ⊢
  linarith [mul_nonneg A_pos.le
    (Real.sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2, Real.pi_pos]))]

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
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : gBoundary t ∈ referenceHull := by
  rw [gBoundary_eq_mirror, mirror_mem_referenceHull]
  exact fBoundary_mem_referenceHull ⟨by linarith [ht.2], by linarith [ht.1]⟩

/-- Every prescribed first-quarter support value is attained in the concrete intersection. -/
theorem angleSupport_referenceHull_eq_f {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    angleSupport referenceHull t = referenceF t :=
  support_eq_of_mem isCompact_referenceHull (fun p hp => ((mem_referenceHull_iff p).1 hp t ht).1.1)
    (fBoundary_mem_referenceHull ht) (coordDot_fBoundary_self t)

/-- Every companion-quarter value is attained by the second explicit arc. -/
theorem angleSupport_referenceHull_eq_g {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    angleSupport referenceHull (t + Real.pi / 2) = referenceG t :=
  support_eq_of_mem isCompact_referenceHull (fun p hp => ((mem_referenceHull_iff p).1 hp t ht).1.2)
    (gBoundary_mem_referenceHull ht) (coordDot_gBoundary_self t)

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
