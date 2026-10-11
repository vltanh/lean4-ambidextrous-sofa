module

public import AmbidextrousSofa.Reference.Parameters

@[expose] public section

/-!
# The explicit three-phase reference support formulas

These are the two upper-quarter coordinate functions of the reference support. Each smooth
phase has actual first and second derivative certificates. The interfaces match
in value and first derivative by the cubic-derived identities in `Parameters`.
The file does not assert that the periodic extension is the support of a
convex body or that its swept-corridor envelope is feasible.
-/

noncomputable section

open Set
open scoped Topology

namespace AmbidextrousSofa.Reference

def fEarly (t : ℝ) : ℝ := Real.cos t + 1 / 2 * Real.sin t

def gEarly (t : ℝ) : ℝ := (2 * A - 1) * Real.sin t + 1 / 2 * Real.cos t + 1 / 2

def fMiddle (t : ℝ) : ℝ :=
  R * Real.cos (t / 2 + Real.pi / 8) + k * Real.cos t + 1 / 2 * Real.sin t

def gMiddle (t : ℝ) : ℝ :=
  R * Real.sin (t / 2 + Real.pi / 8) - k * Real.sin t + 1 / 2 * Real.cos t

def fLate (t : ℝ) : ℝ :=
  (1 - 2 / 3 * A) * Real.cos t + 1 / 2 * Real.sin t + 1 / 2

def gLate (t : ℝ) : ℝ := (8 / 3 * A - 1) * Real.sin t + 1 / 2 * Real.cos t

def fEarlyD (t : ℝ) : ℝ := -Real.sin t + 1 / 2 * Real.cos t

def gEarlyD (t : ℝ) : ℝ := (2 * A - 1) * Real.cos t - 1 / 2 * Real.sin t

def fMiddleD (t : ℝ) : ℝ :=
  -(R / 2) * Real.sin (t / 2 + Real.pi / 8) - k * Real.sin t + 1 / 2 * Real.cos t

def gMiddleD (t : ℝ) : ℝ :=
  R / 2 * Real.cos (t / 2 + Real.pi / 8) - k * Real.cos t - 1 / 2 * Real.sin t

def fLateD (t : ℝ) : ℝ := -(1 - 2 / 3 * A) * Real.sin t + 1 / 2 * Real.cos t

def gLateD (t : ℝ) : ℝ := (8 / 3 * A - 1) * Real.cos t - 1 / 2 * Real.sin t

/-- The first upper-quarter support coordinate; interface values are proved below. -/
def referenceF (t : ℝ) : ℝ :=
  if t ≤ beta then fEarly t else if t ≤ lateSwitch then fMiddle t else fLate t

/-- The companion upper-quarter support coordinate. -/
def referenceG (t : ℝ) : ℝ :=
  if t ≤ beta then gEarly t else if t ≤ lateSwitch then gMiddle t else gLate t

/-- The derivative selected from the same three phases. -/
def referenceFD (t : ℝ) : ℝ :=
  if t ≤ beta then fEarlyD t else if t ≤ lateSwitch then fMiddleD t else fLateD t

/-- The companion derivative selected from the same three phases. -/
def referenceGD (t : ℝ) : ℝ :=
  if t ≤ beta then gEarlyD t else if t ≤ lateSwitch then gMiddleD t else gLateD t

/-- A binary gluing theorem proved from the two one-sided derivative statements. -/
theorem hasDerivAt_if_le (c : ℝ) {f g fD gD : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (fD x) x) (hg : ∀ x, HasDerivAt g (gD x) x)
    (hvalue : f c = g c) (hderiv : fD c = gD c) (x : ℝ) :
    HasDerivAt (fun y => if y ≤ c then f y else g y)
      (if x ≤ c then fD x else gD x) x := by
  rcases lt_trichotomy x c with hlt | rfl | hgt
  · rw [ite_eq_left hlt.le]
    exact (hf x).congr_of_eventuallyEq ((eventually_lt_nhds hlt).mono fun y hy => ite_eq_left hy.le)
  · have hright : ∀ y ∈ Ici x, (if y ≤ x then f y else g y) = g y := fun y hy => by
      split_ifs with h <;> [rw [le_antisymm h hy, hvalue]; rfl]
    rw [ite_eq_left le_rfl, ← hasDerivWithinAt_univ, ← Iic_union_Ici]
    exact ((hf x).hasDerivWithinAt.congr (fun y (hy : y ≤ x) => ite_eq_left hy)
      (ite_eq_left le_rfl)).union
      (((hg x).congr_deriv hderiv.symm).hasDerivWithinAt.congr hright (hright x le_rfl))
  · rw [ite_eq_right (not_le.mpr hgt)]
    exact (hg x).congr_of_eventuallyEq
      ((eventually_gt_nhds hgt).mono fun y hy => ite_eq_right (not_le.mpr hy))

theorem hasDerivAt_middlePhaseAngle (t : ℝ) :
    HasDerivAt (fun x : ℝ => x / 2 + Real.pi / 8) (1 / 2) t := by
  simpa only [one_div] using ((hasDerivAt_id' t).div_const 2).add_const (Real.pi / 8)

theorem hasDerivAt_fEarly (t : ℝ) : HasDerivAt fEarly (fEarlyD t) t :=
  (Real.hasDerivAt_cos t).add ((Real.hasDerivAt_sin t).const_mul (1 / 2))

theorem hasDerivAt_gEarly (t : ℝ) : HasDerivAt gEarly (gEarlyD t) t :=
  ((((Real.hasDerivAt_sin t).const_mul (2 * A - 1)).add
    ((Real.hasDerivAt_cos t).const_mul (1 / 2))).add_const (1 / 2)).congr_deriv
    (by unfold gEarlyD; ring)

theorem hasDerivAt_fMiddle (t : ℝ) : HasDerivAt fMiddle (fMiddleD t) t :=
  ((((hasDerivAt_middlePhaseAngle t).cos.const_mul R).add
    ((Real.hasDerivAt_cos t).const_mul k)).add
    ((Real.hasDerivAt_sin t).const_mul (1 / 2))).congr_deriv (by unfold fMiddleD; ring)

theorem hasDerivAt_gMiddle (t : ℝ) : HasDerivAt gMiddle (gMiddleD t) t :=
  ((((hasDerivAt_middlePhaseAngle t).sin.const_mul R).sub
    ((Real.hasDerivAt_sin t).const_mul k)).add
    ((Real.hasDerivAt_cos t).const_mul (1 / 2))).congr_deriv (by unfold gMiddleD; ring)

theorem hasDerivAt_fLate (t : ℝ) : HasDerivAt fLate (fLateD t) t :=
  ((((Real.hasDerivAt_cos t).const_mul (1 - 2 / 3 * A)).add
    ((Real.hasDerivAt_sin t).const_mul (1 / 2))).add_const (1 / 2)).congr_deriv
    (by unfold fLateD; ring)

theorem hasDerivAt_gLate (t : ℝ) : HasDerivAt gLate (gLateD t) t :=
  (((Real.hasDerivAt_sin t).const_mul (8 / 3 * A - 1)).add
    ((Real.hasDerivAt_cos t).const_mul (1 / 2))).congr_deriv (by unfold gLateD; ring)

theorem hasDerivAt_fEarlyD (t : ℝ) :
    HasDerivAt fEarlyD (-Real.cos t - 1 / 2 * Real.sin t) t :=
  ((Real.hasDerivAt_sin t).neg.add ((Real.hasDerivAt_cos t).const_mul (1 / 2))).congr_deriv
    (by ring)

theorem hasDerivAt_gEarlyD (t : ℝ) :
    HasDerivAt gEarlyD (-(2 * A - 1) * Real.sin t - 1 / 2 * Real.cos t) t :=
  (((Real.hasDerivAt_cos t).const_mul (2 * A - 1)).sub
    ((Real.hasDerivAt_sin t).const_mul (1 / 2))).congr_deriv (by ring)

theorem hasDerivAt_fMiddleD (t : ℝ) :
    HasDerivAt fMiddleD
      (-(R / 4) * Real.cos (t / 2 + Real.pi / 8) -
        k * Real.cos t - 1 / 2 * Real.sin t) t :=
  ((((hasDerivAt_middlePhaseAngle t).sin.const_mul (-(R / 2))).sub
    ((Real.hasDerivAt_sin t).const_mul k)).add
    ((Real.hasDerivAt_cos t).const_mul (1 / 2))).congr_deriv (by ring)

theorem hasDerivAt_gMiddleD (t : ℝ) :
    HasDerivAt gMiddleD
      (-(R / 4) * Real.sin (t / 2 + Real.pi / 8) +
        k * Real.sin t - 1 / 2 * Real.cos t) t :=
  ((((hasDerivAt_middlePhaseAngle t).cos.const_mul (R / 2)).sub
    ((Real.hasDerivAt_cos t).const_mul k)).sub
    ((Real.hasDerivAt_sin t).const_mul (1 / 2))).congr_deriv (by ring)

theorem hasDerivAt_fLateD (t : ℝ) :
    HasDerivAt fLateD
      (-(1 - 2 / 3 * A) * Real.cos t - 1 / 2 * Real.sin t) t :=
  (((Real.hasDerivAt_sin t).const_mul (-(1 - 2 / 3 * A))).add
    ((Real.hasDerivAt_cos t).const_mul (1 / 2))).congr_deriv (by ring)

theorem hasDerivAt_gLateD (t : ℝ) :
    HasDerivAt gLateD (-(8 / 3 * A - 1) * Real.sin t - 1 / 2 * Real.cos t) t :=
  (((Real.hasDerivAt_cos t).const_mul (8 / 3 * A - 1)).sub
    ((Real.hasDerivAt_sin t).const_mul (1 / 2))).congr_deriv (by ring)

theorem curvature_fMiddle (t : ℝ) :
    deriv (deriv fMiddle) t + fMiddle t =
      3 / 4 * R * Real.cos (t / 2 + Real.pi / 8) := by
  rw [show deriv fMiddle = fMiddleD from funext fun x => (hasDerivAt_fMiddle x).deriv,
    (hasDerivAt_fMiddleD t).deriv, fMiddle]
  ring

theorem curvature_gMiddle (t : ℝ) :
    deriv (deriv gMiddle) t + gMiddle t =
      3 / 4 * R * Real.sin (t / 2 + Real.pi / 8) := by
  rw [show deriv gMiddle = gMiddleD from funext fun x => (hasDerivAt_gMiddle x).deriv,
    (hasDerivAt_gMiddleD t).deriv, gMiddle]
  ring

/-- The first-switch identities of `Parameters`, with `k` eliminated. -/
private theorem firstPhase_eqs :
    R * Real.cos (beta / 2 + Real.pi / 8) = 4 / 3 * A * Real.cos beta ∧
      R * Real.sin (beta / 2 + Real.pi / 8) = 2 / 3 ∧ 4 * A * Real.sin beta = 1 :=
  ⟨by rw [R_mul_cos_firstPhase, k, cosBeta]; ring, R_mul_sin_firstPhase, four_mul_A_mul_sinBeta⟩

/-- The phase angles at the second switch, reflected to the first switch. -/
private theorem lateSwitch_trig :
    Real.sin (lateSwitch / 2 + Real.pi / 8) = Real.cos (beta / 2 + Real.pi / 8) ∧
      Real.cos (lateSwitch / 2 + Real.pi / 8) = Real.sin (beta / 2 + Real.pi / 8) ∧
      Real.sin lateSwitch = Real.cos beta ∧ Real.cos lateSwitch = Real.sin beta := by
  rw [show lateSwitch / 2 + Real.pi / 8 = Real.pi / 2 - (beta / 2 + Real.pi / 8) by
    unfold lateSwitch; ring, lateSwitch]
  simp only [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub, and_self]

theorem f_matching_first : fMiddle beta = fEarly beta := by
  unfold fMiddle fEarly k; linear_combination firstPhase_eqs.1

theorem g_matching_first : gMiddle beta = gEarly beta := by
  unfold gMiddle gEarly k; linear_combination firstPhase_eqs.2.1 - firstPhase_eqs.2.2 / 6

theorem fD_matching_first : fMiddleD beta = fEarlyD beta := by
  unfold fMiddleD fEarlyD k; linear_combination firstPhase_eqs.2.2 / 3 - firstPhase_eqs.2.1 / 2

theorem gD_matching_first : gMiddleD beta = gEarlyD beta := by
  unfold gMiddleD gEarlyD k; linear_combination firstPhase_eqs.1 / 2

theorem f_matching_last : fMiddle lateSwitch = fLate lateSwitch := by
  simp only [fMiddle, fLate, k, lateSwitch_trig]
  linear_combination firstPhase_eqs.2.1 - firstPhase_eqs.2.2 / 6

theorem g_matching_last : gMiddle lateSwitch = gLate lateSwitch := by
  simp only [gMiddle, gLate, k, lateSwitch_trig]; linear_combination firstPhase_eqs.1

theorem fD_matching_last : fMiddleD lateSwitch = fLateD lateSwitch := by
  simp only [fMiddleD, fLateD, k, lateSwitch_trig]; linear_combination -firstPhase_eqs.1 / 2

theorem gD_matching_last : gMiddleD lateSwitch = gLateD lateSwitch := by
  simp only [gMiddleD, gLateD, k, lateSwitch_trig]
  linear_combination firstPhase_eqs.2.1 / 2 - firstPhase_eqs.2.2 / 3

theorem fLate_reflection (t : ℝ) :
    fLate (Real.pi / 2 - t) = gEarly t + 2 * k * Real.sin t := by
  simp only [fLate, gEarly, k, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]; ring

theorem gLate_reflection (t : ℝ) :
    gLate (Real.pi / 2 - t) = fEarly t - 2 * k * Real.cos t := by
  simp only [gLate, fEarly, k, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]; ring

theorem gMiddle_reflection (t : ℝ) :
    gMiddle (Real.pi / 2 - t) = fMiddle t - 2 * k * Real.cos t := by
  rw [gMiddle, fMiddle, show (Real.pi / 2 - t) / 2 + Real.pi / 8 =
    Real.pi / 2 - (t / 2 + Real.pi / 8) by ring]
  simp only [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]; ring

/-- The first piecewise support coordinate is differentiable at every switch as well. -/
theorem hasDerivAt_referenceF (t : ℝ) : HasDerivAt referenceF (referenceFD t) t :=
  hasDerivAt_if_le beta hasDerivAt_fEarly (hasDerivAt_if_le lateSwitch hasDerivAt_fMiddle
    hasDerivAt_fLate f_matching_last fD_matching_last)
    (by rw [ite_eq_left beta_lt_lateSwitch.le, f_matching_first])
    (by rw [ite_eq_left beta_lt_lateSwitch.le, fD_matching_first]) t

/-- The companion coordinate has the stated derivative at both joins. -/
theorem hasDerivAt_referenceG (t : ℝ) : HasDerivAt referenceG (referenceGD t) t :=
  hasDerivAt_if_le beta hasDerivAt_gEarly (hasDerivAt_if_le lateSwitch hasDerivAt_gMiddle
    hasDerivAt_gLate g_matching_last gD_matching_last)
    (by rw [ite_eq_left beta_lt_lateSwitch.le, g_matching_first])
    (by rw [ite_eq_left beta_lt_lateSwitch.le, gD_matching_first]) t

/-- The actual piecewise coordinate is continuous, including both joins. -/
theorem continuous_referenceF : Continuous referenceF :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_referenceF t).continuousAt

/-- Continuity of the companion coordinate is also proved at both joins. -/
theorem continuous_referenceG : Continuous referenceG :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_referenceG t).continuousAt

/-- A three-phase join of continuous phases that agree at both switches is continuous. -/
private theorem continuous_phases {p q r : ℝ → ℝ} (hp : Continuous p) (hq : Continuous q)
    (hr : Continuous r) (h₁ : q beta = p beta) (h₂ : q lateSwitch = r lateSwitch) :
    Continuous fun t => if t ≤ beta then p t else if t ≤ lateSwitch then q t else r t :=
  hp.if_le (hq.if_le hr continuous_id continuous_const fun _ (h : _ = _) => h ▸ h₂)
    continuous_id continuous_const fun _ (h : _ = _) => by
      rw [h, ite_eq_left beta_lt_lateSwitch.le, h₁]

theorem continuous_referenceFD : Continuous referenceFD :=
  continuous_phases (by unfold fEarlyD; fun_prop) (by unfold fMiddleD; fun_prop)
    (by unfold fLateD; fun_prop) fD_matching_first fD_matching_last

theorem continuous_referenceGD : Continuous referenceGD :=
  continuous_phases (by unfold gEarlyD; fun_prop) (by unfold gMiddleD; fun_prop)
    (by unfold gLateD; fun_prop) gD_matching_first gD_matching_last

theorem referenceF_zero : referenceF 0 = 1 := by
  norm_num [referenceF, fEarly, le_of_lt beta_pos]

theorem referenceG_zero : referenceG 0 = 1 := by
  norm_num [referenceG, gEarly, le_of_lt beta_pos]

theorem referenceF_pi_div_two : referenceF (Real.pi / 2) = 1 := by
  norm_num [referenceF, fLate, not_le.mpr beta_lt_pi_div_two,
    not_le.mpr lateSwitch_lt_pi_div_two]

theorem referenceG_pi_div_two : referenceG (Real.pi / 2) = 8 / 3 * A - 1 := by
  simp [referenceG, gLate, not_le.mpr beta_lt_pi_div_two,
    not_le.mpr lateSwitch_lt_pi_div_two]

theorem fEarlyD_zero : fEarlyD 0 = 1 / 2 := by simp [fEarlyD]

theorem gLateD_pi_div_two : gLateD (Real.pi / 2) = -(1 / 2) := by simp [gLateD]

theorem fLateD_pi_div_two : fLateD (Real.pi / 2) = 2 / 3 * A - 1 := by simp [fLateD]

theorem gEarlyD_zero : gEarlyD 0 = 2 * A - 1 := by simp [gEarlyD]

/-- The exact upper margin for the cosine curvature. -/
theorem curvature_fMiddle_lt_seven_eighths {t : ℝ}
    (ht : t ∈ Set.Icc beta lateSwitch) :
    deriv (deriv fMiddle) t + fMiddle t < 7 / 8 := by
  have hcos : Real.cos (t / 2 + Real.pi / 8) ≤ Real.cos (beta / 2 + Real.pi / 8) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [beta_pos, Real.pi_pos])
      (by linarith [ht.2, lateSwitch_lt_pi_div_two, Real.pi_pos]) (by linarith [ht.1])
  have h := A_mul_cosBeta_lt_seven_eighths
  unfold cosBeta at h
  rw [curvature_fMiddle]
  linarith [mul_le_mul_of_nonneg_left hcos R_pos.le, firstPhase_eqs.1]

/-- The same exact upper margin for the reflected sine curvature. -/
theorem curvature_gMiddle_lt_seven_eighths {t : ℝ}
    (ht : t ∈ Set.Icc beta lateSwitch) :
    deriv (deriv gMiddle) t + gMiddle t < 7 / 8 := by
  have h := curvature_fMiddle_lt_seven_eighths (t := Real.pi / 2 - t)
    (by unfold lateSwitch at *; constructor <;> linarith [ht.1, ht.2])
  rwa [curvature_fMiddle, show (Real.pi / 2 - t) / 2 + Real.pi / 8 =
    Real.pi / 2 - (t / 2 + Real.pi / 8) by ring, Real.cos_pi_div_two_sub,
    ← curvature_gMiddle] at h

/-- The explicit center lies below every first-quarter reference support line. -/
theorem referenceF_ge_center {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    k * Real.cos t + 1 / 2 * Real.sin t ≤ referenceF t := by
  have hc : 0 ≤ Real.cos t :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
  have hphase : 0 < Real.cos (t / 2 + Real.pi / 8) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2, Real.pi_pos]⟩
  unfold referenceF fEarly fMiddle fLate k
  split_ifs <;> linarith [mul_nonneg A_pos.le hc, mul_pos R_pos hphase]

/-- The same point satisfies all companion upper-quarter support lines. -/
theorem referenceG_ge_center {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    -k * Real.sin t + 1 / 2 * Real.cos t ≤ referenceG t := by
  have hs : 0 ≤ Real.sin t :=
    Real.sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2, Real.pi_pos])
  have hphase : 0 < Real.sin (t / 2 + Real.pi / 8) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1, Real.pi_pos])
      (by linarith [ht.2, Real.pi_pos])
  unfold referenceG gEarly gMiddle gLate k
  split_ifs <;> linarith [mul_nonneg A_pos.le hs, mul_pos R_pos hphase]

end AmbidextrousSofa.Reference
