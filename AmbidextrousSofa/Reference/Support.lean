module

public import AmbidextrousSofa.Reference.Parameters

@[expose] public section

/-!
# The explicit three-phase reference support formulas

These are the two upper-quarter coordinate functions of the reference support, each joined
from three explicit phases at `beta` and `lateSwitch`. The phases match in value and first
derivative by the cubic-derived identities in `Parameters`, so both coordinates are
continuously differentiable. Complementary angles exchange the two coordinates up to the
translation `2k`. The file does not assert that the periodic extension is the support of a
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

/-- The three-phase join at the two switches, for phases matching in value and derivative. -/
theorem hasDerivAt_phases {p q r pD qD rD : ℝ → ℝ} (hp : ∀ x, HasDerivAt p (pD x) x)
    (hq : ∀ x, HasDerivAt q (qD x) x) (hr : ∀ x, HasDerivAt r (rD x) x)
    (h₁ : p beta = q beta) (h₁' : pD beta = qD beta) (h₂ : q lateSwitch = r lateSwitch)
    (h₂' : qD lateSwitch = rD lateSwitch) (t : ℝ) :
    HasDerivAt (fun t => if t ≤ beta then p t else if t ≤ lateSwitch then q t else r t)
      (if t ≤ beta then pD t else if t ≤ lateSwitch then qD t else rD t) t :=
  hasDerivAt_if_le beta hp (hasDerivAt_if_le lateSwitch hq hr h₂ h₂')
    (by rwa [ite_eq_left beta_lt_lateSwitch.le]) (by rwa [ite_eq_left beta_lt_lateSwitch.le]) t

/-- A three-phase join of continuous phases that agree at both switches is continuous. -/
theorem continuous_phases {p q r : ℝ → ℝ} (hp : Continuous p) (hq : Continuous q)
    (hr : Continuous r) (h₁ : p beta = q beta) (h₂ : q lateSwitch = r lateSwitch) :
    Continuous fun t => if t ≤ beta then p t else if t ≤ lateSwitch then q t else r t :=
  hp.if_le (hq.if_le hr continuous_id continuous_const fun _ (h : _ = _) => h ▸ h₂)
    continuous_id continuous_const fun _ (h : _ = _) => by
      rw [h, ite_eq_left beta_lt_lateSwitch.le, h₁]

/-- When the phases agree at both switches, the right-hand phase may own each switch. -/
theorem phases_eq_right {p q r : ℝ → ℝ} (h₁ : p beta = q beta)
    (h₂ : q lateSwitch = r lateSwitch) (t : ℝ) :
    (if t ≤ beta then p t else if t ≤ lateSwitch then q t else r t) =
      if t < beta then p t else if t < lateSwitch then q t else r t := by
  have := beta_lt_lateSwitch
  split_ifs <;> first
    | rfl | (exfalso; linarith)
    | (rw [show t = beta by linarith]; exact h₁) | (rw [show t = lateSwitch by linarith]; exact h₂)

theorem hasDerivAt_middlePhaseAngle (t : ℝ) :
    HasDerivAt (fun x : ℝ => x / 2 + Real.pi / 8) (1 / 2) t := by
  simpa only [one_div] using ((hasDerivAt_id' t).div_const 2).add_const (Real.pi / 8)

theorem f_matching_first : fEarly beta = fMiddle beta := by
  unfold fMiddle fEarly k; linear_combination -firstSwitch_eqs.1

theorem g_matching_first : gEarly beta = gMiddle beta := by
  unfold gMiddle gEarly k; linear_combination firstSwitch_eqs.2.2 / 6 - firstSwitch_eqs.2.1

theorem fD_matching_first : fEarlyD beta = fMiddleD beta := by
  unfold fMiddleD fEarlyD k; linear_combination firstSwitch_eqs.2.1 / 2 - firstSwitch_eqs.2.2 / 3

theorem gD_matching_first : gEarlyD beta = gMiddleD beta := by
  unfold gMiddleD gEarlyD k; linear_combination -firstSwitch_eqs.1 / 2

theorem f_matching_last : fMiddle lateSwitch = fLate lateSwitch := by
  simp only [fMiddle, fLate, k, lateSwitch_trig]
  linear_combination firstSwitch_eqs.2.1 - firstSwitch_eqs.2.2 / 6

theorem g_matching_last : gMiddle lateSwitch = gLate lateSwitch := by
  simp only [gMiddle, gLate, k, lateSwitch_trig]; linear_combination firstSwitch_eqs.1

theorem fD_matching_last : fMiddleD lateSwitch = fLateD lateSwitch := by
  simp only [fMiddleD, fLateD, k, lateSwitch_trig]; linear_combination -firstSwitch_eqs.1 / 2

theorem gD_matching_last : gMiddleD lateSwitch = gLateD lateSwitch := by
  simp only [gMiddleD, gLateD, k, lateSwitch_trig]
  linear_combination firstSwitch_eqs.2.1 / 2 - firstSwitch_eqs.2.2 / 3

/-- The first piecewise support coordinate is differentiable at every switch as well. -/
theorem hasDerivAt_referenceF (t : ℝ) : HasDerivAt referenceF (referenceFD t) t :=
  hasDerivAt_phases
    (fun x => (Real.hasDerivAt_cos x).add ((Real.hasDerivAt_sin x).const_mul (1 / 2)))
    (fun x => ((((hasDerivAt_middlePhaseAngle x).cos.const_mul R).add
      ((Real.hasDerivAt_cos x).const_mul k)).add
      ((Real.hasDerivAt_sin x).const_mul (1 / 2))).congr_deriv (by unfold fMiddleD; ring))
    (fun x => ((((Real.hasDerivAt_cos x).const_mul (1 - 2 / 3 * A)).add
      ((Real.hasDerivAt_sin x).const_mul (1 / 2))).add_const (1 / 2)).congr_deriv
      (by unfold fLateD; ring))
    f_matching_first fD_matching_first f_matching_last fD_matching_last t

/-- The companion coordinate has the stated derivative at both joins. -/
theorem hasDerivAt_referenceG (t : ℝ) : HasDerivAt referenceG (referenceGD t) t :=
  hasDerivAt_phases (fun x => ((((Real.hasDerivAt_sin x).const_mul (2 * A - 1)).add
      ((Real.hasDerivAt_cos x).const_mul (1 / 2))).add_const (1 / 2)).congr_deriv
      (by unfold gEarlyD; ring))
    (fun x => ((((hasDerivAt_middlePhaseAngle x).sin.const_mul R).sub
      ((Real.hasDerivAt_sin x).const_mul k)).add
      ((Real.hasDerivAt_cos x).const_mul (1 / 2))).congr_deriv (by unfold gMiddleD; ring))
    (fun x => (((Real.hasDerivAt_sin x).const_mul (8 / 3 * A - 1)).add
      ((Real.hasDerivAt_cos x).const_mul (1 / 2))).congr_deriv (by unfold gLateD; ring))
    g_matching_first gD_matching_first g_matching_last gD_matching_last t

/-- The actual piecewise coordinate is continuous, including both joins. -/
theorem continuous_referenceF : Continuous referenceF :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_referenceF t).continuousAt

/-- Continuity of the companion coordinate is also proved at both joins. -/
theorem continuous_referenceG : Continuous referenceG :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_referenceG t).continuousAt

theorem continuous_referenceFD : Continuous referenceFD :=
  continuous_phases (by unfold fEarlyD; fun_prop) (by unfold fMiddleD; fun_prop)
    (by unfold fLateD; fun_prop) fD_matching_first fD_matching_last

theorem continuous_referenceGD : Continuous referenceGD :=
  continuous_phases (by unfold gEarlyD; fun_prop) (by unfold gMiddleD; fun_prop)
    (by unfold gLateD; fun_prop) gD_matching_first gD_matching_last

theorem referenceF_eq_right_phases (t : ℝ) :
    referenceF t = if t < beta then fEarly t else if t < lateSwitch then fMiddle t else fLate t :=
  phases_eq_right f_matching_first f_matching_last t

theorem referenceG_eq_right_phases (t : ℝ) :
    referenceG t = if t < beta then gEarly t else if t < lateSwitch then gMiddle t else gLate t :=
  phases_eq_right g_matching_first g_matching_last t

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

theorem referenceFD_zero : referenceFD 0 = 1 / 2 := by simp [referenceFD, fEarlyD, beta_pos.le]

theorem referenceGD_zero : referenceGD 0 = 2 * A - 1 := by
  simp [referenceGD, gEarlyD, beta_pos.le]

theorem referenceFD_pi_div_two : referenceFD (Real.pi / 2) = 2 / 3 * A - 1 := by
  simp [referenceFD, fLateD, not_le.mpr beta_lt_pi_div_two, not_le.mpr lateSwitch_lt_pi_div_two]

theorem referenceGD_pi_div_two : referenceGD (Real.pi / 2) = -(1 / 2) := by
  simp [referenceGD, gLateD, not_le.mpr beta_lt_pi_div_two, not_le.mpr lateSwitch_lt_pi_div_two]

/-- On the middle phase neither component of `R (cos u, sin u)`, `u = t / 2 + π / 8`, exceeds
its value `4 / 3 A cos beta < 7 / 6` at the nearer switch, and the cosine is positive. -/
theorem middlePhase_bounds {t : ℝ} (h₁ : beta ≤ t) (h₂ : t ≤ lateSwitch) :
    0 < R * Real.cos (t / 2 + Real.pi / 8) ∧ R * Real.cos (t / 2 + Real.pi / 8) < 7 / 6 ∧
      R * Real.sin (t / 2 + Real.pi / 8) < 7 / 6 := by
  have hb : R * Real.cos (beta / 2 + Real.pi / 8) < 7 / 6 := by
    have h : A * Real.cos beta < 7 / 8 := A_mul_cosBeta_lt_seven_eighths
    rw [firstSwitch_eqs.1]; linarith
  unfold lateSwitch at h₂
  have := beta_pos; have := Real.pi_pos
  refine ⟨mul_pos R_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩),
    (mul_le_mul_of_nonneg_left (Real.cos_le_cos_of_nonneg_of_le_pi (by linarith)
      (by linarith) (by linarith)) R_pos.le).trans_lt hb,
    (mul_le_mul_of_nonneg_left ?_ R_pos.le).trans_lt hb⟩
  rw [← Real.cos_pi_div_two_sub]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)

/-- Complementary angles exchange the two coordinates, up to the translation `2k`. -/
theorem referenceG_complement (t : ℝ) :
    referenceG (Real.pi / 2 - t) = referenceF t - 2 * k * Real.cos t := by
  -- With right-closed phases, the switches of `referenceG` at `π / 2 - t` are those of
  -- `referenceF` at `t`.
  have h1 : Real.pi / 2 - t < beta ↔ ¬t ≤ lateSwitch := by rw [not_le, sub_lt_comm]; rfl
  have h2 : Real.pi / 2 - t < lateSwitch ↔ ¬t ≤ beta := by
    rw [not_le, sub_lt_comm, lateSwitch, sub_sub_cancel]
  have hu : (Real.pi / 2 - t) / 2 + Real.pi / 8 = Real.pi / 2 - (t / 2 + Real.pi / 8) := by ring
  simp only [referenceG_eq_right_phases, referenceF, h1, h2]
  split_ifs <;> first
    | (exfalso; linarith [beta_lt_lateSwitch])
    | (simp only [gEarly, gMiddle, gLate, fEarly, fMiddle, fLate, k, hu, Real.sin_pi_div_two_sub,
        Real.cos_pi_div_two_sub]; ring)

theorem referenceF_complement (t : ℝ) :
    referenceF (Real.pi / 2 - t) = referenceG t + 2 * k * Real.sin t := by
  have h := referenceG_complement (Real.pi / 2 - t)
  rw [sub_sub_cancel, Real.cos_pi_div_two_sub] at h
  linarith

/-- Differentiating the complement identity relates the two derivatives. -/
theorem referenceGD_complement (t : ℝ) :
    referenceGD (Real.pi / 2 - t) = -referenceFD t - 2 * k * Real.sin t := by
  have h := ((hasDerivAt_referenceF t).sub ((Real.hasDerivAt_cos t).const_mul (2 * k)))
  have := ((hasDerivAt_referenceG (Real.pi / 2 - t)).comp t
    ((hasDerivAt_id' t).const_sub _)).unique (h.congr_of_eventuallyEq
      (.of_forall referenceG_complement))
  linarith

/-- The explicit center lies below every first-quarter reference support line. -/
theorem referenceF_ge_center {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    k * Real.cos t + 1 / 2 * Real.sin t ≤ referenceF t := by
  have hc : 0 ≤ Real.cos t :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
  have hphase : 0 < Real.cos (t / 2 + Real.pi / 8) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2, Real.pi_pos]⟩
  unfold referenceF fEarly fMiddle fLate k
  split_ifs <;> linarith [mul_nonneg A_pos.le hc, mul_pos R_pos hphase]

/-- By the complement identity, the same point satisfies all companion support lines. -/
theorem referenceG_ge_center {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    -k * Real.sin t + 1 / 2 * Real.cos t ≤ referenceG t := by
  have h := referenceF_ge_center (t := Real.pi / 2 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  rw [referenceF_complement, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub] at h
  linarith

end AmbidextrousSofa.Reference
