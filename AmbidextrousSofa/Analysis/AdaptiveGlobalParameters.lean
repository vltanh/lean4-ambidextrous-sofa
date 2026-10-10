module

public import AmbidextrousSofa.Analysis.AdaptiveGlobalBranches
public import AmbidextrousSofa.Reference.Support

@[expose] public section

/-!
# Parameters for a complete stationary family of competitive widths

The switching angle ranges over `[0, pi/4]`. Its two contacts enclose the
fully active middle phase. The resulting widths cover the interval from
`sqrt 2 / 2` to the beginning of the explicit large-width branch.
-/

noncomputable section

open Set
open scoped Topology

namespace AmbidextrousSofa.Analysis

def familyCot (b : ℝ) : ℝ := Real.cos (tailPhase b) / Real.sin (tailPhase b)

def familyWidth (b : ℝ) : ℝ :=
  (Real.sin b + 2 * familyCot b * Real.cos b) / 3

def familyEndpoint (b : ℝ) : ℝ :=
  1 / 2 - Real.cos b / 2 + familyCot b * Real.sin b

def familyRadius (b : ℝ) : ℝ := 2 / (3 * Real.sin (tailPhase b))

def familySineCoefficient (b : ℝ) : ℝ :=
  1 / 2 - Real.cos b / 6 + familyCot b * Real.sin b / 3

def familyLateSwitch (b : ℝ) : ℝ := Real.pi / 2 - b

/-- The elementary scalar value to be identified with the actual
integral of the stationary family. -/
def familyScore (b : ℝ) : ℝ :=
  ((2 * familyEndpoint b - 1) * (familyWidth b + Real.sin b) +
    3 * familyWidth b * Real.cos b + b - 2) / 2

theorem family_phase_bounds {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    0 < tailPhase b ∧ tailPhase b ≤ Real.pi / 4 := by
  unfold tailPhase tailAngle0
  constructor <;> linarith [hb.1, hb.2, Real.pi_pos]

theorem sin_family_phase_pos {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    0 < Real.sin (tailPhase b) :=
  Real.sin_pos_of_pos_of_lt_pi (family_phase_bounds hb).1
    (by linarith [(family_phase_bounds hb).2, Real.pi_pos])

theorem sin_le_cos_on_first_eighth {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    Real.sin t ≤ Real.cos t := by
  rw [← Real.sin_pi_div_two_sub]
  apply Real.sin_le_sin_of_le_of_le_pi_div_two
  · linarith [ht.1, Real.pi_pos]
  · linarith [ht.1]
  · linarith [ht.2]

theorem one_le_familyCot {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    1 ≤ familyCot b := by
  apply (le_div_iff₀ (sin_family_phase_pos hb)).2
  simpa only [one_mul] using
    sin_le_cos_on_first_eighth ⟨(family_phase_bounds hb).1.le, (family_phase_bounds hb).2⟩

theorem familyCot_pos {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    0 < familyCot b := lt_of_lt_of_le (by norm_num) (one_le_familyCot hb)

theorem familyCot_mul_sin_le_cos {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyCot b * Real.sin b ≤ Real.cos b := by
  have hangle : 0 ≤ tailPhase b - b ∧ tailPhase b - b ≤ Real.pi := by
    unfold tailPhase tailAngle0
    constructor <;> linarith [hb.1, hb.2, Real.pi_pos]
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi hangle.1 hangle.2
  rw [Real.sin_sub] at hsin
  unfold familyCot
  apply (mul_le_mul_iff_right₀ (sin_family_phase_pos hb)).mp
  have hc : Real.sin (tailPhase b) *
      (Real.cos (tailPhase b) / Real.sin (tailPhase b) * Real.sin b) =
        Real.cos (tailPhase b) * Real.sin b := by
    field_simp [ne_of_gt (sin_family_phase_pos hb)]
  rw [hc]
  nlinarith

theorem one_le_cos_add_half_sin {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    1 ≤ Real.cos t + Real.sin t / 2 := by
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi ht.1
    (by linarith [ht.2, Real.pi_pos])
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2, Real.pi_pos]⟩
  have hcross := mul_nonneg hs (sub_nonneg.mpr (sin_le_cos_on_first_eighth ht))
  by_contra h
  have hlt : Real.cos t + Real.sin t / 2 < 1 := lt_of_not_ge h
  have hprod := mul_pos (sub_pos.mpr hlt)
    (show 0 < 1 + (Real.cos t + Real.sin t / 2) by linarith)
  nlinarith [Real.sin_sq_add_cos_sq t, sq_nonneg (Real.sin t)]

theorem familyRadius_pos {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    0 < familyRadius b := by
  unfold familyRadius
  exact div_pos (by norm_num) (mul_pos (by norm_num) (sin_family_phase_pos hb))

theorem familyRadius_mul_sin {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyRadius b * Real.sin (tailPhase b) = 2 / 3 := by
  unfold familyRadius
  field_simp [ne_of_gt (sin_family_phase_pos hb)]

theorem familyRadius_mul_cos {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyRadius b * Real.cos (tailPhase b) = 2 / 3 * familyCot b := by
  unfold familyRadius familyCot
  field_simp [ne_of_gt (sin_family_phase_pos hb)]
  <;> ring

theorem family_width_endpoint_rotation (b : ℝ) :
    3 / 2 * familyWidth b * Real.sin b -
        (familyEndpoint b - 1 / 2) * Real.cos b = 1 / 2 ∧
      3 / 2 * familyWidth b * Real.cos b +
        (familyEndpoint b - 1 / 2) * Real.sin b = familyCot b := by
  have hs := Real.sin_sq_add_cos_sq b
  have hscaled := congrArg (fun x : ℝ => familyCot b * x) hs
  unfold familyWidth familyEndpoint
  constructor
  · nlinarith
  · nlinarith [hscaled]

theorem family_switch_order {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    b ≤ familyLateSwitch b := by
  unfold familyLateSwitch
  linarith [hb.2]

theorem hasDerivAt_familyCot {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    HasDerivAt familyCot (-(1 + familyCot b ^ 2) / 2) b := by
  apply (((hasDerivAt_tailPhase b).cos).div ((hasDerivAt_tailPhase b).sin)
    (ne_of_gt (sin_family_phase_pos hb))).congr_deriv
  unfold familyCot
  field_simp [ne_of_gt (sin_family_phase_pos hb)]
  <;> ring

theorem hasDerivAt_familyWidth {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    HasDerivAt familyWidth
      (-(familyCot b * (familyCot b * Real.cos b + 2 * Real.sin b)) / 3) b := by
  apply (((Real.hasDerivAt_sin b).add
    (((hasDerivAt_familyCot hb).const_mul 2).mul (Real.hasDerivAt_cos b))).div_const 3).congr_deriv
  ring

theorem continuousOn_familyWidth :
    ContinuousOn familyWidth (Icc (0 : ℝ) (Real.pi / 4)) :=
  fun _ hb => (hasDerivAt_familyWidth hb).continuousAt.continuousWithinAt

theorem familyWidth_zero :
    familyWidth 0 = 2 / 3 * (Real.cos tailAngle0 / Real.sin tailAngle0) := by
  simp only [familyWidth, familyCot, tailPhase_zero, Real.sin_zero, Real.cos_zero]
  ring

theorem familyWidth_pi_div_four : familyWidth (Real.pi / 4) = Real.sqrt 2 / 2 := by
  have hphase : tailPhase (Real.pi / 4) = Real.pi / 4 := by
    unfold tailPhase tailAngle0
    ring
  have hsqrt : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  unfold familyWidth familyCot
  rw [hphase, Real.sin_pi_div_four, Real.cos_pi_div_four]
  field_simp [hsqrt]
  <;> ring

theorem familyWidth_pi_div_four_lt_four_fifths :
    familyWidth (Real.pi / 4) < 4 / 5 := by
  rw [familyWidth_pi_div_four]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]

/-- Every width between the small endpoint and the tail has an actual
switching parameter; this is the ordinary intermediate value theorem. -/
theorem exists_familyWidth {a : ℝ} (ha : 4 / 5 ≤ a) (htail : a ≤ familyWidth 0) :
    ∃ b ∈ Icc (0 : ℝ) (Real.pi / 4), familyWidth b = a := by
  have hmem : a ∈ Icc (familyWidth (Real.pi / 4)) (familyWidth 0) :=
    ⟨(familyWidth_pi_div_four_lt_four_fifths.le).trans ha, htail⟩
  exact intermediate_value_Icc' (by linarith [Real.pi_pos]) continuousOn_familyWidth hmem

end AmbidextrousSofa.Analysis
