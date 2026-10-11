module

public import AmbidextrousSofa.Reference.Realization
public import AmbidextrousSofa.Geometry.BarrierAnalysis

@[expose] public section

/-!
# The actual reference niche

The two-wall minima have continuous positive parts at both endpoint angles.
Their compact angular maximum is the actual whole-angle niche. The explicit
phase formulas put every corner apex strictly below the horizontal midline;
compactness makes this a uniform strict bound. Complementary angles exchange
the two walls, so the niche is symmetric about the center abscissa.
-/

noncomputable section

open Set
open scoped Topology

namespace AmbidextrousSofa.Reference

/-- The actual full-turn lower niche of the realized reference hull. -/
def referenceNiche (x : ℝ) : ℝ := sweptNiche referenceHull (Real.pi / 2) x

/-- Height of the common intersection point of the two inner wall lines. -/
def referenceApexHeight (t : ℝ) : ℝ :=
  (referenceF t - 1) * Real.sin t + (referenceG t - 1) * Real.cos t

/-- The explicit positive two-wall minimum, including its zero endpoint values. -/
def referenceWallClip (x t : ℝ) : ℝ :=
  max (min ((referenceF t - 1 - x * Real.cos t) / Real.sin t)
    ((referenceG t - 1 + x * Real.sin t) / Real.cos t)) 0

theorem R_lt_sqrt_two : R < Real.sqrt 2 := by
  obtain ⟨h₁, h₂, -⟩ := middlePhase_bounds le_rfl beta_lt_lateSwitch.le
  refine Real.lt_sqrt_of_sq_lt ?_
  have hR : R ^ 2 = (R * Real.cos (beta / 2 + Real.pi / 8)) ^ 2 +
      (R * Real.sin (beta / 2 + Real.pi / 8)) ^ 2 := by
    linear_combination -R ^ 2 * Real.cos_sq_add_sin_sq (beta / 2 + Real.pi / 8)
  rw [hR, R_mul_sin_firstPhase]
  nlinarith

theorem continuous_referenceApexHeight : Continuous referenceApexHeight :=
  ((continuous_referenceF.sub continuous_const).mul Real.continuous_sin).add
    ((continuous_referenceG.sub continuous_const).mul Real.continuous_cos)

theorem referenceApexHeight_zero : referenceApexHeight 0 = 0 := by
  simp [referenceApexHeight, referenceF_zero, referenceG_zero]

theorem earlyApex_lt_half {t : ℝ} (ht : t ∈ Icc (0 : ℝ) beta) :
    (fEarly t - 1) * Real.sin t + (gEarly t - 1) * Real.cos t < 1 / 2 := by
  have hs : Real.sin t ≤ sinBeta := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [ht.1, Real.pi_pos]) beta_lt_pi_div_two.le ht.2
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [ht.1, Real.pi_pos], ht.2.trans_lt beta_lt_pi_div_two⟩
  have hA : 4 * A * Real.sin t ≤ 1 := by
    linarith [mul_le_mul_of_nonneg_left hs A_pos.le, four_mul_A_mul_sinBeta]
  rcases ht.1.eq_or_lt with rfl | ht0
  · norm_num [fEarly, gEarly]
  · have hsin : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht0
      (by linarith [ht.2, beta_lt_pi_div_two, Real.pi_pos])
    unfold fEarly gEarly
    linarith [mul_le_mul_of_nonneg_right hA hc.le, Real.sin_sq_add_cos_sq t]

/-- The middle phase oscillates faster than the enclosing first cosine lobe. -/
theorem middlePhase_sin_le_cos_center {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    Real.sin (3 / 2 * t + Real.pi / 8) ≤ Real.cos (t - Real.pi / 4) := by
  have hu : |t - Real.pi / 4| ≤ Real.pi / 4 :=
    abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  rw [show 3 / 2 * t + Real.pi / 8 = 3 / 2 * (t - Real.pi / 4) + Real.pi / 2 by ring,
    Real.sin_add_pi_div_two, ← Real.cos_abs (3 / 2 * _), ← Real.cos_abs (t - _), abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos])
    (by linarith [abs_nonneg (t - Real.pi / 4)])

theorem middleApex_lt_half {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    (fMiddle t - 1) * Real.sin t + (gMiddle t - 1) * Real.cos t < 1 / 2 := by
  have hcos : 0 < Real.cos (t - Real.pi / 4) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2, Real.pi_pos]⟩
  have hsum : Real.sin t + Real.cos t = Real.sqrt 2 * Real.cos (t - Real.pi / 4) := by
    rw [Real.cos_sub, Real.cos_pi_div_four, Real.sin_pi_div_four]
    linear_combination (-(Real.cos t + Real.sin t) / 2) * Real.sq_sqrt (zero_le_two (α := ℝ))
  have hsin : R * Real.sin (3 / 2 * t + Real.pi / 8) =
      R * Real.sin (t / 2 + Real.pi / 8) * Real.cos t +
        R * Real.cos (t / 2 + Real.pi / 8) * Real.sin t := by
    rw [show 3 / 2 * t + Real.pi / 8 = (t / 2 + Real.pi / 8) + t by ring, Real.sin_add]; ring
  unfold fMiddle gMiddle
  linarith [mul_le_mul_of_nonneg_left (middlePhase_sin_le_cos_center ht) R_pos.le,
    mul_lt_mul_of_pos_right R_lt_sqrt_two hcos, Real.sin_sq_add_cos_sq t]

theorem referenceApexHeight_lt_half {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : referenceApexHeight t < 1 / 2 := by
  -- The apex height is symmetric under `t ↦ π / 2 - t`, which maps the late phase to the
  -- early one.
  wlog hlate : t ≤ lateSwitch generalizing t
  · have h := this (t := Real.pi / 2 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
      (by unfold lateSwitch at hlate ⊢; linarith [beta_lt_pi_div_four])
    simp only [referenceApexHeight, referenceF_complement, referenceG_complement,
      Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub] at h ⊢
    linarith
  unfold referenceApexHeight referenceF referenceG
  split_ifs with hearly
  · exact earlyApex_lt_half ⟨ht.1, hearly⟩
  · exact middleApex_lt_half ht

theorem firstWall_referenceHull {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) (x : ℝ) :
    firstWall referenceHull t x =
      (referenceF t - 1 - x * Real.cos t) / Real.sin t := by
  rw [firstWall, ← angleSupport, angleSupport_referenceHull_eq_f ht]

theorem secondWall_referenceHull {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) (x : ℝ) :
    secondWall referenceHull t x =
      (referenceG t - 1 + x * Real.sin t) / Real.cos t := by
  rw [secondWall, companionNormal_eq_unitNormal, ← angleSupport,
    angleSupport_referenceHull_eq_g ht]

/-- The niche is symmetric about the center abscissa `k`. -/
theorem referenceNiche_mirror (x : ℝ) : referenceNiche (2 * k - x) = referenceNiche x := by
  have h : EqOn (fun t => cornerWall referenceHull t (2 * k - x))
      ((fun t => cornerWall referenceHull t x) ∘ (Real.pi / 2 - ·)) (Ioo 0 (Real.pi / 2)) := by
    intro t ht
    have hs : Real.pi / 2 - t ∈ Icc (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simp only [Function.comp_apply, cornerWall, firstWall_referenceHull (Ioo_subset_Icc_self ht),
      secondWall_referenceHull (Ioo_subset_Icc_self ht), firstWall_referenceHull hs,
      secondWall_referenceHull hs, referenceF_complement, referenceG_complement,
      Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
    rw [min_comm]
    congr 1 <;> ring
  unfold referenceNiche sweptNiche sweptWallValues
  rw [h.image_eq, image_comp, image_const_sub_Ioo, sub_self, sub_zero]

/-- A two-wall tent never exceeds its own apex, at any horizontal coordinate. -/
theorem cornerWall_referenceHull_le_apex {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) (x : ℝ) :
    cornerWall referenceHull t x ≤ referenceApexHeight t := by
  have hs : Real.sin t ≠ 0 := (sin_cos_pos_of_mem_quarter ht).1.ne'
  have hc : Real.cos t ≠ 0 := (sin_cos_pos_of_mem_quarter ht).2.ne'
  calc cornerWall referenceHull t x = cornerWall referenceHull t x * Real.sin t ^ 2 +
        cornerWall referenceHull t x * Real.cos t ^ 2 := by
        rw [← mul_add, Real.sin_sq_add_cos_sq, mul_one]
    _ ≤ firstWall referenceHull t x * Real.sin t ^ 2 +
        secondWall referenceHull t x * Real.cos t ^ 2 := by
        gcongr
        exacts [min_le_left _ _, min_le_right _ _]
    _ = referenceApexHeight t := by
        rw [firstWall_referenceHull ⟨ht.1.le, ht.2.le⟩,
          secondWall_referenceHull ⟨ht.1.le, ht.2.le⟩, referenceApexHeight]
        field_simp
        ring

theorem referenceNiche_nonneg (x : ℝ) : 0 ≤ referenceNiche x :=
  sweptNiche_nonneg referenceHull (Real.pi / 2) x

/-- A strict global midline margin follows from the compact apex maximum. -/
theorem referenceNiche_lt_half (x : ℝ) : referenceNiche x < 1 / 2 := by
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, hzero⟩
    continuous_referenceApexHeight.continuousOn
  refine (sweptNiche_le_of_forall (by linarith [Real.pi_pos])
    (referenceApexHeight_zero.symm.trans_le (hmax hzero)) fun s hs => ?_).trans_lt
    (referenceApexHeight_lt_half ht)
  exact (cornerWall_referenceHull_le_apex hs x).trans (hmax ⟨hs.1.le, hs.2.le⟩)

theorem referenceWallClip_zero (x : ℝ) : referenceWallClip x 0 = 0 := by
  simp [referenceWallClip, referenceF_zero, referenceG_zero]

theorem referenceWallClip_pi_div_two (x : ℝ) : referenceWallClip x (Real.pi / 2) = 0 := by
  simp [referenceWallClip, referenceF_pi_div_two]

theorem referenceWallClip_eq_actual {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) (x : ℝ) :
    referenceWallClip x t = max (cornerWall referenceHull t x) 0 := by
  rw [cornerWall, firstWall_referenceHull ht, secondWall_referenceHull ht]
  rfl

/-- A nonnegative function below a continuous function vanishing at `z` is continuous at `z`. -/
private theorem continuousAt_of_nonneg_of_le {f u : ℝ × ℝ → ℝ} {z : ℝ × ℝ}
    (hu : ContinuousAt u z) (hu0 : u z = 0) (hf0 : f z = 0) (hf : ∀ p, 0 ≤ f p)
    (hfu : ∀ p, f p ≤ u p) :
    ContinuousAt f z := by
  rw [ContinuousAt, hf0]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hu0 ▸ hu.tendsto) hf hfu

/-- At either endpoint the well-defined companion wall squeezes the positive minimum to zero. -/
theorem continuousAt_referenceWallClip {z : ℝ × ℝ}
    (hz : z.2 ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ContinuousAt (fun p : ℝ × ℝ => referenceWallClip p.1 p.2) z := by
  have hf := continuous_referenceF
  have hg := continuous_referenceG
  have hclip (p : ℝ × ℝ) : 0 ≤ referenceWallClip p.1 p.2 := le_max_right _ _
  by_cases hz0 : z.2 = 0
  · exact continuousAt_of_nonneg_of_le
      (u := fun p => max ((referenceG p.2 - 1 + p.1 * Real.sin p.2) / Real.cos p.2) 0)
      (by fun_prop (disch := simp [hz0])) (by simp [hz0, referenceG_zero])
      (by simp [hz0, referenceWallClip_zero]) hclip
      fun p => max_le_max_right 0 (min_le_right _ _)
  by_cases hzL : z.2 = Real.pi / 2
  · exact continuousAt_of_nonneg_of_le
      (u := fun p => max ((referenceF p.2 - 1 - p.1 * Real.cos p.2) / Real.sin p.2) 0)
      (by fun_prop (disch := simp [hzL])) (by simp [hzL, referenceF_pi_div_two])
      (by simp [hzL, referenceWallClip_pi_div_two]) hclip
      fun p => max_le_max_right 0 (min_le_left _ _)
  have hsin : Real.sin z.2 ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi
    (lt_of_le_of_ne hz.1 (Ne.symm hz0)) (by linarith [hz.2, Real.pi_pos])).ne'
  have hcos : Real.cos z.2 ≠ 0 := (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hz.1, Real.pi_pos], lt_of_le_of_ne hz.2 hzL⟩).ne'
  unfold referenceWallClip
  fun_prop (disch := assumption)

theorem continuous_referenceWallClip_on_angles :
    Continuous (fun p : ℝ × Icc (0 : ℝ) (Real.pi / 2) => referenceWallClip p.1 p.2) :=
  continuous_iff_continuousAt.2 fun p =>
    (continuousAt_referenceWallClip (z := (p.1, (p.2 : ℝ))) p.2.2).comp
      (f := fun q : ℝ × Icc (0 : ℝ) (Real.pi / 2) => (q.1, (q.2 : ℝ))) (by fun_prop)

/-- Closed-angle clipping has exactly the same supremum as the actual open-angle niche. -/
theorem referenceNiche_eq_sSup_clipped (x : ℝ) :
    referenceNiche x = sSup ((fun t : Icc (0 : ℝ) (Real.pi / 2) =>
      referenceWallClip x t) '' Set.univ) := by
  let zeroAngle : Icc (0 : ℝ) (Real.pi / 2) := ⟨0, le_rfl, by linarith [Real.pi_pos]⟩
  have hbounded := isCompact_univ.bddAbove_image (continuous_referenceWallClip_on_angles.comp
    (continuous_const.prodMk continuous_id) (f := fun t => (x, t))).continuousOn
  have hzero := le_csSup_of_le hbounded (mem_image_of_mem _ (mem_univ zeroAngle))
    (referenceWallClip_zero x).ge
  apply le_antisymm
  · exact sweptNiche_le_of_forall (by linarith [Real.pi_pos]) hzero fun t ht =>
      le_csSup_of_le hbounded (mem_image_of_mem _ (mem_univ ⟨t, ht.1.le, ht.2.le⟩))
        ((le_max_left _ _).trans (referenceWallClip_eq_actual ⟨ht.1.le, ht.2.le⟩ x).ge)
  · refine csSup_le ⟨_, mem_image_of_mem _ (mem_univ zeroAngle)⟩ ?_
    rintro _ ⟨⟨t, ht⟩, -, rfl⟩
    rcases ht.1.eq_or_lt with rfl | h0
    · exact (referenceWallClip_zero x).trans_le (referenceNiche_nonneg x)
    rcases ht.2.eq_or_lt with rfl | hL
    · exact (referenceWallClip_pi_div_two x).trans_le (referenceNiche_nonneg x)
    exact (referenceWallClip_eq_actual ht x).trans_le (max_le (cornerWall_le_sweptNiche
      (sweptWallValues_bddAbove isCompact_referenceHull le_rfl x) ⟨h0, hL⟩)
      (referenceNiche_nonneg x))

/-- The actual whole-angle reference niche is continuous at every horizontal coordinate. -/
theorem continuous_referenceNiche : Continuous referenceNiche := by
  rw [funext referenceNiche_eq_sSup_clipped]
  exact isCompact_univ.continuous_sSup continuous_referenceWallClip_on_angles

end AmbidextrousSofa.Reference
