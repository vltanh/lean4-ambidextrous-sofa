module

public import AmbidextrousSofa.Reference.Realization
public import AmbidextrousSofa.Geometry.BarrierAnalysis

@[expose] public section

/-!
# The actual reference niche

The two-wall minima have continuous positive parts at both endpoint angles.
Their compact angular maximum is the actual whole-angle niche. The explicit
phase formulas put every corner apex strictly below the horizontal midline;
compactness makes this a uniform strict bound.
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

theorem R_sq_eq_matching_components :
    R ^ 2 = (4 / 3 * (A * cosBeta)) ^ 2 + (2 / 3 : ℝ) ^ 2 := by
  have hcos : R * Real.cos (beta / 2 + Real.pi / 8) = 4 / 3 * (A * cosBeta) := by
    rw [R_mul_cos_firstPhase]
    unfold k
    ring
  calc
    R ^ 2 = (R * Real.cos (beta / 2 + Real.pi / 8)) ^ 2 +
        (R * Real.sin (beta / 2 + Real.pi / 8)) ^ 2 := by
      calc
        _ = R ^ 2 * (Real.cos (beta / 2 + Real.pi / 8) ^ 2 +
            Real.sin (beta / 2 + Real.pi / 8) ^ 2) := by
          rw [Real.cos_sq_add_sin_sq, mul_one]
        _ = _ := by ring
    _ = _ := by rw [hcos, R_mul_sin_firstPhase]

theorem R_sq_lt_sixty_five_over_thirty_six : R ^ 2 < 65 / 36 := by
  have hAc : 0 < A * cosBeta := mul_pos A_pos cosBeta_pos
  have hsq := mul_pos (sub_pos.mpr A_mul_cosBeta_lt_seven_eighths)
    (show 0 < 7 / 8 + A * cosBeta by linarith)
  rw [R_sq_eq_matching_components]
  nlinarith

theorem R_lt_sqrt_two : R < Real.sqrt 2 := by
  apply (sq_lt_sq₀ R_pos.le (Real.sqrt_nonneg 2)).mp
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  linarith [R_sq_lt_sixty_five_over_thirty_six]

theorem continuous_referenceApexHeight : Continuous referenceApexHeight := by
  have hf := continuous_referenceF
  have hg := continuous_referenceG
  unfold referenceApexHeight
  fun_prop

theorem referenceApexHeight_zero : referenceApexHeight 0 = 0 := by
  simp [referenceApexHeight, referenceF_zero, referenceG_zero]

theorem earlyApex_lt_half {t : ℝ} (ht : t ∈ Icc (0 : ℝ) beta) :
    (fEarly t - 1) * Real.sin t + (gEarly t - 1) * Real.cos t < 1 / 2 := by
  have hs : Real.sin t ≤ sinBeta :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [ht.1, Real.pi_pos]) beta_lt_pi_div_two.le ht.2
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [ht.1, Real.pi_pos], ht.2.trans_lt beta_lt_pi_div_two⟩
  have hA : 2 * A * Real.sin t ≤ 1 / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * A by linarith [A_pos]),
      four_mul_A_mul_sinBeta]
  by_cases ht0 : t = 0
  · subst t
    norm_num [fEarly, gEarly]
  · have hsin : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi
      (lt_of_le_of_ne ht.1 (Ne.symm ht0))
      (by linarith [ht.2, beta_lt_pi_div_two, Real.pi_pos])
    have hproduct := mul_le_mul_of_nonneg_right hA hc.le
    unfold fEarly gEarly
    nlinarith [Real.sin_sq_add_cos_sq t]

theorem lateApex_lt_half {t : ℝ} (ht : t ∈ Icc lateSwitch (Real.pi / 2)) :
    (fLate t - 1) * Real.sin t + (gLate t - 1) * Real.cos t < 1 / 2 := by
  have hmirror : Real.pi / 2 - t ∈ Icc (0 : ℝ) beta := by
    unfold lateSwitch at ht
    constructor <;> linarith [ht.1, ht.2]
  have h := earlyApex_lt_half hmirror
  have hf := fLate_reflection (Real.pi / 2 - t)
  have hg := gLate_reflection (Real.pi / 2 - t)
  have hangle : Real.pi / 2 - (Real.pi / 2 - t) = t := by ring
  rw [hangle, Real.sin_pi_div_two_sub] at hf
  rw [hangle, Real.cos_pi_div_two_sub] at hg
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub] at h
  rw [hf, hg]
  nlinarith

/-- The middle phase oscillates faster than the enclosing first cosine lobe. -/
theorem middlePhase_sin_le_cos_center {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    Real.sin (3 / 2 * t + Real.pi / 8) ≤ Real.cos (t - Real.pi / 4) := by
  have hu : |t - Real.pi / 4| ≤ Real.pi / 4 := by
    apply abs_le.mpr
    constructor <;> linarith [ht.1, ht.2]
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (t - Real.pi / 4))
    (show 3 / 2 * |t - Real.pi / 4| ≤ Real.pi by linarith [Real.pi_pos])
    (show |t - Real.pi / 4| ≤ 3 / 2 * |t - Real.pi / 4| by
      nlinarith [abs_nonneg (t - Real.pi / 4)])
  have habs : |3 / 2 * (t - Real.pi / 4)| = 3 / 2 * |t - Real.pi / 4| := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
  rw [← habs] at hcos
  simp only [Real.cos_abs] at hcos
  have hangle : 3 / 2 * t + Real.pi / 8 = Real.pi / 2 + 3 / 2 * (t - Real.pi / 4) := by
    ring
  rw [hangle, Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]
  simpa only [one_mul, zero_mul, add_zero] using hcos

theorem sin_add_cos_eq_sqrt_two_cos_center (t : ℝ) :
    Real.sin t + Real.cos t = Real.sqrt 2 * Real.cos (t - Real.pi / 4) := by
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  calc
    _ = (Real.sqrt 2 ^ 2 / 2) * (Real.cos t + Real.sin t) := by rw [hsqrt]; ring
    _ = _ := by
      rw [Real.cos_sub, Real.cos_pi_div_four, Real.sin_pi_div_four]
      ring

theorem middleApex_lt_half {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    (fMiddle t - 1) * Real.sin t + (gMiddle t - 1) * Real.cos t < 1 / 2 := by
  have hcos : 0 < Real.cos (t - Real.pi / 4) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2, Real.pi_pos]⟩
  have hphase := mul_le_mul_of_nonneg_left (middlePhase_sin_le_cos_center ht) R_pos.le
  have hstrict := mul_lt_mul_of_pos_right R_lt_sqrt_two hcos
  have hangle : (t / 2 + Real.pi / 8) + t = 3 / 2 * t + Real.pi / 8 := by ring
  have hsum := sin_add_cos_eq_sqrt_two_cos_center t
  have hexpand : (fMiddle t - 1) * Real.sin t + (gMiddle t - 1) * Real.cos t =
      1 / 2 + R * Real.sin (3 / 2 * t + Real.pi / 8) - Real.sin t - Real.cos t := by
    calc
      _ = 1 / 2 * (Real.sin t ^ 2 + Real.cos t ^ 2) +
          R * (Real.sin (t / 2 + Real.pi / 8) * Real.cos t +
            Real.cos (t / 2 + Real.pi / 8) * Real.sin t) - Real.sin t - Real.cos t := by
        unfold fMiddle gMiddle
        ring
      _ = _ := by rw [Real.sin_sq_add_cos_sq, ← Real.sin_add, hangle]; ring
  rw [hexpand]
  linarith

theorem referenceApexHeight_lt_half {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : referenceApexHeight t < 1 / 2 := by
  unfold referenceApexHeight referenceF referenceG
  split_ifs with hearly hmiddle
  · exact earlyApex_lt_half ⟨ht.1, hearly⟩
  · exact middleApex_lt_half ht
  · exact lateApex_lt_half ⟨(lt_of_not_ge hmiddle).le, ht.2⟩

theorem firstWall_referenceHull {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) (x : ℝ) :
    firstWall referenceHull t x =
      (referenceF t - 1 - x * Real.cos t) / Real.sin t := by
  unfold firstWall
  rw [show support referenceHull (unitNormal t) = referenceF t from
    angleSupport_referenceHull_eq_f ht]

theorem secondWall_referenceHull {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) (x : ℝ) :
    secondWall referenceHull t x =
      (referenceG t - 1 + x * Real.sin t) / Real.cos t := by
  unfold secondWall
  rw [companionNormal_eq_unitNormal]
  rw [show support referenceHull (unitNormal (t + Real.pi / 2)) = referenceG t from
    angleSupport_referenceHull_eq_g ht]

/-- A two-wall tent never exceeds its own apex, at any horizontal coordinate. -/
theorem cornerWall_referenceHull_le_apex {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) (x : ℝ) :
    cornerWall referenceHull t x ≤ referenceApexHeight t := by
  have hs : Real.sin t ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith [ht.2, Real.pi_pos]))
  have hc : Real.cos t ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)
  calc
    cornerWall referenceHull t x = cornerWall referenceHull t x *
        (Real.sin t ^ 2 + Real.cos t ^ 2) := by rw [Real.sin_sq_add_cos_sq, mul_one]
    _ = cornerWall referenceHull t x * Real.sin t ^ 2 +
        cornerWall referenceHull t x * Real.cos t ^ 2 := by ring
    _ ≤ firstWall referenceHull t x * Real.sin t ^ 2 +
        secondWall referenceHull t x * Real.cos t ^ 2 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _))
        (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _))
    _ = referenceApexHeight t := by
      rw [firstWall_referenceHull ⟨ht.1.le, ht.2.le⟩,
        secondWall_referenceHull ⟨ht.1.le, ht.2.le⟩]
      unfold referenceApexHeight
      field_simp [hs, hc]
      <;> ring

theorem referenceNiche_nonneg (x : ℝ) : 0 ≤ referenceNiche x :=
  sweptNiche_nonneg referenceHull (Real.pi / 2) x

/-- A strict global midline margin follows from the compact apex maximum. -/
theorem exists_referenceNiche_uniform_bound :
    ∃ C : ℝ, 0 ≤ C ∧ C < 1 / 2 ∧ ∀ x, referenceNiche x ≤ C := by
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨le_rfl, by linarith [Real.pi_pos]⟩
  obtain ⟨t, ht, hmax⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) (Real.pi / 2))).exists_isMaxOn
    ⟨0, hzero⟩ continuous_referenceApexHeight.continuousOn
  have hC : 0 ≤ referenceApexHeight t := by
    simpa only [mem_setOf_eq, referenceApexHeight_zero] using hmax hzero
  refine ⟨referenceApexHeight t, hC, referenceApexHeight_lt_half ht, ?_⟩
  intro x
  apply sweptNiche_le_of_forall (by linarith [Real.pi_pos]) hC
  intro s hs
  exact (cornerWall_referenceHull_le_apex hs x).trans (hmax ⟨hs.1.le, hs.2.le⟩)

theorem referenceNiche_lt_half (x : ℝ) : referenceNiche x < 1 / 2 := by
  obtain ⟨C, _, hC, hbound⟩ := exists_referenceNiche_uniform_bound
  exact (hbound x).trans_lt hC

theorem referenceWallClip_zero (x : ℝ) : referenceWallClip x 0 = 0 := by
  simp [referenceWallClip, referenceF_zero, referenceG_zero]

theorem referenceWallClip_pi_div_two (x : ℝ) : referenceWallClip x (Real.pi / 2) = 0 := by
  simp [referenceWallClip, referenceF_pi_div_two]

theorem referenceWallClip_eq_actual {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) (x : ℝ) :
    referenceWallClip x t = max (cornerWall referenceHull t x) 0 := by
  rw [cornerWall, firstWall_referenceHull ht, secondWall_referenceHull ht]
  rfl

/-- At either endpoint the well-defined companion wall squeezes the positive minimum to zero. -/
theorem continuousAt_referenceWallClip {z : ℝ × ℝ}
    (hz : z.2 ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ContinuousAt (fun p : ℝ × ℝ => referenceWallClip p.1 p.2) z := by
  have hf := continuous_referenceF
  have hg := continuous_referenceG
  by_cases hz0 : z.2 = 0
  · let upper : ℝ × ℝ → ℝ := fun p =>
      max ((referenceG p.2 - 1 + p.1 * Real.sin p.2) / Real.cos p.2) 0
    have hupper : ContinuousAt upper z := by
      unfold upper
      fun_prop (disch := simp [hz0])
    have hupper0 : upper z = 0 := by simp [upper, hz0, referenceG_zero]
    have hvalue : referenceWallClip z.1 z.2 = 0 := by rw [hz0, referenceWallClip_zero]
    change Filter.Tendsto _ _ (𝓝 (referenceWallClip z.1 z.2))
    rw [hvalue]
    have hupper' : Filter.Tendsto upper (𝓝 z) (𝓝 0) := by
      have h := hupper.tendsto
      rwa [hupper0] at h
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper'
    · intro p
      exact le_max_right _ _
    · intro p
      exact max_le_max_right 0 (min_le_right _ _)
  by_cases hzL : z.2 = Real.pi / 2
  · let upper : ℝ × ℝ → ℝ := fun p =>
      max ((referenceF p.2 - 1 - p.1 * Real.cos p.2) / Real.sin p.2) 0
    have hupper : ContinuousAt upper z := by
      unfold upper
      fun_prop (disch := simp [hzL])
    have hupper0 : upper z = 0 := by simp [upper, hzL, referenceF_pi_div_two]
    have hvalue : referenceWallClip z.1 z.2 = 0 := by rw [hzL, referenceWallClip_pi_div_two]
    change Filter.Tendsto _ _ (𝓝 (referenceWallClip z.1 z.2))
    rw [hvalue]
    have hupper' : Filter.Tendsto upper (𝓝 z) (𝓝 0) := by
      have h := hupper.tendsto
      rwa [hupper0] at h
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper'
    · intro p
      exact le_max_right _ _
    · intro p
      exact max_le_max_right 0 (min_le_left _ _)
  · have hsin : Real.sin z.2 ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
      (lt_of_le_of_ne hz.1 (Ne.symm hz0)) (by linarith [hz.2, Real.pi_pos]))
    have hcos : Real.cos z.2 ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hz.1, Real.pi_pos], lt_of_le_of_ne hz.2 hzL⟩)
    unfold referenceWallClip
    fun_prop (disch := assumption)

theorem continuous_referenceWallClip_on_angles :
    Continuous (fun p : ℝ × Icc (0 : ℝ) (Real.pi / 2) => referenceWallClip p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  exact (continuousAt_referenceWallClip (z := (p.1, (p.2 : ℝ))) p.2.property).comp
    (f := fun q : ℝ × Icc (0 : ℝ) (Real.pi / 2) => (q.1, (q.2 : ℝ)))
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousAt

/-- Closed-angle clipping has exactly the same supremum as the actual open-angle niche. -/
theorem referenceNiche_eq_sSup_clipped (x : ℝ) :
    referenceNiche x = sSup ((fun t : Icc (0 : ℝ) (Real.pi / 2) =>
      referenceWallClip x t) '' Set.univ) := by
  let zeroAngle : Icc (0 : ℝ) (Real.pi / 2) := ⟨0, le_rfl, by linarith [Real.pi_pos]⟩
  have hcont : Continuous (fun t : Icc (0 : ℝ) (Real.pi / 2) => referenceWallClip x t) :=
    continuous_referenceWallClip_on_angles.comp (continuous_const.prodMk continuous_id)
  have hbounded := (isCompact_univ : IsCompact (Set.univ : Set (Icc (0 : ℝ) (Real.pi / 2)))).bddAbove_image
    hcont.continuousOn
  have hzero : 0 ≤ sSup ((fun t : Icc (0 : ℝ) (Real.pi / 2) =>
      referenceWallClip x t) '' Set.univ) := by
    have h := le_csSup hbounded (mem_image_of_mem _ (mem_univ zeroAngle))
    simpa only [zeroAngle, referenceWallClip_zero] using h
  apply le_antisymm
  · apply sweptNiche_le_of_forall (by linarith [Real.pi_pos]) hzero
    intro t ht
    calc
      cornerWall referenceHull t x ≤ referenceWallClip x t := by
        rw [referenceWallClip_eq_actual ⟨ht.1.le, ht.2.le⟩]
        exact le_max_left _ _
      _ ≤ _ := le_csSup hbounded (mem_image_of_mem _
        (mem_univ (⟨t, ht.1.le, ht.2.le⟩ : Icc (0 : ℝ) (Real.pi / 2))))
  · refine csSup_le ⟨referenceWallClip x zeroAngle, zeroAngle, mem_univ _, rfl⟩ ?_
    rintro y ⟨t, _, rfl⟩
    show referenceWallClip x t ≤ referenceNiche x
    by_cases ht0 : (t : ℝ) = 0
    · rw [ht0, referenceWallClip_zero]
      exact referenceNiche_nonneg x
    by_cases htL : (t : ℝ) = Real.pi / 2
    · rw [htL, referenceWallClip_pi_div_two]
      exact referenceNiche_nonneg x
    · rw [referenceWallClip_eq_actual t.property]
      apply max_le _ (referenceNiche_nonneg x)
      exact cornerWall_le_sweptNiche
        (sweptWallValues_bddAbove isCompact_referenceHull le_rfl x)
        ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0), lt_of_le_of_ne t.property.2 htL⟩

/-- The actual whole-angle reference niche is continuous at every horizontal coordinate. -/
theorem continuous_referenceNiche : Continuous referenceNiche := by
  rw [show referenceNiche = (fun x => sSup ((fun t : Icc (0 : ℝ) (Real.pi / 2) =>
    referenceWallClip x t) '' Set.univ)) from funext referenceNiche_eq_sSup_clipped]
  exact (isCompact_univ : IsCompact (Set.univ : Set (Icc (0 : ℝ) (Real.pi / 2)))).continuous_sSup
    continuous_referenceWallClip_on_angles

end AmbidextrousSofa.Reference
