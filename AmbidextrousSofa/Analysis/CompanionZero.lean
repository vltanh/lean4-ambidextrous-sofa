module

public import AmbidextrousSofa.Analysis.LeftCompanionCap

@[expose] public section

/-!
# The literal zero of the low-wing companion envelope

For a point `(X,Y)` below height one, the rightmost intersection of its
unit circle with the floor is `X + sqrt (1-Y²)`. Minimizing this continuous
quantity over the actual compact cap gives the zero of its companion-wall
envelope. A positive left endpoint height makes the minimizing contact
angle proper. The minimum gives strict wall signs without taking a
supremum over an open, singular angular interval.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace AmbidextrousSofa

def rightCircleAbscissa (p : Plane) : ℝ := p.1 + circleHeight p.2

def companionZero (U : Set Plane) : ℝ := sInf (rightCircleAbscissa '' U)

theorem continuous_rightCircleAbscissa : Continuous rightCircleAbscissa :=
  continuous_fst.add (continuous_circleHeight.comp continuous_snd)

theorem IsDownwardCap.companionZero_le_point {U : Set Plane}
    (hU : IsDownwardCap U) {p : Plane} (hp : p ∈ U) :
    companionZero U ≤ rightCircleAbscissa p :=
  csInf_le (hU.isCompact.bddBelow_image continuous_rightCircleAbscissa.continuousOn)
    (mem_image_of_mem _ hp)

theorem circleHeight_mul_sin_add_mul_cos_le_one {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) (t : ℝ) :
    circleHeight y * Real.sin t + y * Real.cos t ≤ 1 := by
  have h := Real.cos_le_one (Real.arccos y - t)
  rw [Real.cos_sub, Real.cos_arccos (by linarith [hy.1]) hy.2, Real.sin_arccos] at h
  unfold circleHeight
  linarith

/-- Each companion wall lies below the line through the zero with slope `tan t`. -/
theorem IsDownwardCap.secondWall_le_companionZero_slope {U : Set Plane} (hU : IsDownwardCap U)
    {x t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    secondWall U t x ≤ (x - companionZero U) * Real.tan t := by
  have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
  obtain ⟨p, hp, hsupport⟩ := exists_coordDot_eq_support hU.isCompact hU.nonempty
    (companionNormal t)
  have hz := hU.companionZero_le_point hp
  rw [rightCircleAbscissa] at hz
  rw [← companionPointWall_eq_secondWall_of_support hc.ne' hsupport, companionPointWall,
    Real.tan_eq_sin_div_cos, mul_div_assoc', le_div_iff₀ hc, add_mul, div_mul_cancel₀ _ hc.ne']
  nlinarith [circleHeight_mul_sin_add_mul_cos_le_one (hU.inStrip hp) t,
    mul_le_mul_of_nonneg_right hz hs.le]

theorem IsDownwardCap.secondWall_nonpos_of_le_companionZero
    {U : Set Plane} (hU : IsDownwardCap U) {x t : ℝ}
    (hx : x ≤ companionZero U) (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    secondWall U t x ≤ 0 :=
  (hU.secondWall_le_companionZero_slope ht).trans (mul_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.2 hx) (Real.tan_pos_of_pos_of_lt_pi_div_two ht.1 ht.2).le)

theorem IsDownwardCap.secondWall_neg_of_lt_companionZero
    {U : Set Plane} (hU : IsDownwardCap U) {x t : ℝ}
    (hx : x < companionZero U) (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    secondWall U t x < 0 :=
  (hU.secondWall_le_companionZero_slope ht).trans_lt (mul_neg_of_neg_of_pos
    (sub_neg.2 hx) (Real.tan_pos_of_pos_of_lt_pi_div_two ht.1 ht.2))

theorem IsDownwardCap.companionZero_lt_left_add_one
    {U : Set Plane} (hU : IsDownwardCap U) (hheight : capHeight U < 1)
    (hleft : 0 < capRoof U (horizontalLeft U)) :
    companionZero U < horizontalLeft U + 1 := by
  have hp := capRoof_mem hU.isCompact (horizontalLeft_mem hU.nonempty hU.isCompact)
  have hsq := circleHeight_sq ⟨hleft, (hU.snd_le_capHeight hp).trans_lt hheight⟩
  have hroot : circleHeight (capRoof U (horizontalLeft U)) < 1 := by
    nlinarith [circleHeight_nonneg (capRoof U (horizontalLeft U))]
  exact (hU.companionZero_le_point hp).trans_lt (by rw [rightCircleAbscissa]; linarith)

/-- The zero is attained by a genuine support point at a proper angle.
The positive left endpoint excludes a floor contact at the terminal angle. -/
theorem IsDownwardCap.exists_companionZero_contact
    {U : Set Plane} (hU : IsDownwardCap U) (hheight : capHeight U < 1)
    (hleft : 0 < capRoof U (horizontalLeft U)) :
    ∃ p ∈ U, ∃ t ∈ Ioo (0 : ℝ) (Real.pi / 2),
      p.2 = Real.cos t ∧ companionZero U = p.1 + Real.sin t ∧
      companionPointWall p (companionZero U) t = 0 ∧
      secondWall U t (companionZero U) = 0 := by
  obtain ⟨p, hp, hpzero⟩ : ∃ p ∈ U, rightCircleAbscissa p = companionZero U :=
    (hU.isCompact.image continuous_rightCircleAbscissa).sInf_mem (hU.nonempty.image _)
  have hpy0 : 0 < p.2 := (hU.inStrip hp).1.lt_of_ne fun h => by
    simp [rightCircleAbscissa, ← h, circleHeight] at hpzero
    linarith [hU.companionZero_lt_left_add_one hheight hleft, (hU.fst_mem_Icc hp).1]
  have hpy1 : p.2 < 1 := (hU.snd_le_capHeight hp).trans_lt hheight
  have ht : Real.arccos p.2 ∈ Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨Real.arccos_pos.mpr hpy1, Real.arccos_lt_pi_div_two.mpr hpy0⟩
  have hc : Real.cos (Real.arccos p.2) = p.2 := Real.cos_arccos (by linarith) hpy1.le
  have hx : companionZero U = p.1 + Real.sin (Real.arccos p.2) := by
    rw [Real.sin_arccos]
    exact hpzero.symm
  have hpwall : companionPointWall p (companionZero U) (Real.arccos p.2) = 0 := by
    rw [companionPointWall, hx, add_sub_cancel_left]
    nth_rw 1 [← hc]
    field_simp [hc, hpy0.ne']
    linear_combination Real.sin_sq_add_cos_sq (Real.arccos p.2)
  refine ⟨p, hp, _, ht, hc.symm, hx, hpwall, le_antisymm
    (hU.secondWall_nonpos_of_le_companionZero le_rfl ht) ?_⟩
  exact hpwall ▸ companionPointWall_le_secondWall hU hp (hc.symm ▸ hpy0)

theorem IsDownwardCap.exists_secondWall_pos_of_companionZero_lt
    {U : Set Plane} (hU : IsDownwardCap U) (hheight : capHeight U < 1)
    (hleft : 0 < capRoof U (horizontalLeft U)) {x : ℝ}
    (hx : companionZero U < x) :
    ∃ t ∈ Ioo (0 : ℝ) (Real.pi / 2), 0 < secondWall U t x := by
  obtain ⟨-, -, t, ht, -, -, -, hzero⟩ := hU.exists_companionZero_contact hheight hleft
  have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
  rw [secondWall, div_eq_zero_iff, or_iff_left hc.ne'] at hzero
  exact ⟨t, ht, div_pos (by nlinarith) hc⟩

end AmbidextrousSofa
