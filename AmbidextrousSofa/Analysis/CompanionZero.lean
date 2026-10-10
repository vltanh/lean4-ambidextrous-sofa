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

theorem IsDownwardCap.exists_companionZero_point {U : Set Plane}
    (hU : IsDownwardCap U) :
    ∃ p ∈ U, rightCircleAbscissa p = companionZero U := by
  obtain ⟨p, hp, hmin⟩ := hU.isCompact.exists_isMinOn hU.nonempty
    continuous_rightCircleAbscissa.continuousOn
  refine ⟨p, hp, le_antisymm ?_ (hU.companionZero_le_point hp)⟩
  apply le_csInf (hU.nonempty.image _)
  rintro y ⟨q, hq, rfl⟩
  exact hmin hq

theorem circleHeight_mul_sin_add_mul_cos_le_one {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) (t : ℝ) :
    circleHeight y * Real.sin t + y * Real.cos t ≤ 1 := by
  have hroot : circleHeight y ^ 2 + y ^ 2 = 1 := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 - y ^ 2 by
      nlinarith only [mul_nonneg hy.1 (sub_nonneg.mpr hy.2), hy.1, hy.2])
    change circleHeight y ^ 2 = 1 - y ^ 2 at hs
    linarith only [hs]
  have hid : (circleHeight y * Real.sin t + y * Real.cos t) ^ 2 +
      (circleHeight y * Real.cos t - y * Real.sin t) ^ 2 =
      (circleHeight y ^ 2 + y ^ 2) * (Real.sin t ^ 2 + Real.cos t ^ 2) := by ring
  rw [hroot, Real.sin_sq_add_cos_sq, one_mul] at hid
  by_contra hnot
  have hgreater : 1 < circleHeight y * Real.sin t + y * Real.cos t := lt_of_not_ge hnot
  have hprod := mul_pos (sub_pos.mpr hgreater)
    (show 0 < circleHeight y * Real.sin t + y * Real.cos t + 1 by
      linarith only [hgreater])
  nlinarith only [hid, hprod,
    sq_nonneg (circleHeight y * Real.cos t - y * Real.sin t)]

theorem companionPointWall_nonpos_of_le_rightCircleAbscissa
    {p : Plane} {x t : ℝ} (hpy : p.2 ∈ Icc (0 : ℝ) 1)
    (hx : x ≤ rightCircleAbscissa p)
    (hs : 0 ≤ Real.sin t) (hc : 0 < Real.cos t) :
    companionPointWall p x t ≤ 0 := by
  have hcircle := circleHeight_mul_sin_add_mul_cos_le_one hpy t
  have hmul := mul_le_mul_of_nonneg_right
    (show x - p.1 ≤ circleHeight p.2 by
      dsimp only [rightCircleAbscissa] at hx
      linarith only [hx]) hs
  rw [companionPointWall_eq hc.ne']
  apply div_nonpos_of_nonpos_of_nonneg _ hc.le
  dsimp only [coordDot, companionNormal]
  nlinarith only [hcircle, hmul]

theorem companionPointWall_neg_of_lt_rightCircleAbscissa
    {p : Plane} {x t : ℝ} (hpy : p.2 ∈ Icc (0 : ℝ) 1)
    (hx : x < rightCircleAbscissa p)
    (hs : 0 < Real.sin t) (hc : 0 < Real.cos t) :
    companionPointWall p x t < 0 := by
  have hcircle := circleHeight_mul_sin_add_mul_cos_le_one hpy t
  have hmul := mul_lt_mul_of_pos_right
    (show x - p.1 < circleHeight p.2 by
      dsimp only [rightCircleAbscissa] at hx
      linarith only [hx]) hs
  rw [companionPointWall_eq hc.ne']
  apply div_neg_of_neg_of_pos _ hc
  dsimp only [coordDot, companionNormal]
  nlinarith only [hcircle, hmul]

theorem IsDownwardCap.secondWall_nonpos_of_le_companionZero
    {U : Set Plane} (hU : IsDownwardCap U) {x t : ℝ}
    (hx : x ≤ companionZero U) (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    secondWall U t x ≤ 0 := by
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith only [ht.2, Real.pi_pos])
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩
  obtain ⟨p, hp, hsupport⟩ := exists_coordDot_eq_support hU.isCompact hU.nonempty
    (companionNormal t)
  rw [← companionPointWall_eq_secondWall_of_support hc.ne' hsupport]
  exact companionPointWall_nonpos_of_le_rightCircleAbscissa (hU.inStrip hp)
    (hx.trans (hU.companionZero_le_point hp)) hs.le hc

theorem IsDownwardCap.secondWall_neg_of_lt_companionZero
    {U : Set Plane} (hU : IsDownwardCap U) {x t : ℝ}
    (hx : x < companionZero U) (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    secondWall U t x < 0 := by
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith only [ht.2, Real.pi_pos])
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩
  obtain ⟨p, hp, hsupport⟩ := exists_coordDot_eq_support hU.isCompact hU.nonempty
    (companionNormal t)
  rw [← companionPointWall_eq_secondWall_of_support hc.ne' hsupport]
  exact companionPointWall_neg_of_lt_rightCircleAbscissa (hU.inStrip hp)
    (hx.trans_le (hU.companionZero_le_point hp)) hs hc

theorem IsDownwardCap.left_lt_companionZero_of_height_lt_one
    {U : Set Plane} (hU : IsDownwardCap U) (hheight : capHeight U < 1) :
    horizontalLeft U < companionZero U := by
  obtain ⟨p, hp, hpzero⟩ := hU.exists_companionZero_point
  have hpy0 := (hU.inStrip hp).1
  have hpy1 := (hU.snd_le_capHeight hp).trans_lt hheight
  have hs : 0 < circleHeight p.2 := by
    apply Real.sqrt_pos.mpr
    nlinarith only [mul_pos (sub_pos.mpr hpy1)
      (show 0 < 1 + p.2 by linarith only [hpy0])]
  have hpx := (hU.fst_mem_Icc hp).1
  rw [← hpzero, rightCircleAbscissa]
  linarith only [hs, hpx]

theorem IsDownwardCap.companionZero_lt_left_add_one
    {U : Set Plane} (hU : IsDownwardCap U) (hheight : capHeight U < 1)
    (hleft : 0 < capRoof U (horizontalLeft U)) :
    companionZero U < horizontalLeft U + 1 := by
  have hx : horizontalLeft U ∈ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
    exact ⟨le_rfl, horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact⟩
  have hp := capRoof_mem hU.isCompact hx
  have he1 := (hU.snd_le_capHeight hp).trans_lt hheight
  have hsq := circleHeight_sq ⟨hleft, he1⟩
  have hroot : circleHeight (capRoof U (horizontalLeft U)) < 1 := by
    by_contra hnot
    have hge : 1 ≤ circleHeight (capRoof U (horizontalLeft U)) := le_of_not_gt hnot
    have hprod := mul_nonneg (sub_nonneg.mpr hge)
      (show 0 ≤ circleHeight (capRoof U (horizontalLeft U)) + 1 by linarith only [hge])
    nlinarith only [hsq, hprod, sq_pos_of_pos hleft]
  exact (hU.companionZero_le_point hp).trans_lt (by
    dsimp only [rightCircleAbscissa]
    linarith only [hroot])

/-- The zero is attained by a genuine support point at a proper angle.
The positive left endpoint excludes a floor contact at the terminal angle. -/
theorem IsDownwardCap.exists_companionZero_contact
    {U : Set Plane} (hU : IsDownwardCap U) (hheight : capHeight U < 1)
    (hleft : 0 < capRoof U (horizontalLeft U)) :
    ∃ p ∈ U, ∃ t ∈ Ioo (0 : ℝ) (Real.pi / 2),
      p.2 = Real.cos t ∧ companionZero U = p.1 + Real.sin t ∧
      companionPointWall p (companionZero U) t = 0 ∧
      secondWall U t (companionZero U) = 0 := by
  obtain ⟨p, hp, hpzero⟩ := hU.exists_companionZero_point
  have hz := hU.companionZero_lt_left_add_one hheight hleft
  have hpy0 : 0 < p.2 := by
    by_contra hnot
    have heq : p.2 = 0 := le_antisymm (le_of_not_gt hnot) (hU.inStrip hp).1
    have hpx := (hU.fst_mem_Icc hp).1
    simp only [rightCircleAbscissa, heq, circleHeight, zero_pow (by norm_num : 2 ≠ 0),
      sub_zero, Real.sqrt_one] at hpzero
    linarith only [hpzero, hz, hpx]
  have hpy1 : p.2 < 1 := (hU.snd_le_capHeight hp).trans_lt hheight
  let t : ℝ := Real.arccos p.2
  have ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨Real.arccos_pos.mpr hpy1, Real.arccos_lt_pi_div_two.mpr hpy0⟩
  have hc : Real.cos t = p.2 := Real.cos_arccos (by linarith only [hpy0]) hpy1.le
  have hs : Real.sin t = circleHeight p.2 := Real.sin_arccos p.2
  have hx : companionZero U = p.1 + Real.sin t := by
    rw [hs]
    exact hpzero.symm
  have hpwall : companionPointWall p (companionZero U) t = 0 := by
    rw [companionPointWall, hx, add_sub_cancel_left, ← hc]
    have hcircle := Real.sin_sq_add_cos_sq t
    field_simp [show Real.cos t ≠ 0 by rw [hc]; exact hpy0.ne']
    nlinarith only [hcircle]
  refine ⟨p, hp, t, ht, hc.symm, hx, hpwall, ?_⟩
  apply le_antisymm (hU.secondWall_nonpos_of_le_companionZero le_rfl ht)
  rw [← hpwall]
  exact companionPointWall_le_secondWall hU hp (by simpa only [hc] using hpy0)

theorem IsDownwardCap.exists_secondWall_pos_of_companionZero_lt
    {U : Set Plane} (hU : IsDownwardCap U) (hheight : capHeight U < 1)
    (hleft : 0 < capRoof U (horizontalLeft U)) {x : ℝ}
    (hx : companionZero U < x) :
    ∃ t ∈ Ioo (0 : ℝ) (Real.pi / 2), 0 < secondWall U t x := by
  obtain ⟨p, hp, t, ht, hpy, hpx, hpwall, _⟩ :=
    hU.exists_companionZero_contact hheight hleft
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith only [ht.2, Real.pi_pos])
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩
  have hdiff : companionPointWall p x t =
      companionPointWall p (companionZero U) t +
        (x - companionZero U) * Real.sin t / Real.cos t := by
    unfold companionPointWall
    ring
  have hpoint : 0 < companionPointWall p x t := by
    rw [hdiff, hpwall, zero_add]
    exact div_pos (mul_pos (sub_pos.mpr hx) hs) hc
  exact ⟨t, ht, hpoint.trans_le (companionPointWall_le_secondWall hU hp hc)⟩

theorem IsDownwardCap.companionZero_lt_iff_exists_secondWall_pos
    {U : Set Plane} (hU : IsDownwardCap U) (hheight : capHeight U < 1)
    (hleft : 0 < capRoof U (horizontalLeft U)) (x : ℝ) :
    companionZero U < x ↔
      ∃ t ∈ Ioo (0 : ℝ) (Real.pi / 2), 0 < secondWall U t x := by
  constructor
  · exact hU.exists_secondWall_pos_of_companionZero_lt hheight hleft
  · rintro ⟨t, ht, hpos⟩
    by_contra hnot
    exact not_lt_of_ge (hU.secondWall_nonpos_of_le_companionZero (le_of_not_gt hnot) ht) hpos

end AmbidextrousSofa
