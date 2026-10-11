module

public import AmbidextrousSofa.Analysis.TopInsertion
public import AmbidextrousSofa.Analysis.CapReflection

@[expose] public section

/-!
# The high endpoint of an affine middle roof is at height one

For a nonnegative middle slope, concavity bounds every roof value to the
left of the middle's right endpoint by that endpoint's value. If it were
below one, every attained height-one point would lie strictly to its right,
where the actual top-insertion variation improves the score. Reflection
gives the negative-slope statement.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem roofChord_eq_affine {f : ℝ → ℝ} {a b m c : ℝ} (hab : a < b)
    (ha : f a = m * a + c) (hb : f b = m * b + c) (x : ℝ) :
    roofChord f a b x = m * x + c := by
  rw [roofChord, ha, hb]
  field_simp [(sub_pos.mpr hab).ne']
  ring

theorem IsFullCapMaximizer.middle_right_eq_one_of_affine_nonneg
    {U : Set Plane} (hU : IsFullCapMaximizer U) (hheight : capHeight U = 1)
    {m c : ℝ} (hm : 0 ≤ m)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    capRoof U (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) = 1 := by
  set l := horizontalLeft U
  set r := horizontalRight U
  have hw : M ≤ r - l := hU.width_bounds.1
  have hab : l + (r - l) / 4 < r - (r - l) / 4 := by linarith [one_lt_M]
  have hbU : r - (r - l) / 4 ∈ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex]
    constructor <;> linarith [one_lt_M]
  have hA := haffine _ ⟨le_rfl, hab.le⟩
  have hB := haffine _ ⟨hab.le, le_rfl⟩
  refine le_antisymm (capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip _)
    (not_lt.mp fun hlow => ?_)
  -- A highest point of the cap lies at or to the right of the middle's right endpoint.
  obtain ⟨q, hq, hqH⟩ := exists_coordDot_eq_support hU.isCap.isCompact hU.isCap.nonempty (0, 1)
  have hqone : q.2 = 1 := by simpa [coordDot] using hqH.trans hheight
  have hbq : r - (r - l) / 4 ≤ q.1 := by
    by_contra! hqb
    have hline : capRoof U q.1 ≤ m * q.1 + c := by
      rcases le_or_gt q.1 (l + (r - l) / 4) with hqa | hqa
      · simpa only [roofChord_eq_affine hab hA hB] using
          ConcaveOn.le_roofChord_of_le hU.isCap.concaveOn_capRoof ⟨q, hq, rfl⟩ hbU hab hqa
      · exact (haffine q.1 ⟨hqa.le, hqb.le⟩).le
    linarith [hqone.ge.trans (le_capRoof hU.isCap.isCompact hq),
      mul_nonneg hm (sub_nonneg.mpr hqb.le)]
  exact hlow.ne (hU.middle_right_eq_one_of_top_right
    (by simpa only [← hqone, Prod.mk.eta] using hq) hbq)

theorem IsFullCapMaximizer.middle_left_eq_one_of_affine_nonpos
    {U : Set Plane} (hU : IsFullCapMaximizer U) (hheight : capHeight U = 1)
    {m c : ℝ} (hm : m ≤ 0)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    capRoof U (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4) = 1 := by
  have heq := hU.horizontalMirror.middle_right_eq_one_of_affine_nonneg
    (by rw [capHeight_horizontalMirror, hheight]) (neg_nonneg.mpr hm) (c := c) fun x hx => by
      rw [horizontalLeft_horizontalMirror hU.isCap, horizontalRight_horizontalMirror hU.isCap]
        at hx
      rw [capRoof_horizontalMirror, haffine (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩]
      ring
  rw [horizontalLeft_horizontalMirror hU.isCap, horizontalRight_horizontalMirror hU.isCap,
    capRoof_horizontalMirror] at heq
  convert heq using 2
  ring

end AmbidextrousSofa
