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
  unfold roofChord
  rw [ha, hb]
  field_simp [(sub_pos.mpr hab).ne']
  ring

theorem IsFullCapMaximizer.middle_right_eq_one_of_affine_nonneg
    {U : Set Plane} (hU : IsFullCapMaximizer U) (hheight : capHeight U = 1)
    {m c : ℝ} (hm : 0 ≤ m)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    capRoof U (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) = 1 := by
  let l := horizontalLeft U
  let r := horizontalRight U
  let a := l + (r - l) / 4
  let b := r - (r - l) / 4
  have hlr : l < r := by
    have hw := hU.width_bounds.1
    change M ≤ r - l at hw
    linarith [one_lt_M]
  have hab : a < b := by dsimp [a, b]; linarith
  have hla : l ≤ a := by dsimp [a]; linarith
  have hbr : b ≤ r := by dsimp [b]; linarith
  have hproj : horizontalProjection U = Icc l r :=
    horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex
  have hbU : b ∈ horizontalProjection U := by
    rw [hproj]
    exact ⟨hla.trans hab.le, hbr⟩
  have hA : capRoof U a = m * a + c := haffine a ⟨le_rfl, hab.le⟩
  have hB : capRoof U b = m * b + c := haffine b ⟨hab.le, le_rfl⟩
  apply le_antisymm (capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip _)
  by_contra h
  have hlow : capRoof U b < 1 := lt_of_not_ge h
  obtain ⟨q, hq, hqH⟩ := exists_coordDot_eq_support hU.isCap.isCompact hU.isCap.nonempty (0, 1)
  have hqone : q.2 = 1 := by
    change q.1 * 0 + q.2 * 1 = capHeight U at hqH
    simpa only [mul_zero, mul_one, zero_add, hheight] using hqH
  have hqroof : 1 ≤ capRoof U q.1 := by
    rw [← hqone]
    exact le_capRoof hU.isCap.isCompact (by simpa only [Prod.mk.eta] using hq)
  have hbq : b ≤ q.1 := by
    by_contra hnot
    have hqb : q.1 ≤ b := (lt_of_not_ge hnot).le
    have hline : capRoof U q.1 ≤ m * q.1 + c := by
      by_cases hqa : q.1 ≤ a
      · have hchord := ConcaveOn.le_roofChord_of_le hU.isCap.concaveOn_capRoof
          (show q.1 ∈ horizontalProjection U from ⟨q, hq, rfl⟩) hbU hab hqa
        rwa [roofChord_eq_affine hab hA hB] at hchord
      · exact (haffine q.1 ⟨le_of_not_ge hqa, hqb⟩).le
    have hproduct := mul_nonneg hm (sub_nonneg.mpr hqb)
    rw [hB] at hlow
    nlinarith
  have htop : (q.1, 1) ∈ U := by simpa only [← hqone, Prod.mk.eta] using hq
  have heq := hU.middle_right_eq_one_of_top_right htop hbq
  exact (ne_of_lt hlow) heq

theorem IsFullCapMaximizer.middle_left_eq_one_of_affine_nonpos
    {U : Set Plane} (hU : IsFullCapMaximizer U) (hheight : capHeight U = 1)
    {m c : ℝ} (hm : m ≤ 0)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    capRoof U (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4) = 1 := by
  have hV := hU.horizontalMirror
  have hheightV : capHeight (AmbidextrousSofa.horizontalMirror U) = 1 := by
    rw [capHeight_horizontalMirror, hheight]
  have haffineV : ∀ x ∈ middleHalfInterval
      (horizontalLeft (AmbidextrousSofa.horizontalMirror U)) (horizontalRight (AmbidextrousSofa.horizontalMirror U)),
      capRoof (AmbidextrousSofa.horizontalMirror U) x = (-m) * x + c := by
    intro x hx
    rw [horizontalLeft_horizontalMirror hU.isCap,
      horizontalRight_horizontalMirror hU.isCap] at hx
    rw [capRoof_horizontalMirror, haffine (-x) (by
      change -horizontalRight U + (-horizontalLeft U - -horizontalRight U) / 4 ≤ x ∧
        x ≤ -horizontalLeft U - (-horizontalLeft U - -horizontalRight U) / 4 at hx
      change horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4 ≤ -x ∧
        -x ≤ horizontalRight U - (horizontalRight U - horizontalLeft U) / 4
      constructor <;> linarith [hx.1, hx.2])]
    ring
  have heq := hV.middle_right_eq_one_of_affine_nonneg hheightV (neg_nonneg.mpr hm) haffineV
  rw [horizontalLeft_horizontalMirror hU.isCap,
    horizontalRight_horizontalMirror hU.isCap, capRoof_horizontalMirror] at heq
  convert heq using 1
  congr 1
  ring

end AmbidextrousSofa
