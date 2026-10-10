module

public import AmbidextrousSofa.Analysis.ThreeAngleWidth
public import AmbidextrousSofa.Analysis.PartialEndpointComplementarity

@[expose] public section

/-!
# Actual proper width bounds in both middle orientations

The partial endpoint identities are proved for the original maximizer.
For a descending middle, reflection swaps the two literal endpoint
heights and the two original pressure values inside the finite
three-angle comparison. The reflected cap is used only as a comparison
body. No maximality or outgoing endpoint law is asserted for it.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem IsJointCapMaximizer.threeAngle_reference_le {U : Set Plane} {α : ℝ}
    (hU : IsJointCapMaximizer U α) : 41 / 50 ≤ threeAngleComparisonScore U :=
  forty_one_fiftieths_lt_half_M.le.trans (hU.reference_le.trans
    (hU.isCap.capScore_le_threeAngleComparisonScore hU.threeAngle_last_lt_terminal.le hU.angle_mem.2))

theorem IsJointCapMaximizer.centered_partial_endpoint_laws_low_right
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α) {a h : ℝ}
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1) (hright : capRoof U (a / 2) = 1 - h)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c) :
    capRoof U (-a) = 1 / 2 + h / 4 +
      (3 * partialBarrier U α (-a / 2) - partialBarrier U α (a / 2)) / 4 ∧
    capRoof U a = 1 / 2 - 3 * h / 4 +
      (3 * partialBarrier U α (a / 2) - partialBarrier U α (-a / 2)) / 4 := by
  have hAff : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c := by
    simpa only [hl, hr, middleHalfInterval_centered] using haffine
  obtain ⟨hR, hL⟩ := hU.partial_endpoint_heights_eq_pressures_of_affine hproper hheight hAff
  unfold partialRightEndpointPressure rightEndpointPressure at hR
  unfold partialLeftEndpointPressure leftEndpointPressure at hL
  rw [hl, hr, show a - (a - -a) / 4 = a / 2 by ring,
    show -a + (a - -a) / 4 = -a / 2 by ring, hleft, hright] at hR hL
  constructor <;> linarith only [hR, hL]

theorem IsJointCapMaximizer.centered_proper_half_width_bounds_of_affine_nonneg
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α) {a m c : ℝ}
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hheight : capHeight U = 1) (hm : 0 ≤ m)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    1001 / 1000 < a ∧ a < 37 / 25 ∧ 1 - capRoof U (-a / 2) < 17 / 50 := by
  have hw : capWidth U = 2 * a := by unfold capWidth; rw [hl, hr]; ring
  have ha0 : 0 < a := by linarith only [hU.width_bounds.1, one_lt_M, hw]
  have ha1 : a < 3 := by linarith only [hU.width_bounds.2, hw]
  let h := 1 - capRoof U (-a / 2)
  have hh0 : 0 ≤ h := sub_nonneg.mpr
    (capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip _)
  have hh1 : h < 1 / 2 := by
    have hend := (hU.middle_endpoints_gt_half_of_affine hheight ⟨m, c, haffine⟩).1
    rw [hl, hr, show -a + (a - -a) / 4 = -a / 2 by ring] at hend
    dsimp [h]
    linarith only [hend]
  have hleft : capRoof U (-a / 2) = 1 - h := by dsimp [h]; ring
  have hright : capRoof U (a / 2) = 1 := by
    have h := hU.middle_right_eq_one_of_affine_nonneg hheight hm haffine
    rw [hl, hr, show a - (a - -a) / 4 = a / 2 by ring] at h
    exact h
  have hAff : ∃ m' c' : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m' * x + c' := by
    exact ⟨m, c, by simpa only [hl, hr, middleHalfInterval_centered] using haffine⟩
  have hEP := hU.centered_partial_endpoint_laws hproper hheight hl hr hleft hright hAff
  exact hU.isCap.threeAngle_width_bounds_of_endpoint_laws ha0 ha1 hh0 hh1
    hl hr hleft hright hAff (partialBarrier_nonneg U α (a / 2))
    (partialBarrier_nonneg U α (-a / 2)) hEP.1 hEP.2 hU.threeAngle_reference_le

theorem IsJointCapMaximizer.centered_proper_half_width_bounds_of_affine_nonpos
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α) {a m c : ℝ}
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hheight : capHeight U = 1) (hm : m ≤ 0)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    1001 / 1000 < a ∧ a < 37 / 25 ∧ 1 - capRoof U (a / 2) < 17 / 50 := by
  have hw : capWidth U = 2 * a := by unfold capWidth; rw [hl, hr]; ring
  have ha0 : 0 < a := by linarith only [hU.width_bounds.1, one_lt_M, hw]
  have ha1 : a < 3 := by linarith only [hU.width_bounds.2, hw]
  let h := 1 - capRoof U (a / 2)
  have hh0 : 0 ≤ h := sub_nonneg.mpr
    (capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip _)
  have hh1 : h < 1 / 2 := by
    have hend := (hU.middle_endpoints_gt_half_of_affine hheight ⟨m, c, haffine⟩).2
    rw [hl, hr, show a - (a - -a) / 4 = a / 2 by ring] at hend
    dsimp [h]
    linarith only [hend]
  have hright : capRoof U (a / 2) = 1 - h := by dsimp [h]; ring
  have hleft : capRoof U (-a / 2) = 1 := by
    have h := hU.middle_left_eq_one_of_affine_nonpos hheight hm haffine
    rw [hl, hr, show -a + (a - -a) / 4 = -a / 2 by ring] at h
    exact h
  have hAff : ∃ m' c' : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m' * x + c' := by
    exact ⟨m, c, by simpa only [hl, hr, middleHalfInterval_centered] using haffine⟩
  have hEP := hU.centered_partial_endpoint_laws_low_right hproper hheight hl hr hleft hright hAff
  have hVl : horizontalLeft (horizontalMirror U) = -a := by
    rw [horizontalLeft_horizontalMirror hU.isCap, hr]
  have hVr : horizontalRight (horizontalMirror U) = a := by
    rw [horizontalRight_horizontalMirror hU.isCap, hl, neg_neg]
  have hVleft : capRoof (horizontalMirror U) (-a / 2) = 1 - h := by
    rw [capRoof_horizontalMirror, show -(-a / 2) = a / 2 by ring]
    exact hright
  have hVright : capRoof (horizontalMirror U) (a / 2) = 1 := by
    rw [capRoof_horizontalMirror, show -(a / 2) = -a / 2 by ring]
    exact hleft
  have hVaffine : ∃ m' c' : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2),
      capRoof (horizontalMirror U) x = m' * x + c' := by
    refine ⟨-m, c, ?_⟩
    intro x hx
    have hxU : -x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U) := by
      rw [hl, hr, middleHalfInterval_centered]
      constructor <;> linarith only [hx.1, hx.2]
    rw [capRoof_horizontalMirror, haffine (-x) hxU]
    ring
  have hVEPR : capRoof (horizontalMirror U) a = 1 / 2 + h / 4 +
      (3 * partialBarrier U α (-a / 2) - partialBarrier U α (a / 2)) / 4 := by
    rw [capRoof_horizontalMirror]
    exact hEP.1
  have hVEPL : capRoof (horizontalMirror U) (-a) = 1 / 2 - 3 * h / 4 +
      (3 * partialBarrier U α (a / 2) - partialBarrier U α (-a / 2)) / 4 := by
    rw [capRoof_horizontalMirror, neg_neg]
    exact hEP.2
  have hVscore : 41 / 50 ≤ threeAngleComparisonScore (horizontalMirror U) := by
    rw [threeAngleComparisonScore_horizontalMirror hU.isCap]
    exact hU.threeAngle_reference_le
  exact hU.isCap.horizontalMirror.threeAngle_width_bounds_of_endpoint_laws ha0 ha1 hh0 hh1
    hVl hVr hVleft hVright hVaffine (partialBarrier_nonneg U α (-a / 2))
    (partialBarrier_nonneg U α (a / 2)) hVEPR hVEPL hVscore

theorem IsJointCapMaximizer.centered_proper_half_width_bounds_of_affine
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α) {a m c : ℝ}
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    1001 / 1000 < a ∧ a < 37 / 25 := by
  by_cases hm : 0 ≤ m
  · have h := hU.centered_proper_half_width_bounds_of_affine_nonneg
      hproper hl hr hheight hm haffine
    exact ⟨h.1, h.2.1⟩
  · have h := hU.centered_proper_half_width_bounds_of_affine_nonpos
      hproper hl hr hheight (le_of_not_ge hm) haffine
    exact ⟨h.1, h.2.1⟩

theorem IsJointCapMaximizer.proper_quarter_width_bounds
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α)
    (hproper : α < Real.pi / 2) :
    1001 / 2000 < capWidth U / 4 ∧ capWidth U / 4 < 37 / 50 := by
  have hcenter : IsJointCapMaximizer (centeredCap U) α :=
    hU.of_score_le hU.isCap.centeredCap hU.angle_mem (by rw [capScore_centeredCap hU.isCap])
  obtain ⟨V, hV, hproj, hheight, _, m, c, haffine⟩ := hcenter.exists_heightOne_affine_middle
  let a := capWidth U / 2
  have hl : horizontalLeft V = -a := by
    calc
      _ = horizontalLeft (centeredCap U) := by unfold horizontalLeft; rw [hproj]
      _ = _ := by rw [horizontalLeft_centeredCap hU.isCap]; dsimp [a]; ring
  have hr : horizontalRight V = a := by
    calc
      _ = horizontalRight (centeredCap U) := by unfold horizontalRight; rw [hproj]
      _ = _ := horizontalRight_centeredCap hU.isCap
  have h := hV.centered_proper_half_width_bounds_of_affine hproper hl hr hheight haffine
  dsimp [a] at h
  constructor <;> linarith only [h.1, h.2]

end AmbidextrousSofa
