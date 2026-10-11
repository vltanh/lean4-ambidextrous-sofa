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
    (hU.isCap.capScore_le_threeAngleComparisonScore hU.threeAngle_last_lt_terminal.le
      hU.angle_mem.2))

theorem IsJointCapMaximizer.centered_proper_half_width_bounds_of_affine_nonneg
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α) {a m c : ℝ}
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hheight : capHeight U = 1) (hm : 0 ≤ m)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    1001 / 1000 < a ∧ a < 37 / 25 ∧ 1 - capRoof U (-a / 2) < 17 / 50 := by
  have hw : capWidth U = 2 * a := by unfold capWidth; rw [hl, hr]; ring
  have hend := (hU.middle_endpoints_gt_half_of_affine hheight ⟨m, c, haffine⟩).1
  rw [hl, hr, show -a + (a - -a) / 4 = -a / 2 by ring] at hend
  have hright := hU.middle_right_eq_one_of_affine_nonneg hheight hm haffine
  rw [hr, hw, show a - 2 * a / 4 = a / 2 by ring] at hright
  have hAff : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c :=
    ⟨m, c, by simpa only [hl, hr, middleHalfInterval_centered] using haffine⟩
  have hEP := hU.centered_partial_endpoint_laws (h := 1 - capRoof U (-a / 2)) hproper hheight
    hl hr (by ring) hright hAff
  exact hU.isCap.threeAngle_width_bounds_of_endpoint_laws (h := 1 - capRoof U (-a / 2))
    (by linarith [hU.width_bounds.1, one_lt_M]) (by linarith [hU.width_bounds.2])
    (sub_nonneg.2 (capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip _)) (by linarith) hl hr
    (by ring) hright hAff (partialBarrier_nonneg U α _) (partialBarrier_nonneg U α _) hEP.1 hEP.2
    hU.threeAngle_reference_le

theorem IsJointCapMaximizer.centered_proper_half_width_bounds_of_affine_nonpos
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α) {a m c : ℝ}
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hheight : capHeight U = 1) (hm : m ≤ 0)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    1001 / 1000 < a ∧ a < 37 / 25 ∧ 1 - capRoof U (a / 2) < 17 / 50 := by
  have hw : capWidth U = 2 * a := by unfold capWidth; rw [hl, hr]; ring
  have hend := (hU.middle_endpoints_gt_half_of_affine hheight ⟨m, c, haffine⟩).2
  rw [hl, hr, show a - (a - -a) / 4 = a / 2 by ring] at hend
  have hleft := hU.middle_left_eq_one_of_affine_nonpos hheight hm haffine
  rw [hl, hw, show -a + 2 * a / 4 = -a / 2 by ring] at hleft
  obtain ⟨hR, hL⟩ :=
    hU.partial_endpoint_heights_eq_pressures_of_affine hproper hheight ⟨m, c, haffine⟩
  unfold partialRightEndpointPressure rightEndpointPressure at hR
  unfold partialLeftEndpointPressure leftEndpointPressure at hL
  rw [hl, hr, show a - (a - -a) / 4 = a / 2 by ring, show -a + (a - -a) / 4 = -a / 2 by ring,
    hleft] at hR hL
  rw [hl, hr, middleHalfInterval_centered] at haffine
  have hV := capRoof_horizontalMirror U
  exact hU.isCap.horizontalMirror.threeAngle_width_bounds_of_endpoint_laws (a := a)
    (h := 1 - capRoof U (a / 2)) (by linarith [hU.width_bounds.1, one_lt_M])
    (by linarith [hU.width_bounds.2])
    (sub_nonneg.2 (capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip _)) (by linarith)
    (by rw [horizontalLeft_horizontalMirror hU.isCap, hr])
    (by rw [horizontalRight_horizontalMirror hU.isCap, hl, neg_neg])
    (by rw [hV, neg_div, neg_neg]; ring) (by rw [hV, ← neg_div, hleft])
    ⟨-m, c, fun x hx => by
      rw [hV, haffine (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩]; ring⟩
    (partialBarrier_nonneg U α (-a / 2)) (partialBarrier_nonneg U α (a / 2))
    (by rw [hV]; linarith) (by rw [hV, neg_neg]; linarith)
    (by rw [threeAngleComparisonScore_horizontalMirror hU.isCap]; exact hU.threeAngle_reference_le)

theorem IsJointCapMaximizer.proper_quarter_width_bounds
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α)
    (hproper : α < Real.pi / 2) :
    1001 / 2000 < capWidth U / 4 ∧ capWidth U / 4 < 37 / 50 := by
  obtain ⟨V, hV, hproj, hheight, -, m, c, haffine⟩ := (hU.of_score_le hU.isCap.centeredCap
    hU.angle_mem (by rw [capScore_centeredCap hU.isCap])).exists_heightOne_affine_middle
  have hl : horizontalLeft V = -(capWidth U / 2) :=
    (congrArg sInf hproj).trans ((horizontalLeft_centeredCap hU.isCap).trans (neg_div _ _))
  have hr : horizontalRight V = capWidth U / 2 :=
    (congrArg sSup hproj).trans (horizontalRight_centeredCap hU.isCap)
  have h : 1001 / 1000 < capWidth U / 2 ∧ capWidth U / 2 < 37 / 25 := by
    rcases le_total 0 m with hm | hm
    · exact (hV.centered_proper_half_width_bounds_of_affine_nonneg hproper hl hr hheight hm
        haffine).imp_right And.left
    · exact (hV.centered_proper_half_width_bounds_of_affine_nonpos hproper hl hr hheight hm
        haffine).imp_right And.left
  constructor <;> linarith [h.1, h.2]

end AmbidextrousSofa
