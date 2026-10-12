module

public import AmbidextrousSofa.Analysis.ThreeAngleWidth
public import AmbidextrousSofa.Analysis.PartialEndpointComplementarity

@[expose] public section

/-!
# Actual proper width bounds in both middle orientations

Centering and the height-one middle-chord replacement keep the maximizing
angle. The partial endpoint identities are proved for the original
maximizer. For a descending middle, reflection swaps the two literal
endpoint heights and the two original pressure values inside the finite
three-angle comparison. The reflected cap is used only as a comparison
body. No maximality or outgoing endpoint law is asserted for it.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

/-- A joint maximizer has a centered height-one replacement with an affine middle at the same
angle. -/
theorem IsJointCapMaximizer.exists_centered_heightOne_affine {U : Set Plane} {α : ℝ}
    (hU : IsJointCapMaximizer U α) :
    ∃ V : Set Plane, IsJointCapMaximizer V α ∧ horizontalLeft V = -2 * (capWidth U / 4) ∧
      horizontalRight V = 2 * (capWidth U / 4) ∧ capHeight V = 1 ∧ ∃ m c : ℝ, ∀ x ∈
        middleHalfInterval (horizontalLeft V) (horizontalRight V), capRoof V x = m * x + c := by
  obtain ⟨V, hV, hproj, hheight, -, haffine⟩ := (hU.of_score_le hU.isCap.centeredCap
    hU.angle_mem (capScore_centeredCap hU.isCap α).ge).exists_heightOne_affine_middle
  refine ⟨V, hV, (congrArg sInf hproj).trans ?_, (congrArg sSup hproj).trans ?_, hheight, haffine⟩
  · rw [← horizontalLeft, horizontalLeft_centeredCap hU.isCap]; ring
  · rw [← horizontalRight, horizontalRight_centeredCap hU.isCap]; ring

/-- Both middle orientations give the proper width bounds; a rising middle also bounds the drop
`1 - capRoof U (-a / 2)` of its low middle endpoint. -/
theorem IsJointCapMaximizer.centered_proper_half_width_bounds
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α) {a m c : ℝ}
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    1 < a ∧ a < 37 / 25 ∧ (0 ≤ m → 1 - capRoof U (-a / 2) < 1 / 3) := by
  have hw : capWidth U = 2 * a := by unfold capWidth; rw [hl, hr]; ring
  have ha : 0 < a ∧ a < 3 := ⟨by linarith only [hw, hU.width_bounds.1, one_lt_M],
    by linarith only [hw, hU.width_bounds.2]⟩
  have hscore : M / 2 ≤ threeAngleComparisonScore U :=
    hU.reference_le.trans
      (hU.isCap.capScore_le_threeAngleComparisonScore hU.threeAngle_last_lt_terminal.le
        hU.angle_mem.2)
  have h1 := capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip
  have hq := partialBarrier_nonneg U α
  -- The endpoint identities, at the quarter points `±a / 2` of the centered cap.
  have hend := hU.middle_endpoints_gt_half_of_affine hheight ⟨m, c, haffine⟩
  obtain ⟨hR, hL⟩ :=
    hU.partial_endpoint_heights_eq_pressures_of_affine hproper hheight ⟨m, c, haffine⟩
  simp only [partialRightEndpointPressure, rightEndpointPressure, partialLeftEndpointPressure,
    leftEndpointPressure, hl, hr, show a - (a - -a) / 4 = a / 2 by ring,
    show -a + (a - -a) / 4 = -a / 2 by ring] at hR hL hend
  rcases le_total 0 m with hm | hm
  · have hright := hU.middle_right_eq_one_of_affine_nonneg hheight hm haffine
    rw [hr, hw, show a - 2 * a / 4 = a / 2 by ring] at hright
    rw [hl, hr, middleHalfInterval_centered] at haffine
    have h := hU.isCap.threeAngle_width_bounds_of_endpoint_laws (h := 1 - capRoof U (-a / 2))
      ha.1 ha.2 (sub_nonneg.2 (h1 _)) (by linarith only [hend.1]) hl hr (by ring) hright
      ⟨m, c, haffine⟩ (hq (a / 2)) (hq (-a / 2)) (by linear_combination hR + 3 / 4 * hright)
      (by linear_combination hL - 1 / 4 * hright) hscore
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  -- A descending middle: compare the reflected cap.
  have hleft := hU.middle_left_eq_one_of_affine_nonpos hheight hm haffine
  rw [hl, hw, show -a + 2 * a / 4 = -a / 2 by ring] at hleft
  rw [hl, hr, middleHalfInterval_centered] at haffine
  have hV := capRoof_horizontalMirror U
  have h := hU.isCap.horizontalMirror.threeAngle_width_bounds_of_endpoint_laws (a := a)
    (h := 1 - capRoof U (a / 2)) ha.1 ha.2 (sub_nonneg.2 (h1 _)) (by linarith only [hend.2])
    (by rw [horizontalLeft_horizontalMirror hU.isCap, hr])
    (by rw [horizontalRight_horizontalMirror hU.isCap, hl, neg_neg])
    (by rw [hV, neg_div, neg_neg]; ring) (by rw [hV, ← neg_div, hleft])
    ⟨-m, c, fun x hx => by
      rw [hV, haffine (-x) ⟨by linarith only [hx.2], by linarith only [hx.1]⟩]; ring⟩
    (hq (-a / 2)) (hq (a / 2)) (by rw [hV]; linear_combination hL + 3 / 4 * hleft)
    (by rw [hV, neg_neg]; linear_combination hR - 1 / 4 * hleft)
    (by rwa [threeAngleComparisonScore_horizontalMirror hU.isCap])
  exact ⟨h.1, h.2.1, fun _ => by linarith only [hleft]⟩

theorem IsJointCapMaximizer.proper_quarter_width_bounds
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α)
    (hproper : α < Real.pi / 2) :
    1 / 2 < capWidth U / 4 ∧ capWidth U / 4 < 37 / 50 := by
  obtain ⟨V, hV, hl, hr, hheight, m, c, haffine⟩ := hU.exists_centered_heightOne_affine
  have h := hV.centered_proper_half_width_bounds hproper (hl.trans (neg_mul _ _)) hr hheight haffine
  constructor <;> linarith only [h.1, h.2.1]

end AmbidextrousSofa
