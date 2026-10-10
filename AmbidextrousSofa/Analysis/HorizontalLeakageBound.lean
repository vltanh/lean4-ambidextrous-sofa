import AmbidextrousSofa.Analysis.HorizontalLeakageOccupation
import AmbidextrousSofa.Analysis.HorizontalEndpointBounds
import AmbidextrousSofa.Analysis.CapReflection

/-!
# The actual endpoint niches satisfy every applicable leakage row

The maximizing cap supplies its bounded curvature density, endpoint
heights, source laws and first crossings. The exact row bounds the
resulting compact quadratic envelope. The open-arc kernel and the box
wall then bound every visited angle, and reflection supplies the other
endpoint.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem sin_horizontal_box_angle {C : ℝ} (hC0 : 0 ≤ C) (hC1 : C ≤ 1) :
    Real.sin (2 * Real.arctan ((1 - C) / (1 + C))) = horizontalLeakageBoxSine C := by
  let b : ℝ := 2 * Real.arctan ((1 - C) / (1 + C))
  have hb0 : 0 ≤ b := by
    have hz : 0 ≤ (1 - C) / (1 + C) := div_nonneg (sub_nonneg.mpr hC1) (by positivity)
    have ha := Real.arctan_nonneg.mpr hz
    dsimp [b]
    linarith
  have hbπ : b ≤ Real.pi := by
    dsimp [b]
    linarith [Real.arctan_lt_pi_div_two ((1 - C) / (1 + C))]
  have hs0 : 0 ≤ Real.sin b := Real.sin_nonneg_of_mem_Icc ⟨hb0, hbπ⟩
  have hB0 : 0 ≤ horizontalLeakageBoxSine C := by
    unfold horizontalLeakageBoxSine
    apply div_nonneg _ (by positivity)
    nlinarith [mul_nonneg hC0 (sub_nonneg.mpr hC1)]
  have hcos : Real.cos b = 2 * C / (1 + C ^ 2) := cos_horizontal_box_angle hC0
  have hsq : Real.sin b ^ 2 = horizontalLeakageBoxSine C ^ 2 := by
    calc
      _ = 1 - Real.cos b ^ 2 := by nlinarith [Real.sin_sq_add_cos_sq b]
      _ = _ := by
        rw [hcos]
        unfold horizontalLeakageBoxSine
        field_simp [show (1 + C ^ 2) ≠ 0 by positivity]
        <;> ring
  exact le_antisymm ((sq_le_sq₀ hs0 hB0).mp hsq.le)
    ((sq_le_sq₀ hB0 hs0).mp hsq.ge)

theorem horizontalLeakageBoxSine_le_sin_of_box_angle_le {C t : ℝ}
    (hC0 : 0 ≤ C) (hC1 : C ≤ 1) (ht : t ≤ Real.pi / 2)
    (hbt : 2 * Real.arctan ((1 - C) / (1 + C)) ≤ t) :
    horizontalLeakageBoxSine C ≤ Real.sin t := by
  rw [← sin_horizontal_box_angle hC0 hC1]
  apply Real.sin_le_sin_of_le_of_le_pi_div_two _ ht hbt
  have hz : 0 ≤ (1 - C) / (1 + C) := div_nonneg (sub_nonneg.mpr hC1) (by positivity)
  have ha := Real.arctan_nonneg.mpr hz
  linarith [Real.pi_pos]

theorem IsFullCapMaximizer.right_endpoint_niche_le_horizontalLeakageRow
    {U : Set Plane} (hU : IsFullCapMaximizer U) (R : HorizontalLeakageRow) {C : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = 1)
    (hC : 2 / 3 < C) (haC : R.a ≤ C) (hCb : C ≤ R.b) :
    sweptNiche U (Real.pi / 2) C ≤ R.B := by
  have hC0 : 0 ≤ C := by linarith
  have hC1 : C < 1 := hCb.trans_lt R.b_lt_one
  have hwidth : capWidth U = 4 * C := by unfold capWidth; rw [hl, hr]; ring
  have hheightBounds := (hU.horizontal_endpoint_heights_bounds
    hl hr hC0 hC1.le hheight hmiddle).1
  have hH := R.box_height_le hC0 hCb
  have he0 : 1 / 2 - R.H / 4 ≤ capRoof U (horizontalRight U) := by
    linarith [hheightBounds.1]
  have he1 : capRoof U (horizontalRight U) ≤ 1 / 2 + 3 * R.H / 4 := by
    linarith [hheightBounds.2]
  have hepos : 0 < capRoof U (horizontalRight U) := by linarith [R.H_le_one]
  have hcross : capRoof U (horizontalRight U) ≤ 3 * C * R.T - R.T ^ 2 / 2 := by
    have hmul := mul_nonneg (sub_nonneg.mpr haC) R.T_nonneg
    nlinarith [R.crossing]
  have henergy : 9 * C ^ 2 - capRoof U (horizontalRight U) *
      (1 - capRoof U (horizontalRight U)) ≤
        (2 + (R.h ^ 2 + 2 * R.h) / 4) ^ 2 := by
    have hsqC := (sq_le_sq₀ hC0 (R.a_pos.le.trans R.a_le_b)).2 hCb
    have helo : 0 ≤ capRoof U (horizontalRight U) - 1 / 2 + 3 * R.H / 4 := by
      linarith [R.H_nonneg]
    have hehi : 0 ≤ 3 * R.H / 4 - (capRoof U (horizontalRight U) - 1 / 2) := by
      linarith
    have hsqe := mul_nonneg helo hehi
    nlinarith [R.excess]
  have haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = (0 : ℝ) * x + 1 := by
    simpa only [zero_mul, zero_add] using hmiddle
  obtain ⟨ρ, hρ, hb, hK, heq, _hnegative⟩ :=
    hU.curvature_density_corner_controls hheight haffine
  have hρ0 := fun s => (hb s).1
  have hκ := fun s => (hb s).2
  obtain ⟨A, hA, henvelope⟩ := hU.exists_horizontal_quadratic_excess_envelope
    hheight hmiddle hwidth hC hepos hρ hρ0 hK hκ heq
    R.h_nonneg R.h_lt_one R.T_nonneg hcross henergy
  let b : ℝ := 2 * Real.arctan ((1 - C) / (1 + C))
  have htb : R.t ≤ b := R.box_angle_le hC0 hCb
  apply sweptNiche_le_of_forall (by linarith [Real.pi_pos]) R.B_nonneg
  intro t ht
  apply (min_le_left (firstWall U t C) (secondWall U t C)).trans
  by_cases hsmall : t ≤ b
  · exact (hU.isCap.firstWall_nonpos_before_horizontal_box_angle
      hl hr hC0 hC1.le ht hsmall).trans R.B_nonneg
  · have hbt : b ≤ t := (lt_of_not_ge hsmall).le
    have hkernel := horizontal_density_kernel_le_envelope_moments
      hρ hρ0 hK R.h_nonneg ht hbt henvelope
    have hfactor : max (A - b) 0 ≤ max (R.T - R.t) 0 :=
      max_le_max (by linarith [hA.2]) le_rfl
    have hmom : horizontalLeakageA0 R.h * max (A - b) 0 + horizontalLeakageA1 R.h ≤
        R.B * horizontalLeakageBoxSine R.b := by
      apply (add_le_add_right
        (mul_le_mul_of_nonneg_left hfactor (horizontalLeakageA0_nonneg R.h_nonneg)) _).trans
      exact R.leakage
    have hsin : horizontalLeakageBoxSine R.b ≤ Real.sin t :=
      (horizontalLeakageBoxSine_antitone hC0 hCb).trans
        (horizontalLeakageBoxSine_le_sin_of_box_angle_le hC0 hC1.le ht.2.le hbt)
    have hfull := hkernel.trans (hmom.trans
      (mul_le_mul_of_nonneg_left hsin R.B_nonneg))
    have he := hU.firstWall_eq_horizontal_density_kernel hheight hmiddle hρ hρ0 hK heq ht
    have hright : horizontalRight U - capWidth U / 4 = C := by rw [hr, hwidth]; ring
    rw [hright] at he
    rw [he]
    exact (div_le_iff₀ (Real.sin_pos_of_pos_of_lt_pi ht.1
      (by linarith [ht.2, Real.pi_pos]))).mpr hfull

/-- Both actual endpoint niches satisfy the same applicable rational row.
The reflected cap is itself a full maximizer and constructs its own
literal density; no reflected representative at an atom is assumed. -/
theorem IsFullCapMaximizer.endpoint_niches_le_horizontalLeakageRow
    {U : Set Plane} (hU : IsFullCapMaximizer U) (R : HorizontalLeakageRow) {C : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = 1)
    (hC : 2 / 3 < C) (haC : R.a ≤ C) (hCb : C ≤ R.b) :
    sweptNiche U (Real.pi / 2) (-C) ≤ R.B ∧
      sweptNiche U (Real.pi / 2) C ≤ R.B := by
  have hlV : horizontalLeft (horizontalMirror U) = -2 * C := by
    rw [horizontalLeft_horizontalMirror hU.isCap, hr]
    ring
  have hrV : horizontalRight (horizontalMirror U) = 2 * C := by
    rw [horizontalRight_horizontalMirror hU.isCap, hl]
    ring
  have hmiddleV : ∀ x ∈ middleHalfInterval
      (horizontalLeft (horizontalMirror U)) (horizontalRight (horizontalMirror U)),
      capRoof (horizontalMirror U) x = 1 := by
    intro x hx
    rw [capRoof_horizontalMirror]
    apply hmiddle
    rw [hlV, hrV] at hx
    rw [hl, hr]
    change -2 * C + (2 * C - -2 * C) / 4 ≤ -x ∧
      -x ≤ 2 * C - (2 * C - -2 * C) / 4
    change -2 * C + (2 * C - -2 * C) / 4 ≤ x ∧
      x ≤ 2 * C - (2 * C - -2 * C) / 4 at hx
    constructor <;> linarith [hx.1, hx.2]
  have hheightV : capHeight (horizontalMirror U) = 1 := by
    rw [capHeight_horizontalMirror, hheight]
  have hleft := hU.horizontalMirror.right_endpoint_niche_le_horizontalLeakageRow
    R hlV hrV hheightV hmiddleV hC haC hCb
  exact ⟨by simpa only [sweptNiche_horizontalMirror] using hleft,
    hU.right_endpoint_niche_le_horizontalLeakageRow R hl hr hheight hmiddle hC haC hCb⟩

end AmbidextrousSofa
