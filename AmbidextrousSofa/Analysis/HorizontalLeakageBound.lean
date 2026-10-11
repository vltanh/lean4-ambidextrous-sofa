module

public import AmbidextrousSofa.Analysis.HorizontalLeakageOccupation
public import AmbidextrousSofa.Analysis.HorizontalEndpointBounds
public import AmbidextrousSofa.Analysis.CapReflection

@[expose] public section

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

theorem sin_horizontal_box_angle {C : ℝ} (hC0 : 0 ≤ C) :
    Real.sin (2 * Real.arctan ((1 - C) / (1 + C))) = horizontalLeakageBoxSine C := by
  rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan, horizontalLeakageBoxSine]
  have h1 : 0 < 1 + C := by linarith
  field_simp
  rw [Real.sq_sqrt (by positivity)]
  field_simp
  ring

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
  have hwidth : capWidth U = 4 * C := by rw [capWidth, hl, hr]; ring
  have he := (hU.horizontal_endpoint_laws hl hr hC0 hheight hmiddle).1
  have hn := hU.isCap.middle_niche_le_box_height_of_endpoints hl hr hC0 hC1.le
  have hH := R.box_height_le hC0 hCb
  have he0 : 1 / 2 - R.H / 4 ≤ capRoof U (horizontalRight U) := by
    linarith [hn.1, sweptNiche_nonneg U (Real.pi / 2) C]
  have he1 : capRoof U (horizontalRight U) ≤ 1 / 2 + 3 * R.H / 4 := by
    linarith [hn.2, sweptNiche_nonneg U (Real.pi / 2) (-C)]
  obtain ⟨ρ, hρ, hb, hK, heq, -⟩ :=
    hU.curvature_density_corner_controls hheight (m := 0) (c := 1) (by simpa using hmiddle)
  have hρ0 s := (hb s).1
  obtain ⟨A, hA, henvelope⟩ := hU.exists_horizontal_quadratic_excess_envelope hheight hmiddle
    hwidth hC (by linarith [R.H_le_one]) hρ hρ0 hK (fun s => (hb s).2) heq
    R.h_nonneg R.h_lt_one R.T_nonneg
    (by nlinarith [R.crossing, mul_nonneg (sub_nonneg.mpr haC) R.T_nonneg])
    (by nlinarith [R.excess, R.H_nonneg, (sq_le_sq₀ hC0 (R.a_pos.le.trans R.a_le_b)).2 hCb])
  have htb := R.box_angle_le hC0 hCb
  refine sweptNiche_le_of_forall (by linarith [Real.pi_pos]) R.B_nonneg
    fun t ht => (min_le_left _ _).trans ?_
  rcases le_or_gt t (2 * Real.arctan ((1 - C) / (1 + C))) with hsmall | hbt
  · exact (hU.isCap.firstWall_nonpos_before_horizontal_box_angle hl hr hC0 hC1.le ht
      hsmall).trans R.B_nonneg
  have he := hU.firstWall_eq_horizontal_density_kernel hheight hmiddle hρ hρ0 hK heq ht
  rw [show horizontalRight U - capWidth U / 4 = C from (centered_quarter_points hl hr).2.1] at he
  rw [he, div_le_iff₀ (sin_cos_pos_of_mem_quarter ht).1]
  calc _ ≤ _ := horizontal_density_kernel_le_envelope_moments hρ hρ0 hK R.h_nonneg ht hbt.le
        henvelope
    _ ≤ R.B * horizontalLeakageBoxSine R.b := by
      refine le_trans ?_ R.leakage
      gcongr
      · exact horizontalLeakageA0_nonneg R.h_nonneg
      · linarith [hA.2]
    _ ≤ R.B * Real.sin t := by
      refine mul_le_mul_of_nonneg_left ?_ R.B_nonneg
      refine (horizontalLeakageBoxSine_antitone hC0 hCb).trans ?_
      rw [← sin_horizontal_box_angle hC0]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [R.t_nonneg, Real.pi_pos])
        ht.2.le hbt.le

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
  obtain ⟨hl', hr', hheight', hmid⟩ :=
    hU.isCap.horizontalMirror_centered rfl hl hr hheight hmiddle
  have hleft := hU.horizontalMirror.right_endpoint_niche_le_horizontalLeakageRow R hl' hr'
    hheight' hmid hC haC hCb
  exact ⟨by simpa only [sweptNiche_horizontalMirror] using hleft,
    hU.right_endpoint_niche_le_horizontalLeakageRow R hl hr hheight hmiddle hC haC hCb⟩

end AmbidextrousSofa
