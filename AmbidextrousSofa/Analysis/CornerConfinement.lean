module

public import AmbidextrousSofa.Analysis.CornerTrigonometry
public import AmbidextrousSofa.Geometry.BarrierAnalysis

@[expose] public section

/-!
# Actual attached corners lie over the middle interval

The corner is the intersection of the two actual attached inner walls.
The unit-height box and the two attained middle endpoint contacts bound
its horizontal coordinate directly. The rational trigonometric margin
then confines every corner, including corners of negative height. No
curvature bound, lifted cap, or change of support convention is required.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

def attachedCorner (U : Set Plane) (θ : ℝ) : Plane :=
  ((support U (unitNormal θ) - 1) * Real.cos θ -
      (support U (companionNormal θ) - 1) * Real.sin θ,
    (support U (unitNormal θ) - 1) * Real.sin θ +
      (support U (companionNormal θ) - 1) * Real.cos θ)

theorem firstWall_le_secondWall_iff {U : Set Plane} {θ x : ℝ}
    (hs : 0 < Real.sin θ) (hc : 0 < Real.cos θ) :
    firstWall U θ x ≤ secondWall U θ x ↔ (attachedCorner U θ).1 ≤ x := by
  rw [firstWall, secondWall, div_le_div_iff₀ hs hc]
  have := congrArg (x * ·) (Real.cos_sq_add_sin_sq θ)
  dsimp only [attachedCorner] at this ⊢
  constructor <;> intro h <;> linarith

theorem secondWall_le_firstWall_iff {U : Set Plane} {θ x : ℝ}
    (hs : 0 < Real.sin θ) (hc : 0 < Real.cos θ) :
    secondWall U θ x ≤ firstWall U θ x ↔ x ≤ (attachedCorner U θ).1 := by
  rw [secondWall, firstWall, div_le_div_iff₀ hc hs]
  have := congrArg (x * ·) (Real.cos_sq_add_sin_sq θ)
  dsimp only [attachedCorner] at this ⊢
  constructor <;> intro h <;> linarith

theorem cornerWall_eq_firstWall_of_corner_le {U : Set Plane} {θ x : ℝ}
    (hs : 0 < Real.sin θ) (hc : 0 < Real.cos θ) (hx : (attachedCorner U θ).1 ≤ x) :
    cornerWall U θ x = firstWall U θ x :=
  min_eq_left ((firstWall_le_secondWall_iff hs hc).mpr hx)

theorem cornerWall_eq_secondWall_of_le_corner {U : Set Plane} {θ x : ℝ}
    (hs : 0 < Real.sin θ) (hc : 0 < Real.cos θ) (hx : x ≤ (attachedCorner U θ).1) :
    cornerWall U θ x = secondWall U θ x :=
  min_eq_right ((secondWall_le_firstWall_iff hs hc).mpr hx)

theorem IsDownwardCap.support_unitNormal_le_centeredBox {U : Set Plane}
    (hU : IsDownwardCap U) {C θ : ℝ}
    (hbox : U ⊆ Icc (-2 * C) (2 * C) ×ˢ Icc (0 : ℝ) 1)
    (hs : 0 ≤ Real.sin θ) (hc : 0 ≤ Real.cos θ) :
    support U (unitNormal θ) ≤ 2 * C * Real.cos θ + Real.sin θ :=
  support_le_of_forall hU.nonempty fun _ hp => add_le_add (mul_le_mul_of_nonneg_right
    (hbox hp).1.2 hc) ((mul_le_mul_of_nonneg_right (hbox hp).2.2 hs).trans_eq (one_mul _))

theorem IsDownwardCap.support_companionNormal_le_centeredBox {U : Set Plane}
    (hU : IsDownwardCap U) {C θ : ℝ}
    (hbox : U ⊆ Icc (-2 * C) (2 * C) ×ˢ Icc (0 : ℝ) 1)
    (hs : 0 ≤ Real.sin θ) (hc : 0 ≤ Real.cos θ) :
    support U (companionNormal θ) ≤ 2 * C * Real.sin θ + Real.cos θ :=
  support_le_of_forall hU.nonempty fun _ hp => add_le_add
    ((mul_le_mul_of_nonpos_right (hbox hp).1.1 (neg_nonpos.mpr hs)).trans_eq (by ring))
    ((mul_le_mul_of_nonneg_right (hbox hp).2.2 hc).trans_eq (one_mul _))

theorem IsDownwardCap.subset_centeredBox_of_endpoints {U : Set Plane}
    (hU : IsDownwardCap U) {C : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C) :
    U ⊆ Icc (-2 * C) (2 * C) ×ˢ Icc (0 : ℝ) 1 := fun p hp =>
  ⟨hl ▸ hr ▸ horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex ▸ ⟨p, hp, rfl⟩,
    hU.inStrip hp⟩

theorem IsDownwardCap.attachedCorner_fst_mem_middle_of_roof_endpoints
    {U : Set Plane} (hU : IsDownwardCap U) {C h θ : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hleft : capRoof U (-C) = 1 - h) (hright : capRoof U C = 1)
    (hC0 : 1 / 2 ≤ C) (hC1 : C ≤ 37 / 50) (hh : h ≤ 17 / 50)
    (hθ : θ ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    (attachedCorner U θ).1 ∈ Ioo (-C) C := by
  have hmem (x : ℝ) (hx : x ∈ Icc (-C) C) : (x, capRoof U x) ∈ U := capRoof_mem hU.isCompact (by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hl, hr]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  have hbox := hU.subset_centeredBox_of_endpoints hl hr
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  -- Lower bounds on both supports from the two attained roof points.
  have hflo : C * Real.cos θ + Real.sin θ ≤ support U (unitNormal θ) := by
    simpa only [coordDot, unitNormal, hright, one_mul] using
      coordDot_le_support hU.isCompact (hmem C ⟨by linarith, le_rfl⟩) (unitNormal θ)
  have hglo : C * Real.sin θ + (1 - h) * Real.cos θ ≤ support U (companionNormal θ) := by
    simpa only [coordDot, companionNormal, hleft, neg_mul_neg] using
      coordDot_le_support hU.isCompact (hmem (-C) ⟨le_rfl, by linarith⟩) (companionNormal θ)
  have hcircle : C * Real.cos θ ^ 2 + C * Real.sin θ ^ 2 = C := by
    rw [← mul_add, Real.cos_sq_add_sin_sq, mul_one]
  dsimp only [attachedCorner]
  constructor
  · linarith [corner_margin_pos hc hs (Real.sin_sq_add_cos_sq θ) hC0 hC1 (h := 0) (by norm_num),
      mul_le_mul_of_nonneg_right hflo hc.le,
      mul_le_mul_of_nonneg_right (hU.support_companionNormal_le_centeredBox hbox hs.le hc.le) hs.le]
  · linarith [corner_margin_trig_pos hθ.1 hθ.2 hC0 hC1 hh, mul_le_mul_of_nonneg_right hglo hs.le,
      mul_le_mul_of_nonneg_right (hU.support_unitNormal_le_centeredBox hbox hs.le hc.le) hc.le]

end AmbidextrousSofa
