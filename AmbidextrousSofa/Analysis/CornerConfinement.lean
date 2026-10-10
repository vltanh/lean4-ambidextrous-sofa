import AmbidextrousSofa.Analysis.CornerTrigonometry
import AmbidextrousSofa.Geometry.BarrierAnalysis

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
  have hcircle := congrArg (fun v : ℝ => x * v) (Real.cos_sq_add_sin_sq θ)
  change _ ↔ (support U (unitNormal θ) - 1) * Real.cos θ -
    (support U (companionNormal θ) - 1) * Real.sin θ ≤ x
  constructor <;> intro h <;> nlinarith

theorem secondWall_le_firstWall_iff {U : Set Plane} {θ x : ℝ}
    (hs : 0 < Real.sin θ) (hc : 0 < Real.cos θ) :
    secondWall U θ x ≤ firstWall U θ x ↔ x ≤ (attachedCorner U θ).1 := by
  rw [secondWall, firstWall, div_le_div_iff₀ hc hs]
  have hcircle := congrArg (fun v : ℝ => x * v) (Real.cos_sq_add_sin_sq θ)
  change _ ↔ x ≤ (support U (unitNormal θ) - 1) * Real.cos θ -
    (support U (companionNormal θ) - 1) * Real.sin θ
  constructor <;> intro h <;> nlinarith

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
    support U (unitNormal θ) ≤ 2 * C * Real.cos θ + Real.sin θ := by
  apply support_le_of_forall hU.nonempty
  intro p hp
  have hpx := mul_le_mul_of_nonneg_right (hbox hp).1.2 hc
  have hpy := mul_le_mul_of_nonneg_right (hbox hp).2.2 hs
  dsimp only [coordDot, unitNormal]
  nlinarith

theorem IsDownwardCap.support_companionNormal_le_centeredBox {U : Set Plane}
    (hU : IsDownwardCap U) {C θ : ℝ}
    (hbox : U ⊆ Icc (-2 * C) (2 * C) ×ˢ Icc (0 : ℝ) 1)
    (hs : 0 ≤ Real.sin θ) (hc : 0 ≤ Real.cos θ) :
    support U (companionNormal θ) ≤ 2 * C * Real.sin θ + Real.cos θ := by
  apply support_le_of_forall hU.nonempty
  intro p hp
  have hpx := mul_le_mul_of_nonneg_right (hbox hp).1.1 hs
  have hpy := mul_le_mul_of_nonneg_right (hbox hp).2.2 hc
  dsimp only [coordDot, companionNormal]
  nlinarith

theorem IsDownwardCap.attachedCorner_fst_mem_middle_of_box_contacts
    {U : Set Plane} (hU : IsDownwardCap U) {C h θ : ℝ}
    (hbox : U ⊆ Icc (-2 * C) (2 * C) ×ˢ Icc (0 : ℝ) 1)
    (hleft : (-C, 1 - h) ∈ U) (hright : (C, 1) ∈ U)
    (hC0 : 1 / 2 ≤ C) (hC1 : C ≤ 37 / 50) (hh : h ≤ 17 / 50)
    (hθ : θ ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    (attachedCorner U θ).1 ∈ Ioo (-C) C := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hfup := hU.support_unitNormal_le_centeredBox hbox hs.le hc.le
  have hgup := hU.support_companionNormal_le_centeredBox hbox hs.le hc.le
  have hflo : C * Real.cos θ + Real.sin θ ≤ support U (unitNormal θ) := by
    simpa only [coordDot, unitNormal, one_mul] using
      coordDot_le_support hU.isCompact hright (unitNormal θ)
  have hglo : C * Real.sin θ + (1 - h) * Real.cos θ ≤
      support U (companionNormal θ) := by
    simpa only [coordDot, companionNormal, neg_mul_neg] using
      coordDot_le_support hU.isCompact hleft (companionNormal θ)
  have hcircle := congrArg (fun v : ℝ => C * v) (Real.cos_sq_add_sin_sq θ)
  constructor
  · have hmargin := corner_margin_pos hc hs
      (by linarith [Real.cos_sq_add_sin_sq θ]) hC0 hC1 (h := 0) (by norm_num)
    have hf := mul_le_mul_of_nonneg_right hflo hc.le
    have hg := mul_le_mul_of_nonneg_right hgup hs.le
    change -C < (support U (unitNormal θ) - 1) * Real.cos θ -
      (support U (companionNormal θ) - 1) * Real.sin θ
    nlinarith
  · have hmargin := corner_margin_trig_pos hθ.1 hθ.2 hC0 hC1 hh
    have hf := mul_le_mul_of_nonneg_right hfup hc.le
    have hg := mul_le_mul_of_nonneg_right hglo hs.le
    change (support U (unitNormal θ) - 1) * Real.cos θ -
      (support U (companionNormal θ) - 1) * Real.sin θ < C
    nlinarith

theorem IsDownwardCap.subset_centeredBox_of_endpoints {U : Set Plane}
    (hU : IsDownwardCap U) {C : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C) :
    U ⊆ Icc (-2 * C) (2 * C) ×ˢ Icc (0 : ℝ) 1 := by
  intro p hp
  refine ⟨?_, hU.inStrip hp⟩
  have hx : p.1 ∈ horizontalProjection U := ⟨p, hp, rfl⟩
  rwa [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hl, hr] at hx

theorem IsDownwardCap.attachedCorner_fst_mem_middle_of_roof_endpoints
    {U : Set Plane} (hU : IsDownwardCap U) {C h θ : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hleft : capRoof U (-C) = 1 - h) (hright : capRoof U C = 1)
    (hC0 : 1 / 2 ≤ C) (hC1 : C ≤ 37 / 50) (hh : h ≤ 17 / 50)
    (hθ : θ ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    (attachedCorner U θ).1 ∈ Ioo (-C) C := by
  have hleftI : -C ∈ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hl, hr]
    constructor <;> linarith
  have hrightI : C ∈ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hl, hr]
    constructor <;> linarith
  have hleftmem := capRoof_mem hU.isCompact hleftI
  have hrightmem := capRoof_mem hU.isCompact hrightI
  rw [hleft] at hleftmem
  rw [hright] at hrightmem
  exact hU.attachedCorner_fst_mem_middle_of_box_contacts
    (hU.subset_centeredBox_of_endpoints hl hr) hleftmem hrightmem hC0 hC1 hh hθ

end AmbidextrousSofa
