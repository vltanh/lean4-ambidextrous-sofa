module

public import AmbidextrousSofa.Analysis.SelectedSequence
public import AmbidextrousSofa.Analysis.SupportCurvature

@[expose] public section

/-!
# Literal facet mass and selected outer-wall exposure

The Stieltjes atom is the actual supporting segment length. On an upward
nonhorizontal face its horizontal projection has length `sin t` times
that atom. For an actual circumscribed polygon, the outer envelope chooses
that face at almost every point of its projection. Ties between different
affine leaves form a null set by the proved distinct-slope theorem.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem IsDownwardCap.face_fst_order {U : Set Plane} (hU : IsDownwardCap U)
    {t : ℝ} (ht : 0 ≤ Real.sin t) :
    (MovingSofaOptimality.vplus U t).1 ≤ (MovingSofaOptimality.vminus U t).1 := by
  have h := congrArg Prod.fst (MovingSofaOptimality.proposition2_1_2 hU.imported_isConvexBody t).2
  change (MovingSofaOptimality.vplus U t).1 = (MovingSofaOptimality.vminus U t).1 +
    MovingSofaOptimality.sigmaAt U t * -Real.sin t at h
  have hmass : 0 ≤ MovingSofaOptimality.sigmaAt U t := ENNReal.toReal_nonneg
  nlinarith

theorem IsDownwardCap.horizontalProjection_edge {U : Set Plane} (hU : IsDownwardCap U)
    {t : ℝ} (ht : 0 ≤ Real.sin t) :
    horizontalProjection (MovingSofaOptimality.edge U t) =
      Icc (MovingSofaOptimality.vplus U t).1 (MovingSofaOptimality.vminus U t).1 := by
  unfold horizontalProjection
  rw [MovingSofaOptimality.edge_eq_segment hU.imported_isConvexBody]
  change (AffineMap.fst : Plane →ᵃ[ℝ] ℝ) ''
    segment ℝ (MovingSofaOptimality.vminus U t) (MovingSofaOptimality.vplus U t) = _
  rw [image_segment, segment_symm, AffineMap.coe_fst, segment_eq_Icc (hU.face_fst_order ht)]

theorem IsDownwardCap.upperCurvature_atom_eq_projection {U : Set Plane}
    (hU : IsDownwardCap U) {t : ℝ} (ht : 0 < Real.sin t) :
    (upperCurvature U {t}).toReal =
      volume.real (horizontalProjection (MovingSofaOptimality.edge U t)) / Real.sin t := by
  rw [hU.horizontalProjection_edge ht.le, Real.volume_real_Icc_of_le (hU.face_fst_order ht.le)]
  have h := congrArg Prod.fst (MovingSofaOptimality.proposition2_1_2 hU.imported_isConvexBody t).2
  change (MovingSofaOptimality.vplus U t).1 = (MovingSofaOptimality.vminus U t).1 +
    (upperCurvature U {t}).toReal * -Real.sin t at h
  apply (eq_div_iff ht.ne').mpr
  nlinarith

theorem IsDownwardCap.capRoof_eq_of_mem_upper_edge {U : Set Plane}
    (hU : IsDownwardCap U) {t : ℝ} (ht : 0 < Real.sin t)
    {p : Plane} (hp : p ∈ MovingSofaOptimality.edge U t) : p.2 = capRoof U p.1 := by
  have hx : p.1 ∈ horizontalProjection U := ⟨p, hp.1, rfl⟩
  have hroof := coordDot_le_support hU.isCompact (capRoof_mem hU.isCompact hx) (unitNormal t)
  have hface : coordDot p (unitNormal t) = support U (unitNormal t) := hp.2
  have hle := le_capRoof hU.isCompact hp.1
  unfold coordDot unitNormal at hroof hface
  apply le_antisymm hle
  apply (mul_le_mul_iff_left₀ ht).mp
  nlinarith

namespace FinitePolygon

variable {ι : Type*}

theorem eq_upper_line_iff {n : Plane} (hny : n.2 ≠ 0) (height x y : ℝ) :
    y = -n.1 / n.2 * x + height / n.2 ↔ coordDot (x, y) n = height := by
  rw [show -n.1 / n.2 * x + height / n.2 = (height - x * n.1) / n.2 by ring,
    eq_div_iff hny]
  unfold coordDot
  constructor <;> intro h <;> linarith

theorem capRoof_eq_roofEnvelope_of_circumscription [Fintype ι] {U : Set Plane}
    (hU : IsDownwardCap U) (normal : ι → Plane)
    (hnormal : ∀ i, 0 < (normal i).2) (hpoly : U = circumscription U normal)
    {x : ℝ} (hx : x ∈ Icc (horizontalLeft U) (horizontalRight U)) :
    capRoof U x = roofEnvelope normal (fun i => support U (normal i)) x := by
  calc
    capRoof U x = capRoof (circumscription U normal) x := congrArg (fun V => capRoof V x) hpoly
    _ = _ := capRoof_upperPolygon _ _ normal _ hnormal (circumscription_baseline hU normal) hx

/-- On the actual projection, selecting the outer wall is equivalent
almost everywhere to belonging to the literal supporting face projection. -/
theorem outerSource_ae_eq_faceProjection [Fintype ι] [DecidableEq ι]
    {U : Set Plane} (hU : IsDownwardCap U) (normal : ι → Plane)
    (hnormal : ∀ i, 0 < (normal i).2) (hslopes : Function.Injective (wallSlope normal))
    (hpoly : U = circumscription U normal) (j : ι) {t : ℝ}
    (hangle : normal j = unitNormal t) :
    (Icc (horizontalLeft U) (horizontalRight U) ∩
      (roofExpr (ι := ι)).sourceSet (wallSlope normal)
        (roofIntercept normal (fun i => support U (normal i))) (some j)) =ᵐ[volume]
      horizontalProjection (MovingSofaOptimality.edge U t) := by
  have hsin : 0 < Real.sin t := by simpa only [hangle, unitNormal] using hnormal j
  have hroof (x : ℝ) (hx : x ∈ Icc (horizontalLeft U) (horizontalRight U)) :
      capRoof U x = roofEnvelope normal (fun i => support U (normal i)) x :=
    capRoof_eq_roofEnvelope_of_circumscription hU normal hnormal hpoly hx
  filter_upwards [WallExpr.ae_injective_affine
    (b := roofIntercept normal (fun i => support U (normal i))) hslopes] with x hinj
  rw [eq_iff_iff]
  constructor
  · rintro ⟨hx, hsource⟩
    have hxU : x ∈ horizontalProjection U := by
      rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
      exact hx
    have hvalue := (roofExpr (ι := ι)).eval_eq_source
      (fun i => wallSlope normal i * x + roofIntercept normal (fun j => support U (normal j)) i)
    change (roofExpr (ι := ι)).source
      (fun i => wallSlope normal i * x + roofIntercept normal (fun j => support U (normal j)) i) =
        some j at hsource
    rw [hsource] at hvalue
    have hline : capRoof U x = -(normal j).1 / (normal j).2 * x +
        support U (normal j) / (normal j).2 := (hroof x hx).trans hvalue
    have hdot := (eq_upper_line_iff (hnormal j).ne' (support U (normal j)) x (capRoof U x)).mp hline
    refine ⟨(x, capRoof U x), ⟨capRoof_mem hU.isCompact hxU, ?_⟩, rfl⟩
    rw [hangle] at hdot
    exact hdot
  · rintro ⟨p, hp, rfl⟩
    have hx : p.1 ∈ Icc (horizontalLeft U) (horizontalRight U) := by
      rw [← horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
      exact ⟨p, hp.1, rfl⟩
    refine ⟨hx, ?_⟩
    have hpy := hU.capRoof_eq_of_mem_upper_edge hsin hp
    have hdot : coordDot (p.1, capRoof U p.1) (normal j) = support U (normal j) := by
      rw [← hpy, hangle]
      exact hp.2
    have hline := (eq_upper_line_iff (hnormal j).ne' (support U (normal j)) p.1
      (capRoof U p.1)).mpr hdot
    change (roofExpr (ι := ι)).source
      (fun i => wallSlope normal i * p.1 + roofIntercept normal (fun k => support U (normal k)) i) =
        some j
    apply hinj
    exact ((roofExpr (ι := ι)).eval_eq_source _).symm.trans ((hroof p.1 hx).symm.trans hline)

/-- The entire outer selected-source derivative is exactly the atom of
the actual Stieltjes curvature measure. -/
theorem integral_outerSource_eq_curvature_atom [Fintype ι] [DecidableEq ι]
    {U : Set Plane} (hU : IsDownwardCap U) (normal : ι → Plane)
    (hnormal : ∀ i, 0 < (normal i).2) (hslopes : Function.Injective (wallSlope normal))
    (hpoly : U = circumscription U normal) (j : ι) {t : ℝ}
    (hangle : normal j = unitNormal t) :
    (∫ x in (horizontalLeft U)..(horizontalRight U),
      (roofExpr (ι := ι)).sourceDensity (wallSlope normal)
        (roofIntercept normal (fun i => support U (normal i))) (outwardVelocity normal j) x) =
      (upperCurvature U {t}).toReal := by
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  rw [integral_sourceDensity_outward _ _ _ _ hlr]
  have hAE := outerSource_ae_eq_faceProjection hU normal hnormal hslopes hpoly j hangle
  have hmeasure : volume.real (Ioc (horizontalLeft U) (horizontalRight U) ∩
      (roofExpr (ι := ι)).sourceSet (wallSlope normal)
        (roofIntercept normal (fun i => support U (normal i))) (some j)) =
      volume.real (horizontalProjection (MovingSofaOptimality.edge U t)) := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [hAE, volume.ae_ne (horizontalLeft U)] with x hx hxl
    have hinterval : x ∈ Ioc (horizontalLeft U) (horizontalRight U) ↔
        x ∈ Icc (horizontalLeft U) (horizontalRight U) := by
      constructor
      · intro h
        exact ⟨h.1.le, h.2⟩
      · intro h
        exact ⟨lt_of_le_of_ne h.1 (Ne.symm hxl), h.2⟩
    simpa only [mem_inter_iff, hinterval] using hx
  rw [hmeasure, hangle]
  exact (hU.upperCurvature_atom_eq_projection
    (by simpa only [hangle, unitNormal] using hnormal j)).symm

/-- On a subwindow the source derivative is the actual clipped face
projection length. This is the middle-facet term retained in the spatial
curvature inequality. -/
theorem integral_outerSource_eq_clipped_projection [Fintype ι] [DecidableEq ι]
    {U : Set Plane} (hU : IsDownwardCap U) (normal : ι → Plane)
    (hnormal : ∀ i, 0 < (normal i).2) (hslopes : Function.Injective (wallSlope normal))
    (hpoly : U = circumscription U normal) (j : ι) {t a b : ℝ}
    (hangle : normal j = unitNormal t) (hab : a ≤ b)
    (hwindow : Ioc a b ⊆ Icc (horizontalLeft U) (horizontalRight U)) :
    (∫ x in a..b,
      (roofExpr (ι := ι)).sourceDensity (wallSlope normal)
        (roofIntercept normal (fun i => support U (normal i))) (outwardVelocity normal j) x) =
      volume.real (Ioc a b ∩ horizontalProjection (MovingSofaOptimality.edge U t)) / Real.sin t := by
  rw [integral_sourceDensity_outward _ _ _ _ hab]
  have hAE := outerSource_ae_eq_faceProjection hU normal hnormal hslopes hpoly j hangle
  have hmeasure : volume.real (Ioc a b ∩
      (roofExpr (ι := ι)).sourceSet (wallSlope normal)
        (roofIntercept normal (fun i => support U (normal i))) (some j)) =
      volume.real (Ioc a b ∩ horizontalProjection (MovingSofaOptimality.edge U t)) := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [hAE] with x hx
    by_cases hxwindow : x ∈ Ioc a b
    · have hxprojection := hwindow hxwindow
      simpa only [mem_inter_iff, hxwindow, hxprojection, true_and] using hx
    · simp only [mem_inter_iff, hxwindow, false_and]
  rw [hmeasure, hangle]
  rfl

end FinitePolygon

end AmbidextrousSofa
