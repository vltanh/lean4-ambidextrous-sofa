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
  linarith [mul_nonneg (show 0 ≤ MovingSofaOptimality.sigmaAt U t from ENNReal.toReal_nonneg) ht]

theorem IsDownwardCap.horizontalProjection_edge {U : Set Plane} (hU : IsDownwardCap U)
    {t : ℝ} (ht : 0 ≤ Real.sin t) :
    horizontalProjection (MovingSofaOptimality.edge U t) =
      Icc (MovingSofaOptimality.vplus U t).1 (MovingSofaOptimality.vminus U t).1 := by
  rw [horizontalProjection, MovingSofaOptimality.edge_eq_segment hU.imported_isConvexBody,
    ← AffineMap.coe_fst (k := ℝ), image_segment, AffineMap.coe_fst, segment_symm,
    segment_eq_Icc (hU.face_fst_order ht)]

theorem IsDownwardCap.upperCurvature_atom_eq_projection {U : Set Plane}
    (hU : IsDownwardCap U) {t : ℝ} (ht : 0 < Real.sin t) :
    (upperCurvature U {t}).toReal =
      volume.real (horizontalProjection (MovingSofaOptimality.edge U t)) / Real.sin t := by
  rw [hU.horizontalProjection_edge ht.le, Real.volume_real_Icc_of_le (hU.face_fst_order ht.le),
    eq_div_iff ht.ne']
  have h := congrArg Prod.fst (MovingSofaOptimality.proposition2_1_2 hU.imported_isConvexBody t).2
  change (MovingSofaOptimality.vplus U t).1 = (MovingSofaOptimality.vminus U t).1 +
    (upperCurvature U {t}).toReal * -Real.sin t at h
  linarith

theorem IsDownwardCap.capRoof_eq_of_mem_upper_edge {U : Set Plane}
    (hU : IsDownwardCap U) {t : ℝ} (ht : 0 < Real.sin t)
    {p : Plane} (hp : p ∈ MovingSofaOptimality.edge U t) : p.2 = capRoof U p.1 := by
  have hroof := coordDot_le_support hU.isCompact (capRoof_mem hU.isCompact ⟨p, hp.1, rfl⟩)
    (unitNormal t)
  have hface : coordDot p (unitNormal t) = support U (unitNormal t) := hp.2
  simp only [coordDot, unitNormal] at hroof hface
  exact le_antisymm (le_capRoof hU.isCompact hp.1) (le_of_mul_le_mul_right (by linarith) ht)

namespace FinitePolygon

variable {ι : Type*}

theorem eq_upper_line_iff {n : Plane} (hny : n.2 ≠ 0) (height x y : ℝ) :
    y = -n.1 / n.2 * x + height / n.2 ↔ coordDot (x, y) n = height := by
  rw [show -n.1 / n.2 * x + height / n.2 = (height - x * n.1) / n.2 by ring,
    eq_div_iff hny, coordDot]
  constructor <;> intro h <;> linarith

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
  have hproj := hU.horizontalProjection_eq_Icc
  -- On the projection, the roof lies on the line of leaf `j` iff it lies on the face.
  have hline x (hx : x ∈ Icc (horizontalLeft U) (horizontalRight U)) :
      capRoof U x = -(normal j).1 / (normal j).2 * x + support U (normal j) / (normal j).2 ↔
        (x, capRoof U x) ∈ MovingSofaOptimality.edge U t := by
    rw [eq_upper_line_iff (hnormal j).ne', hangle]
    exact ⟨fun h => ⟨capRoof_mem hU.isCompact (hproj ▸ hx), h⟩, fun h => h.2⟩
  filter_upwards [WallExpr.ae_injective_affine
    (b := roofIntercept normal (fun i => support U (normal i))) hslopes] with x hinj
  rw [eq_iff_iff]
  constructor
  · rintro ⟨hx, hsource⟩
    refine ⟨_, (hline x hx).1 ?_, rfl⟩
    rw [← eqOn_roofEnvelope_of_circumscription hU normal hnormal hpoly hx, roofEnvelope,
      WallExpr.eval_eq_source, show roofExpr.source _ = some j from hsource]
    rfl
  · rintro ⟨p, hp, rfl⟩
    have hx : p.1 ∈ Icc (horizontalLeft U) (horizontalRight U) := hproj ▸ ⟨p, hp.1, rfl⟩
    have hp' : (p.1, capRoof U p.1) ∈ MovingSofaOptimality.edge U t := by
      rwa [← hU.capRoof_eq_of_mem_upper_edge (by simpa only [hangle, unitNormal] using hnormal j)
        hp]
    exact ⟨hx, hinj (((roofExpr (ι := ι)).eval_eq_source _).symm.trans
      ((eqOn_roofEnvelope_of_circumscription hU normal hnormal hpoly hx).trans
        ((hline _ hx).2 hp')))⟩

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
  rw [integral_sourceDensity_outward _ _ _ _ (horizontalLeft_le_horizontalRight hU.nonempty
    hU.isCompact), measureReal_congr (ae_eq_set_inter Ioc_ae_eq_Icc (ae_eq_refl _) |>.trans
      (outerSource_ae_eq_faceProjection hU normal hnormal hslopes hpoly j hangle)), hangle]
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
  have h := ae_eq_set_inter (s := Ioc a b) (t := Ioc a b) (ae_eq_refl _)
    (outerSource_ae_eq_faceProjection hU normal hnormal hslopes hpoly j hangle)
  rw [← inter_assoc, inter_eq_left.2 hwindow] at h
  rw [integral_sourceDensity_outward _ _ _ _ hab, measureReal_congr h, hangle]
  rfl

end FinitePolygon

end AmbidextrousSofa
