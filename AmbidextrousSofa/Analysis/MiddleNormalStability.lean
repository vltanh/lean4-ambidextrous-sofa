module

public import AmbidextrousSofa.Analysis.FacetPinning
public import AmbidextrousSofa.Analysis.SelectedCurvature
public import AmbidextrousSofa.Analysis.CapCompactness

@[expose] public section

/-!
# Stability of supporting normals above an affine middle roof

Three actual support inequalities give a quantitative statement. A
supporting point of a nearby cap, above a strict interior point of a
target affine segment, has a normal nearly perpendicular to that segment.
This uses Hausdorff distance directly and requires no derivative
convergence or regularity assumption on either cap.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace AmbidextrousSofa

/-- Actual support points above the interior of a limiting affine face
can only have normals close to the normal of that face. -/
theorem affine_face_normal_stability {U K : Set Plane}
    (hU : IsDownwardCap U) (hK : IsDownwardCap K)
    {a b m c ε t : ℝ} {p : Plane}
    (ha : (a, m * a + c) ∈ K) (hb : (b, m * b + c) ∈ K)
    (hface : support K (-m, 1) = c)
    (hp : p ∈ MovingSofaOptimality.edge U t) (hsin : 0 ≤ Real.sin t)
    (hx : p.1 ∈ Icc (a + ε) (b - ε)) :
    ε * |Real.cos t + m * Real.sin t| ≤
      (|m| + 3) * Metric.hausdorffDist U K := by
  have hd : 0 ≤ Metric.hausdorffDist U K := Metric.hausdorffDist_nonneg
  have hcentral := support_le_add_hausdorff hU.isCompact hU.nonempty hK.isCompact hK.nonempty
    (-m, 1)
  have hunit := support_le_add_hausdorff hK.isCompact hK.nonempty hU.isCompact hU.nonempty
    (unitNormal t)
  rw [Metric.hausdorffDist_comm] at hunit
  generalize Metric.hausdorffDist U K = d at hd hcentral hunit ⊢
  have hpoint := coordDot_le_support hU.isCompact hp.1 (-m, 1)
  have hpS : coordDot p (unitNormal t) = support U (unitNormal t) := hp.2
  have hpa := coordDot_le_support hK.isCompact ha (unitNormal t)
  have hpb := coordDot_le_support hK.isCompact hb (unitNormal t)
  rw [coordDot_affine_graph_normal] at hpa hpb
  simp only [coordDot, unitNormal, hface, abs_neg, abs_one] at hcentral hunit hpoint hpS hpa hpb
  have h1 := mul_le_mul_of_nonneg_right (show p.2 ≤ m * p.1 + c + d * (|m| + 1) by linarith) hsin
  have h2 := mul_le_mul_of_nonneg_left (Real.sin_le_one t) (by positivity : 0 ≤ d * (|m| + 1))
  have h3 := mul_le_mul_of_nonneg_left (show |Real.cos t| + |Real.sin t| ≤ 2 by
    linarith [Real.abs_cos_le_one t, Real.abs_sin_le_one t]) hd
  rcases le_total 0 (Real.cos t + m * Real.sin t) with hk | hk
  · rw [abs_of_nonneg hk]
    linarith [mul_le_mul_of_nonneg_right (by linarith [hx.2] : ε ≤ b - p.1) hk]
  · rw [abs_of_nonpos hk]
    linarith [mul_le_mul_of_nonneg_right (by linarith [hx.1] : ε ≤ p.1 - a) (neg_nonneg.mpr hk)]

theorem CapHausdorffTendsto.eventually_no_middle_edge
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    {a b m c x τ : ℝ} {E : Set ℝ}
    (ha : (a, m * a + c) ∈ K) (hb : (b, m * b + c) ∈ K)
    (hface : support K (-m, 1) = c) (hx : x ∈ Ioo a b) (hτ : 0 < τ)
    (hE : ∀ t ∈ E, 0 ≤ Real.sin t ∧ τ ≤ |Real.cos t + m * Real.sin t|) :
    ∀ᶠ n in atTop, ∀ t ∈ E, (x, capRoof (U n) x) ∉ MovingSofaOptimality.edge (U n) t := by
  obtain ⟨ε, hε, hεa, hεb⟩ : ∃ ε > 0, ε ≤ x - a ∧ ε ≤ b - x :=
    ⟨_, lt_min (sub_pos.mpr hx.1) (sub_pos.mpr hx.2), min_le_left _ _, min_le_right _ _⟩
  filter_upwards [h.eventually (Iio_mem_nhds (by positivity : 0 < ε * τ / (|m| + 3)))]
    with n hn t ht hp
  rw [lt_div_iff₀ (by positivity)] at hn
  linarith [affine_face_normal_stability (hU n) hK ha hb hface hp (hE t ht).1
    (show x ∈ Icc (a + ε) (b - ε) from ⟨by linarith, by linarith⟩),
    mul_le_mul_of_nonneg_left (hE t ht).2 hε.le]

namespace FinitePolygon

/-- A selected outer leaf always gives an actual support point. The
converse needs distinct affine leaves only at ties; this direction does
not have an exceptional set. -/
theorem outerSource_mem_edge {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U : Set Plane} (hU : IsDownwardCap U) (normal : ι → Plane)
    (hnormal : ∀ i, 0 < (normal i).2) (hpoly : U = circumscription U normal)
    (j : ι) {t x : ℝ} (hangle : normal j = unitNormal t)
    (hx : x ∈ horizontalProjection U)
    (hsource : x ∈ (roofExpr (ι := ι)).sourceSet (wallSlope normal)
      (roofIntercept normal (fun i => support U (normal i))) (some j)) :
    (x, capRoof U x) ∈ MovingSofaOptimality.edge U t := by
  have hvalue := (roofExpr (ι := ι)).eval_eq_source
    (fun i => wallSlope normal i * x + roofIntercept normal (fun j => support U (normal j)) i)
  rw [show (roofExpr (ι := ι)).source _ = some j from hsource] at hvalue
  have hdot := (eq_upper_line_iff (hnormal j).ne' (support U (normal j)) x (capRoof U x)).mp
    ((capRoof_eq_roofEnvelope_of_circumscription hU normal hnormal hpoly
      (horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex ▸ hx)).trans hvalue)
  rw [hangle] at hdot
  exact ⟨capRoof_mem hU.isCompact hx, hdot⟩

end FinitePolygon

end AmbidextrousSofa
