import AmbidextrousSofa.Analysis.FacetPinning
import AmbidextrousSofa.Analysis.SelectedCurvature
import AmbidextrousSofa.Analysis.CapCompactness

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
    (hp : p ∈ Imported.edge U t) (hsin : 0 ≤ Real.sin t)
    (hε : 0 ≤ ε) (hx : p.1 ∈ Icc (a + ε) (b - ε)) :
    ε * |Real.cos t + m * Real.sin t| ≤
      (|m| + 3) * Metric.hausdorffDist U K := by
  let d := Metric.hausdorffDist U K
  let k := Real.cos t + m * Real.sin t
  have hd : 0 ≤ d := Metric.hausdorffDist_nonneg
  have hm : 0 ≤ |m| + 1 := by positivity
  have hcentral := support_le_add_hausdorff hU.isCompact hU.nonempty
    hK.isCompact hK.nonempty (-m, 1)
  rw [hface] at hcentral
  simp only [abs_neg, abs_one] at hcentral
  have hpoint := coordDot_le_support hU.isCompact hp.1 (-m, 1)
  have hheight : p.2 ≤ m * p.1 + c + d * (|m| + 1) := by
    change p.1 * (-m) + p.2 * 1 ≤ _ at hpoint
    change support U (-m, 1) ≤ c + d * (|m| + 1) at hcentral
    nlinarith
  have hunit := support_le_add_hausdorff hK.isCompact hK.nonempty
    hU.isCompact hU.nonempty (unitNormal t)
  rw [Metric.hausdorffDist_comm] at hunit
  have hunit' : support K (unitNormal t) ≤ support U (unitNormal t) + 2 * d := by
    have hnorm : |Real.cos t| + |Real.sin t| ≤ 2 := by
      linarith [Real.abs_cos_le_one t, Real.abs_sin_le_one t]
    have hmul := mul_le_mul_of_nonneg_left hnorm hd
    change support K (unitNormal t) ≤ support U (unitNormal t) +
      d * (|Real.cos t| + |Real.sin t|) at hunit
    linarith
  have hpSupport : support U (unitNormal t) =
      p.1 * Real.cos t + p.2 * Real.sin t := hp.2.symm
  have hupper : support U (unitNormal t) ≤ p.1 * k + c * Real.sin t +
      d * (|m| + 1) := by
    have hmul := mul_le_mul_of_nonneg_right hheight hsin
    have herror := mul_le_mul_of_nonneg_left (Real.sin_le_one t) (mul_nonneg hd hm)
    rw [hpSupport]
    dsimp only [k]
    nlinarith
  have hpa := coordDot_le_support hK.isCompact ha (unitNormal t)
  have hpb := coordDot_le_support hK.isCompact hb (unitNormal t)
  rw [coordDot_affine_graph_normal] at hpa hpb
  change a * k + c * Real.sin t ≤ support K (unitNormal t) at hpa
  change b * k + c * Real.sin t ≤ support K (unitNormal t) at hpb
  have hleft : (a - p.1) * k ≤ (|m| + 3) * d := by nlinarith
  have hright : (b - p.1) * k ≤ (|m| + 3) * d := by nlinarith
  rcases le_total 0 k with hk | hk
  · rw [abs_of_nonneg hk]
    have hmul := mul_le_mul_of_nonneg_right (by linarith [hx.2] : ε ≤ b - p.1) hk
    exact hmul.trans hright
  · rw [abs_of_nonpos hk]
    have hmul := mul_le_mul_of_nonneg_right (by linarith [hx.1] : ε ≤ p.1 - a)
      (neg_nonneg.mpr hk)
    nlinarith

theorem CapHausdorffTendsto.eventually_no_middle_edge
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    {a b m c x τ : ℝ} {E : Set ℝ}
    (ha : (a, m * a + c) ∈ K) (hb : (b, m * b + c) ∈ K)
    (hface : support K (-m, 1) = c) (hx : x ∈ Ioo a b) (hτ : 0 < τ)
    (hE : ∀ t ∈ E, 0 ≤ Real.sin t ∧ τ ≤ |Real.cos t + m * Real.sin t|) :
    ∀ᶠ n in atTop, ∀ t ∈ E, (x, capRoof (U n) x) ∉ Imported.edge (U n) t := by
  let ε := min (x - a) (b - x)
  have hε : 0 < ε := lt_min (sub_pos.mpr hx.1) (sub_pos.mpr hx.2)
  have hC : 0 < |m| + 3 := by positivity
  have hsmall : 0 < ε * τ / (|m| + 3) := div_pos (mul_pos hε hτ) hC
  filter_upwards [h.eventually (Iio_mem_nhds hsmall)] with n hn t ht hp
  have hxε : x ∈ Icc (a + ε) (b - ε) := by
    constructor
    · linarith [min_le_left (x - a) (b - x)]
    · linarith [min_le_right (x - a) (b - x)]
  have hbound := affine_face_normal_stability (hU n) hK ha hb hface hp
    (hE t ht).1 hε.le hxε
  have hmul := mul_le_mul_of_nonneg_left (hE t ht).2 hε.le
  rw [lt_div_iff₀ hC] at hn
  nlinarith

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
    (x, capRoof U x) ∈ Imported.edge U t := by
  have hxI : x ∈ Icc (horizontalLeft U) (horizontalRight U) := by
    rwa [← horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
  have hroof := capRoof_eq_roofEnvelope_of_circumscription hU normal hnormal hpoly hxI
  have hvalue := (roofExpr (ι := ι)).eval_eq_source
    (fun i => wallSlope normal i * x + roofIntercept normal (fun j => support U (normal j)) i)
  change (roofExpr (ι := ι)).source
    (fun i => wallSlope normal i * x + roofIntercept normal (fun j => support U (normal j)) i) =
      some j at hsource
  rw [hsource] at hvalue
  have hline : capRoof U x = -(normal j).1 / (normal j).2 * x +
      support U (normal j) / (normal j).2 := hroof.trans hvalue
  have hdot := (eq_upper_line_iff (hnormal j).ne' (support U (normal j)) x (capRoof U x)).mp hline
  exact ⟨capRoof_mem hU.isCompact hx, by simpa only [hangle] using hdot⟩

end FinitePolygon

end AmbidextrousSofa
