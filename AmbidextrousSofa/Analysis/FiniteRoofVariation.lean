module

public import AmbidextrousSofa.Analysis.FiniteSpatialVariation
public import AmbidextrousSofa.Analysis.PolygonEnvelope
public import AmbidextrousSofa.Analysis.Chord

@[expose] public section

/-!
# Absolute spatial variation of finite concave roofs

The selected line is an actual global upper supporting line of the finite
roof. Its slope therefore has the appropriate sign on either side of a
maximum. The exact variation is twice the maximum minus the two endpoint
values. Concavity then gives a sharper two-wing bound using the difference
of the actual middle endpoint heights. No monotonicity of the selected
polygon's whole roof or fixed location of its top face is assumed.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace FinitePolygon

variable {ι : Type*} [Fintype ι]

theorem roofExpr_eval_le (v : Option ι → ℝ) (i : Option ι) :
    (roofExpr (ι := ι)).eval v ≤ v i := by
  obtain ⟨h0, h⟩ := (le_eval_roofExpr_iff v _).mp le_rfl
  cases i
  exacts [h0, h _]

theorem roofGraph_le_source_line (a b : Option ι → ℝ) (x z : ℝ) :
    (roofExpr (ι := ι)).affineGraph a b z ≤
      (roofExpr (ι := ι)).affineGraph a b x +
        (roofExpr (ι := ι)).sourceDensity a b a x * (z - x) := by
  have hx := (roofExpr (ι := ι)).eval_eq_source fun i => a i * x + b i
  have hz := roofExpr_eval_le (fun i => a i * z + b i)
    ((roofExpr (ι := ι)).source fun i => a i * x + b i)
  simp only [WallExpr.affineGraph, WallExpr.sourceDensity]
  linarith

theorem roof_sourceSlope_nonneg_of_right_value (a b : Option ι → ℝ) {x z : ℝ}
    (hxz : x < z)
    (hvalue : (roofExpr (ι := ι)).affineGraph a b x ≤
      (roofExpr (ι := ι)).affineGraph a b z) :
    0 ≤ (roofExpr (ι := ι)).sourceDensity a b a x := by
  nlinarith [roofGraph_le_source_line a b x z]

theorem roof_sourceSlope_nonpos_of_left_value (a b : Option ι → ℝ) {z x : ℝ}
    (hzx : z < x)
    (hvalue : (roofExpr (ι := ι)).affineGraph a b x ≤
      (roofExpr (ι := ι)).affineGraph a b z) :
    (roofExpr (ι := ι)).sourceDensity a b a x ≤ 0 := by
  nlinarith [roofGraph_le_source_line a b x z]

theorem roof_absSlope_integral_eq (a b : Option ι → ℝ)
    (ha : Function.Injective a) {l z r : ℝ} (hz : z ∈ Icc l r)
    (hmax : ∀ x ∈ Icc l r, (roofExpr (ι := ι)).affineGraph a b x ≤
      (roofExpr (ι := ι)).affineGraph a b z) :
    (∫ x in l..r, (roofExpr (ι := ι)).sourceDensity a b (fun i => |a i|) x) =
      2 * (roofExpr (ι := ι)).affineGraph a b z - (roofExpr (ι := ι)).affineGraph a b l -
        (roofExpr (ι := ι)).affineGraph a b r := by
  have hint (p q : ℝ) :=
    (roofExpr (ι := ι)).intervalIntegrable_sourceDensity a b (fun i => |a i|) p q
  have hleft : (∫ x in l..z, (roofExpr (ι := ι)).sourceDensity a b (fun i => |a i|) x) =
      ∫ x in l..z, (roofExpr (ι := ι)).sourceDensity a b a x := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [volume.ae_ne z] with x hxz hx
    rw [uIoc_of_le hz.1] at hx
    exact abs_of_nonneg (roof_sourceSlope_nonneg_of_right_value a b (hx.2.lt_of_ne hxz)
      (hmax x ⟨hx.1.le, hx.2.trans hz.2⟩))
  have hright : (∫ x in z..r, (roofExpr (ι := ι)).sourceDensity a b (fun i => |a i|) x) =
      ∫ x in z..r, -(roofExpr (ι := ι)).sourceDensity a b a x := by
    refine intervalIntegral.integral_congr_ae (ae_of_all _ fun x hx => ?_)
    rw [uIoc_of_le hz.2] at hx
    exact abs_of_nonpos (roof_sourceSlope_nonpos_of_left_value a b hx.1
      (hmax x ⟨hz.1.trans hx.1.le, hx.2⟩))
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint l z) (hint z r), hleft, hright,
    intervalIntegral.integral_neg, (roofExpr (ι := ι)).integral_sourceSlope a b ha,
    (roofExpr (ι := ι)).integral_sourceSlope a b ha]
  ring

theorem roof_absSlope_integral_le (a b : Option ι → ℝ)
    (ha : Function.Injective a) {l r H : ℝ} (hlr : l ≤ r)
    (hH : ∀ x ∈ Icc l r, (roofExpr (ι := ι)).affineGraph a b x ≤ H) :
    (∫ x in l..r, (roofExpr (ι := ι)).sourceDensity a b (fun i => |a i|) x) ≤
      2 * H - (roofExpr (ι := ι)).affineGraph a b l -
        (roofExpr (ι := ι)).affineGraph a b r := by
  obtain ⟨z, hz, hmax⟩ := isCompact_Icc.exists_isMaxOn
    ⟨l, le_rfl, hlr⟩ ((roofExpr (ι := ι)).continuous_affineGraph a b).continuousOn
  linarith [roof_absSlope_integral_eq a b ha hz hmax, hH z hz]

theorem roof_outer_absSlope_integrals_le (a b : Option ι → ℝ)
    (ha : Function.Injective a) {l u v r H : ℝ}
    (hlu : l ≤ u) (huv : u < v) (hvr : v ≤ r)
    (hH : ∀ x ∈ Icc l r, (roofExpr (ι := ι)).affineGraph a b x ≤ H) :
    (∫ x in l..u, (roofExpr (ι := ι)).sourceDensity a b (fun i => |a i|) x) +
      (∫ x in v..r, (roofExpr (ι := ι)).sourceDensity a b (fun i => |a i|) x) ≤
      2 * H - |(roofExpr (ι := ι)).affineGraph a b v -
        (roofExpr (ι := ι)).affineGraph a b u| -
        (roofExpr (ι := ι)).affineGraph a b l - (roofExpr (ι := ι)).affineGraph a b r := by
  rcases le_total ((roofExpr (ι := ι)).affineGraph a b u)
    ((roofExpr (ι := ι)).affineGraph a b v) with hvalue | hvalue
  · have hs := roof_sourceSlope_nonneg_of_right_value a b huv hvalue
    have hL := roof_absSlope_integral_eq a b ha ⟨hlu, le_rfl⟩ fun x hx => by
      nlinarith [roofGraph_le_source_line a b u x, hx.2]
    have hR := roof_absSlope_integral_le a b ha hvr
      (fun x hx => hH x ⟨hlu.trans (huv.le.trans hx.1), hx.2⟩)
    linarith [abs_of_nonneg (sub_nonneg.mpr hvalue)]
  · have hs := roof_sourceSlope_nonpos_of_left_value a b huv hvalue
    have hL := roof_absSlope_integral_le a b ha hlu
      (fun x hx => hH x ⟨hx.1, hx.2.trans (huv.le.trans hvr)⟩)
    have hR := roof_absSlope_integral_eq a b ha ⟨le_rfl, hvr⟩ fun x hx => by
      nlinarith [roofGraph_le_source_line a b v x, hx.1]
    linarith [abs_of_nonpos (sub_nonpos.mpr hvalue)]

end FinitePolygon

end AmbidextrousSofa
