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
  have h := (le_eval_roofExpr_iff v ((roofExpr (ι := ι)).eval v)).mp le_rfl
  cases i with
  | none => exact h.1
  | some i => exact h.2 i

theorem concaveOn_roofGraph (a b : Option ι → ℝ) :
    ConcaveOn ℝ univ ((roofExpr (ι := ι)).affineGraph a b) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ u v hu hv huv
  change u * (roofExpr (ι := ι)).affineGraph a b x +
      v * (roofExpr (ι := ι)).affineGraph a b y ≤
    (roofExpr (ι := ι)).affineGraph a b (u * x + v * y)
  have hbound (i : Option ι) :
      u * (roofExpr (ι := ι)).affineGraph a b x +
        v * (roofExpr (ι := ι)).affineGraph a b y ≤ a i * (u * x + v * y) + b i := by
    have hx := mul_le_mul_of_nonneg_left (roofExpr_eval_le (fun j => a j * x + b j) i) hu
    have hy := mul_le_mul_of_nonneg_left (roofExpr_eval_le (fun j => a j * y + b j) i) hv
    have hc := congrArg (fun t : ℝ => t * b i) huv
    change u * (roofExpr (ι := ι)).eval (fun j => a j * x + b j) +
      v * (roofExpr (ι := ι)).eval (fun j => a j * y + b j) ≤ _
    nlinarith
  exact (le_eval_roofExpr_iff _ _).mpr ⟨hbound none, fun i => hbound (some i)⟩

theorem roofGraph_le_source_line (a b : Option ι → ℝ) (x z : ℝ) :
    (roofExpr (ι := ι)).affineGraph a b z ≤
      (roofExpr (ι := ι)).affineGraph a b x +
        (roofExpr (ι := ι)).sourceDensity a b a x * (z - x) := by
  let j := (roofExpr (ι := ι)).source (fun i => a i * x + b i)
  have hx : (roofExpr (ι := ι)).affineGraph a b x = a j * x + b j :=
    (roofExpr (ι := ι)).eval_eq_source _
  change (roofExpr (ι := ι)).affineGraph a b z ≤
    (roofExpr (ι := ι)).affineGraph a b x + a j * (z - x)
  rw [hx]
  calc
    _ ≤ a j * z + b j := roofExpr_eval_le (fun i => a i * z + b i) j
    _ = a j * x + b j + a j * (z - x) := by ring

theorem roof_sourceSlope_nonneg_of_right_value (a b : Option ι → ℝ) {x z : ℝ}
    (hxz : x < z)
    (hvalue : (roofExpr (ι := ι)).affineGraph a b x ≤
      (roofExpr (ι := ι)).affineGraph a b z) :
    0 ≤ (roofExpr (ι := ι)).sourceDensity a b a x := by
  have hline := roofGraph_le_source_line a b x z
  exact nonneg_of_mul_nonneg_left (by linarith :
    0 ≤ (roofExpr (ι := ι)).sourceDensity a b a x * (z - x)) (sub_pos.mpr hxz)

theorem roof_sourceSlope_nonpos_of_left_value (a b : Option ι → ℝ) {z x : ℝ}
    (hzx : z < x)
    (hvalue : (roofExpr (ι := ι)).affineGraph a b x ≤
      (roofExpr (ι := ι)).affineGraph a b z) :
    (roofExpr (ι := ι)).sourceDensity a b a x ≤ 0 := by
  have hline := roofGraph_le_source_line a b x z
  exact nonpos_of_mul_nonpos_left (by nlinarith :
    (roofExpr (ι := ι)).sourceDensity a b a x * (x - z) ≤ 0) (sub_pos.mpr hzx)

theorem roof_absSlope_integral_of_max_right (a b : Option ι → ℝ)
    (ha : Function.Injective a) {l r : ℝ} (hlr : l ≤ r)
    (hmax : ∀ x ∈ Icc l r, (roofExpr (ι := ι)).affineGraph a b x ≤
      (roofExpr (ι := ι)).affineGraph a b r) :
    (∫ x in l..r, (roofExpr (ι := ι)).sourceDensity a b (fun i => |a i|) x) =
      (roofExpr (ι := ι)).affineGraph a b r - (roofExpr (ι := ι)).affineGraph a b l := by
  rw [← (roofExpr (ι := ι)).integral_sourceSlope a b ha l r]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [volume.ae_ne r] with x hxne hx
  rw [uIoc_of_le hlr] at hx
  have hsign := roof_sourceSlope_nonneg_of_right_value a b
    (lt_of_le_of_ne hx.2 hxne) (hmax x ⟨hx.1.le, hx.2⟩)
  exact abs_of_nonneg hsign

theorem roof_absSlope_integral_of_max_left (a b : Option ι → ℝ)
    (ha : Function.Injective a) {l r : ℝ} (hlr : l ≤ r)
    (hmax : ∀ x ∈ Icc l r, (roofExpr (ι := ι)).affineGraph a b x ≤
      (roofExpr (ι := ι)).affineGraph a b l) :
    (∫ x in l..r, (roofExpr (ι := ι)).sourceDensity a b (fun i => |a i|) x) =
      (roofExpr (ι := ι)).affineGraph a b l - (roofExpr (ι := ι)).affineGraph a b r := by
  calc
    _ = ∫ x in l..r, -(roofExpr (ι := ι)).sourceDensity a b a x := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [] with x hx
      rw [uIoc_of_le hlr] at hx
      have hsign := roof_sourceSlope_nonpos_of_left_value a b hx.1
        (hmax x ⟨hx.1.le, hx.2⟩)
      exact abs_of_nonpos hsign
    _ = -((roofExpr (ι := ι)).affineGraph a b r -
        (roofExpr (ι := ι)).affineGraph a b l) := by
      rw [intervalIntegral.integral_neg, (roofExpr (ι := ι)).integral_sourceSlope a b ha l r]
    _ = _ := by ring

theorem roof_absSlope_integral_le (a b : Option ι → ℝ)
    (ha : Function.Injective a) {l r H : ℝ} (hlr : l ≤ r)
    (hH : ∀ x ∈ Icc l r, (roofExpr (ι := ι)).affineGraph a b x ≤ H) :
    (∫ x in l..r, (roofExpr (ι := ι)).sourceDensity a b (fun i => |a i|) x) ≤
      2 * H - (roofExpr (ι := ι)).affineGraph a b l -
        (roofExpr (ι := ι)).affineGraph a b r := by
  obtain ⟨z, hz, hmax⟩ := (isCompact_Icc : IsCompact (Icc l r)).exists_isMaxOn
    ⟨l, le_rfl, hlr⟩ ((roofExpr (ι := ι)).continuous_affineGraph a b).continuousOn
  have hL := roof_absSlope_integral_of_max_right a b ha hz.1
    (fun x hx => hmax ⟨hx.1, hx.2.trans hz.2⟩)
  have hR := roof_absSlope_integral_of_max_left a b ha hz.2
    (fun x hx => hmax ⟨hz.1.trans hx.1, hx.2⟩)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    ((roofExpr (ι := ι)).intervalIntegrable_sourceDensity a b (fun i => |a i|) l z)
    ((roofExpr (ι := ι)).intervalIntegrable_sourceDensity a b (fun i => |a i|) z r)
  linarith [hH z hz]

theorem roofGraph_le_middle_left (a b : Option ι → ℝ) {u v x : ℝ}
    (huv : u < v) (hx : x ≤ u)
    (hvalue : (roofExpr (ι := ι)).affineGraph a b u ≤
      (roofExpr (ι := ι)).affineGraph a b v) :
    (roofExpr (ι := ι)).affineGraph a b x ≤ (roofExpr (ι := ι)).affineGraph a b u := by
  have hchord := (concaveOn_roofGraph a b).le_roofChord_of_le
    (mem_univ x) (mem_univ v) huv hx
  have hprod := mul_nonpos_of_nonneg_of_nonpos
    (div_nonneg (sub_nonneg.mpr hvalue) (sub_pos.mpr huv).le) (sub_nonpos.mpr hx)
  unfold roofChord at hchord
  linarith

theorem roofGraph_le_middle_right (a b : Option ι → ℝ) {u v x : ℝ}
    (huv : u < v) (hx : v ≤ x)
    (hvalue : (roofExpr (ι := ι)).affineGraph a b v ≤
      (roofExpr (ι := ι)).affineGraph a b u) :
    (roofExpr (ι := ι)).affineGraph a b x ≤ (roofExpr (ι := ι)).affineGraph a b v := by
  have hchord := (concaveOn_roofGraph a b).le_roofChord_of_ge
    (mem_univ u) (mem_univ x) huv hx
  have hprod := mul_nonpos_of_nonpos_of_nonneg
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hvalue) (sub_pos.mpr huv).le)
    (sub_nonneg.mpr hx)
  have hline : roofChord ((roofExpr (ι := ι)).affineGraph a b) u v x =
      (roofExpr (ι := ι)).affineGraph a b v +
        ((roofExpr (ι := ι)).affineGraph a b v - (roofExpr (ι := ι)).affineGraph a b u) /
          (v - u) * (x - v) := by
    unfold roofChord
    field_simp [(sub_pos.mpr huv).ne']
    ring
  rw [hline] at hchord
  linarith

theorem roof_outer_absSlope_integrals_le (a b : Option ι → ℝ)
    (ha : Function.Injective a) {l u v r H : ℝ}
    (hlu : l ≤ u) (huv : u < v) (hvr : v ≤ r)
    (hH : ∀ x ∈ Icc l r, (roofExpr (ι := ι)).affineGraph a b x ≤ H) :
    (∫ x in l..u, (roofExpr (ι := ι)).sourceDensity a b (fun i => |a i|) x) +
      (∫ x in v..r, (roofExpr (ι := ι)).sourceDensity a b (fun i => |a i|) x) ≤
      2 * H - |(roofExpr (ι := ι)).affineGraph a b v -
        (roofExpr (ι := ι)).affineGraph a b u| -
        (roofExpr (ι := ι)).affineGraph a b l - (roofExpr (ι := ι)).affineGraph a b r := by
  by_cases hvalue : (roofExpr (ι := ι)).affineGraph a b u ≤
      (roofExpr (ι := ι)).affineGraph a b v
  · have hL := roof_absSlope_integral_of_max_right a b ha hlu
      (fun x hx => roofGraph_le_middle_left a b huv hx.2 hvalue)
    have hR := roof_absSlope_integral_le a b ha hvr
      (fun x hx => hH x ⟨hlu.trans (huv.le.trans hx.1), hx.2⟩)
    rw [abs_of_nonneg (sub_nonneg.mpr hvalue)]
    linarith
  · have hvalue' := le_of_not_ge hvalue
    have hL := roof_absSlope_integral_le a b ha hlu
      (fun x hx => hH x ⟨hx.1, hx.2.trans (huv.le.trans hvr)⟩)
    have hR := roof_absSlope_integral_of_max_left a b ha hvr
      (fun x hx => roofGraph_le_middle_right a b huv hx.1 hvalue')
    rw [abs_of_nonpos (sub_nonpos.mpr hvalue')]
    linarith

end FinitePolygon

end AmbidextrousSofa
