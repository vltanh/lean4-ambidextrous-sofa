module

public import AmbidextrousSofa.Analysis.PolygonExposure

@[expose] public section

/-!
# Actual endpoint movement from a positive vertical end face

Moving a displayed box wall need not move the actual projection. Here a
positive end face gives a point strictly below every nonaxis upper wall.
Its small horizontal displacement lies in the enlarged polygon and
realizes the new endpoint. All sampled upper supports stay fixed. This is
the geometric condition needed before applying the moving-window pressure
formulas.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace FinitePolygon

variable {ι : Type*}

theorem baseline_halfspace_of_endpoints {l r x height : ℝ} {n : Plane}
    (hl : coordDot (l, 0) n ≤ height) (hr : coordDot (r, 0) n ≤ height)
    (hx : x ∈ Icc l r) : coordDot (x, 0) n ≤ height := by
  simp only [coordDot, zero_mul, add_zero] at hl hr ⊢
  by_cases hn : 0 ≤ n.1
  · exact (mul_le_mul_of_nonneg_right hx.2 hn).trans hr
  · exact (mul_le_mul_of_nonpos_right hx.1 (le_of_not_ge hn)).trans hl

theorem upperPolygon_subset_of_interval_subset {l r l' r' : ℝ}
    (normal : ι → Plane) (height : ι → ℝ) (hinterval : Icc l r ⊆ Icc l' r') :
    upperPolygon l r normal height ⊆ upperPolygon l' r' normal height := by
  intro p hp
  obtain ⟨hx, hy, hhalf⟩ := (mem_upperPolygon_iff _ _ _ _ _).mp hp
  exact (mem_upperPolygon_iff _ _ _ _ _).mpr ⟨hinterval hx, hy, hhalf⟩

theorem support_upperPolygon_of_interval_subset {l r l' r' : ℝ}
    (normal : ι → Plane) (height : ι → ℝ) (hinterval : Icc l r ⊆ Icc l' r')
    (hne : (upperPolygon l r normal height).Nonempty)
    (hexact : ∀ i, support (upperPolygon l r normal height) (normal i) = height i) (i : ι) :
    support (upperPolygon l' r' normal height) (normal i) = height i := by
  have hsub := upperPolygon_subset_of_interval_subset normal height hinterval
  apply le_antisymm
  · apply support_le_of_forall (hne.mono hsub)
    intro p hp
    exact ((mem_upperPolygon_iff _ _ _ _ _).mp hp).2.2 i
  · rw [← hexact i]
    exact support_mono hsub hne (isCompact_upperPolygon _ _ _ _) _

/-- A positive right end face gives actual outward movement of the right
projection endpoint. The top and all nonaxis supporting parameters stay
fixed throughout this family. -/
theorem exists_right_axis_variation [Fintype ι] {l r e : ℝ}
    (normal : ι → Plane) (height : ι → ℝ) (hlr : l ≤ r)
    (hnormal : ∀ i, 0 < (normal i).2)
    (hbaseline : ∀ x ∈ Icc l r, ∀ i, coordDot (x, 0) (normal i) ≤ height i)
    (hexact : ∀ i, support (upperPolygon l r normal height) (normal i) = height i)
    (hface : (r, e) ∈ upperPolygon l r normal height) (he : 0 < e) :
    ∃ δ > 0, ∀ ε ∈ Ico (0 : ℝ) δ,
      IsDownwardCap (upperPolygon l (r + ε) normal height) ∧
      (∀ x ∈ Icc l (r + ε), ∀ i, coordDot (x, 0) (normal i) ≤ height i) ∧
      horizontalProjection (upperPolygon l (r + ε) normal height) = Icc l (r + ε) ∧
      ∀ i, support (upperPolygon l (r + ε) normal height) (normal i) = height i := by
  have hfacehalf := ((mem_upperPolygon_iff _ _ _ _ _).mp hface).2.2
  have hstrict : ∀ i, coordDot (r, e / 2) (normal i) < height i := by
    intro i
    have h := hfacehalf i
    unfold coordDot at h ⊢
    nlinarith [mul_pos he (hnormal i)]
  have hnear : ∀ᶠ ε : ℝ in 𝓝 0,
      ∀ i, coordDot (r + ε, e / 2) (normal i) < height i := by
    apply eventually_all.mpr
    intro i
    have hc : Continuous (fun ε : ℝ => coordDot (r + ε, e / 2) (normal i)) := by
      unfold coordDot
      fun_prop
    exact hc.continuousAt (Iio_mem_nhds (by simpa only [add_zero] using hstrict i))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨δ, hδ, ?_⟩
  intro ε hε
  have hεball : ε ∈ Metric.ball (0 : ℝ) δ := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hε.1] using hε.2
  have hnew := hball hεball
  have hbaseline' : ∀ x ∈ Icc l (r + ε), ∀ i, coordDot (x, 0) (normal i) ≤ height i := by
    intro x hx i
    apply baseline_halfspace_of_endpoints (hbaseline l ⟨le_rfl, hlr⟩ i) ?_ hx
    have h := hnew i
    unfold coordDot at h ⊢
    nlinarith [mul_pos he (hnormal i)]
  have hlr' : l ≤ r + ε := by linarith [hε.1]
  refine ⟨isDownwardCap_upperPolygon _ _ _ _ hlr' (fun i => (hnormal i).le) hbaseline',
    hbaseline', horizontalProjection_upperPolygon _ _ _ _ hbaseline', ?_⟩
  intro i
  apply support_upperPolygon_of_interval_subset normal height ?_ ⟨(r, e), hface⟩ hexact i
  intro x hx
  exact ⟨hx.1, by linarith [hx.2, hε.1]⟩

/-- The left endpoint has the same positive-face justification, with its
actual coordinate moving at speed minus one. -/
theorem exists_left_axis_variation [Fintype ι] {l r e : ℝ}
    (normal : ι → Plane) (height : ι → ℝ) (hlr : l ≤ r)
    (hnormal : ∀ i, 0 < (normal i).2)
    (hbaseline : ∀ x ∈ Icc l r, ∀ i, coordDot (x, 0) (normal i) ≤ height i)
    (hexact : ∀ i, support (upperPolygon l r normal height) (normal i) = height i)
    (hface : (l, e) ∈ upperPolygon l r normal height) (he : 0 < e) :
    ∃ δ > 0, ∀ ε ∈ Ico (0 : ℝ) δ,
      IsDownwardCap (upperPolygon (l - ε) r normal height) ∧
      (∀ x ∈ Icc (l - ε) r, ∀ i, coordDot (x, 0) (normal i) ≤ height i) ∧
      horizontalProjection (upperPolygon (l - ε) r normal height) = Icc (l - ε) r ∧
      ∀ i, support (upperPolygon (l - ε) r normal height) (normal i) = height i := by
  have hfacehalf := ((mem_upperPolygon_iff _ _ _ _ _).mp hface).2.2
  have hstrict : ∀ i, coordDot (l, e / 2) (normal i) < height i := by
    intro i
    have h := hfacehalf i
    unfold coordDot at h ⊢
    nlinarith [mul_pos he (hnormal i)]
  have hnear : ∀ᶠ ε : ℝ in 𝓝 0,
      ∀ i, coordDot (l - ε, e / 2) (normal i) < height i := by
    apply eventually_all.mpr
    intro i
    have hc : Continuous (fun ε : ℝ => coordDot (l - ε, e / 2) (normal i)) := by
      unfold coordDot
      fun_prop
    exact hc.continuousAt (Iio_mem_nhds (by simpa only [sub_zero] using hstrict i))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨δ, hδ, ?_⟩
  intro ε hε
  have hεball : ε ∈ Metric.ball (0 : ℝ) δ := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hε.1] using hε.2
  have hnew := hball hεball
  have hbaseline' : ∀ x ∈ Icc (l - ε) r, ∀ i, coordDot (x, 0) (normal i) ≤ height i := by
    intro x hx i
    apply baseline_halfspace_of_endpoints ?_ (hbaseline r ⟨hlr, le_rfl⟩ i) hx
    have h := hnew i
    unfold coordDot at h ⊢
    nlinarith [mul_pos he (hnormal i)]
  have hlr' : l - ε ≤ r := by linarith [hε.1]
  refine ⟨isDownwardCap_upperPolygon _ _ _ _ hlr' (fun i => (hnormal i).le) hbaseline',
    hbaseline', horizontalProjection_upperPolygon _ _ _ _ hbaseline', ?_⟩
  intro i
  apply support_upperPolygon_of_interval_subset normal height ?_ ⟨(l, e), hface⟩ hexact i
  intro x hx
  exact ⟨by linarith [hx.1, hε.1], hx.2⟩

/-- The actual upper-system expression for the unchanged finite barrier. -/
def barrierEnvelope (normal : ι → Plane) (height : ι → ℝ)
    (corners : List (ι × ι)) (terminal : Option ι) (x : ℝ) : ℝ :=
  (barrierExpr corners terminal).eval
    (fun i => wallSlope normal i * x + barrierIntercept normal height i)

theorem continuous_barrierEnvelope (normal : ι → Plane) (height : ι → ℝ)
    (corners : List (ι × ι)) (terminal : Option ι) :
    Continuous (barrierEnvelope normal height corners terminal) :=
  (barrierExpr corners terminal).continuous_eval (fun _ => by fun_prop)

end FinitePolygon

end AmbidextrousSofa
