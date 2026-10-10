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

/-- The actual right-wall pressure, including the two moving middle-window
endpoints and an optional sampled endpoint penalty. -/
theorem selected_right_axis_pressure [Fintype ι] {l r e : ℝ}
    (normal : ι → Plane) (height weight target : ι → ℝ)
    (corners : List (ι × ι)) (terminal : Option ι) (endpointWeight endpointTarget : ℝ)
    (hlr : l ≤ r) (hnormal : ∀ i, 0 < (normal i).2)
    (hbaseline : ∀ x ∈ Icc l r, ∀ i, coordDot (x, 0) (normal i) ≤ height i)
    (hexact : ∀ i, support (upperPolygon l r normal height) (normal i) = height i)
    (hface : (r, e) ∈ upperPolygon l r normal height) (he : 0 < e)
    (hmax : ∀ V : Set Plane, IsDownwardCap V →
      finiteSpatialScore V normal corners terminal - sampledPenalty V normal weight target -
          endpointWeight * (horizontalRight V - endpointTarget) ^ 2 ≤
        finiteSpatialScore (upperPolygon l r normal height) normal corners terminal -
          sampledPenalty (upperPolygon l r normal height) normal weight target -
          endpointWeight * (r - endpointTarget) ^ 2) :
    roofEnvelope normal height r +
        (roofEnvelope normal height (l + (r - l) / 4) +
          barrierEnvelope normal height corners terminal (l + (r - l) / 4)) / 4 -
        3 * (roofEnvelope normal height (r - (r - l) / 4) +
          barrierEnvelope normal height corners terminal (r - (r - l) / 4)) / 4 ≤
      2 * endpointWeight * (r - endpointTarget) := by
  obtain ⟨δ, hδ, hfamily⟩ := exists_right_axis_variation normal height hlr hnormal
    hbaseline hexact hface he
  let F : ℝ → ℝ := fun ε => intervalSpatialScore (roofEnvelope normal height)
      (barrierEnvelope normal height corners terminal) l (r + ε) -
    heightPenalty weight target height - endpointWeight * (r + ε - endpointTarget) ^ 2
  have hline : HasDerivAt (fun ε : ℝ => r + ε - endpointTarget) 1 0 := by
    simpa only [zero_add, sub_zero] using
      ((hasDerivAt_const (0 : ℝ) r).add (hasDerivAt_id (0 : ℝ))).sub_const endpointTarget
  have hpenalty : HasDerivAt (fun ε : ℝ => endpointWeight * (r + ε - endpointTarget) ^ 2)
      (2 * endpointWeight * (r - endpointTarget)) 0 := by
    convert (hline.pow 2).const_mul endpointWeight using 1 <;> norm_num <;> ring
  have hderiv := ((hasDerivAt_intervalSpatialScore_right
    (continuous_roofEnvelope normal height)
    (continuous_barrierEnvelope normal height corners terminal) l r).sub_const
      (heightPenalty weight target height)).sub hpenalty
  have hFmax : ∀ᶠ ε in 𝓝[>] (0 : ℝ), F ε ≤ F 0 := by
    have hsmall : Iio δ ∈ 𝓝[>] (0 : ℝ) :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)
    filter_upwards [hsmall, self_mem_nhdsWithin] with ε hεδ hεpos
    have hε : 0 ≤ ε := (show 0 < ε from hεpos).le
    obtain ⟨hcap, hbase, _, hsupport⟩ := hfamily ε ⟨hε, hεδ⟩
    have h := hmax _ hcap
    have hlr' : l ≤ r + ε := by linarith
    rw [finiteSpatialScore_upperPolygon normal height hlr' hnormal hbase hsupport,
      sampledPenalty_eq_heightPenalty normal weight target height hsupport,
      horizontalRight_upperPolygon normal height hlr' hbase,
      finiteSpatialScore_upperPolygon normal height hlr hnormal hbaseline hexact,
      sampledPenalty_eq_heightPenalty normal weight target height hexact] at h
    simpa only [F, barrierEnvelope, add_zero] using h
  have hsign := hasDerivAt_nonpos_of_right_max hderiv hFmax
  linarith

/-- The left pressure uses outward speed minus one, including the correct
three-quarter motion of the left middle-window endpoint. -/
theorem selected_left_axis_pressure [Fintype ι] {l r e : ℝ}
    (normal : ι → Plane) (height weight target : ι → ℝ)
    (corners : List (ι × ι)) (terminal : Option ι) (endpointWeight endpointTarget : ℝ)
    (hlr : l ≤ r) (hnormal : ∀ i, 0 < (normal i).2)
    (hbaseline : ∀ x ∈ Icc l r, ∀ i, coordDot (x, 0) (normal i) ≤ height i)
    (hexact : ∀ i, support (upperPolygon l r normal height) (normal i) = height i)
    (hface : (l, e) ∈ upperPolygon l r normal height) (he : 0 < e)
    (hmax : ∀ V : Set Plane, IsDownwardCap V →
      finiteSpatialScore V normal corners terminal - sampledPenalty V normal weight target -
          endpointWeight * (-horizontalLeft V - endpointTarget) ^ 2 ≤
        finiteSpatialScore (upperPolygon l r normal height) normal corners terminal -
          sampledPenalty (upperPolygon l r normal height) normal weight target -
          endpointWeight * (-l - endpointTarget) ^ 2) :
    roofEnvelope normal height l -
        3 * (roofEnvelope normal height (l + (r - l) / 4) +
          barrierEnvelope normal height corners terminal (l + (r - l) / 4)) / 4 +
        (roofEnvelope normal height (r - (r - l) / 4) +
          barrierEnvelope normal height corners terminal (r - (r - l) / 4)) / 4 ≤
      2 * endpointWeight * (-l - endpointTarget) := by
  obtain ⟨δ, hδ, hfamily⟩ := exists_left_axis_variation normal height hlr hnormal
    hbaseline hexact hface he
  let F : ℝ → ℝ := fun ε => intervalSpatialScore (roofEnvelope normal height)
      (barrierEnvelope normal height corners terminal) (l - ε) r -
    heightPenalty weight target height - endpointWeight * (-(l - ε) - endpointTarget) ^ 2
  have hline : HasDerivAt (fun ε : ℝ => -(l - ε) - endpointTarget) 1 0 := by
    convert (((hasDerivAt_const (0 : ℝ) l).sub (hasDerivAt_id (0 : ℝ))).neg).sub_const
      endpointTarget using 1 <;> norm_num
  have hpenalty : HasDerivAt (fun ε : ℝ => endpointWeight * (-(l - ε) - endpointTarget) ^ 2)
      (2 * endpointWeight * (-l - endpointTarget)) 0 := by
    convert (hline.pow 2).const_mul endpointWeight using 1 <;> norm_num <;> ring
  have hderiv := ((hasDerivAt_intervalSpatialScore_left
    (continuous_roofEnvelope normal height)
    (continuous_barrierEnvelope normal height corners terminal) l r).sub_const
      (heightPenalty weight target height)).sub hpenalty
  have hFmax : ∀ᶠ ε in 𝓝[>] (0 : ℝ), F ε ≤ F 0 := by
    have hsmall : Iio δ ∈ 𝓝[>] (0 : ℝ) :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)
    filter_upwards [hsmall, self_mem_nhdsWithin] with ε hεδ hεpos
    have hε : 0 ≤ ε := (show 0 < ε from hεpos).le
    obtain ⟨hcap, hbase, _, hsupport⟩ := hfamily ε ⟨hε, hεδ⟩
    have h := hmax _ hcap
    have hlr' : l - ε ≤ r := by linarith
    rw [finiteSpatialScore_upperPolygon normal height hlr' hnormal hbase hsupport,
      sampledPenalty_eq_heightPenalty normal weight target height hsupport,
      horizontalLeft_upperPolygon normal height hlr' hbase,
      finiteSpatialScore_upperPolygon normal height hlr hnormal hbaseline hexact,
      sampledPenalty_eq_heightPenalty normal weight target height hexact] at h
    simpa only [F, barrierEnvelope, sub_zero] using h
  have hsign := hasDerivAt_nonpos_of_right_max hderiv hFmax
  linarith

end FinitePolygon

end AmbidextrousSofa
