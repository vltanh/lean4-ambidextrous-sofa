module

public import AmbidextrousSofa.Analysis.MiddleNormalStability
public import AmbidextrousSofa.Analysis.DyadicNeighbors
public import AmbidextrousSofa.Analysis.CapScoreContinuity

@[expose] public section

/-!
# Disappearance of the off-facet middle source mass

The source of a finite roof is an actual single leaf, including at ties.
Thus the sum of the arclength densities whose normals lie in a compact
upper angular set is bounded by the reciprocal of its minimum sine.
The quantitative affine-face stability theorem makes that density zero
eventually at each strict interior middle abscissa. The moving endpoints
form a null exceptional set, so dominated convergence gives the actual
vanishing middle mass needed for the wing curvature argument.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

private theorem IsDownwardCap.middleHalfInterval_subset_projection {U : Set Plane}
    (hU : IsDownwardCap U) :
    middleHalfInterval (horizontalLeft U) (horizontalRight U) ⊆ horizontalProjection U := by
  rw [hU.horizontalProjection_eq_Icc]
  exact middleHalfInterval_subset (horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact)

namespace AngularGrid

open FinitePolygon

def outerAngleDensity (U : Set Plane) (grid : Finset QuarterAngle) (E : Set ℝ) : ℝ → ℝ := by
  classical
  exact fun x => ∑ j ∈ Finset.univ.filter (fun j : SourceIndex grid => fullAngle grid j ∈ E),
    outerDensity U grid j x

theorem outerAngleDensity_nonneg (U : Set Plane) (grid : Finset QuarterAngle)
    (E : Set ℝ) (x : ℝ) : 0 ≤ outerAngleDensity U grid E x :=
  Finset.sum_nonneg fun j _ => outerDensity_nonneg U grid j x

/-- The literal source partition has total multiplicity at most one,
even at ties and even if several zero-length facets are present. -/
theorem outerAngleDensity_le {U : Set Plane} {grid : Finset QuarterAngle} {E : Set ℝ}
    {s : ℝ} (hs : 0 < s) (hE : ∀ t ∈ E, s ≤ Real.sin t) (x : ℝ) :
    outerAngleDensity U grid E x ≤ 1 / s := by
  classical
  let v := fun i => wallSlope (normal grid) i * x +
    roofIntercept (normal grid) (fun j => support U (normal grid j)) i
  change (∑ j ∈ Finset.univ.filter (fun j : SourceIndex grid => fullAngle grid j ∈ E),
    outwardVelocity (normal grid) j ((roofExpr (ι := SourceIndex grid)).source v)) ≤ _
  rcases (roofExpr (ι := SourceIndex grid)).source v with _ | i
  · simp [outwardVelocity, hs.le]
  simp only [outwardVelocity, Finset.sum_ite_eq]
  split_ifs with hi
  · refine one_div_le_one_div_of_le hs ?_
    simpa only [normal_eq_unitNormal, unitNormal] using hE _ (Finset.mem_filter.mp hi).2
  · positivity

theorem outerAngleDensity_eq_zero_of_no_edge {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (hpoly : U = circumscription U (normal grid))
    (E : Set ℝ) {x : ℝ} (hx : x ∈ horizontalProjection U)
    (hno : ∀ t ∈ E, (x, capRoof U x) ∉ MovingSofaOptimality.edge U t) :
    outerAngleDensity U grid E x = 0 := by
  classical
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [outerDensity, outwardVelocity_eq_single, WallExpr.sourceDensity_single, indicator_of_notMem]
  exact fun hsource => hno _ (Finset.mem_filter.mp hj).2 (outerSource_mem_edge hU (normal grid)
    (normal_snd_pos grid) hpoly j (normal_eq_unitNormal grid j) hx hsource)

def middleAngleDensity (U : Set Plane) (grid : Finset QuarterAngle) (E : Set ℝ) : ℝ → ℝ :=
  (middleHalfInterval (horizontalLeft U) (horizontalRight U)).indicator
    (outerAngleDensity U grid E)

theorem measurable_middleAngleDensity (U : Set Plane) (grid : Finset QuarterAngle) (E : Set ℝ) :
    Measurable (middleAngleDensity U grid E) :=
  (Finset.measurable_sum _ fun _ _ => WallExpr.measurable_sourceDensity _ _ _ _).indicator
    (measurableSet_middleHalfInterval _ _)

open Classical in
theorem integral_middleAngleDensity {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (E : Set ℝ) :
    (∫ x : ℝ, middleAngleDensity U grid E x) =
      ∑ j ∈ Finset.univ.filter (fun j : SourceIndex grid => fullAngle grid j ∈ E),
        middleOuterMass U grid j := by
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  rw [middleAngleDensity, integral_indicator (measurableSet_middleHalfInterval _ _),
    middleHalfInterval, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith)]
  exact intervalIntegral.integral_finsetSum fun j _ => intervalIntegrable_outerDensity U grid j _ _

theorem middleAngleDensity_eventually_zero
    {U : ℕ → Set Plane} {K : Set Plane} {grid : ℕ → Finset QuarterAngle}
    (h : CapHausdorffTendsto U K) (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    (hpoly : ∀ n, U n = circumscription (U n) (normal (grid n)))
    {m c τ : ℝ} {E : Set ℝ} (hwidth : 0 < capWidth K)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft K) (horizontalRight K),
      capRoof K x = m * x + c)
    (hτ : 0 < τ)
    (hE : ∀ t ∈ E, 0 ≤ Real.sin t ∧ τ ≤ |Real.cos t + m * Real.sin t|) :
    ∀ᵐ x : ℝ ∂volume, ∀ᶠ n in atTop, middleAngleDensity (U n) (grid n) E x = 0 := by
  obtain ⟨ha, hb, hab⟩ := hK.middleChord_endpoints hwidth
  filter_upwards [volume.ae_ne (horizontalLeft K + capWidth K / 4),
    volume.ae_ne (horizontalRight K - capWidth K / 4), h.middle_membership_ae hU hK]
    with x hxa hxb hmem
  by_cases hx : x ∈ middleHalfInterval (horizontalLeft K) (horizontalRight K)
  · filter_upwards [hmem, h.eventually_no_middle_edge hU hK
      (haffine _ ⟨le_rfl, hab.le⟩ ▸ capRoof_mem hK.isCompact ha)
      (haffine _ ⟨hab.le, le_rfl⟩ ▸ capRoof_mem hK.isCompact hb)
      (hK.support_of_affine_segment ha hb hab haffine)
      ⟨hx.1.lt_of_ne hxa.symm, hx.2.lt_of_ne hxb⟩ hτ hE] with n hn hno
    rw [middleAngleDensity, indicator_of_mem (hn.mpr hx)]
    exact outerAngleDensity_eq_zero_of_no_edge (hU n) (grid n) (hpoly n) E
      ((hU n).middleHalfInterval_subset_projection (hn.mpr hx)) hno
  · filter_upwards [hmem] with n hn
    exact indicator_of_notMem (fun hxn => hx (hn.mp hxn)) _

open Classical in
/-- Compact angular sets disjoint from the affine-face normal supply
the positive sine and perpendicularity margins automatically. -/
theorem middleOuterMass_sum_tendsto_of_compact
    {U : ℕ → Set Plane} {K : Set Plane} {grid : ℕ → Finset QuarterAngle}
    (h : CapHausdorffTendsto U K) (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    (hpoly : ∀ n, U n = circumscription (U n) (normal (grid n)))
    {R m c : ℝ} {E : Set ℝ}
    (hbox : ∀ n, U n ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hwidth : 0 < capWidth K)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft K) (horizontalRight K),
      capRoof K x = m * x + c)
    (hE : IsCompact E) (hupper : E ⊆ Ioo 0 Real.pi)
    (hperp : ∀ t ∈ E, Real.cos t + m * Real.sin t ≠ 0) :
    Tendsto (fun n => ∑ j ∈ Finset.univ.filter
      (fun j : SourceIndex (grid n) => fullAngle (grid n) j ∈ E),
        middleOuterMass (U n) (grid n) j) atTop (𝓝 0) := by
  rcases E.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨u, hu, hsin⟩ := hE.exists_isMinOn hne Real.continuous_sin.continuousOn
  obtain ⟨v, hv, hnormal⟩ := hE.exists_isMinOn hne
    (by fun_prop : ContinuousOn (fun t : ℝ => |Real.cos t + m * Real.sin t|) E)
  have hs : 0 < Real.sin u := Real.sin_pos_of_mem_Ioo (hupper hu)
  -- Dominated convergence, with the bound `1 / sin u` on the box `[-R, R]`.
  have hdom (n : ℕ) : ∀ᵐ x : ℝ ∂volume, ‖middleAngleDensity (U n) (grid n) E x‖ ≤
      (Icc (-R) R).indicator (fun _ => 1 / Real.sin u) x := by
    refine Eventually.of_forall fun x => ?_
    rw [middleAngleDensity, Real.norm_of_nonneg
      (indicator_nonneg (fun _ _ => outerAngleDensity_nonneg _ _ _ _) _)]
    refine (indicator_le_indicator (outerAngleDensity_le hs hsin x)).trans
      (indicator_le_indicator_of_subset (fun y hy => ?_) (fun _ => by positivity) x)
    obtain ⟨p, hp, rfl⟩ := (hU n).middleHalfInterval_subset_projection hy
    exact (hbox n hp).1
  simpa only [integral_middleAngleDensity (hU _), integral_zero] using
    tendsto_integral_of_dominated_convergence _
      (fun n => (measurable_middleAngleDensity (U n) (grid n) E).aestronglyMeasurable)
      (continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc) hdom
      ((middleAngleDensity_eventually_zero h hU hK hpoly hwidth haffine (abs_pos.mpr (hperp v hv))
        fun t ht => ⟨hs.le.trans (hsin ht), hnormal ht⟩).mono
          fun x hx => (tendsto_congr' hx).mpr tendsto_const_nhds)

end AngularGrid

end AmbidextrousSofa
