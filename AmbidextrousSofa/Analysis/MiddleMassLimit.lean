import AmbidextrousSofa.Analysis.MiddleNormalStability
import AmbidextrousSofa.Analysis.DyadicNeighbors
import AmbidextrousSofa.Analysis.CapScoreContinuity

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

namespace AngularGrid

open FinitePolygon

def outerAngleDensity (U : Set Plane) (grid : Finset QuarterAngle) (E : Set ℝ) : ℝ → ℝ := by
  classical
  exact fun x => ∑ j ∈ Finset.univ.filter (fun j : SourceIndex grid => fullAngle grid j ∈ E),
    outerDensity U grid j x

theorem outerAngleDensity_nonneg (U : Set Plane) (grid : Finset QuarterAngle)
    (E : Set ℝ) (x : ℝ) : 0 ≤ outerAngleDensity U grid E x := by
  classical
  exact Finset.sum_nonneg (fun j _ => outerDensity_nonneg U grid j x)

theorem measurable_outerAngleDensity (U : Set Plane) (grid : Finset QuarterAngle) (E : Set ℝ) :
    Measurable (outerAngleDensity U grid E) := by
  classical
  apply Finset.measurable_sum
  intro j _
  exact (roofExpr (ι := SourceIndex grid)).measurable_sourceDensity _ _ _

/-- The literal source partition has total multiplicity at most one,
even at ties and even if several zero-length facets are present. -/
theorem outerAngleDensity_le {U : Set Plane} {grid : Finset QuarterAngle} {E : Set ℝ}
    {s : ℝ} (hs : 0 < s) (hE : ∀ t ∈ E, s ≤ Real.sin t) (x : ℝ) :
    outerAngleDensity U grid E x ≤ 1 / s := by
  classical
  let F := Finset.univ.filter (fun j : SourceIndex grid => fullAngle grid j ∈ E)
  let v := fun i => wallSlope (normal grid) i * x +
    roofIntercept (normal grid) (fun j => support U (normal grid j)) i
  change (∑ j ∈ F, outwardVelocity (normal grid) j ((roofExpr (ι := SourceIndex grid)).source v)) ≤ _
  cases hsource : (roofExpr (ι := SourceIndex grid)).source v with
  | none => simp [outwardVelocity, (div_pos (by norm_num) hs).le]
  | some i =>
    by_cases hi : i ∈ F
    · rw [Finset.sum_eq_single_of_mem i hi]
      · simp only [outwardVelocity, if_pos rfl]
        apply one_div_le_one_div_of_le hs
        simpa only [normal_eq_unitNormal, unitNormal] using
          hE (fullAngle grid i) (Finset.mem_filter.mp hi).2
      · intro j _ hji
        simp only [outwardVelocity, if_neg (Ne.symm hji)]
    · have hzero : (∑ j ∈ F, outwardVelocity (normal grid) j (some i)) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have hij : i ≠ j := by intro heq; exact hi (heq.symm ▸ hj)
        simp only [outwardVelocity, if_neg hij]
      rw [hzero]
      exact (div_pos (by norm_num) hs).le

theorem outerAngleDensity_eq_zero_of_no_edge {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (hpoly : U = circumscription U (normal grid))
    (E : Set ℝ) {x : ℝ} (hx : x ∈ horizontalProjection U)
    (hno : ∀ t ∈ E, (x, capRoof U x) ∉ Imported.edge U t) :
    outerAngleDensity U grid E x = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro j hj
  have hjE := (Finset.mem_filter.mp hj).2
  have hnot : x ∉ (roofExpr (ι := SourceIndex grid)).sourceSet (wallSlope (normal grid))
      (roofIntercept (normal grid) (fun i => support U (normal grid i))) (some j) := by
    intro hsource
    exact hno (fullAngle grid j) hjE
      (outerSource_mem_edge hU (normal grid) (normal_snd_pos grid) hpoly j
        (normal_eq_unitNormal grid j) hx hsource)
  unfold outerDensity
  rw [outwardVelocity_eq_single, WallExpr.sourceDensity_single,
    indicator_of_notMem hnot]

def middleAngleDensity (U : Set Plane) (grid : Finset QuarterAngle) (E : Set ℝ) : ℝ → ℝ :=
  (middleHalfInterval (horizontalLeft U) (horizontalRight U)).indicator
    (outerAngleDensity U grid E)

theorem measurable_middleAngleDensity (U : Set Plane) (grid : Finset QuarterAngle) (E : Set ℝ) :
    Measurable (middleAngleDensity U grid E) :=
  (measurable_outerAngleDensity U grid E).indicator (measurableSet_middleHalfInterval _ _)

theorem integral_middleAngleDensity {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (E : Set ℝ) :
    (∫ x : ℝ, middleAngleDensity U grid E x) =
      ∑ j ∈ Finset.univ.filter (fun j : SourceIndex grid => fullAngle grid j ∈ E),
        middleOuterMass U grid j := by
  classical
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  have hmiddle : horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4 ≤
      horizontalRight U - (horizontalRight U - horizontalLeft U) / 4 := by linarith
  rw [middleAngleDensity, integral_indicator (measurableSet_middleHalfInterval _ _)]
  change (∫ x in Icc (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)
      (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4), _) = _
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hmiddle]
  exact intervalIntegral.integral_finsetSum
    (fun j _ => intervalIntegrable_outerDensity U grid j _ _)

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
  let a := horizontalLeft K + capWidth K / 4
  let b := horizontalRight K - capWidth K / 4
  obtain ⟨ha, hb, hab⟩ := hK.middleChord_endpoints hwidth
  have hfa : capRoof K a = m * a + c := haffine a ⟨le_rfl, hab.le⟩
  have hfb : capRoof K b = m * b + c := haffine b ⟨hab.le, le_rfl⟩
  have hpointa : (a, m * a + c) ∈ K := by rw [← hfa]; exact capRoof_mem hK.isCompact ha
  have hpointb : (b, m * b + c) ∈ K := by rw [← hfb]; exact capRoof_mem hK.isCompact hb
  have hface := hK.support_of_affine_segment ha hb hab haffine
  have hxa : ∀ᵐ x : ℝ ∂volume, x ≠ a := by
    simpa only [mem_singleton_iff] using
      (measure_eq_zero_iff_ae_notMem.mp (measure_singleton a : volume {a} = 0))
  have hxb : ∀ᵐ x : ℝ ∂volume, x ≠ b := by
    simpa only [mem_singleton_iff] using
      (measure_eq_zero_iff_ae_notMem.mp (measure_singleton b : volume {b} = 0))
  filter_upwards [hxa, hxb, h.middle_membership_ae hU hK] with x hxa hxb hmem
  by_cases hx : x ∈ middleHalfInterval (horizontalLeft K) (horizontalRight K)
  · have hx' : x ∈ Ioo a b :=
      ⟨lt_of_le_of_ne hx.1 hxa.symm, lt_of_le_of_ne hx.2 hxb⟩
    filter_upwards [hmem, h.eventually_no_middle_edge hU hK hpointa hpointb hface hx' hτ hE]
      with n hn hno
    have hxmid := hn.mpr hx
    rw [middleAngleDensity, indicator_of_mem hxmid]
    apply outerAngleDensity_eq_zero_of_no_edge (hU n) (grid n) (hpoly n) E ?_ hno
    rw [horizontalProjection_eq_Icc (hU n).nonempty (hU n).isCompact (hU n).convex]
    exact middleHalfInterval_subset
      (horizontalLeft_le_horizontalRight (hU n).nonempty (hU n).isCompact) hxmid
  · filter_upwards [hmem] with n hn
    exact indicator_of_notMem (fun hxn => hx (hn.mp hxn)) _

/-- The actual off-facet middle mass tends to zero. No selected maximum
assumption is needed once the target has an affine middle segment. -/
theorem middleOuterMass_sum_tendsto
    {U : ℕ → Set Plane} {K : Set Plane} {grid : ℕ → Finset QuarterAngle}
    (h : CapHausdorffTendsto U K) (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    (hpoly : ∀ n, U n = circumscription (U n) (normal (grid n)))
    {R m c s τ : ℝ} {E : Set ℝ}
    (hbox : ∀ n, U n ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hwidth : 0 < capWidth K)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft K) (horizontalRight K),
      capRoof K x = m * x + c)
    (hs : 0 < s) (hτ : 0 < τ)
    (hsin : ∀ t ∈ E, s ≤ Real.sin t)
    (hnormal : ∀ t ∈ E, τ ≤ |Real.cos t + m * Real.sin t|) :
    Tendsto (fun n => ∑ j ∈ Finset.univ.filter
      (fun j : SourceIndex (grid n) => fullAngle (grid n) j ∈ E),
        middleOuterMass (U n) (grid n) j) atTop (𝓝 0) := by
  classical
  let B := (Icc (-R) R).indicator (fun _ : ℝ => 1 / s)
  have hB : Integrable B volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
  have hdom : ∀ n, ∀ᵐ x : ℝ ∂volume, ‖middleAngleDensity (U n) (grid n) E x‖ ≤ B x := by
    intro n
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ middleHalfInterval (horizontalLeft (U n)) (horizontalRight (U n))
    · have hxproj : x ∈ horizontalProjection (U n) := by
        rw [horizontalProjection_eq_Icc (hU n).nonempty (hU n).isCompact (hU n).convex]
        exact middleHalfInterval_subset
          (horizontalLeft_le_horizontalRight (hU n).nonempty (hU n).isCompact) hx
      obtain ⟨p, hp, hpx⟩ := hxproj
      have hxB : x ∈ Icc (-R) R := by simpa only [hpx] using (hbox n hp).1
      rw [middleAngleDensity, indicator_of_mem hx, Real.norm_of_nonneg
        (outerAngleDensity_nonneg _ _ _ _)]
      simpa only [B, indicator_of_mem hxB] using outerAngleDensity_le hs hsin x
    · rw [middleAngleDensity, indicator_of_notMem hx, norm_zero]
      exact indicator_nonneg (fun _ _ => (div_pos (by norm_num) hs).le) x
  have hzero := middleAngleDensity_eventually_zero h hU hK hpoly hwidth haffine hτ
    (fun t ht => ⟨hs.le.trans (hsin t ht), hnormal t ht⟩)
  have hlim : ∀ᵐ x : ℝ ∂volume,
      Tendsto (fun n => middleAngleDensity (U n) (grid n) E x) atTop (𝓝 0) := by
    filter_upwards [hzero] with x hx
    exact tendsto_const_nhds.congr' hx.symm
  have h := tendsto_integral_of_dominated_convergence B
    (fun n => (measurable_middleAngleDensity (U n) (grid n) E).aestronglyMeasurable)
    hB hdom hlim
  have hIntegral (n : ℕ) := integral_middleAngleDensity (hU n) (grid n) E
  simpa only [hIntegral, integral_zero] using h

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
  classical
  by_cases hne : E.Nonempty
  · obtain ⟨u, hu, hminsin⟩ := hE.exists_isMinOn hne Real.continuous_sin.continuousOn
    have hcont : ContinuousOn (fun t : ℝ => |Real.cos t + m * Real.sin t|) E := by fun_prop
    obtain ⟨v, hv, hminperp⟩ := hE.exists_isMinOn hne hcont
    exact middleOuterMass_sum_tendsto h hU hK hpoly hbox hwidth haffine
      (Real.sin_pos_of_mem_Ioo (hupper hu)) (abs_pos.mpr (hperp v hv))
      hminsin hminperp
  · have hempty := Set.not_nonempty_iff_eq_empty.mp hne
    subst E
    simpa only [Set.mem_empty_iff_false, Finset.filter_false, Finset.sum_empty] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

end AngularGrid

end AmbidextrousSofa
