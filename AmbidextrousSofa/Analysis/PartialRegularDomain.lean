module

public import AmbidextrousSofa.Analysis.PartialSharpCurvatureDensity

@[expose] public section

/-!
# The actual proper regular upper domain

The terminal normal is removed in addition to the top and affine-middle
normals. Restricting the previously proved three-wing measure argument
to each side of the terminal normal glues the actual proper interval
bounds. The resulting density is the curvature of the original cap on
this entire regular domain.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

def regularProperCurvatureDomain (α m : ℝ) : Set ℝ :=
  regularCurvatureDomain m \ {α}

theorem isOpen_regularProperCurvatureDomain (α m : ℝ) :
    IsOpen (regularProperCurvatureDomain α m) :=
  (isOpen_Ioo.sdiff (Set.toFinite _).isClosed).sdiff isClosed_singleton

theorem regularProperCurvatureDomain_subset (α m : ℝ) :
    regularProperCurvatureDomain α m ⊆ Ioo (0 : ℝ) Real.pi :=
  sdiff_subset.trans (regularCurvatureDomain_subset m)

theorem measure_restrict_regularProperCurvatureDomain_le
    {μ ν : Measure ℝ} {α m : ℝ}
    (h : ∀ A B : ℝ, 0 ≤ A → B ≤ Real.pi → Real.pi / 2 ∉ Ioo A B →
      α ∉ Ioo A B → (∀ t ∈ Ioo A B, Real.cos t + m * Real.sin t ≠ 0) →
        μ.restrict (Ioo A B) ≤ ν.restrict (Ioo A B)) :
    μ.restrict (regularProperCurvatureDomain α m) ≤
      ν.restrict (regularProperCurvatureDomain α m) := by
  have hR := measurableSet_regularCurvatureDomain m
  have hbelow : (μ.restrict (Iio α)).restrict (regularCurvatureDomain m) ≤
      (ν.restrict (Iio α)).restrict (regularCurvatureDomain m) :=
    measure_restrict_regularCurvatureDomain_le fun A B hA hB htop hperp => by
      have hsub : Ioo A (min B α) ⊆ Ioo A B := Ioo_subset_Ioo_right (min_le_left _ _)
      simpa only [Measure.restrict_restrict measurableSet_Ioo, Ioo_inter_Iio] using
        h A (min B α) hA ((min_le_left _ _).trans hB) (fun ht => htop (hsub ht))
          (fun ht => (min_le_right B α).not_gt ht.2) (fun t ht => hperp t (hsub ht))
  have habove : (μ.restrict (Ioi α)).restrict (regularCurvatureDomain m) ≤
      (ν.restrict (Ioi α)).restrict (regularCurvatureDomain m) :=
    measure_restrict_regularCurvatureDomain_le fun A B hA hB htop hperp => by
      have hsub : Ioo (max A α) B ⊆ Ioo A B := Ioo_subset_Ioo_left (le_max_left _ _)
      have hinter : Ioo A B ∩ Ioi α = Ioo (max A α) B := by
        ext; simp only [mem_inter_iff, mem_Ioo, mem_Ioi, max_lt_iff]; tauto
      simpa only [Measure.restrict_restrict measurableSet_Ioo, hinter] using
        h (max A α) B (hA.trans (le_max_left _ _)) hB (fun ht => htop (hsub ht))
          (fun ht => (le_max_right A α).not_gt ht.1) (fun t ht => hperp t (hsub ht))
  simp only [Measure.restrict_restrict hR] at hbelow habove
  have hd : Disjoint (regularCurvatureDomain m ∩ Iio α) (regularCurvatureDomain m ∩ Ioi α) :=
    Ioi_disjoint_Iio_same.symm.mono inter_subset_right inter_subset_right
  rw [show regularProperCurvatureDomain α m = (regularCurvatureDomain m ∩ Iio α) ∪
      (regularCurvatureDomain m ∩ Ioi α) by rw [← inter_union_distrib_left, Iio_union_Ioi]; rfl,
    Measure.restrict_union hd (hR.inter measurableSet_Ioi),
    Measure.restrict_union hd (hR.inter measurableSet_Ioi)]
  exact add_le_add hbelow habove

theorem IsJointCapMaximizer.curvature_density_on_regular_proper_domain
    {K : Set Plane} {α m c : ℝ} (hK : IsJointCapMaximizer K α)
    (hproper : α < Real.pi / 2)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft K) (horizontalRight K),
      capRoof K x = m * x + c) :
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧
      (∀ t, 0 ≤ ρ t ∧ ρ t ≤ sourceKappa (upperCornerVelocity K t)) ∧
      (∀ t, ρ t ≤ 8 * (|horizontalLeft K| + |horizontalRight K| + 1) + 24) ∧
      (upperCurvature K).restrict (regularProperCurvatureDomain α m) =
        (volume.restrict (regularProperCurvatureDomain α m)).withDensity
          (fun t => ENNReal.ofReal (ρ t)) := by
  have hfin (μ : Measure ℝ) [IsLocallyFiniteMeasure μ] :
      IsFiniteMeasure (μ.restrict (regularProperCurvatureDomain α m)) :=
    isFiniteMeasure_restrict.mpr ((measure_mono (regularProperCurvatureDomain_subset α m)).trans_lt
      measure_Ioo_lt_top).ne
  have := hfin (upperCurvature K)
  have := hfin volume
  refine exists_real_density_of_two_bounds (by positivity)
    (continuous_sourceKappa.measurable.comp hK.isCap.measurable_upperCornerVelocity)
    (fun t => sourceKappa_nonneg _) ?_ ?_
  · have h := measure_restrict_regularProperCurvatureDomain_le (μ := upperCurvature K)
      (ν := ENNReal.ofReal (8 * (|horizontalLeft K| + |horizontalRight K| + 1) + 24) • volume)
      (α := α) (m := m) fun A B hA hB htop hterminal hperp => by
        simpa only [Measure.restrict_smul] using
          hK.curvature_restrict_le_on_proper_open_wing hproper haffine hA hB htop hterminal hperp
    simpa only [Measure.restrict_smul] using h
  · have h := measure_restrict_regularProperCurvatureDomain_le (μ := upperCurvature K)
      (ν := volume.withDensity fun t => ENNReal.ofReal (sourceKappa (upperCornerVelocity K t)))
      (α := α) (m := m) fun A B hA hB htop hterminal hperp => by
        simpa only [restrict_withDensity measurableSet_Ioo] using
          hK.curvature_restrict_le_source_density_on_proper_open_wing hproper haffine
            hA hB htop hterminal hperp
    simpa only [restrict_withDensity (isOpen_regularProperCurvatureDomain α m).measurableSet]
      using h

theorem IsJointCapMaximizer.sigmaAt_eq_zero_on_regular_proper_domain
    {K : Set Plane} {α m c t : ℝ} (hK : IsJointCapMaximizer K α)
    (hproper : α < Real.pi / 2)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft K) (horizontalRight K),
      capRoof K x = m * x + c)
    (ht : t ∈ regularProperCurvatureDomain α m) : MovingSofaOptimality.sigmaAt K t = 0 := by
  obtain ⟨ρ, hρ, hρbounds, _, heq⟩ := hK.curvature_density_on_regular_proper_domain hproper haffine
  have h := measureReal_eq_integral_of_restrict_withDensity hρ (fun x => (hρbounds x).1)
    heq (measurableSet_singleton t) (singleton_subset_iff.mpr ht)
  simpa [MovingSofaOptimality.sigmaAt, upperCurvature, measureReal_def, integral_singleton] using h

end AmbidextrousSofa
