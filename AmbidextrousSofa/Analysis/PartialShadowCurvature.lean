module

public import AmbidextrousSofa.Analysis.PartialShadowSecants
public import AmbidextrousSofa.Analysis.PartialAtomIntervalLimit

@[expose] public section

/-!
# The actual proper same-sign curvature laws

The selected polygons and their moving neighboring-wall margins belong
to the original proper maximizer. Summation keeps every unsampled atom
and both vanishing errors. Lebesgue differentiation then gives the
zero and half-density bounds in the two same-sign quadrants. The actual
terminal normal is excluded from the regular domain throughout.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

/-- Both support directions avoid the actual exceptional normals. -/
def regularProperCornerDomain (α m : ℝ) : Set ℝ :=
  Ioo (0 : ℝ) (Real.pi / 2) ∩ (regularProperCurvatureDomain α m ∩
    (fun t : ℝ => t + Real.pi / 2) ⁻¹' regularProperCurvatureDomain α m)

theorem isOpen_regularProperCornerDomain (α m : ℝ) :
    IsOpen (regularProperCornerDomain α m) :=
  have hreg := isOpen_regularProperCurvatureDomain α m
  isOpen_Ioo.inter (hreg.inter (hreg.preimage (continuous_id.add_const (Real.pi / 2))))

namespace PartialGrid

variable {α : TerminalAngle} {hαL : (α : ℝ) < Real.pi / 2}

theorem curvature_local_shadow_bound
    {target : Set Plane} {U : ℕ → Set Plane}
    {boxLeft boxRight R m c t ε : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    {ρ : ℝ → ℝ}
    (hTarget : IsDownwardCap target)
    (hU : ∀ n, IsSelectedPolygon target α hαL boxLeft boxRight (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hbox : ∀ n, U n ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hwidth : 0 < capWidth target)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
      capRoof target x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s)
    (heq : (upperCurvature target).restrict (regularProperCurvatureDomain α m) =
      (volume.restrict (regularProperCurvatureDomain α m)).withDensity
        (fun s => ENNReal.ofReal (ρ s)))
    (positive : Bool) (ht : t ∈ regularProperCurvatureDomain α m)
    (hpaired : sourceQuarterAngle t ∈ regularProperCornerDomain α m)
    (hmargin : 0 < sameSignVelocityMargin positive target (sourceQuarterAngle t))
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ d : ℝ, 0 < d → d < δ →
      (upperCurvature target).real (Ioc t (t + d)) ≤
        (sameSignCoefficient positive t + ε) * d := by
  obtain ⟨δ₀, hδ₀, hfinite⟩ := eventually_shadow_atoms_le hTarget hU hHausdorff hlevel hc
    (isCompact_Icc.prod isCompact_Icc) hbox positive (mem_regularCurvatureDomain_iff.mp ht.1).2.2.1
    (sigmaAt_eq_zero_of_density hρ hρ0 heq hpaired.2.1)
    (sigmaAt_eq_zero_of_density hρ hρ0 heq hpaired.2.2) hmargin hε
  obtain ⟨a, b, htIoo, hIoo⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    ((isOpen_regularProperCurvatureDomain α m).mem_nhds ht)
  refine ⟨min δ₀ (b - t), lt_min hδ₀ (sub_pos.mpr htIoo.2), fun d hd hdδ => ?_⟩
  have hdδ₀ := hdδ.trans_le (min_le_left _ _)
  have hdb := hdδ.trans_le (min_le_right _ _)
  have hreg : Icc t (t + d) ⊆ regularProperCurvatureDomain α m := fun s hs =>
    hIoo ⟨htIoo.1.trans_le hs.1, by linarith [hs.2]⟩
  simpa only [add_sub_cancel_left] using curvature_Ioc_le_of_eventual_sampled_atom_bound
    hTarget hU hHausdorff hlevel hc hrate hbox hwidth haffine
    (add_nonneg (sameSignCoefficient_nonneg positive t) hε.le) (by linarith) hreg
    (sigmaAt_eq_zero_of_density hρ hρ0 heq ht)
    (sigmaAt_eq_zero_of_density hρ hρ0 heq (hreg ⟨by linarith, le_rfl⟩))
    (hfinite.mono fun n hn j hj =>
      hn j (abs_lt.mpr ⟨by linarith [hj.1], by linarith [hj.2]⟩))

end PartialGrid

/-- The actual proper maximum supplies its own selected sequence. The
density premise is only the literal curvature representation already
constructed on its regular domain. The bound is applied at `t` and at
`t + π / 2`, which both fold to the quarter angle `t`. -/
theorem IsJointCapMaximizer.ae_proper_density_same_sign_bound
    {K : Set Plane} {α m c C : ℝ} (hK : IsJointCapMaximizer K α)
    (hproper : α < Real.pi / 2) {ρ : ℝ → ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft K) (horizontalRight K),
      capRoof K x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (heq : (upperCurvature K).restrict (regularProperCurvatureDomain α m) =
      (volume.restrict (regularProperCurvatureDomain α m)).withDensity
        (fun t => ENNReal.ofReal (ρ t)))
    (positive : Bool) :
    ∀ᵐ t ∂volume.restrict (regularProperCornerDomain α m),
      0 < sameSignVelocityMargin positive K t →
        ρ t ≤ (if positive then 0 else 1 / 2) ∧
          ρ (t + Real.pi / 2) ≤ (if positive then 1 / 2 else 0) := by
  have hR : 0 ≤ |horizontalLeft K| + |horizontalRight K| + 1 := by positivity
  obtain ⟨level, coefficient, U, hlevel, hc, hrate, hU, -, hHausdorff⟩ :=
    PartialGrid.exists_selected_sequence ⟨α, hK.angle_mem⟩ hproper hK (neg_le_self hR)
      (subset_symmetricBox_of_horizontalBox fun p hp =>
        ⟨hK.isCap.fst_mem_Icc hp, hK.isCap.inStrip hp⟩)
  have h := ae_density_le_of_conditional_local_bound (isOpen_regularProperCurvatureDomain α m)
    hρ hρ0 hρC heq (f := sameSignCoefficient positive) (P := fun t =>
      sourceQuarterAngle t ∈ regularProperCornerDomain α m ∧
        0 < sameSignVelocityMargin positive K (sourceQuarterAngle t))
    fun t ht hP ε hε => PartialGrid.curvature_local_shadow_bound hK.isCap hU hHausdorff
      (tendsto_atTop_mono hlevel tendsto_id) (fun n => (hc n).le) hrate (fun n => (hU n).inBox)
      (by linarith only [hK.width_bounds.1, one_lt_M]) haffine hρ hρ0 heq positive ht
      hP.1 hP.2 hε
  filter_upwards [ae_restrict_mem (isOpen_regularProperCornerDomain α m).measurableSet,
    ae_restrict_of_ae h, ae_restrict_of_ae
      ((measurePreserving_add_right volume (Real.pi / 2)).quasiMeasurePreserving.ae h)]
    with t ht h1 h2 hm
  have hnot : ¬ t + Real.pi / 2 < Real.pi / 2 := by linarith only [ht.1.1]
  have hbase : sourceQuarterAngle t = t := ite_eq_left ht.1.2
  have hshift : sourceQuarterAngle (t + Real.pi / 2) = t := by simp [sourceQuarterAngle, hnot]
  constructor
  · simpa [sameSignCoefficient, ht.1.2] using h1 ht.2.1 ⟨hbase.symm ▸ ht, hbase.symm ▸ hm⟩
  · simpa [sameSignCoefficient, hnot] using h2 ht.2.2 ⟨hshift.symm ▸ ht, hshift.symm ▸ hm⟩

/-- In the convention `p = -secondCornerVelocity` and
`q = firstCornerVelocity`, these are the `++` and `--` source laws.
Both densities represent curvature of the original proper cap. -/
theorem IsJointCapMaximizer.ae_proper_curvature_same_sign_quadrants
    {K : Set Plane} {α m c C : ℝ} (hK : IsJointCapMaximizer K α)
    (hproper : α < Real.pi / 2) {ρ : ℝ → ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft K) (horizontalRight K),
      capRoof K x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (heq : (upperCurvature K).restrict (regularProperCurvatureDomain α m) =
      (volume.restrict (regularProperCurvatureDomain α m)).withDensity
        (fun t => ENNReal.ofReal (ρ t))) :
    ∀ᵐ t ∂volume.restrict (regularProperCornerDomain α m),
      (0 < firstCornerVelocity K t ∧ secondCornerVelocity K t < 0 →
        ρ t = 0 ∧ ρ (t + Real.pi / 2) ≤ 1 / 2) ∧
      (firstCornerVelocity K t < 0 ∧ 0 < secondCornerVelocity K t →
        ρ (t + Real.pi / 2) = 0 ∧ ρ t ≤ 1 / 2) := by
  filter_upwards [hK.ae_proper_density_same_sign_bound hproper haffine hρ hρ0 hρC heq true,
    hK.ae_proper_density_same_sign_bound hproper haffine hρ hρ0 hρC heq false] with t hp hn
  refine ⟨fun ⟨hq, hr⟩ => ?_, fun ⟨hq, hr⟩ => ?_⟩
  · obtain ⟨h1, h2⟩ := hp (lt_min (neg_pos.mpr hr) hq)
    exact ⟨le_antisymm h1 (hρ0 t), h2⟩
  · obtain ⟨h1, h2⟩ := hn (lt_min hr (neg_pos.mpr hq))
    exact ⟨le_antisymm h2 (hρ0 _), h1⟩

end AmbidextrousSofa
