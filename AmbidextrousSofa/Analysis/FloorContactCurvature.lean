module

public import AmbidextrousSofa.Analysis.CornerDynamics

@[expose] public section

/-!
# Strict unit-curvature control at floor contact

The sharp source-density bound and the actual zero-height velocity
equations force strictly positive horizontal corner velocity. The unit
circle identity then puts both source velocities strictly between minus
one and one, so both curvature densities are strictly below one. A local
null-set argument covers the entire regular quarter-turn domain; no
assumption about the number of floor-contact components is used.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

/-- The two zero vertical derivatives, combined with the actual source
density bounds, imply positive horizontal speed and strict unit density. -/
theorem floor_contact_curvature_control {s k q r u v : ℝ}
    (hs : 0 < s) (hk : 0 < k) (hcircle : s ^ 2 + k ^ 2 = 1)
    (hu0 : 0 ≤ u) (hv0 : 0 ≤ v) (hu : u ≤ sourceKappa q) (hv : v ≤ sourceKappa r)
    (hy : -r * s + q * k = 0)
    (hacc : u * s + v * k - s - k + 2 * (-r * k - q * s) = 0) :
    0 < -r * k - q * s ∧ u < 1 ∧ v < 1 := by
  obtain ⟨z, hz⟩ : ∃ z, -r * k - q * s = z := ⟨_, rfl⟩
  have hq : |q| = |z| * s := by
    rw [show q = -(z * s) by linear_combination k * hy - q * hcircle - s * hz, abs_neg, abs_mul,
      abs_of_pos hs]
  have hr : |r| = |z| * k := by
    rw [show r = -(z * k) by linear_combination -s * hy - r * hcircle - k * hz, abs_neg, abs_mul,
      abs_of_pos hk]
  have hκ (p : ℝ) : sourceKappa p ≤ |p| + 1 / 2 :=
    max_le (by linarith [abs_nonneg p]) (by linarith [abs_nonneg p])
  have hus := mul_le_mul_of_nonneg_right (hq ▸ hu.trans (hκ q)) hs.le
  have hvk := mul_le_mul_of_nonneg_right (hr ▸ hv.trans (hκ r)) hk.le
  rw [hz] at hacc ⊢
  have hz0 : 0 < z := lt_of_not_ge fun h => by
    rw [abs_of_nonpos h] at hus hvk
    linarith [congrArg (z * ·) hcircle]
  have hs1 : s < 1 := by nlinarith only [hcircle, hs, sq_pos_of_pos hk]
  have hk1 : k ≤ 1 := by nlinarith only [hcircle, hk, sq_nonneg s]
  have hz1 : z < 1 := by linarith [mul_nonneg hu0 hs.le, mul_nonneg hv0 hk.le]
  have hq1 : |q| < 1 := by rw [hq, abs_of_pos hz0]; exact (mul_lt_of_lt_one_right hz0 hs1).trans hz1
  have hr1 : |r| < 1 := by
    rw [hr, abs_of_pos hz0]; exact (mul_le_of_le_one_right hz0.le hk1).trans_lt hz1
  exact ⟨hz0, hu.trans_lt (max_lt hq1 (by linarith)), hv.trans_lt (max_lt hr1 (by linarith))⟩

theorem IsDownwardCap.ae_floor_curvature_lt_one_on_interval
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {C a b : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (hκ : ∀ t, ρ t ≤ sourceKappa (upperCornerVelocity U t))
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hab : a ≤ b) (hquarter : Icc a b ⊆ Ioo (0 : ℝ) (Real.pi / 2))
    (hbase : Icc a b ⊆ S) (hshift : Icc (a + Real.pi / 2) (b + Real.pi / 2) ⊆ S) :
    ∀ᵐ x ∂volume.restrict (Ioo a b), (attachedCorner U x).2 = 0 →
      0 < cornerVelocityX U x ∧ ρ x < 1 ∧ ρ (x + Real.pi / 2) < 1 := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    hU.ae_corner_floor_flatness_of_density hρ hρ0 hρC heq hab hbase hshift]
    with x hx hflat hfloor
  obtain ⟨hx0, hx1⟩ := hquarter (Ioo_subset_Icc_self hx)
  have hfirst : ρ x ≤ sourceKappa (firstCornerVelocity U x) := by
    simpa [upperCornerVelocity, hx1] using hκ x
  have hsecond : ρ (x + Real.pi / 2) ≤ sourceKappa (secondCornerVelocity U x) := by
    simpa [upperCornerVelocity, hx0.not_gt] using hκ (x + Real.pi / 2)
  exact floor_contact_curvature_control (Real.sin_pos_of_pos_of_lt_pi hx0 (by linarith))
    (Real.cos_pos_of_mem_Ioo ⟨by linarith, hx1⟩) (Real.sin_sq_add_cos_sq x)
    (hρ0 x) (hρ0 _) hfirst hsecond (hflat hfloor).1 (hflat hfloor).2

/-- Both support directions avoid the actual exceptional upper normals. -/
def regularCornerDomain (m : ℝ) : Set ℝ :=
  Ioo (0 : ℝ) (Real.pi / 2) ∩ (regularCurvatureDomain m ∩
    (fun t : ℝ => t + Real.pi / 2) ⁻¹' regularCurvatureDomain m)

theorem isOpen_regularCornerDomain (m : ℝ) : IsOpen (regularCornerDomain m) :=
  have hreg := isOpen_regularCurvatureDomain m
  isOpen_Ioo.inter (hreg.inter (hreg.preimage (continuous_id.add_const _)))

/-- Local density/ODE control applies throughout the actual regular
domain, with arbitrary floor-contact sets and no component enumeration. -/
theorem IsDownwardCap.ae_floor_curvature_lt_one_of_density
    {U : Set Plane} (hU : IsDownwardCap U) {ρ : ℝ → ℝ} {C m : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (hκ : ∀ t, ρ t ≤ sourceKappa (upperCornerVelocity U t))
    (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
      (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t))) :
    ∀ᵐ x ∂volume.restrict (regularCornerDomain m), (attachedCorner U x).2 = 0 →
      0 < cornerVelocityX U x ∧ ρ x < 1 ∧ ρ (x + Real.pi / 2) < 1 := by
  set P : ℝ → Prop := fun x => (attachedCorner U x).2 = 0 →
    0 < cornerVelocityX U x ∧ ρ x < 1 ∧ ρ (x + Real.pi / 2) < 1
  -- The failure set is null near each of its points, hence null.
  have hzero : volume {x ∈ regularCornerDomain m | ¬ P x} = 0 := by
    refine measure_null_of_locally_null _ fun x hx => ?_
    obtain ⟨l, r, ⟨hl, hr⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
      ((isOpen_regularCornerDomain m).mem_nhds hx.1)
    have hclosed : Icc ((l + x) / 2) ((x + r) / 2) ⊆ regularCornerDomain m := fun t ht =>
      hsub ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hlocal := (ae_restrict_iff' measurableSet_Ioo).mp
      (hU.ae_floor_curvature_lt_one_on_interval hρ hρ0 hρC hκ heq (by linarith)
        (fun t ht => (hclosed ht).1) (fun t ht => (hclosed ht).2.1) fun t ht => by
          simpa using (hclosed (show t - Real.pi / 2 ∈ Icc _ _ from
            ⟨by linarith [ht.1], by linarith [ht.2]⟩)).2.2)
    refine ⟨Ioo ((l + x) / 2) ((x + r) / 2) ∩ {x ∈ regularCornerDomain m | ¬ P x},
      inter_mem (nhdsWithin_le_nhds (Ioo_mem_nhds (by linarith) (by linarith)))
        self_mem_nhdsWithin, measure_mono_null ?_ (ae_iff.mp hlocal)⟩
    exact fun t ht hp => ht.2.2 (hp ht.1)
  refine (ae_restrict_iff' (isOpen_regularCornerDomain m).measurableSet).mpr ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hzero] with x hx hxreg
  exact not_not.mp fun hfail => hx ⟨hxreg, hfail⟩

/-- An actual full maximizer supplies its own curvature density and its
own strict floor-contact control. No sharpness or unit-curvature field
is assumed in this statement. -/
theorem IsFullCapMaximizer.curvature_density_floor_control
    {U : Set Plane} (hU : IsFullCapMaximizer U) {m c : ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧
      (∀ t, 0 ≤ ρ t ∧ ρ t ≤ sourceKappa (upperCornerVelocity U t)) ∧
      (∀ t, ρ t ≤ 4 * (|horizontalLeft U| + |horizontalRight U| + 1) + 10) ∧
      (upperCurvature U).restrict (regularCurvatureDomain m) =
        (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)) ∧
      (∀ᵐ x ∂volume.restrict (regularCornerDomain m), (attachedCorner U x).2 = 0 →
        0 < cornerVelocityX U x ∧ ρ x < 1 ∧ ρ (x + Real.pi / 2) < 1) := by
  obtain ⟨ρ, hρ, hbounds, hbound, heq⟩ := hU.curvature_density_on_regular_domain haffine
  exact ⟨ρ, hρ, hbounds, hbound, heq,
    hU.isCap.ae_floor_curvature_lt_one_of_density hρ (fun t => (hbounds t).1) hbound
      (fun t => (hbounds t).2) heq⟩

theorem regularCornerDomain_zero : regularCornerDomain 0 = Ioo (0 : ℝ) (Real.pi / 2) := by
  refine Subset.antisymm (fun t ht => ht.1) fun t ht => ⟨ht, ?_, ?_⟩ <;>
    simp only [mem_preimage, mem_regularCurvatureDomain_iff, zero_mul, add_zero,
      Real.cos_add_pi_div_two, neg_ne_zero]
  · exact ⟨ht.1, by linarith [ht.1, ht.2], ht.2.ne,
      (Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, ht.2], ht.2⟩).ne'⟩
  · exact ⟨by linarith [ht.1, ht.2], by linarith [ht.2], by linarith [ht.1],
      (Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.1, ht.2])).ne'⟩

end AmbidextrousSofa
