import AmbidextrousSofa.Analysis.CornerDynamics

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

theorem sourceKappa_le_abs_add_half (q : ℝ) : sourceKappa q ≤ |q| + 1 / 2 := by
  unfold sourceKappa
  apply max_le <;> linarith [abs_nonneg q]

theorem sourceKappa_lt_one_iff (q : ℝ) : sourceKappa q < 1 ↔ |q| < 1 := by
  unfold sourceKappa
  rw [max_lt_iff]
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, by linarith⟩

/-- The two zero vertical derivatives, combined with the actual source
density bounds, imply positive horizontal speed and strict unit density. -/
theorem floor_contact_curvature_control {s k q r u v : ℝ}
    (hs : 0 < s) (hk : 0 < k) (hcircle : s ^ 2 + k ^ 2 = 1)
    (hu0 : 0 ≤ u) (hv0 : 0 ≤ v) (hu : u ≤ sourceKappa q) (hv : v ≤ sourceKappa r)
    (hy : -r * s + q * k = 0)
    (hacc : u * s + v * k - s - k + 2 * (-r * k - q * s) = 0) :
    0 < -r * k - q * s ∧ u < 1 ∧ v < 1 := by
  let z := -r * k - q * s
  have hq : q = -(z * s) := by
    dsimp [z]
    nlinarith [congrArg (fun w : ℝ => q * w) hcircle,
      congrArg (fun w : ℝ => w * k) hy]
  have hr : r = -(z * k) := by
    dsimp [z]
    nlinarith [congrArg (fun w : ℝ => r * w) hcircle,
      congrArg (fun w : ℝ => w * s) hy]
  have hqabs : |q| = |z| * s := by rw [hq, abs_neg, abs_mul, abs_of_pos hs]
  have hrabs : |r| = |z| * k := by rw [hr, abs_neg, abs_mul, abs_of_pos hk]
  have hu' : u ≤ |z| * s + 1 / 2 := by
    simpa only [hqabs] using hu.trans (sourceKappa_le_abs_add_half q)
  have hv' : v ≤ |z| * k + 1 / 2 := by
    simpa only [hrabs] using hv.trans (sourceKappa_le_abs_add_half r)
  have hweighted : u * s + v * k ≤ |z| + (s + k) / 2 := by
    have hsu := mul_le_mul_of_nonneg_right hu' hs.le
    have hkv := mul_le_mul_of_nonneg_right hv' hk.le
    have hsq := congrArg (fun w : ℝ => |z| * w) hcircle
    nlinarith
  have hbalance : u * s + v * k = s + k - 2 * z := by
    dsimp [z]
    linarith
  have hz0 : 0 < z := by
    by_contra hz
    have hz' : z ≤ 0 := le_of_not_gt hz
    rw [abs_of_nonpos hz'] at hweighted
    linarith
  have hsum0 : 0 ≤ u * s + v * k :=
    add_nonneg (mul_nonneg hu0 hs.le) (mul_nonneg hv0 hk.le)
  have hzsum : z ≤ (s + k) / 2 := by linarith
  have hs1 : s < 1 := by nlinarith [sq_pos_of_pos hk]
  have hk1 : k ≤ 1 := by nlinarith [sq_nonneg s]
  have hsum : s + k < 2 := by linarith
  have hz1 : z < 1 := by linarith
  have hq1 : |q| < 1 := by
    rw [hqabs, abs_of_pos hz0]
    have hle : z * s ≤ z := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hs1.le hz0.le
    exact hle.trans_lt hz1
  have hr1 : |r| < 1 := by
    rw [hrabs, abs_of_pos hz0]
    have hle : z * k ≤ z := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hk1 hz0.le
    exact hle.trans_lt hz1
  exact ⟨hz0, hu.trans_lt ((sourceKappa_lt_one_iff q).mpr hq1),
    hv.trans_lt ((sourceKappa_lt_one_iff r).mpr hr1)⟩

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
    with x hx hflat
  intro hfloor
  have hxq := hquarter (Ioo_subset_Icc_self hx)
  have hs := Real.sin_pos_of_pos_of_lt_pi hxq.1 (by linarith [hxq.2, Real.pi_pos])
  have hk := Real.cos_pos_of_mem_Ioo ⟨by linarith [hxq.1, Real.pi_pos], hxq.2⟩
  have hfirst : ρ x ≤ sourceKappa (firstCornerVelocity U x) := by
    simpa only [upperCornerVelocity, if_pos hxq.2] using hκ x
  have hnot : ¬ x + Real.pi / 2 < Real.pi / 2 := by linarith [hxq.1]
  have hsecond : ρ (x + Real.pi / 2) ≤ sourceKappa (secondCornerVelocity U x) := by
    simpa only [upperCornerVelocity, if_neg hnot, add_sub_cancel_right] using
      hκ (x + Real.pi / 2)
  exact floor_contact_curvature_control hs hk (Real.sin_sq_add_cos_sq x)
    (hρ0 x) (hρ0 (x + Real.pi / 2)) hfirst hsecond (hflat hfloor).1 (hflat hfloor).2

/-- Both support directions avoid the actual exceptional upper normals. -/
def regularCornerDomain (m : ℝ) : Set ℝ :=
  Ioo (0 : ℝ) (Real.pi / 2) ∩ (regularCurvatureDomain m ∩
    (fun t : ℝ => t + Real.pi / 2) ⁻¹' regularCurvatureDomain m)

theorem isOpen_regularCornerDomain (m : ℝ) : IsOpen (regularCornerDomain m) := by
  have hreg : IsOpen (regularCurvatureDomain m) := by
    rw [regularCurvatureDomain_eq_three]
    exact (isOpen_Ioo.union isOpen_Ioo).union isOpen_Ioo
  exact isOpen_Ioo.inter (hreg.inter (hreg.preimage (continuous_id.add_const (Real.pi / 2))))

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
  let P : ℝ → Prop := fun x => (attachedCorner U x).2 = 0 →
    0 < cornerVelocityX U x ∧ ρ x < 1 ∧ ρ (x + Real.pi / 2) < 1
  let B : Set ℝ := {x ∈ regularCornerDomain m | ¬ P x}
  have hzero : volume B = 0 := by
    apply measure_null_of_locally_null B
    intro x hx
    obtain ⟨l, r, ⟨hl, hr⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
      ((isOpen_regularCornerDomain m).mem_nhds hx.1)
    let a := (l + x) / 2
    let b := (x + r) / 2
    have hax : a < x := by dsimp [a]; linarith
    have hxb : x < b := by dsimp [b]; linarith
    have hab : a ≤ b := (hax.trans hxb).le
    have hclosed : Icc a b ⊆ regularCornerDomain m := by
      intro t ht
      apply hsub
      constructor <;> dsimp [a, b] at ht <;> linarith [ht.1, ht.2]
    have hbase : Icc a b ⊆ regularCurvatureDomain m := fun t ht => (hclosed ht).2.1
    have hshift : Icc (a + Real.pi / 2) (b + Real.pi / 2) ⊆ regularCurvatureDomain m := by
      intro t ht
      have ht' : t - Real.pi / 2 ∈ Icc a b := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      simpa only [sub_add_cancel] using (hclosed ht').2.2
    have hlocal : ∀ᵐ t ∂volume.restrict (Ioo a b), P t :=
      hU.ae_floor_curvature_lt_one_on_interval hρ hρ0 hρC hκ heq hab
        (fun t ht => (hclosed ht).1) hbase hshift
    have hlocal' : ∀ᵐ t : ℝ ∂volume, t ∈ Ioo a b → P t :=
      (ae_restrict_iff' measurableSet_Ioo).mp hlocal
    have hlocalNull : volume {t : ℝ | ¬ (t ∈ Ioo a b → P t)} = 0 := ae_iff.mp hlocal'
    refine ⟨Ioo a b ∩ B, inter_mem
      (nhdsWithin_le_nhds (Ioo_mem_nhds hax hxb)) self_mem_nhdsWithin, ?_⟩
    apply measure_mono_null _ hlocalNull
    intro t ht hp
    exact ht.2.2 (hp ht.1)
  have hnot : ∀ᵐ x : ℝ ∂volume, x ∉ B := measure_eq_zero_iff_ae_notMem.mp hzero
  apply (ae_restrict_iff' (isOpen_regularCornerDomain m).measurableSet).mpr
  filter_upwards [hnot] with x hx hxreg
  by_contra hfail
  exact hx ⟨hxreg, hfail⟩

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
  ext t
  constructor
  · exact fun ht => ht.1
  · intro ht
    refine ⟨ht, ?_, ?_⟩
    · apply mem_regularCurvatureDomain_iff.mpr
      refine ⟨ht.1, by linarith [ht.2, Real.pi_pos], ht.2.ne, ?_⟩
      simpa only [zero_mul, add_zero] using
        (Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩).ne'
    · apply mem_regularCurvatureDomain_iff.mpr
      refine ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2],
        by linarith [ht.1], ?_⟩
      have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])
      simpa only [zero_mul, add_zero, Real.cos_add_pi_div_two, neg_ne_zero] using hs.ne'

/-- In the horizontal-middle case no interior quarter-turn angle is
exceptional, so the actual floor-contact estimate holds on the whole
open quarter. -/
theorem IsFullCapMaximizer.horizontal_curvature_density_floor_control
    {U : Set Plane} (hU : IsFullCapMaximizer U) {c : ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = c) :
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧
      (∀ t, 0 ≤ ρ t ∧ ρ t ≤ sourceKappa (upperCornerVelocity U t)) ∧
      (∀ t, ρ t ≤ 4 * (|horizontalLeft U| + |horizontalRight U| + 1) + 10) ∧
      (upperCurvature U).restrict (regularCurvatureDomain 0) =
        (volume.restrict (regularCurvatureDomain 0)).withDensity (fun t => ENNReal.ofReal (ρ t)) ∧
      (∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), (attachedCorner U x).2 = 0 →
        0 < cornerVelocityX U x ∧ ρ x < 1 ∧ ρ (x + Real.pi / 2) < 1) := by
  have h := hU.curvature_density_floor_control
    (m := 0) (c := c) (by simpa only [zero_mul, zero_add] using haffine)
  simpa only [regularCornerDomain_zero] using h

end AmbidextrousSofa
