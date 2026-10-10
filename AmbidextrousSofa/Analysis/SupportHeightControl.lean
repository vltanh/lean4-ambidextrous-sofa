module

public import AmbidextrousSofa.Analysis.Extrusion
public import AmbidextrousSofa.Analysis.CapCompactness

@[expose] public section

/-!
# Support control at the horizontal top direction

In a fixed unit-height box, the support's difference from the actual cap
height vanishes at least linearly with the horizontal normal component.
This controls the Green weight near the top direction. The residual height
deficit tends to zero under actual Hausdorff convergence to a height-one cap.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace AmbidextrousSofa

theorem IsDownwardCap.abs_support_sub_height_le_box {U : Set Plane}
    (hU : IsDownwardCap U) {R : ℝ}
    (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    {v : Plane} (hv : coordDot v v = 1) (hvy : 0 ≤ v.2) :
    |support U v - capHeight U| ≤ (R + 1) * |v.1| := by
  have hvunit : v.1 ^ 2 + v.2 ^ 2 = 1 := by simpa only [coordDot, pow_two] using hv
  have hvy1 : v.2 ≤ 1 := by nlinarith [sq_nonneg v.1]
  have hgap : 1 - v.2 ≤ |v.1| := by
    apply (sq_le_sq₀ (sub_nonneg.mpr hvy1) (abs_nonneg v.1)).mp
    rw [sq_abs]
    nlinarith [mul_nonneg hvy (sub_nonneg.mpr hvy1)]
  have hpoint (p : Plane) (hp : p ∈ U) :
      |coordDot p v - p.2| ≤ (R + 1) * |v.1| := by
    have hx : |p.1| ≤ R := abs_le.mpr (hbox hp).1
    have hy0 := (hbox hp).2.1
    have hy1 := (hbox hp).2.2
    have hxm := mul_le_mul_of_nonneg_right hx (abs_nonneg v.1)
    have hym : p.2 * (1 - v.2) ≤ 1 - v.2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hy1) (sub_nonneg.mpr hvy1)]
    calc
      |coordDot p v - p.2| = |p.1 * v.1 + p.2 * (v.2 - 1)| := by
        congr 1
        unfold coordDot
        ring
      _ ≤ |p.1 * v.1| + |p.2 * (v.2 - 1)| := abs_add_le _ _
      _ = |p.1| * |v.1| + p.2 * (1 - v.2) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hy0, abs_of_nonpos (sub_nonpos.mpr hvy1)]
        ring
      _ ≤ (R + 1) * |v.1| := by nlinarith
  obtain ⟨p, hp, hpv⟩ := exists_coordDot_eq_support hU.isCompact hU.nonempty v
  obtain ⟨q, hq, hqH⟩ := exists_coordDot_eq_support hU.isCompact hU.nonempty (0, 1)
  have hpH := hU.snd_le_capHeight hp
  have hqv := coordDot_le_support hU.isCompact hq v
  have hqheight : q.2 = capHeight U := by
    simpa only [coordDot, capHeight, mul_zero, mul_one, zero_add] using hqH
  have hpbound := hpoint p hp
  have hqbound := hpoint q hq
  rw [hpv] at hpbound
  rw [hqheight] at hqbound
  apply abs_le.mpr
  constructor
  · linarith [(abs_le.mp hqbound).1]
  · linarith [(abs_le.mp hpbound).2]

theorem IsDownwardCap.abs_support_sub_one_le_box {U : Set Plane}
    (hU : IsDownwardCap U) {R : ℝ}
    (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    {v : Plane} (hv : coordDot v v = 1) (hvy : 0 ≤ v.2) :
    |support U v - 1| ≤ (R + 1) * |v.1| + (1 - capHeight U) := by
  calc
    |support U v - 1| ≤ |support U v - capHeight U| + |capHeight U - 1| :=
      abs_sub_le _ _ _
    _ ≤ (R + 1) * |v.1| + (1 - capHeight U) := by
      rw [abs_of_nonpos (sub_nonpos.mpr hU.capHeight_le_one)]
      have h := hU.abs_support_sub_height_le_box hbox hv hvy
      linarith

theorem CapHausdorffTendsto.capHeight_tendsto
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K) :
    Tendsto (fun n => capHeight (U n)) atTop (𝓝 (capHeight K)) :=
  h.support_tendsto (fun n => (hU n).isCompact) (fun n => (hU n).nonempty)
    hK.isCompact hK.nonempty (0, 1)

end AmbidextrousSofa
