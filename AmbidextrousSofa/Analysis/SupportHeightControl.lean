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

theorem IsDownwardCap.abs_support_sub_one_le_box {U : Set Plane}
    (hU : IsDownwardCap U) {R : ℝ}
    (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    {v : Plane} (hv : coordDot v v = 1) (hvy : 0 ≤ v.2) :
    |support U v - 1| ≤ (R + 1) * |v.1| + (1 - capHeight U) := by
  simp only [coordDot] at hv
  have hgap : 1 - v.2 ≤ |v.1| := by nlinarith [abs_nonneg v.1, sq_abs v.1]
  have hx (p : Plane) (hp : p ∈ U) : |p.1 * v.1| ≤ R * |v.1| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right (abs_le.mpr (hbox hp).1) (abs_nonneg _)
  obtain ⟨p, hp, hpv⟩ := exists_coordDot_eq_support hU.isCompact hU.nonempty v
  obtain ⟨q, hq, hqH⟩ := exists_coordDot_eq_support hU.isCompact hU.nonempty (0, 1)
  have hqv := coordDot_le_support hU.isCompact hq v
  have hpH := hU.snd_le_capHeight hp
  have hH := hU.capHeight_le_one
  have hp2 := (hbox hp).2.1
  have hq2 := (hbox hq).2.2
  unfold capHeight at *
  simp only [coordDot, mul_zero, mul_one, zero_add] at hpv hqH hqv
  rw [abs_le]
  constructor <;> nlinarith [abs_le.mp (hx p hp), abs_le.mp (hx q hq)]

theorem CapHausdorffTendsto.capHeight_tendsto
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K) :
    Tendsto (fun n => capHeight (U n)) atTop (𝓝 (capHeight K)) :=
  h.support_tendsto (fun n => (hU n).isCompact) (fun n => (hU n).nonempty)
    hK.isCompact hK.nonempty (0, 1)

end AmbidextrousSofa
