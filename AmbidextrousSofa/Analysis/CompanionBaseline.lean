module

public import AmbidextrousSofa.Analysis.FirstUnitNiche

@[expose] public section

/-!
# Earlier companion walls while the tangent stays below the floor

The baseline abscissa is the zero of a companion wall. Its derivative
has the sign of the companion tangent height. Thus an initially
nonpositive tangent height makes the baseline antitone, even when the
companion curvature exceeds one. Every positive point on a later wall
then lies strictly above all earlier walls.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

def companionBaseline (g : ℝ → ℝ) (t : ℝ) : ℝ := (1 - g t) / Real.sin t

/-- This strict comparison uses no bound on the companion density. A
zero or a plateau of its tangent height is also allowed. -/
theorem companion_wall_lt_later_of_initial_tangent_nonpos
    {g gD : ℝ → ℝ} {x r t : ℝ}
    (ht : t ∈ Ioo 0 (Real.pi / 2)) (hr : r ∈ Ioo 0 t)
    (hg : ∀ s ∈ Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt g (gD s) s)
    (hfloor : ∀ s ∈ Ioc (0 : ℝ) t, (secondTangentPoint g gD s).2 ≤ 0)
    (hy : 0 < (g t - 1 + x * Real.sin t) / Real.cos t) :
    (g r - 1 + x * Real.sin r) / Real.cos r <
      (g t - 1 + x * Real.sin t) / Real.cos t := by
  have hsin {s : ℝ} (h0 : 0 < s) (h1 : s ≤ t) : Real.sin s ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [ht.2, Real.pi_pos])).ne'
  -- Each wall is `tan s * (x - companionBaseline g s)`.
  have hwall {s : ℝ} (h0 : 0 < s) (h1 : s ≤ t) : (g s - 1 + x * Real.sin s) / Real.cos s =
      Real.tan s * (x - companionBaseline g s) := by
    have hc := (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1.trans_lt ht.2⟩).ne'
    rw [Real.tan_eq_sin_div_cos, companionBaseline]
    field_simp [hsin h0 h1, hc]
    ring
  -- The baseline is antitone: its derivative has the sign of the companion tangent height.
  have hbase : companionBaseline g t ≤ companionBaseline g r := by
    refine endpoint_le_of_hasDerivAt_nonpos hr.2.le (fun s hs =>
      ((hg s ⟨hr.1.trans_le hs.1, hs.2.trans_lt ht.2⟩).const_sub 1).div
        (Real.hasDerivAt_sin s) (hsin (hr.1.trans_le hs.1) hs.2))
      fun s hs => div_nonpos_of_nonpos_of_nonneg ?_ (sq_nonneg _)
    have h := hfloor s ⟨hr.1.trans hs.1, hs.2.le⟩
    simp only [secondTangentPoint, companionSupportPoint_coordinates] at h
    linarith
  rw [hwall ht.1 le_rfl] at hy ⊢
  rw [hwall hr.1 hr.2.le]
  have htt := Real.tan_pos_of_pos_of_lt_pi_div_two ht.1 ht.2
  linear_combination mul_nonneg (Real.tan_nonneg_of_nonneg_of_le_pi_div_two hr.1.le
      (hr.2.trans ht.2).le) (sub_nonneg.2 hbase) +
    mul_pos (sub_pos.2 (Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two hr.1.le ht.2 hr.2))
      ((mul_pos_iff_of_pos_left htt).mp hy)

end AmbidextrousSofa
