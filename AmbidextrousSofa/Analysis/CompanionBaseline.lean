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

theorem hasDerivAt_companionBaseline {g gD : ℝ → ℝ} {t : ℝ}
    (hg : HasDerivAt g (gD t) t) (hs : Real.sin t ≠ 0) :
    HasDerivAt (companionBaseline g)
      ((secondTangentPoint g gD t).2 / Real.sin t ^ 2) t := by
  have hd := (hg.const_sub 1).div (Real.hasDerivAt_sin t) hs
  apply hd.congr_deriv
  rw [secondTangentPoint, companionSupportPoint_coordinates]
  dsimp only [Prod.snd]
  ring

theorem companionBaseline_antitone_of_initial_tangent_nonpos
    {g gD : ℝ → ℝ} {b : ℝ} (hb : b ∈ Ioo 0 (Real.pi / 2))
    (hg : ∀ t ∈ Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt g (gD t) t)
    (hfloor : ∀ t ∈ Ioc (0 : ℝ) b, (secondTangentPoint g gD t).2 ≤ 0) :
    AntitoneOn (companionBaseline g) (Ioc 0 b) := by
  intro r hr s hs hrs
  apply endpoint_le_of_hasDerivAt_nonpos hrs
    (fun t ht => hasDerivAt_companionBaseline
      (hg t ⟨hr.1.trans_le ht.1, (ht.2.trans hs.2).trans_lt hb.2⟩)
      (Real.sin_pos_of_pos_of_lt_pi (hr.1.trans_le ht.1)
        (by linarith only [ht.2, hs.2, hb.2, Real.pi_pos])).ne')
  intro t ht
  exact div_nonpos_of_nonpos_of_nonneg
    (hfloor t ⟨hr.1.trans ht.1, ht.2.le.trans hs.2⟩) (sq_nonneg _)

theorem companion_wall_eq_tan_baseline (g : ℝ → ℝ) {x t : ℝ}
    (hs : Real.sin t ≠ 0) (hc : Real.cos t ≠ 0) :
    (g t - 1 + x * Real.sin t) / Real.cos t =
      Real.tan t * (x - companionBaseline g t) := by
  rw [Real.tan_eq_sin_div_cos, companionBaseline]
  field_simp [hs, hc]
  ring

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
  have hsr : 0 < Real.sin r := Real.sin_pos_of_pos_of_lt_pi hr.1
    (by linarith only [hr.2, ht.2, Real.pi_pos])
  have hst : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith only [ht.2, Real.pi_pos])
  have hcr : 0 < Real.cos r := Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [hr.1, Real.pi_pos], hr.2.trans ht.2⟩
  have hct : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩
  have htr : 0 ≤ Real.tan r := by rw [Real.tan_eq_sin_div_cos]; positivity
  have htt : 0 < Real.tan t := by rw [Real.tan_eq_sin_div_cos]; positivity
  have htan : Real.tan r < Real.tan t :=
    Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two hr.1.le ht.2 hr.2
  have hbase := companionBaseline_antitone_of_initial_tangent_nonpos ht hg hfloor
    ⟨hr.1, hr.2.le⟩ ⟨ht.1, le_rfl⟩ hr.2.le
  rw [companion_wall_eq_tan_baseline g hst.ne' hct.ne'] at hy ⊢
  rw [companion_wall_eq_tan_baseline g hsr.ne' hcr.ne']
  have hbracket : 0 < x - companionBaseline g t := (mul_pos_iff_of_pos_left htt).mp hy
  calc
    Real.tan r * (x - companionBaseline g r) ≤
        Real.tan r * (x - companionBaseline g t) :=
      mul_le_mul_of_nonneg_left (by linarith only [hbase]) htr
    _ < Real.tan t * (x - companionBaseline g t) :=
      mul_lt_mul_of_pos_right htan hbracket

end AmbidextrousSofa
