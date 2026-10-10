import AmbidextrousSofa.Analysis.DiagonalTent
import AmbidextrousSofa.Analysis.LowHeightAlgebra
import AmbidextrousSofa.Analysis.Chord
import AmbidextrousSofa.Analysis.FiniteScore
import AmbidextrousSofa.Measure.GraphIntegral

/-!
# Actual roofs below the low-middle-height ceiling

The projection is centered as [-2C,2C]. An affine middle roof joining a
value at most one half to height one lies below the displayed affine
ceiling through the first three quarters. Concavity extends that bound
to the charged left wing. The diagonal support excesses are then bounded
using actual points and the actual support maximum.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

def lowCeiling (C x : ℝ) : ℝ := 3 / 4 + x / (4 * C)

theorem continuous_lowCeiling (C : ℝ) : Continuous (lowCeiling C) := by
  unfold lowCeiling
  fun_prop

theorem eqOn_roofChord_of_affine {f : ℝ → ℝ} {a b m c : ℝ} (hab : a < b)
    (hf : ∀ x ∈ Icc a b, f x = m * x + c) : EqOn f (roofChord f a b) (Icc a b) := by
  intro x hx
  rw [roofChord, hf a ⟨le_rfl, hab.le⟩, hf b ⟨hab.le, le_rfl⟩, hf x hx]
  field_simp [(sub_pos.mpr hab).ne']
  ring

theorem IsDownwardCap.capRoof_le_lowCeiling_of_affine_middle
    {U : Set Plane} (hU : IsDownwardCap U) {C : ℝ} (hC : 0 < C)
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C)
    (hlow : capRoof U (-C) ≤ 1 / 2) (hhigh : capRoof U C = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c) :
    ∀ x ∈ Icc (-2 * C) C, capRoof U x ≤ lowCeiling C x := by
  obtain ⟨m, c, haffine⟩ := haffine
  have hproj : horizontalProjection U = Icc (-2 * C) (2 * C) := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hleft, hright]
  have hneg : -C < C := by linarith
  have hcentral := eqOn_roofChord_of_affine hneg haffine
  intro x hx
  have hxU : x ∈ horizontalProjection U := by
    rw [hproj]
    exact ⟨hx.1, by linarith [hx.2]⟩
  have hCmem : C ∈ horizontalProjection U := by rw [hproj]; constructor <;> linarith
  have hchord : capRoof U x ≤ roofChord (capRoof U) (-C) C x := by
    by_cases hxc : x ≤ -C
    · exact hU.concaveOn_capRoof.le_roofChord_of_le hxU hCmem hneg hxc
    · exact (hcentral ⟨le_of_not_ge hxc, hx.2⟩).le
  let t : ℝ := (x + C) / (2 * C)
  have ht : t ≤ 1 := by
    dsimp [t]
    apply (div_le_iff₀ (by positivity : 0 < 2 * C)).mpr
    linarith [hx.2]
  have hproduct := mul_nonneg (sub_nonneg.mpr hlow) (sub_nonneg.mpr ht)
  have hchord_eq : roofChord (capRoof U) (-C) C x =
      capRoof U (-C) + (1 - capRoof U (-C)) * t := by
    unfold roofChord
    rw [hhigh]
    dsimp [t]
    simp only [sub_neg_eq_add]
    rw [show C + C = 2 * C by ring]
    ring
  have hceiling : lowCeiling C x = 1 / 2 + t / 2 := by
    unfold lowCeiling
    dsimp [t]
    field_simp [hC.ne']
    ring
  rw [hchord_eq] at hchord
  rw [hceiling]
  nlinarith

theorem integral_lowCeiling_left {C : ℝ} (hC : 0 < C) :
    (∫ x in (-2 * C)..(-C), lowCeiling C x) = 3 * C / 8 := by
  unfold lowCeiling
  rw [intervalIntegral.integral_add (continuous_const.intervalIntegrable _ _)
    ((continuous_id.div_const (4 * C)).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_div_const, integral_id]
  simp only [smul_eq_mul]
  field_simp [hC.ne']
  ring

theorem lowCeiling_eq_quarter_add {C : ℝ} (hC : C ≠ 0) (x : ℝ) :
    lowCeiling C x = 1 / 4 + (x + 2 * C) / (4 * C) := by
  unfold lowCeiling
  field_simp [hC]
  ring

/-- The excesses are defined from the true diagonal supports, rather than
introduced as independent relaxed support parameters. -/
theorem IsDownwardCap.lowHeight_diagonal_excess_bounds
    {U : Set Plane} (hU : IsDownwardCap U) {C : ℝ} (hC : 1 / 2 ≤ C)
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C)
    (hhigh : capRoof U C = 1)
    (hceiling : ∀ x ∈ Icc (-2 * C) C, capRoof U x ≤ lowCeiling C x) :
    0 ≤ diagonalRight U - 2 * C ∧ 1 - C ≤ diagonalRight U - 2 * C ∧
      diagonalRight U - 2 * C ≤ 1 ∧
      0 ≤ diagonalLeft U - 2 * C ∧ diagonalLeft U - 2 * C ≤ 1 / 4 := by
  have hCpos : 0 < C := by linarith
  have hproj : horizontalProjection U = Icc (-2 * C) (2 * C) := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hleft, hright]
  have hr := hU.diagonalRight_ge hU.right_baseline_mem
  have hl := hU.diagonalLeft_ge hU.left_baseline_mem
  rw [hright] at hr
  rw [hleft] at hl
  have hCmem : C ∈ horizontalProjection U := by rw [hproj]; constructor <;> linarith
  have hhighmem : (C, 1) ∈ U := by simpa only [hhigh] using capRoof_mem hU.isCompact hCmem
  have hhighSupport := hU.diagonalRight_ge hhighmem
  have hrUpper := hU.diagonalRight_le
  rw [hright] at hrUpper
  have hlUpper : diagonalLeft U ≤ 2 * C + 1 / 4 := by
    apply support_le_of_forall hU.nonempty
    intro p hp
    have hx : p.1 ∈ Icc (-2 * C) (2 * C) := by
      rw [← hproj]
      exact ⟨p, hp, rfl⟩
    have hy := le_capRoof hU.isCompact (show (p.1, p.2) ∈ U by simpa only [Prod.mk.eta] using hp)
    simp only [coordDot, mul_neg_one, mul_one]
    by_cases hxc : p.1 ≤ C
    · have hroof := hceiling p.1 ⟨hx.1, hxc⟩
      rw [lowCeiling_eq_quarter_add hCpos.ne'] at hroof
      have hdiv : (p.1 + 2 * C) / (4 * C) ≤ p.1 + 2 * C :=
        div_le_self (by linarith [hx.1]) (by linarith)
      linarith
    · have hstrip := (hU.inStrip hp).2
      linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- The unrefined two-wing reward bound used at small and large widths. -/
theorem IsDownwardCap.lowHeight_reward_le
    {U : Set Plane} (hU : IsDownwardCap U) {C : ℝ} (hC : 0 < C)
    (hceiling : ∀ x ∈ Icc (-2 * C) C, capRoof U x ≤ lowCeiling C x) :
    (∫ x in (-2 * C)..(-C), capRoof U x) +
      (∫ x in C..(2 * C), capRoof U x) ≤ 11 * C / 8 := by
  have hleft : (∫ x in (-2 * C)..(-C), capRoof U x) ≤ 3 * C / 8 := by
    rw [← integral_lowCeiling_left hC]
    apply intervalIntegral.integral_mono_on (by linarith)
      (hU.intervalIntegrable_capRoof _ _) ((continuous_lowCeiling C).intervalIntegrable _ _)
    intro x hx
    exact hceiling x ⟨hx.1, by linarith [hx.2]⟩
  have hright : (∫ x in C..(2 * C), capRoof U x) ≤ C := by
    have h := intervalIntegral.integral_mono_on (by linarith : C ≤ 2 * C)
      (hU.intervalIntegrable_capRoof C (2 * C)) (continuous_const.intervalIntegrable _ _)
      (fun x _ => capRoof_le_one hU.isCompact hU.inStrip x)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_one,
      show 2 * C - C = C by ring] using h
  linarith

end AmbidextrousSofa
