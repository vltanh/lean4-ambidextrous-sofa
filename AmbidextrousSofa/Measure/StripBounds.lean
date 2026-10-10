module

public import AmbidextrousSofa.Measure.Fibers
public import AmbidextrousSofa.Geometry.Hallway

@[expose] public section

/-!
# Horizontal sections of strips and of the wrong-way hallway

These are direct area bounds for subsets of actual strips and hallways. At
the wrong-handed angle `-π/4`, every horizontal hallway section is an interval
of length `√2`, regardless of the two hallway offsets. The resulting area
obstruction uses only the incoming unit strip, not convexity or full height.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

def horizontalIntervalRegion (I : Set ℝ) (left right : ℝ → ℝ) : Set Plane :=
  {p | p.2 ∈ I ∧ p.1 ∈ Icc (left p.2) (right p.2)}

theorem measurableSet_horizontalIntervalRegion {I : Set ℝ} {left right : ℝ → ℝ}
    (hI : MeasurableSet I) (hleft : Measurable left) (hright : Measurable right) :
    MeasurableSet (horizontalIntervalRegion I left right) := by
  exact (hI.preimage measurable_snd).inter
    ((measurableSet_le (hleft.comp measurable_snd) measurable_fst).inter
      (measurableSet_le measurable_fst (hright.comp measurable_snd)))

theorem volume_horizontalIntervalRegion_eq_lintegral
    {I : Set ℝ} {left right : ℝ → ℝ}
    (hI : MeasurableSet I) (hleft : Measurable left) (hright : Measurable right) :
    volume (horizontalIntervalRegion I left right) =
      ∫⁻ y in I, ENNReal.ofReal (right y - left y) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm
    (measurableSet_horizontalIntervalRegion hI hleft hright)]
  calc
    (∫⁻ y, volume ((fun x : ℝ => (x, y)) ⁻¹'
        horizontalIntervalRegion I left right)) =
        ∫⁻ y, I.indicator (fun y => ENNReal.ofReal (right y - left y)) y := by
      apply lintegral_congr
      intro y
      by_cases hy : y ∈ I
      · have hsection : (fun x : ℝ => (x, y)) ⁻¹'
            horizontalIntervalRegion I left right = Icc (left y) (right y) := by
          ext x
          simp [horizontalIntervalRegion, hy]
        rw [hsection, Real.volume_Icc, indicator_of_mem hy]
      · have hsection : (fun x : ℝ => (x, y)) ⁻¹'
            horizontalIntervalRegion I left right = ∅ := by
          ext x
          simp [horizontalIntervalRegion, hy]
        rw [hsection, measure_empty, indicator_of_notMem hy]
    _ = ∫⁻ y in I, ENNReal.ofReal (right y - left y) := lintegral_indicator hI _

theorem volume_horizontalIntervalRegion_unit_of_constant_width
    {left right : ℝ → ℝ} {w : ℝ}
    (hleft : Measurable left) (hright : Measurable right)
    (hwidth : ∀ y, right y - left y = w) :
    volume (horizontalIntervalRegion (Icc 0 1) left right) = ENNReal.ofReal w := by
  rw [volume_horizontalIntervalRegion_eq_lintegral measurableSet_Icc hleft hright]
  simp only [hwidth]
  simp [Real.volume_Icc]

/-- A measurable family of constant-width horizontal intervals in the incoming
unit strip bounds the area of every subset, including nonconvex subsets. -/
theorem volumeReal_le_of_horizontal_intervals {S : Set Plane}
    {left right : ℝ → ℝ} {w : ℝ} (hw : 0 ≤ w)
    (hleft : Measurable left) (hright : Measurable right)
    (hwidth : ∀ y, right y - left y = w)
    (hS : S ⊆ horizontalIntervalRegion (Icc 0 1) left right) :
    volume.real S ≤ w := by
  have hvol : volume S ≤ ENNReal.ofReal w :=
    (measure_mono hS).trans_eq
      (volume_horizontalIntervalRegion_unit_of_constant_width hleft hright hwidth)
  exact ENNReal.toReal_le_of_le_ofReal hw hvol

/-- The intersection of a horizontal unit strip and a second unit strip whose
normal has positive first coordinate has area at most the reciprocal of that
coordinate. The second strip may be translated arbitrarily. -/
theorem volumeReal_le_of_unitStrip_and_frameStrip {S : Set Plane} {θ a : ℝ}
    (hstrip : S ⊆ unitStrip) (hcos : 0 < Real.cos θ)
    (hframe : ∀ p ∈ S, a ≤ coordDot p (unitNormal θ) ∧
      coordDot p (unitNormal θ) ≤ a + 1) :
    volume.real S ≤ 1 / Real.cos θ := by
  apply volumeReal_le_of_horizontal_intervals (left := fun y =>
    (a - Real.sin θ * y) / Real.cos θ) (right := fun y =>
    (a + 1 - Real.sin θ * y) / Real.cos θ)
    (by positivity) (by fun_prop) (by fun_prop)
  · intro y
    ring
  · intro p hp
    obtain ⟨hlo, hhi⟩ := hframe p hp
    change a ≤ p.1 * Real.cos θ + p.2 * Real.sin θ at hlo
    change p.1 * Real.cos θ + p.2 * Real.sin θ ≤ a + 1 at hhi
    refine ⟨hstrip hp, ?_, ?_⟩
    · apply (div_le_iff₀ hcos).2
      nlinarith
    · apply (le_div_iff₀ hcos).2
      nlinarith

theorem cos_ge_sqrt_two_div_two_of_mem_smallAngle {θ : ℝ}
    (hθ : θ ∈ Icc (-(Real.pi / 4)) (Real.pi / 4)) :
    Real.sqrt 2 / 2 ≤ Real.cos θ := by
  have habs : |θ| ≤ Real.pi / 4 := abs_le.mpr hθ
  have h := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg θ)
    (by linarith [Real.pi_pos]) habs
  simpa only [Real.cos_abs, Real.cos_pi_div_four] using h

theorem volumeReal_le_sqrt_two_of_unitStrip_and_smallAngleStrip
    {S : Set Plane} {θ a : ℝ} (hstrip : S ⊆ unitStrip)
    (hθ : θ ∈ Icc (-(Real.pi / 4)) (Real.pi / 4))
    (hframe : ∀ p ∈ S, a ≤ coordDot p (unitNormal θ) ∧
      coordDot p (unitNormal θ) ≤ a + 1) :
    volume.real S ≤ Real.sqrt 2 := by
  have hsqrt : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsquare : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hcos := cos_ge_sqrt_two_div_two_of_mem_smallAngle hθ
  have hc : 0 < Real.cos θ := by linarith
  apply (volumeReal_le_of_unitStrip_and_frameStrip hstrip hc hframe).trans
  apply (div_le_iff₀ hc).2
  nlinarith [mul_le_mul_of_nonneg_left hcos hsqrt.le]

theorem sqrt_two_mul_dot_wrongWay_unit (p : Plane) :
    Real.sqrt 2 * coordDot p (unitNormal (-(Real.pi / 4))) = p.1 - p.2 := by
  simp only [coordDot, unitNormal, Real.cos_neg, Real.sin_neg,
    Real.cos_pi_div_four, Real.sin_pi_div_four]
  calc
    Real.sqrt 2 * (p.1 * (Real.sqrt 2 / 2) + p.2 * -(Real.sqrt 2 / 2)) =
        (Real.sqrt 2 ^ 2 / 2) * (p.1 - p.2) := by ring
    _ = p.1 - p.2 := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring

theorem sqrt_two_mul_dot_wrongWay_companion (p : Plane) :
    Real.sqrt 2 * coordDot p (companionNormal (-(Real.pi / 4))) = p.1 + p.2 := by
  simp only [coordDot, companionNormal, Real.cos_neg, Real.sin_neg,
    Real.cos_pi_div_four, Real.sin_pi_div_four, neg_neg]
  calc
    Real.sqrt 2 * (p.1 * (Real.sqrt 2 / 2) + p.2 * (Real.sqrt 2 / 2)) =
        (Real.sqrt 2 ^ 2 / 2) * (p.1 + p.2) := by ring
    _ = p.1 + p.2 := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring

/-- The lower endpoint of each wrong-way horizontal hallway section. -/
def wrongWayLeft (a b y : ℝ) : ℝ :=
  min (Real.sqrt 2 * a + y) (Real.sqrt 2 * b - y)

/-- An exact section formula: the two outer walls give the same minimum as
the inner disjunction, shifted right by `√2`. -/
theorem mem_wrongWay_frameHall_iff (a b : ℝ) (p : Plane) :
    p ∈ frameHall (unitNormal (-(Real.pi / 4)))
      (companionNormal (-(Real.pi / 4))) a b ↔
    p.1 ∈ Icc (wrongWayLeft a b p.2) (wrongWayLeft a b p.2 + Real.sqrt 2) := by
  have hsqrt : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hunit := sqrt_two_mul_dot_wrongWay_unit p
  have hcomp := sqrt_two_mul_dot_wrongWay_companion p
  have huOuter : coordDot p (unitNormal (-(Real.pi / 4))) ≤ a + 1 ↔
      p.1 ≤ Real.sqrt 2 * a + p.2 + Real.sqrt 2 := by
    calc
      _ ↔ Real.sqrt 2 * coordDot p (unitNormal (-(Real.pi / 4))) ≤
          Real.sqrt 2 * (a + 1) := (mul_le_mul_iff_right₀ hsqrt).symm
      _ ↔ _ := by rw [hunit]; constructor <;> intro h <;> nlinarith
  have hvOuter : coordDot p (companionNormal (-(Real.pi / 4))) ≤ b + 1 ↔
      p.1 ≤ Real.sqrt 2 * b - p.2 + Real.sqrt 2 := by
    calc
      _ ↔ Real.sqrt 2 * coordDot p (companionNormal (-(Real.pi / 4))) ≤
          Real.sqrt 2 * (b + 1) := (mul_le_mul_iff_right₀ hsqrt).symm
      _ ↔ _ := by rw [hcomp]; constructor <;> intro h <;> nlinarith
  have huInner : a ≤ coordDot p (unitNormal (-(Real.pi / 4))) ↔
      Real.sqrt 2 * a + p.2 ≤ p.1 := by
    calc
      _ ↔ Real.sqrt 2 * a ≤
          Real.sqrt 2 * coordDot p (unitNormal (-(Real.pi / 4))) :=
        (mul_le_mul_iff_right₀ hsqrt).symm
      _ ↔ _ := by rw [hunit]; constructor <;> intro h <;> nlinarith
  have hvInner : b ≤ coordDot p (companionNormal (-(Real.pi / 4))) ↔
      Real.sqrt 2 * b - p.2 ≤ p.1 := by
    calc
      _ ↔ Real.sqrt 2 * b ≤
          Real.sqrt 2 * coordDot p (companionNormal (-(Real.pi / 4))) :=
        (mul_le_mul_iff_right₀ hsqrt).symm
      _ ↔ _ := by rw [hcomp]; constructor <;> intro h <;> nlinarith
  change (_ ∧ _ ∧ (_ ∨ _)) ↔ (_ ≤ p.1 ∧ p.1 ≤ _)
  rw [huOuter, hvOuter, huInner, hvInner]
  unfold wrongWayLeft
  constructor
  · rintro ⟨hu, hv, hinner⟩
    refine ⟨min_le_iff.mpr hinner, ?_⟩
    rcases le_total (Real.sqrt 2 * a + p.2) (Real.sqrt 2 * b - p.2) with hab | hba
    · simpa only [min_eq_left hab] using hu
    · simpa only [min_eq_right hba] using hv
  · rintro ⟨hlo, hhi⟩
    refine ⟨?_, ?_, min_le_iff.mp hlo⟩
    · exact hhi.trans (add_le_add_left (min_le_left _ _) _)
    · exact hhi.trans (add_le_add_left (min_le_right _ _) _)

/-- Visiting the wrong-handed angle forces the actual body area below `√2`.
Both hallway offsets are arbitrary and the body need not be convex. -/
theorem volumeReal_le_sqrt_two_of_wrongWay_frameHall {S : Set Plane}
    (hstrip : S ⊆ unitStrip) {a b : ℝ}
    (hhall : S ⊆ frameHall (unitNormal (-(Real.pi / 4)))
      (companionNormal (-(Real.pi / 4))) a b) :
    volume.real S ≤ Real.sqrt 2 := by
  apply volumeReal_le_of_horizontal_intervals
    (left := wrongWayLeft a b) (right := fun y => wrongWayLeft a b y + Real.sqrt 2)
    (Real.sqrt_nonneg 2) (by unfold wrongWayLeft; fun_prop)
    (by unfold wrongWayLeft; fun_prop)
  · intro y
    ring
  · intro p hp
    exact ⟨hstrip hp, (mem_wrongWay_frameHall_iff a b p).mp (hhall hp)⟩

end AmbidextrousSofa
