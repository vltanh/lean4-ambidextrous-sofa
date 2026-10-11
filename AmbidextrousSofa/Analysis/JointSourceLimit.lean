module

public import AmbidextrousSofa.Analysis.JointSourceMeasure
public import Mathlib.MeasureTheory.Measure.Prokhorov

@[expose] public section

/-!
# A common weak limit of the actual joint source measures

The finite source measures have bounded total mass and one fixed compact
support. Compactness of finite measures therefore gives a common weak
limit along an ultrafilter refining the natural-number tail filter.
Every already proved limit of the selected polygon sequence continues
to hold along this same refinement.

The selected sequence and the limiting measure are constructed from the
given full maximum. In particular, their existence is not a geometric
occupation hypothesis at a later application.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa
namespace AngularGrid

/-- One nontrivial refinement is used for both source families and both
graph coordinates. -/
def sourceLimitFilter : Ultrafilter ℕ := Ultrafilter.of atTop

theorem sourceLimitFilter_le_atTop : (sourceLimitFilter : Filter ℕ) ≤ atTop :=
  Ultrafilter.of_le atTop

/-- A selected approximation sequence together with the common weak
limit of its literal finite inner source measures. -/
structure SelectedJointSourceLimit (target : Set Plane) (a b : ℝ) where
  level : ℕ → ℕ
  coefficient : ℕ → ℝ
  caps : ℕ → Set Plane
  level_ge : ∀ n, n ≤ level n
  coefficient_pos : ∀ n, 0 < coefficient n
  coefficient_tendsto : Tendsto coefficient atTop (𝓝 0)
  selected : ∀ n, IsSelectedPolygon target a b (level n) (coefficient n) (caps n)
  hausdorff : CapHausdorffTendsto caps target
  measure : FiniteMeasure Plane
  converges : Tendsto (fun n => innerJointFiniteMeasure (caps n) (dyadic (level n))
    (horizontalLeft (caps n) + capWidth (caps n) / 4)
    (horizontalRight (caps n) - capWidth (caps n) / 4))
    (sourceLimitFilter : Filter ℕ) (𝓝 measure)
  mass_le : measure.mass ≤ Real.toNNReal ((4 * (|a| + |b| + 1) + 12) * Real.pi)
  outside_box : (measure : Measure Plane)
    (Icc (0 : ℝ) Real.pi ×ˢ Icc (-(|a| + |b| + 1)) (|a| + |b| + 1))ᶜ = 0

namespace SelectedJointSourceLimit

variable {target : Set Plane} {a b : ℝ} (J : SelectedJointSourceLimit target a b)

def finiteMeasure (n : ℕ) : FiniteMeasure Plane :=
  innerJointFiniteMeasure (J.caps n) (dyadic (J.level n))
    (horizontalLeft (J.caps n) + capWidth (J.caps n) / 4)
    (horizontalRight (J.caps n) - capWidth (J.caps n) / 4)

theorem isCap (n : ℕ) : IsDownwardCap (J.caps n) := (J.selected n).isCap

theorem level_tendsto : Tendsto J.level atTop atTop :=
  tendsto_atTop_mono J.level_ge tendsto_id

/-- The already established source-curvature occupation limit remains
valid for this very same joint measure sequence and filter. -/
theorem angular_mass_tendsto
    (hTarget : IsFullCapMaximizer target) (hheight : capHeight target = 1)
    {m c s t : ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
      capRoof target x = m * x + c)
    (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hleft : a < horizontalLeft target) (hright : horizontalRight target < b)
    (hst : s ≤ t) (hregular : Icc s t ⊆ regularCurvatureDomain m) :
    Tendsto (fun n => (J.finiteMeasure n : Measure Plane).real (Ioc s t ×ˢ univ))
      (sourceLimitFilter : Filter ℕ) (𝓝 ((upperCurvature target).real (Ioc s t))) := by
  refine ((innerAngularMass_Ioc_tendsto_of_canonical_maximum hTarget hheight haffine hTargetBox
    J.selected J.hausdorff J.level_tendsto (fun n => (J.coefficient_pos n).le)
    J.coefficient_tendsto hleft hright hst hregular).mono_left sourceLimitFilter_le_atTop).congr
    fun n => ?_
  have hlr := horizontalLeft_le_horizontalRight (J.isCap n).nonempty (J.isCap n).isCompact
  exact (innerJointMeasure_angular_mass _ _ (by linarith) measurableSet_Ioc).symm

end SelectedJointSourceLimit

theorem exists_selected_joint_source_limit {target : Set Plane}
    (hTarget : IsFullCapMaximizer target) {a b : ℝ} (hab : a ≤ b)
    (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1) :
    Nonempty (SelectedJointSourceLimit target a b) := by
  obtain ⟨level, coefficient, U, hlevel, hc, hrate, hU, -, hHausdorff⟩ :=
    exists_selected_sequence hTarget hab hTargetBox
  let ν n := innerJointFiniteMeasure (U n) (dyadic (level n))
    (horizontalLeft (U n) + capWidth (U n) / 4) (horizontalRight (U n) - capWidth (U n) / 4)
  have hν (n : ℕ) : (ν n).mass ≤ Real.toNNReal ((4 * (|a| + |b| + 1) + 12) * Real.pi) ∧
      ν n (Icc (0 : ℝ) Real.pi ×ˢ Icc (-(|a| + |b| + 1)) (|a| + |b| + 1))ᶜ = 0 := by
    have hbox := subset_symmetricBox_of_horizontalBox (hU n).inBox
    exact ⟨(Real.le_toNNReal_iff_coe_le (by positivity)).2
      (innerJointMeasure_middle_mass_dyadic_le (hU n).isCap (by positivity) hbox (level n)),
      (FiniteMeasure.null_iff_toMeasure_null _ _).mpr
        (innerJointMeasure_middle_compl_box_eq_zero (hU n).isCap hbox (dyadic (level n)))⟩
  obtain ⟨μ, hμ, hlim⟩ := (isCompact_setOfPred_finiteMeasure_le_of_isCompact _
    (isCompact_Icc.prod isCompact_Icc)).ultrafilter_le_nhds' (sourceLimitFilter.map ν)
      (Ultrafilter.mem_map.2 (univ_mem' hν))
  exact ⟨⟨level, coefficient, U, hlevel, hc, hrate, hU, hHausdorff, μ, hlim, hμ.1,
    (FiniteMeasure.null_iff_toMeasure_null _ _).mp hμ.2⟩⟩

end AngularGrid

/-- The box, selected sequence, and common joint source limit are all
chosen internally from the prescribed full maximum. -/
theorem IsFullCapMaximizer.exists_jointSourceLimit {U : Set Plane}
    (hU : IsFullCapMaximizer U) :
    ∃ a b : ℝ, a < horizontalLeft U ∧ horizontalRight U < b ∧
      U ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 ∧
      Nonempty (AngularGrid.SelectedJointSourceLimit U a b) := by
  have hlr := horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact
  have hbox : U ⊆ Icc (horizontalLeft U - 1) (horizontalRight U + 1) ×ˢ Icc (0 : ℝ) 1 :=
    fun P hP => ⟨⟨by linarith [(hU.isCap.fst_mem_Icc hP).1],
      by linarith [(hU.isCap.fst_mem_Icc hP).2]⟩, hU.isCap.inStrip hP⟩
  exact ⟨_, _, by linarith, by linarith, hbox,
    AngularGrid.exists_selected_joint_source_limit hU (by linarith) hbox⟩

end AmbidextrousSofa
