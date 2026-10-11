module

public import AmbidextrousSofa.Analysis.PartialCurvatureIntervals
public import AmbidextrousSofa.Analysis.OpenWingCurvature
public import AmbidextrousSofa.Analysis.RegularCurvatureDomain

@[expose] public section

/-!
# Actual proper-angle curvature density

The literal selected source interval bounds imply domination by a finite
multiple of Lebesgue measure on every open wing away from the top, middle
and terminal normals. On the companion semicircle the terminal normal is
absent automatically; this regular companion domain lies in the regular
curvature domain of the full quarter turn.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

/-- The selected polygon sequence belongs to the actual given joint
maximum and is constructed inside this theorem. -/
theorem IsJointCapMaximizer.curvature_restrict_le_on_proper_open_wing
    {K : Set Plane} {α m c A B : ℝ} (hK : IsJointCapMaximizer K α)
    (hproper : α < Real.pi / 2)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft K) (horizontalRight K),
      capRoof K x = m * x + c)
    (hA : 0 ≤ A) (hB : B ≤ Real.pi) (htop : Real.pi / 2 ∉ Ioo A B)
    (hterminal : α ∉ Ioo A B)
    (hperp : ∀ t ∈ Ioo A B, Real.cos t + m * Real.sin t ≠ 0) :
    (upperCurvature K).restrict (Ioo A B) ≤
      ENNReal.ofReal (8 * (|horizontalLeft K| + |horizontalRight K| + 1) + 24) •
        volume.restrict (Ioo A B) := by
  obtain ⟨level, coefficient, U, hlevel, hc, hrate, hU, hHausdorff⟩ :=
    hK.exists_symmetric_selected_sequence hproper
  exact restrict_Ioo_le_smul_of_Icc_le (by positivity) fun a b ha hab hb =>
    PartialGrid.curvature_Icc_le_on_wing hK.isCap hU hHausdorff hlevel hc hrate (by positivity)
      (fun n => (hU n).inBox) (by linarith only [hK.width_bounds.1, one_lt_M]) haffine hA hB htop
      hterminal hperp ha hab hb

def regularCompanionDomain (m : ℝ) : Set ℝ :=
  Ioo (Real.pi / 2) Real.pi \ {affineNormalAngle m}

theorem regularCompanionDomain_subset_regularCurvatureDomain (m : ℝ) :
    regularCompanionDomain m ⊆ regularCurvatureDomain m :=
  fun t ht => ⟨⟨by linarith [ht.1.1, Real.pi_pos], ht.1.2⟩, by
    rintro (h | h)
    exacts [ht.1.1.ne' h, ht.2 h]⟩

theorem firstQuarter_subset_regularCurvatureDomain_of_nonneg {m : ℝ} (hm : 0 ≤ m) :
    Ioo (0 : ℝ) (Real.pi / 2) ⊆ regularCurvatureDomain m := by
  intro t ht
  obtain ⟨hs, hc⟩ := sin_cos_pos_of_mem_quarter ht
  exact mem_regularCurvatureDomain_iff.mpr ⟨ht.1, by linarith [ht.2, Real.pi_pos], ht.2.ne,
    (add_pos_of_pos_of_nonneg hc (mul_nonneg hm hs.le)).ne'⟩

end AmbidextrousSofa
