module

public import AmbidextrousSofa.Analysis.FirstUnitTopOverhang

@[expose] public section

/-!
# Literal tangent displacements and the four first-unit moments

All four moments follow from the absolutely continuous coordinates of
the actual support pair. The initial companion moment uses its first
floor abscissa, which is allowed to differ from the global circle
minimum. That abscissa lies right of the low-wing zero, because the cut
wall passes through the floor contact, and at most one unit right of the
low middle endpoint; the exact top identity turns these into the
displacement inequalities of the final energy argument.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

section ActualPair

variable {U : Set Plane} (hU : IsFullCapMaximizer U)
  {m c : ℝ} {ρ : ℝ → ℝ} {K : ℝ} (hm : 0 ≤ m)
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
    capRoof U x = m * x + c)
  (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
  (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))

open scoped ActualPair

theorem fullTiltedSupportQuarterPair_tangent_displacements {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Real.pi / 2) :
    (∫ t in a..b, (1 - ρ t) * Real.sin t) = (B b).1 - (B a).1 ∧
      (∫ t in a..b, (1 - ρ t) * Real.cos t) = (B a).2 - (B b).2 ∧
      (∫ t in a..b, (1 - v t) * Real.cos t) = (D b).1 - (D a).1 ∧
      (∫ t in a..b, (1 - v t) * Real.sin t) = (D b).2 - (D a).2 := by
  obtain ⟨hBx, hBy, hDx, hDy, hderiv⟩ :=
    fullTiltedSupportQuarterPair_tangent_calculus hU hm haffine hρ hρ0 hρK heq
  have hsub : uIcc a b ⊆ uIcc 0 (Real.pi / 2) :=
    uIcc_subset_uIcc (mem_uIcc_of_le ha (hab.trans hb)) (mem_uIcc_of_le (ha.trans hab) hb)
  have hd := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo ha hb) hderiv
  have hBy' : (∫ t in a..b, (1 - ρ t) * Real.cos t) = _ :=
    integral_eq_sub_of_ac_of_ae_hasDerivAt hab (hBy.neg.mono hsub)
      (hd.mono fun _ ht => ht.2.1.neg.congr_deriv (by ring))
  refine ⟨integral_eq_sub_of_ac_of_ae_hasDerivAt hab (hBx.mono hsub) (hd.mono fun _ ht => ht.1),
    hBy'.trans (by simp only [Pi.neg_apply]; ring),
    integral_eq_sub_of_ac_of_ae_hasDerivAt hab (hDx.mono hsub) (hd.mono fun _ ht => ht.2.2.1),
    integral_eq_sub_of_ac_of_ae_hasDerivAt hab (hDy.mono hsub) (hd.mono fun _ ht => ht.2.2.2)⟩

/-- The first-unit hypothesis identifies the right middle niche height
with the actual first tangent height. No moment identity is supplied as
an assumption. -/
theorem FirstUnitSetting.first_floor_right_moments {C h β γ : ℝ}
    (P : FirstUnitSetting U m ρ C h) (hβ : β ∈ Ioo 0 (Real.pi / 2))
    (hγ : γ ∈ Icc 0 (Real.pi / 2)) (hβx : (B β).1 = C) (hγy : (D γ).2 = 0) :
    (∫ t in 0..γ, (1 - v t) * Real.cos t) = C + (D γ).1 ∧
      (∫ t in 0..γ, (1 - v t) * Real.sin t) = h ∧
      (∫ t in β..(Real.pi / 2), (1 - ρ t) * Real.sin t) =
        (MovingSofaOptimality.vminus U (Real.pi / 2)).1 - C ∧
      (∫ t in β..(Real.pi / 2), (1 - ρ t) * Real.cos t) =
        sweptNiche U (Real.pi / 2) C := by
  obtain ⟨-, hBL, hD0, -⟩ := fullTiltedSupportQuarterPair_tangent_traces
    hU hm haffine hρ hρ0 hρK heq P.hl P.hr P.hmpos P.hheight P.hlow
  have hniche := fullTiltedSupportQuarterPair_niche_first_tangency hU hm haffine hρ hρ0 hρK heq
    P.hunit hβ (P.first_momentum_neg_after_middle hU hm haffine hρ hρ0 hρK heq
      (Ioo_subset_Icc_self hβ) hβx.ge).2.le
    (fullTiltedSupportQuarterPair_first_tangent_nonneg hU hm haffine hρ hρ0 hρK heq P.hheight
      P.hunit (Ioo_subset_Icc_self hβ))
  obtain ⟨-, -, hS, hh⟩ := fullTiltedSupportQuarterPair_tangent_displacements
    hU hm haffine hρ hρ0 hρK heq le_rfl hγ.1 hγ.2
  obtain ⟨hT, hz, -⟩ := fullTiltedSupportQuarterPair_tangent_displacements
    hU hm haffine hρ hρ0 hρK heq hβ.1.le hβ.2.le le_rfl
  rw [hD0] at hS hh
  rw [hBL, hβx] at hT
  rw [hBL, ← hniche, hβx] at hz
  refine ⟨hS.trans ?_, hh.trans ?_, hT, hz.trans ?_⟩ <;> simp only [hγy] <;> ring

/-- Every actual companion floor contact lies right of the global low-wing
zero and at most one unit right of the low middle endpoint. The exact top
identity gives the three displacement inequalities needed by the final
energy argument. -/
theorem FirstUnitSetting.floor_abscissa_bounds {C h γ : ℝ} (P : FirstUnitSetting U m ρ C h)
    (hγ : γ ∈ Ioo 0 (Real.pi / 2)) (hγy : (D γ).2 = 0) :
    (MovingSofaOptimality.vminus U (Real.pi / 2)).1 - C ≤ C + (D γ).1 ∧
      C + (D γ).1 ≤ 1 ∧ (MovingSofaOptimality.vminus U (Real.pi / 2)).1 - C ≤ C := by
  have hwall : secondWall V γ (D γ).1 = (D γ).2 := by
    rw [fullTiltedSupportQuarterPair_cut_wall_eq_scalar hU hm haffine hρ hρ0 hρK heq,
      div_eq_iff (sin_cos_pos_of_mem_quarter hγ).2.ne', secondTangentPoint,
      companionSupportPoint_coordinates]
    dsimp only
    linear_combination (1 - (F).g γ) * Real.sin_sq_add_cos_sq γ
  have hz : companionZero V ≤ (D γ).1 := not_lt.mp fun h => by
    linarith only [hU.isCap_fullLeftCompanion.secondWall_neg_of_lt_companionZero h hγ, hwall, hγy]
  have hx : (Reference.companionSupportPoint (F).g (F).gD γ).1 ≤
      horizontalLeft U + capWidth U / 4 :=
    ((fullTiltedSupportQuarterPair_points_mem hU hm haffine hρ hρ0 hρK heq).2 γ
      (Ioo_subset_Icc_self hγ)).2.2
  rw [P.left_quarter] at hz hx
  rw [companionSupportPoint_coordinates] at hx
  have hright := (hU.isCap.fst_mem_Icc
    (MovingSofaOptimality.vminus_mem_edge hU.isCap.imported_isConvexBody (Real.pi / 2)).1).2
  refine ⟨by linarith only [(P.top_overhang hU hm haffine hρ hρ0 hρK heq).2.1, hz], ?_,
    by linarith only [hright, P.hr]⟩
  rw [secondTangentPoint, companionSupportPoint_coordinates]
  dsimp only at hx ⊢
  linarith [Real.sin_le_one γ]

end ActualPair

end AmbidextrousSofa
