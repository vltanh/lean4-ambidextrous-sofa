module

public import AmbidextrousSofa.Analysis.CoreContactGeometry
public import AmbidextrousSofa.Analysis.RegularCorner

@[expose] public section

/-!
# The actual niche slope at tangent and core contacts

At a strict wall contact, the actual niche lies locally above that
affine wall and agrees with it at the contact point. Their derivatives
therefore coincide. At a corner contact, the niche lies above the
entire nearby corner curve, so differentiation of the resulting local
minimum gives the graph chain rule. These statements require no source
decomposition or occupation coefficient.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem hasDerivAt_firstWall_spatial (U : Set Plane) (t x : ℝ) :
    HasDerivAt (firstWall U t) (-Real.cos t / Real.sin t) x :=
  ((hasDerivAt_mul_const (Real.cos t)).const_sub _).div_const (Real.sin t)

theorem hasDerivAt_secondWall_spatial (U : Set Plane) (t x : ℝ) :
    HasDerivAt (secondWall U t) (Real.sin t / Real.cos t) x :=
  ((hasDerivAt_mul_const (Real.sin t)).const_add _).div_const (Real.cos t)

/-- A curve lying below a differentiable graph and touching it has
the same tangent slope after composition with its horizontal coordinate.
No nonzero horizontal velocity is needed. -/
theorem graph_derivative_mul_eq_of_contact
    {n X Y : ℝ → ℝ} {t g Xd Yd : ℝ}
    (hX : HasDerivAt X Xd t) (hY : HasDerivAt Y Yd t)
    (hn : HasDerivAt n g (X t)) (hcontact : n (X t) = Y t)
    (hbelow : ∀ᶠ s in 𝓝 t, Y s ≤ n (X s)) : g * Xd = Yd := by
  have hmin : IsLocalMin (fun s => n (X s) - Y s) t :=
    hbelow.mono fun s hs => by simpa [hcontact] using hs
  exact sub_eq_zero.mp (hmin.hasDerivAt_eq_zero ((hn.comp t hX).sub hY))

theorem IsDownwardCap.niche_derivative_at_strict_first_contact
    {U : Set Plane} (hU : IsDownwardCap U) {t x g : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hderiv : HasDerivAt (sweptNiche U (Real.pi / 2)) g x)
    (hcontact : firstWall U t x = sweptNiche U (Real.pi / 2) x)
    (hstrict : firstWall U t x < secondWall U t x) :
    g = -Real.cos t / Real.sin t := by
  have hfirst := hasDerivAt_firstWall_spatial U t x
  refine (mul_one g).symm.trans (graph_derivative_mul_eq_of_contact (hasDerivAt_id x) hfirst
    hderiv hcontact.symm ?_)
  filter_upwards [hfirst.continuousAt.eventually_lt
    (hasDerivAt_secondWall_spatial U t x).continuousAt hstrict] with y hy
  simpa only [cornerWall, min_eq_left hy.le, id_eq] using
    cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU.isCompact le_rfl y) ht

theorem IsDownwardCap.niche_derivative_at_strict_second_contact
    {U : Set Plane} (hU : IsDownwardCap U) {t x g : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hderiv : HasDerivAt (sweptNiche U (Real.pi / 2)) g x)
    (hcontact : secondWall U t x = sweptNiche U (Real.pi / 2) x)
    (hstrict : secondWall U t x < firstWall U t x) :
    g = Real.sin t / Real.cos t := by
  have hsecond := hasDerivAt_secondWall_spatial U t x
  refine (mul_one g).symm.trans (graph_derivative_mul_eq_of_contact (hasDerivAt_id x) hsecond
    hderiv hcontact.symm ?_)
  filter_upwards [hsecond.continuousAt.eventually_lt
    (hasDerivAt_firstWall_spatial U t x).continuousAt hstrict] with y hy
  simpa only [cornerWall, min_eq_right hy.le, id_eq] using
    cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU.isCompact le_rfl y) ht

section ActualPair

variable {U : Set Plane} (hU : IsFullCapMaximizer U)
  {m c : ℝ} {ρ : ℝ → ℝ} {K : ℝ} (hm : 0 ≤ m)
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
    capRoof U x = m * x + c)
  (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
  (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))

local notation "F" => fullTiltedSupportQuarterPair hU hm haffine hρ hρ0 hρK heq
set_option quotPrecheck false in
local notation "Z" => innerCornerPoint (F).f (F).g
set_option quotPrecheck false in
local notation "p" => supportP (F).fD (F).g
set_option quotPrecheck false in
local notation "q" => supportQ (F).gD (F).f

theorem fullTiltedSupportQuarterPair_niche_core_slope {t g : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hderiv : HasDerivAt (sweptNiche U (Real.pi / 2)) g (Z t).1)
    (hcontact : sweptNiche U (Real.pi / 2) (Z t).1 = (Z t).2) :
    g * (p t * Real.cos t - q t * Real.sin t) =
      p t * Real.sin t + q t * Real.cos t := by
  obtain ⟨hX, hY⟩ := fullTiltedSupportQuarterPair_core_hasDerivAt hU hm haffine hρ hρ0 hρK heq ht
  refine graph_derivative_mul_eq_of_contact hX hY hderiv hcontact ?_
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  obtain ⟨h1, h2⟩ := fullTiltedSupportQuarterPair_walls_core hU hm haffine hρ hρ0 hρK heq hs
  have hsecond := secondWall_mono (leftCompanionCap_subset _ _)
    hU.isCap_fullLeftCompanion.nonempty hU.isCap.isCompact
    (sin_cos_pos_of_mem_quarter hs).2 (Z s).1
  have hwall := cornerWall_le_sweptNiche
    (sweptWallValues_bddAbove hU.isCap.isCompact le_rfl (Z s).1) hs
  rwa [cornerWall, h1, min_eq_left (h2 ▸ hsecond)] at hwall

/-- After the affine normal the actual original contact supplies the
same slope identity for the closed two-cap support pair. -/
theorem fullTiltedSupportQuarterPair_niche_attachedCorner_slope_after_affine {t g : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) (hmt : Real.arctan m ≤ t)
    (hderiv : HasDerivAt (sweptNiche U (Real.pi / 2)) g (attachedCorner U t).1)
    (hcontact : sweptNiche U (Real.pi / 2) (attachedCorner U t).1 =
      (attachedCorner U t).2) :
    g * (p t * Real.cos t - q t * Real.sin t) =
      p t * Real.sin t + q t * Real.cos t := by
  have hmatch := (fullTiltedSupportQuarterPair_other_points_after_affine
    hU hm haffine hρ hρ0 hρK heq ⟨ht.1.le, ht.2⟩ hmt).2
  exact fullTiltedSupportQuarterPair_niche_core_slope hU hm haffine hρ hρ0 hρK heq ht
    (hmatch ▸ hderiv) (hmatch ▸ hcontact)

end ActualPair

end AmbidextrousSofa
