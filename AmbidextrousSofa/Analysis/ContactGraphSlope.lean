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
    HasDerivAt (firstWall U t) (-Real.cos t / Real.sin t) x := by
  simpa only [firstWall, one_mul, zero_sub] using
    (((hasDerivAt_const x (support U (unitNormal t) - 1)).sub
      ((hasDerivAt_id x).mul_const (Real.cos t))).div_const (Real.sin t))

theorem hasDerivAt_secondWall_spatial (U : Set Plane) (t x : ℝ) :
    HasDerivAt (secondWall U t) (Real.sin t / Real.cos t) x := by
  simpa only [secondWall, one_mul, zero_add] using
    (((hasDerivAt_const x (support U (companionNormal t) - 1)).add
      ((hasDerivAt_id x).mul_const (Real.sin t))).div_const (Real.cos t))

theorem IsDownwardCap.niche_derivative_at_strict_first_contact
    {U : Set Plane} (hU : IsDownwardCap U) {t x g : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hderiv : HasDerivAt (sweptNiche U (Real.pi / 2)) g x)
    (hcontact : firstWall U t x = sweptNiche U (Real.pi / 2) x)
    (hstrict : firstWall U t x < secondWall U t x) :
    g = -Real.cos t / Real.sin t := by
  have hfirst := hasDerivAt_firstWall_spatial U t x
  have hsecond := hasDerivAt_secondWall_spatial U t x
  have hgap := hfirst.continuousAt.tendsto.eventually_lt
    hsecond.continuousAt.tendsto hstrict
  have hmin : IsLocalMin
      (fun y => sweptNiche U (Real.pi / 2) y - firstWall U t y) x := by
    change ∀ᶠ y in 𝓝 x,
      sweptNiche U (Real.pi / 2) x - firstWall U t x ≤
        sweptNiche U (Real.pi / 2) y - firstWall U t y
    filter_upwards [hgap] with y hy
    rw [hcontact, sub_self]
    apply sub_nonneg.mpr
    have hwall := cornerWall_le_sweptNiche
      (sweptWallValues_bddAbove hU.isCompact le_rfl y) ht
    simpa only [cornerWall, min_eq_left hy.le] using hwall
  exact sub_eq_zero.mp (hmin.hasDerivAt_eq_zero (hderiv.sub hfirst))

theorem IsDownwardCap.niche_derivative_at_strict_second_contact
    {U : Set Plane} (hU : IsDownwardCap U) {t x g : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hderiv : HasDerivAt (sweptNiche U (Real.pi / 2)) g x)
    (hcontact : secondWall U t x = sweptNiche U (Real.pi / 2) x)
    (hstrict : secondWall U t x < firstWall U t x) :
    g = Real.sin t / Real.cos t := by
  have hfirst := hasDerivAt_firstWall_spatial U t x
  have hsecond := hasDerivAt_secondWall_spatial U t x
  have hgap := hsecond.continuousAt.tendsto.eventually_lt
    hfirst.continuousAt.tendsto hstrict
  have hmin : IsLocalMin
      (fun y => sweptNiche U (Real.pi / 2) y - secondWall U t y) x := by
    change ∀ᶠ y in 𝓝 x,
      sweptNiche U (Real.pi / 2) x - secondWall U t x ≤
        sweptNiche U (Real.pi / 2) y - secondWall U t y
    filter_upwards [hgap] with y hy
    rw [hcontact, sub_self]
    apply sub_nonneg.mpr
    have hwall := cornerWall_le_sweptNiche
      (sweptWallValues_bddAbove hU.isCompact le_rfl y) ht
    simpa only [cornerWall, min_eq_right hy.le] using hwall
  exact sub_eq_zero.mp (hmin.hasDerivAt_eq_zero (hderiv.sub hsecond))

/-- A curve lying below a differentiable graph and touching it has
the same tangent slope after composition with its horizontal coordinate.
No nonzero horizontal velocity is needed. -/
theorem graph_derivative_mul_eq_of_contact
    {n X Y : ℝ → ℝ} {t g Xd Yd : ℝ}
    (hX : HasDerivAt X Xd t) (hY : HasDerivAt Y Yd t)
    (hn : HasDerivAt n g (X t)) (hcontact : n (X t) = Y t)
    (hbelow : ∀ᶠ s in 𝓝 t, Y s ≤ n (X s)) : g * Xd = Yd := by
  have hmin : IsLocalMin (fun s => n (X s) - Y s) t := by
    change ∀ᶠ s in 𝓝 t, n (X t) - Y t ≤ n (X s) - Y s
    filter_upwards [hbelow] with s hs
    rw [hcontact, sub_self]
    exact sub_nonneg.mpr hs
  exact sub_eq_zero.mp (hmin.hasDerivAt_eq_zero ((hn.comp t hX).sub hY))

theorem IsDownwardCap.attachedCorner_le_sweptNiche
    {U : Set Plane} (hU : IsDownwardCap U) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    (attachedCorner U t).2 ≤ sweptNiche U (Real.pi / 2) (attachedCorner U t).1 := by
  have hs : Real.sin t ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith only [ht.2, Real.pi_pos])).ne'
  have hc : Real.cos t ≠ 0 := (Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩).ne'
  have hwall := cornerWall_le_sweptNiche
    (sweptWallValues_bddAbove hU.isCompact le_rfl (attachedCorner U t).1) ht
  simpa only [cornerWall, firstWall_attachedCorner U hs,
    secondWall_attachedCorner U hc, min_self] using hwall

theorem IsDownwardCap.niche_derivative_at_attachedCorner
    {U : Set Plane} (hU : IsDownwardCap U) {t g Xd Yd : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hX : HasDerivAt (fun s => (attachedCorner U s).1) Xd t)
    (hY : HasDerivAt (fun s => (attachedCorner U s).2) Yd t)
    (hderiv : HasDerivAt (sweptNiche U (Real.pi / 2)) g (attachedCorner U t).1)
    (hcontact : sweptNiche U (Real.pi / 2) (attachedCorner U t).1 =
      (attachedCorner U t).2) : g * Xd = Yd := by
  apply graph_derivative_mul_eq_of_contact hX hY hderiv hcontact
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact hU.attachedCorner_le_sweptNiche hs

/-- The original regular corner velocities come from the actual
curvature density; its graph identity has no occupation-law premise. -/
theorem IsDownwardCap.niche_derivative_corner_velocity
    {U : Set Plane} (hU : IsDownwardCap U) {m K t g : ℝ} {ρ : ℝ → ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
      (volume.restrict (regularCurvatureDomain m)).withDensity (fun s => ENNReal.ofReal (ρ s)))
    (ht : t ∈ regularCornerDomain m)
    (hderiv : HasDerivAt (sweptNiche U (Real.pi / 2)) g (attachedCorner U t).1)
    (hcontact : sweptNiche U (Real.pi / 2) (attachedCorner U t).1 =
      (attachedCorner U t).2) :
    g * cornerVelocityX U t = cornerVelocityY U t := by
  obtain ⟨hX, hY⟩ := hU.hasDerivAt_corner_coordinates_on_regularCornerDomain hρ hρ0 hρK heq ht
  exact hU.niche_derivative_at_attachedCorner ht.1 hX hY hderiv hcontact

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
local notation "V" => leftCompanionCap U (horizontalLeft U + capWidth U / 4)

theorem fullTiltedSupportQuarterPair_core_le_sweptNiche {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    (Z t).2 ≤ sweptNiche U (Real.pi / 2) (Z t).1 := by
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩
  have hw := fullTiltedSupportQuarterPair_walls_core hU hm haffine hρ hρ0 hρK heq ht
  have hsecond : (Z t).2 ≤ secondWall U t (Z t).1 := by
    rw [← hw.2]
    exact secondWall_mono (leftCompanionCap_subset _ _) hU.isCap_fullLeftCompanion.nonempty
      hU.isCap.isCompact hc _
  have hcorner : cornerWall U t (Z t).1 = (Z t).2 := by
    rw [cornerWall, hw.1, min_eq_left hsecond]
  rw [← hcorner]
  exact cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU.isCap.isCompact le_rfl _) ht

theorem fullTiltedSupportQuarterPair_niche_core_slope {t g : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hderiv : HasDerivAt (sweptNiche U (Real.pi / 2)) g (Z t).1)
    (hcontact : sweptNiche U (Real.pi / 2) (Z t).1 = (Z t).2) :
    g * (p t * Real.cos t - q t * Real.sin t) =
      p t * Real.sin t + q t * Real.cos t := by
  obtain ⟨hX, hY⟩ := fullTiltedSupportQuarterPair_core_hasDerivAt
    hU hm haffine hρ hρ0 hρK heq ht
  apply graph_derivative_mul_eq_of_contact hX hY hderiv hcontact
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact fullTiltedSupportQuarterPair_core_le_sweptNiche hU hm haffine hρ hρ0 hρK heq hs

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
  apply fullTiltedSupportQuarterPair_niche_core_slope hU hm haffine hρ hρ0 hρK heq ht
  · simpa only [hmatch] using hderiv
  · simpa only [hmatch] using hcontact

end ActualPair

end AmbidextrousSofa
