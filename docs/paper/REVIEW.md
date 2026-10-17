# Manuscript review and checks

Date: 12 October 2026, US Central Time.

- The manuscript presents a mathematical proof of optimality, uniqueness, and the quarter-turn conclusion.
- Its eleven main sections follow the proof stages explained in the introduction.
- Eight mathematical appendices supply the ordinary-sofa input, the reference construction, and the auxiliary
  estimates.

## Mathematical review

Three writers reviewed sections written by the others. The review checked the following points:

- The reduction retains the actual two motions and permits pauses, reversals, different initial translations, and proper terminal angles. The terminal first wall is included over the whole projection.
- Connectedness makes the signed envelope fibers nonnegative. The reduction records the nonnegative deficits needed to identify both original caps in the equality case.
- Penalized polygon selection approximates each prescribed maximum. The two weighted source measures give the variation laws without assuming convergence of unweighted niche boundary length.
- The full-turn argument includes the ordered contacts, joint occupation, two-unit strip moments, and folded-wing energy estimate. The geometric exclusions precede the support-functional comparison.
- The calibration applies to the stated class of continuously differentiable support profiles, proves the coercivity constant, and identifies the unique root of the stationary cubic.
- The proper-angle argument applies to each prescribed maximizing pair, with its actual terminal facet and reflected impulse. The circle and curvature estimates exclude that pair's proper angle.
- The preliminary width and tilt exclusions use the actual barrier. Exact calculations check the scalar estimates; the horizontal argument now uses one stopping bound and dry endpoints.
- The reference support curve, face atoms, phase matching, niche constraints, two passages, and exact area are proved explicitly. Differentiation checks all three area primitives and the endpoint fluxes.
- Equal cap scores align the original caps through their common projection. Containment and regular closedness recover equality of compact sets and the conclusion for every witnessing pair of motions.

### Findings

- The review found no unresolved substantive mathematical error.
- It clarified the competitive range for a concavity argument and the reference hull's nonempty interior.
- This is an agent review; human mathematical review remains outstanding.

## Build and layout checks

- `make check` passes: no undefined references, duplicate labels, overflowing lines, or BibTeX warnings.
- The manuscript has 109 pages. All labels and cross-references resolve in the active source files.
- `make arxiv` produces a 31-entry source archive and compiles its 109-page PDF separately with `pdflatex` alone. The archive contains only the active manuscript inputs, bibliography, and figure PDFs.
- Representative pages were inspected visually: the title and main theorem, introduction and organization, support-functional section, reference appendix, contact-energy calculation, and numerical estimates.
- The six figure assets retain their numerical geometry checks from the preceding build.
- Whitespace and source scans pass. The archived research manuscript is unchanged.

## Numerical choices and their origin (11–12 October 2026)

- The earlier pass removed 364 occurrences of large literal fractions.
- That digit-count criterion did not address arbitrary choices with smaller numerators and denominators. This
  revision changes the mathematical comparisons themselves:

| Estimate | Current argument |
| --- | --- |
| Reference cubic root | Start with `[1/4, 1/3]` and apply a proved lower/upper Newton update twice. The root enclosure and reference half-area budget remain formulas. The fitted root approximations `14/47` and `19/64` are gone. |
| Diagonal offset | Two Newton steps from `3/2` bound the square root; the reciprocal gives the lower bound. The old `41/99` lower bound and independently displayed upper enclosure are replaced throughout the Lean proof by this common procedure. |
| Common score comparison | The manuscript uses the formula-generated reference budget instead of a separately chosen `41/50` threshold. The Lean scalar certificates retain coarse bounds where they simplify arithmetic. |
| Initial-angle comparison | Integrate fixed wall pieces and complete two squares, with weighted Cauchy–Schwarz paying for the tent apex. Split widths at the geometric offset `K = √2 − 1`; derive the complementary tent gap from `K` and the angular endpoint. The concavity proof, critical-point clipping checks, slope split at `3/5`, and fitted inset and tent-gap tolerances are removed. Complete the width square and compare the exact angular endpoint with the generated reference half-area. |
| Short-width comparison | Exclude widths at most one, the unit-corridor boundary. The extra width tolerance `2⁻¹⁰` is gone. With `k = √2 − 1` and `N = √(1+k²)`, use the full wall height `η = 1 − N + k²`; its support threshold is `k − η` and its companion midpoint is `(N + η/k)/2`. These replace `2/25`, `8/25`, and `16/25` in this argument. |
| Horizontal short caps | Apply the same three-tent lemma with zero tilt. The duplicate proof and its independent height, tip, and deficit choices are removed. |
| Short-width stability and cuts | The width and tilt reserves are `1 − k²/4` and `k²/4`; the complete outer-cut budget is its geometric triangle area. These replace `9/10`, `1/23`, `23/200`, and `1/110` in this argument. All scalar boundary checks use the generated reference budget. |

- The manuscript states the Newton recurrences, the wall-height interpretation, the constrained quadratic
  comparisons, and the exact companion identity. No expanded fractions are needed to reproduce these calculations.
- [check_numeric_estimates.py](../../scripts/check_numeric_estimates.py) independently checks their arithmetic
  together with the circle and stopping estimates.

## Revision of the arguments (11–12 October 2026)

- This pass reviewed all eleven main sections and eight appendices for the reasoning behind their calculations.
- Each stage now explains the obstruction it addresses, the quantity that measures that obstruction, and how the
  estimate advances the proof.
- Several arguments also changed mathematically:

| Argument | Revision |
| --- | --- |
| Motion reduction and the score | Explain why the middle half balances the two cap areas, why its constant contribution cancels, and why the positive wall differences are precisely the defects that must be retained. |
| Selection of maxima | Explain the quadratic tent cost that prevents width from escaping, why inserting the canonical roof increases the score, and why the penalty keeps the prescribed maximum in the limit. |
| Variation laws | Connect the endpoint pressures to the moving middle window, the facet law to an area change, and the source constraints to visible niche length. |
| Full-turn geometry | Organize the curvature test around the competing floor and momentum-zero events. Explain the squared-radius tests and shared corner occupation. Collect the folded-wing costs into a decreasing function of the contact angle, bounded at the 3–4–5 direction. |
| Support calibration | Derive the functional and its three Euler phases. Use the exact Dirichlet coefficient instead of intermediate numerical margins. Derive the width derivative from boundary flux, explaining why the optimum has endpoint height one half, and remove the duplicate expanded flux table. |
| Proper terminal angles | Present the contradiction as a comparison of two lengths. Explain how missing curvature and the terminal facet enter the reflected motion. Compare the joint crossing and decay time by differences of squares, increasing width before height. This removes the small-height branch. Use one Newton check of the zero-tilt baseline and pay the angular overlap by its cubic moment. |
| Equality and body recovery | Reuse the established constant bound and regular closedness instead of proving them again. Explain how the common projection aligns the caps before recovering the body. |
| Reference matching | The cubic gives `tan(β/2 + π/8) = 2Y`. Angle addition then gives both matching coefficients directly. The Lean proof follows the same argument, replacing expanded trigonometric cross-products. |
| Three-tent comparison | A general supporting plane handles all clipping patterns. One tilt payment then pays for the full, proper, and dry-endpoint floor corrections. The angle parameters retain their geometric quadratic identities, and one Newton rule compares their complete area bounds directly with the generated reference budget. Separate fitted certificates for the final slope, curvature, stationary square, and floor squares are removed. |
| Low-middle-height exclusion | Split at `C = √2 − 1/4`, where the diagonal tail reaches the clipping boundary. Use the simpler score bound `4/5`; the extra fitted width threshold is removed. |
| Horizontal curvature and width | Reuse the preliminary width cut. One crossing and decay estimate ends every curvature excess before endpoint contact, so both middle endpoints are dry. Stationarity fixes both axis heights at one half; the chord-area bound and 3–4–5 direction give `C < √17/6`. The five leakage intervals, Newton junction, and duplicate wide-width exclusions are removed. |
| Terminal circle margin | Use the cosine of the established terminal-angle endpoint for the circle tangent. Its gain pays for the cubic shift of the chord center. Concavity leaves two width endpoints; their actual minimum gap pays for the cubic overlap. Four Newton updates from the unit seed check every root. The chosen reserve `1/100` and separate endpoint seeds, fitted choice `q² = 1/8`, and sine approximation `14/15` are removed. |
| Proper reflected excess | Retain the outgoing wall and endpoint height together. A top overhang or a descending height loss spends one angular time budget, compared with one zero-tilt baseline. The terminal atom costs less than its inset squared. The overlap is linear in terminal slope, so its cubic moment pays the linear cosine margin. The split at cotangent `1/8`, the two fixed impulse costs, and the three stopping-time boxes are removed. |
| Tilted first-wing selector | Define the height where the radius and floor-energy tests meet, and use its radius to determine the width. Below it, the dry endpoint makes floor energy monotone in momentum, leaving two height endpoints. Above it, the triangle bound applies at every height and decreases to zero tilt. The width split `73/100`, height split `21/100`, separate high/middle strips, and fitted endpoint momentum and sine witnesses are removed. |
| Tilted and reflected excess | Before the floor, the exact circle gives the geometric angle `π/6` directly. After the floor, compare with zero tilt: a floor-energy loss of at least `5h` shortens the excess by at least `h`, paying for the crossing delay of at most `h`. The stopping proof no longer divides tilt at `1/25`, width at `54/25`, or reflected height at `2/3`. The shared corner comparison also removes the height split at `3/10`. The reflected energy margin is `1/8` and its duration uses the common bound `1/3`. |
| Corner confinement | Use the circle identity to bound cosine below by a quadratic, then use a tangent to the cubic. Above the sign change, use the 3–4–5 tangent to the circle. Two quadratic discriminant tests replace the translated quartic and squared cubic certificates. |
| Intermediate tilt | One common price pays both clipped perspective losses and the positive niche apex. The two support coordinates cancel, leaving one price square. Direct comparison with the generated reference area gives `h < 1/3`, replacing `17/50` throughout the later domains and endpoints. The coupled loss is bounded by the reference budget instead of `9/25`. |
| Wide and tilted preliminary estimates | A midpoint square completion and the endpoint law price the exact span needed by both nearby-angle peaks. This replaces the three cuts `a < 9/5`, `h < 1/4`, and `a + h < 37/20`; the full-cap endpoint heights follow directly from their pressure laws. Retain the exact triangle demand and reciprocal prices `4 + 5k`. A common price cancels tilt, leaving one midpoint square. |
| Small positive tilt | Use the shared radius-width reduction. A failed radius test gives the joint pressure budget `h + 3z/5 ≤ h₀`; the same area prices as the floor test pay that budget. Rationalizing the two circle radii supplies the width gain. The separate width cut `29/40`, momentum cut `4/15`, niche cut `27/100`, and split at height `1/40` are removed. Newton steps and one quadratic-loss comparison handle the floor test. |

### The revisions in Lean

- The small-height argument uses `centered_width_lt_radiusWidth_of_dry` in both the selector and the
  ordinary-area comparison.
  - Its scalar estimate takes the proved radius width in place of the coarser containing width, and no longer
    assumes the separate niche enclosure `z ≤ 33/100`; the actual cap theorem keeps its original hypotheses.
  - `smallTilt_radius_budget_payment` and `smallTilt_radius_gain_positive` correspond to the common prices and
    rationalized circle-radius gain in Lemma `lem:tilted-small-height`.
  - The coefficients are retained as their chord, width, projection and leakage contributions, matching
    `smallTiltHeightLoss`, `smallTiltNicheLoss`, `smallTiltFloorLinear` and `smallTiltFloorQuadratic`.
  - The two physical energy tests remain, but neither requires a further small-height subdivision.

- The intermediate tilt estimate follows `tiltedDiagonalRelaxation_eq_perspective`,
  `tiltedDiagonalRelaxation_le_price`, and `tiltedDiagonalBound_high_score`.
  - The perspective identity and common price replace the two-support stationary-point construction and its
    clipping feasibility proof.
  - `clipped_perspective_ge_tangent` is shared with the wide argument through `DiagonalScalar.lean`.
  - The scalar area bound needs only the elementary offset enclosure `[1/3, 1/2]`; the endpoint comparison uses
    the existing generated reference and offset bounds.
  - It compares at height one third directly with `referenceHalfAreaLower`, removing this argument's `41/50`
    intermediary and expanded `160/303` coefficient.
  - Both actual callers use the same scalar consequence, and every later height domain, containing box and
    endpoint check uses `1/3` in place of `17/50`.
  - The full and proper canonical consequences and all nine main Challenge statements retain their original
    geometric hypotheses.

- The wide-cap strategy now follows `wide_diagonal_high_score_fitting` and `threeAngle_wide_high_score_fitting`.
  - At the first wide width, the midpoint square completion and endpoint law give a width price, height price,
    and area reserve. One affine budget pays the weighted span `(1 - k/2)a + h`, which is the sufficient
    peak-fitting condition itself.
  - The natural clipping boundary `a = 1 + 2k` remains; the independent cuts `9/5`, `1/4`, and `37/20` are
    removed from this argument and its actual callers.
  - `wide_peak_fits` takes the weighted span directly, and `wide_piece_fitting` uses only the original height
    range.
  - The full-angle wrapper obtains both endpoint height bounds from `partialTriangle_endpoint_lower_bounds`,
    removing its niche-box detour.
  - The paper explicitly uses the inner support-cut halves, matching the formal payment, and derives the final
    supporting plane from the midpoint square and the positive-part square inequality.
  - The exact demand is `wideGainDemand`, its payment is `wide_gain_sum_ge_demand`, and `widePaidBound_le_price`
    cancels tilt with the common price before completing the midpoint square. Its root enclosures and the first
    wide width remain.
  - The manuscript and Lean have been revised together under the owner's request; the nine main statements are
    unchanged.

- The tilted selector uses `initialFloorEnergyConditions_of_radius_width` and `false_of_radius_width_zero_left`,
  with the common geometry defined in `TiltedRadiusWidth.lean`.
  - These correspond to Lemma `lem:tilted-unit-regions` and the strengthened all-height triangle exclusion
    `lem:tilted-medium-width`.
  - The triangle floor comparison accepts signed depth bounds; the common clipping test now needs only midpoint
    height `3/4`, replacing `179/200`. All three floor corrections are compared at zero tilt.
  - The height boundary is now the unique energy-balance root, enclosed by three updates from the canonical
    interval.
  - The lower floor endpoint is equality by definition; the upper endpoint uses only squared radius at most five,
    radius at least two, and sine at least two thirds.
  - Common triangle helpers retain coarse clipping brackets.

- The initial-angle proof now follows `initialAngleRelaxation_first_region_le` and
  `initialAngleRelaxation_second_region_le` directly, corresponding to the fixed-wall and square comparisons in
  Appendix E.
  - The reference parameters only center algebraic identities; no feasible critical point is required.
  - `initialAngleRelaxation_all_width_lt` uses the natural width `K`, and `initialAngleRelaxation_complement_lt`
    uses `initialAngleComplementGap`, derived from the same offset and the minimum cotangent.
  - The later terminal-corner cut is derived from `3C sin α > 1 + cos α` at the angular endpoint, replacing
    `49/100`. `width_gt_initialAngleCornerWidth` and `terminal_corner_width_scale` carry this geometric threshold
    into both actual callers.
  - These are coordinated revisions of the manuscript and its Lean proof under the owner's request.

- The horizontal argument:
  - The new horizontal energy threshold uses the proved axis height one half, replacing the former box-only
    criterion.
  - Lean proves the dry-endpoint result from the actual curvature density and wall kernel, without adding a
    hypothesis.
  - The original cap supplies both unit-curvature quarters, so choosing a reflected orientation is no longer
    necessary.
- The triangle comparisons:
  - The triangle payment is `triangle_tilt_payment`, and the whole-score parameter comparison is
    `triangleCornerScore_le_Newton`; they correspond to Lemmas `lem:triangle-tilt-payment` and
    `lem:triangle-newton-corners`.
  - Its three scalar callers use the cosine identity proved by `fullTriangleCos_quadratic`, so the stronger
    coupling assumption is supplied by the actual geometry.
  - These triangle exclusions compare directly with `referenceHalfAreaLower`; their former `41/50` score
    intermediary is removed from the manuscript and Lean callers.
- The changes to the reference identities, general triangle comparison, low-height bound, horizontal threshold,
  tilt cancellation, joint stopping comparison, and small-tilt losses are reflected in the Lean proofs and their
  callers.
- The stopping arguments:
  - Lemma `lem:joint-stopping-corner` corresponds to `properExcessEnd_mono_width`, `properExcessEnd_mono_height`,
    and `properExcessEnd_lt_of_corner`; its zero-tilt consequence is `zero_tilt_excess_stops_early`.
  - The additional energy condition is checked at each far width, so no main theorem acquires a hypothesis.
  - The proper reflected proof uses `properExcessEnd_le_baseline_payment` and
    `properExcessEnd_le_angular_deadline`, corresponding to Lemma `lem:angular-stopping-budget`. Its actual
    parameters come from `centered_terminal_reflected_angular_budget_of_tail_regime`.
  - The envelope retains its decay-dependent coefficient `(1 + ellMax)/2`, checked at `ellMax = 3/5`.
  - Proposition `app:partial-reflection` now states the uniform bound on the weighted error required by the
    terminal comparison; the former near-full zero-error assertion is no longer needed as a separate result. The
    actual impulse energy and density are retained.
- The terminal circle proof uses `terminal_circle_joint_average_comparison` and `terminal_circle_average_gap`, with
  the intrinsic endpoint-gap margin and its original geometric hypotheses; its actual-height and reserve-interval
  callers use the new comparison.
- The calibration:
  - The manuscript now derives the calibration derivative from boundary flux; Lean retains its direct
    differentiation proof of the same identity.
  - Its exact Dirichlet estimate also gives the manuscript's coefficient, while the formal maximum theorem retains
    the coarser numerical consequence.
- The main statements of the Challenge are unchanged. These revisions used one agent with the
  formalize-math-paper and humanizer skills; they are revisions and verification, not an independent mathematical
  review.

- The latest round made eight further changes, retaining all nine main Challenge statements:
  - exact wide demand and weighted triangle prices;
  - a terminal margin defined by its two circle gaps;
  - a height determined by equality of the two energy tests;
  - the existing 3–4–5 circle point for the post-floor height range;
  - the integrated envelope moment instead of `1/40`;
  - radius-derived projection and containing-width prices instead of `10/9` and the small-height width allowance;
  - the established angular endpoint for the circle chord, removing `q² = 1/8`;
  - the same generated sine endpoint in the cubic price instead of `14/15`.
- `TiltedBalanceHeight.lean`, `terminalCircleGap_gt_cubicPrice`, `firstExcessMoment_le_short_envelope_moment`, and
  the revised small-tilt constants carry these comparisons through the actual geometric callers.
  - This removes the fitted height `1/20` from the selector and the auxiliary triangle parameter range.
  - It changes auxiliary estimates and the manuscript together.

### Remaining numerical choices

- Several other exclusions still use explicit finite certificates.
- Their constants have been simplified in the preceding pass, but they have not all been replaced by intrinsic
  geometric quantities:

| Remaining family | Role of the numbers |
| --- | --- |
| Intermediate tilt | The comparison uses the existing generated root enclosures and one height endpoint at one third. No support critical point or additional clipping box is needed. |
| Wide preliminary comparison | The first wide width and coarse root enclosures remain. The exact peak span follows from one endpoint price budget. The final bound uses exact demand, reciprocal triangle weights, and a tilt-canceling price. |
| Full and proper triangle bounds | Their width thresholds remain; the height enclosure is now one third. All three floor corrections share one zero-tilt payment and one generated whole-score comparison. The dry-endpoint width comes from the initial-circle radius. Lean retains coarse angle and support enclosures for clipping. |
| Small positive tilt | The 3–4–5 direction and circle radii determine the gains. The height is the energy-balance root, the projection bound comes from radius five, and the leakage moment is the integrated envelope itself. There is one sine-endpoint check and a common pressure-budget payment. The stopping deadline `11/15` and envelope duration `1/3` still use finite enclosure checks. |
| Preliminary terminal angle and width | The angular endpoint remains `3/8`. The calibration width is the diagonal offset `K`; the corner width solves its separation equality at that endpoint. No independent width tolerance remains in these comparisons. |
| Terminal circle and reflected excess | The circle has two generated width checks. Its retained margin is the actual minimum endpoint gap, with the same generated sine bound in the cubic price; the reflected error uses one baseline and an angular budget; its additional angle split and three stopping boxes are gone. The preliminary terminal-angle cut and coarse root enclosures remain. |
| Imported ordinary-sofa benchmark | `2.2199` is the exact decimal enclosure in the imported Gerver-area theorem. |

- The remaining subdivisions and endpoint comparisons are finite arithmetic parts of the proof. Their purpose and
  defining comparisons are stated explicitly.
- The width cuts `37/50` and `8/5`, the cotangent cut `3/8`, and stopping enclosures such as `11/15` remain
  fitted. Replacing them by roots of scalar comparison formulas also requires proving the adjoining clipping and
  stopping estimates on those new domains. That step is unresolved.
- Fractions forced by geometry and integration remain as well; this revision does not claim to eliminate every
  numerical choice.

## Checks after the revisions

- The nine main theorem statements are unchanged.
- The full Lean build passes (9,476 jobs). The audit checks all 5,545 project declarations and all 4,235 copied
  ordinary-sofa declarations; only standard axioms occur.
- Comparator accepts all nine statements under NanoDa and Lean.
- Definition synchronization, exact arithmetic, metadata, Markdown tables, and whitespace checks pass.
- The 109-page manuscript and its 31-entry standalone source archive compile cleanly.
- The revised proof pages have been inspected visually, including the energy-balance height, radius-derived
  small-height prices, natural endpoint circle chord, and exact wide-triangle demand.
- The arithmetic checker covers the current generated enclosures, geometric area payments, stopping comparisons,
  and energy endpoints.

## References

- The bibliography uses mathematical sources.
- The preceding citation check consulted the primary sources for [Romik's construction](https://arxiv.org/abs/1606.08111), [Baek's theorem](https://arxiv.org/abs/2411.19826), [Kallus and Romik's bounds](https://arxiv.org/abs/1706.06630), [Georgiev, Gómez-Serrano, Tao and Wagner](https://arxiv.org/abs/2511.02864), and [O'Keefe's work](https://github.com/devinokeefe/ambidextrous-sofa-bounds).
- This was a targeted citation check rather than an exhaustive literature survey.
