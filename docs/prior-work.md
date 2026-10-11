# Prior work

[Back to the README](../README.md)

The sources below come from a search on 10 October 2026 of arXiv, journal and publisher pages, GitHub repositories
and issue trackers, the Palomar registry, and press and blog coverage.

## The moving sofa problem

- Leo Moser asked for the planar shape of maximal area that can be moved around a right-angled corner in a hallway
  of unit width (Problem 66-11, *Moving furniture through a hallway*, SIAM Review 8 (1966), 381,
  [doi:10.1137/1008074](https://doi.org/10.1137/1008074)). Joseph Gerver constructed a shape of area 2.21953166…
  and conjectured that it is optimal (Geometriae Dedicata 42 (1992), 267-283,
  [doi:10.1007/BF02414066](https://doi.org/10.1007/BF02414066)).
- The prior work on this ordinary problem, with its history, its upper bounds and its formalizations, and the
  related work on verified computations and AI-assisted proofs, is on
  [lean4-moving-sofa's page](https://github.com/vltanh/lean4-moving-sofa/blob/main/docs/prior-work.md). This page
  covers the ambidextrous variant, and Baek's theorem only as a result that the proof here uses.

## The ambidextrous variant and early computations

- Romik's account of the variant (§1.2 of his paper, below) follows I. Stewart, *Another Fine Math You've Got Me
  Into…* (W. H. Freeman, 1992; Dover, 2004). Around the time the problem was posed, John H. Conway, G. C. Shephard
  (Shepard in Romik's paper) and other mathematicians were said to have worked at a geometry conference on the
  problem and on several variants, each apparently assigned to one member of the group.
  - Their rough guesses at the solution were nicknamed the "Conway car" and the "Shepard piano". H. T. Croft, K. J.
    Falconer and R. K. Guy draw a shape that they call the Conway car (*Unsolved Problems in Geometry*, Springer,
    1991, pp. 171-172, [doi:10.1007/978-1-4612-0963-8](https://doi.org/10.1007/978-1-4612-0963-8)).
  - Philip Gibbs, also citing Stewart, places the meeting in Copenhagen in the late 1960s.
- The variant that Romik calls the ambidextrous moving sofa problem asks for the planar shape of maximal area that
  can turn right-angled corners both to the right and to the left in a hallway of width 1. Another variant asks for
  the largest shape that can turn around in a T-junction, and Romik remarks that the two may have the same answer.
- Kiyoshi Maruyama computed polygonal approximations by a heuristic tree search over what he called angularly
  simple polygons, for Moser's hallway and for several others, among them one with a left and a right turn
  (technical report UIUCDCS-R-71-489, University of Illinois, 1971,
  [scan](https://digital.library.unt.edu/ark:/67531/metadc1032476/m2/1/high_res_d/4717606.pdf); *An approximation
  method for solving the sofa problem*, International Journal of Computer and Information Sciences 2 (1973), 29-48,
  [doi:10.1007/BF00987151](https://doi.org/10.1007/BF00987151)).
- Gibbs, in an unrefereed note, *A computational study of sofas and cars*
  ([viXra:1411.0038](https://vixra.org/abs/1411.0038), November 2014), intersected a fixed sofa with N rotated and
  translated copies of the hallway and optimized their positions numerically. For the ordinary problem his
  extrapolated areas agree with Gerver's to nearly eight significant figures.
  - For the left-and-right problem he used copies rotated through angles in [0°, 90°] and in [270°, 360°], so that
    both turns start from the same placement.
  - He found a shape with a four-fold symmetry that he had not imposed, nicknamed "the bikini", of area 1.64495,
    and expected its curves to be given by Gerver's equations with other constants.
  - He wrote that his computations support the conjecture that the same shape is optimal for the T-junction
    problem.

## Romik's ambidextrous sofa

- Dan Romik, *Differential equations and exact solutions in the moving sofa problem*, Experimental Mathematics 27
  (2018), 316-330 ([doi:10.1080/10586458.2016.1270858](https://doi.org/10.1080/10586458.2016.1270858);
  [arXiv:1606.08111](https://arxiv.org/abs/1606.08111), June 2016, revised July 2016).
  - Extending Gerver's method, Romik derives six differential equations from the maximality of the area and
    recovers Gerver's sofa from them.
  - He constructs a shape "that we propose as a possible solution to the ambidextrous moving sofa problem"
    (abstract).
  - A Mathematica package, MovingSofas, accompanies the paper for checking some of its computations
    ([Romik's page](https://www.math.ucdavis.edu/~romik/movingsofa/)).
- He restricts to motions that rotate the shape monotonically from 0 to π/2, and makes assumptions on the rotation
  path, among them symmetry, smoothness, and three phases of contact separated at a critical angle β.
- The shape `Σ = S_x ∩ ρ(S_x)` intersects the shape `S_x` of a rotation path `x` with its image under the
  reflection `ρ` in the line `y = 1/2`.
  - His Theorem 5 states that Σ can move around corners both to the left and to the right, and that `x` is the
    unique rotation path that satisfies his assumptions and the necessary conditions of his differential equations
    at every angle other than β and π/2 − β.
  - The boundary of Σ consists of 18 curves, pieces of circles and of sextic curves.
- The area of Σ is `∛(3 + 2√2) + ∛(3 − 2√2) − 1 + arctan(½(∛(√2 + 1) − ∛(√2 − 1))) ≈ 1.644955218425440`.
  - He also writes it `X + arctan Y`, where `X` and `Y` are the real roots of `x²(x + 3) = 8` and `x(4x² + 3) = 1`;
    the arctan term is the critical angle β.
  - He notes that Σ looks the same as Gibbs's numerical shape and that its area agrees with Gibbs's 1.64495.
- He calls Σ "a highly plausible candidate to be the solution" (§5). Problem 1 of his open problems (§7) asks to
  prove that Gerver's sofa and Σ are local maxima of the area in their problems; he does not conjecture global
  optimality.

## Upper bounds and Baek's theorem

- Yoav Kallus and Dan Romik proved with computer assistance that every moving sofa has area at most 2.37 (*Improved
  upper bounds in the moving sofa problem*, Advances in Mathematics 340 (2018), 960-982,
  [doi:10.1016/j.aim.2018.10.022](https://doi.org/10.1016/j.aim.2018.10.022);
  [arXiv:1706.06630](https://arxiv.org/abs/1706.06630)).
  - They note that Romik's constant is a lower bound for the ambidextrous problem, and that any upper bound for the
    ordinary problem, 2.37 included, is also an upper bound for it.
  - They suggest extending their method to the ambidextrous problem.
- Jineon Baek, *Optimality of Gerver's sofa*, [arXiv:2411.19826](https://arxiv.org/abs/2411.19826) (preprint,
  submitted 29 November 2024, 119 pages), proves that Gerver's sofa has maximal area.
  - The paper does not mention the ambidextrous variant. With Kallus and Romik's remark, it bounds the area of
    every ambidextrous sofa by Gerver's area 2.2195…, and the proof in this repository uses the theorem
    ([below](#this-repository)).
  - On 10 October 2026 the paper is a preprint: arXiv lists one version and no journal reference, and the list of
    forthcoming papers of the Annals of Mathematics does not include it
    ([list](https://annals.math.princeton.edu/toappear)).
  - Press reports of January 2026 said that it was under review there
    ([Korea Herald](https://www.koreaherald.com/article/10648326)), and Quanta Magazine reported in February 2025
    that the proof was "still being peer-reviewed"
    ([Quanta](https://www.quantamagazine.org/the-largest-sofa-you-can-move-around-a-corner-20250214/)).
  - Romik's page says that the problem was "solved by Jineon Baek in 2024" and lists the paper as a preprint
    ([Romik's page](https://danromik.com/pages/sofas.html)). Georgiev, Gómez-Serrano, Tao and Wagner write that
    Baek "showed that this bound was sharp" ([arXiv:2511.02864](https://arxiv.org/abs/2511.02864)).
- Three Lean formalizations of Baek's theorem were posted in September and October 2026: Dean Cureton's
  [MovingSofa](https://github.com/deancureton/MovingSofa), Ruifeng Cao's
  [sofa-formal](https://github.com/RuifengCao/sofa-formal) and
  [lean4-moving-sofa](https://github.com/vltanh/lean4-moving-sofa), whose prior-work page describes them. This
  repository uses the one in lean4-moving-sofa.

## The ambidextrous problem as an open problem

- John Baez wrote in December 2016: "Nobody has proved his solution is optimal. We're not even sure that it's
  locally optimal"
  ([AMS Visual Insight](https://blogs.ams.org/visualinsight/2016/12/15/romiks-ambidextrous-sofa/)).
- Zhipeng Deng's preprint *Solving moving sofa problem using calculus of variations*
  ([arXiv:2407.02587](https://arxiv.org/abs/2407.02587), July 2024) assumes that the trajectories and envelopes are
  convex, and states that Gerver's sofa and "Romik's car" satisfy the Euler-Lagrange equations, a necessary
  condition for maximal area.
  - Its concluding section says that it addressed Romik's question of local maximality, and also that "We need to
    calculate the second variation".
- Romik called his sofa "a good candidate to be a solution" in a talk in 2024
  ([slides](https://sites.lsa.umich.edu/speyer/wp-content/uploads/sites/1332/2024/08/Romik.pdf)), and his page
  describes its area as one "which may be the largest possible area".
- Bogdan Georgiev, Javier Gómez-Serrano, Terence Tao and Adam Zsolt Wagner, *Mathematical exploration and discovery
  at scale*, [arXiv:2511.02864](https://arxiv.org/abs/2511.02864) (version 3, December 2025, preprint), list the
  problem as Problem 6.63, "Ambidextrous sofa (Conway's car)": the largest area of a connected shape that can pass
  a left-turning and a right-turning corner of unit width.
  - They write that "Romik introduced the 'Romik sofa' that produced a lower bound 1.6449… . It remains open
    whether this bound is sharp."
  - Their statement does not require the two passages to start in the same orientation. Without that condition the
    answer would be Gerver's area, since Gerver's sofa, which is symmetric in a vertical line, passes the
    left-turning hallway after a half turn ([Definitions](definitions.md#ambidextrous-sofas)).
- On 19 September 2026 an issue and a pull request proposed adding the problem to Google DeepMind's
  formal-conjectures repository ([issue #6423](https://github.com/google-deepmind/formal-conjectures/issues/6423);
  [pull request #6424](https://github.com/google-deepmind/formal-conjectures/pull/6424)); both were open on 10
  October 2026.
  - The pull request defines an ambidextrous sofa as a moving sofa, in the sense of the repository's
    [statement of the ordinary problem](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/MovingSofa.lean),
    whose reflection in the line `y = 1/2` is also a moving sofa. Since both motions start at the identity, the two
    passages start from the same placement.
  - It defines Romik's area as `X + arctan Y` without defining his shape, states the lower bound as solved and
    leaves its proof as `sorry`, and states the equality as open ("Even its local optimality is open").
  - It proves that the ambidextrous constant is at most the ordinary one. Its author writes: "AI was used to draft
    this proof, but we hand-edited it."
- Three repositories give upper bounds or partial results for the ambidextrous problem; none reports a peer review.
  - Devin O'Keefe's [ambidextrous-sofa-bounds](https://github.com/devinokeefe/ambidextrous-sofa-bounds), which
    contains a paper, states: "We prove with computer assistance that every ambidextrous sofa has area at most
    353/200 = 1.765, and give a computer-free proof of the bound 2√2 − 1 = 1.8284…". The bound 2√2 − 1 is proved in
    Lean.
    - For 353/200, a Lean theorem says that the bound holds if a checker written in Lean accepts a certificate. The
      compiled checker accepted a certificate of 1.7 GB with 436,160,442 leaves in about 13 minutes on 28 September
      2026.
    - The paper lists what this route trusts: the Lean kernel, the Lean compiler and runtime, including the C
      compiler, the few unverified lines that read the certificate file, and the formal definitions, which are
      copied from formal-conjectures and from pull request #6424.
    - It states that Claude Opus 5.5 and GPT-6 Pro helped develop the arguments and write the programs, the Lean
      formalization and the paper.
  - [larskarbo/ambidextrous-sofa-174](https://github.com/larskarbo/ambidextrous-sofa-174), created on 10 October
    2026, claims the bound 1.74, obtained by adding a test to O'Keefe's C checker. It states that an AI agent,
    Claude, did the work and that the result is "not peer reviewed, and not formalised in Lean".
  - Vico Bonfioli's [moving-sofa-local-max](https://github.com/ElVec1o/moving-sofa-local-max)
    ([Zenodo](https://doi.org/10.5281/zenodo.20434287)), *The ambidextrous moving sofa problem: separation,
    constants, and obstructions*, describes itself as "Not a claim of a solved problem" and lists the optimality of
    Romik's sofa as open.
    - Some of its lemmas, on the two niches of the shape and on connectedness, are checked in Lean; its C²-local
      main theorem and its upper bound 2√2 − 1, proved by hand with a ball certificate, are not.

## Numerical searches and related variants

- AlphaEvolve, in the work of Georgiev, Gómez-Serrano, Tao and Wagner, evolves programs that propose a path of
  translations and rotations. Evaluation code then computes the largest sofa that fits along the path, as an
  intersection of hallway polygons computed with the Python library shapely.
  - It found Romik's sofa within 1.5% when the experiments stopped, and the paper reports no larger shape.
  - Its runs for the ambidextrous problem include a T-junction corridor, with area 1.6226, and a corridor that
    turns twice, with area 1.5995.
  - The public notebook says that the sofas may "clip into the wall slightly" because of the discrete steps, and
    that "none of the final intersection values should be taken as rigorous lower bounds"
    ([notebook](https://github.com/google-deepmind/alphaevolve_repository_of_problems/blob/main/experiments/the_2d_moving_sofa/the_2d_moving_sofa.ipynb)).
- Xingyi He computed locally optimal areas for corridors whose corner has an angle between 15° and 150°
  ([arXiv:2608.11206](https://arxiv.org/abs/2608.11206), 2026, preprint).

## This repository

- This repository proves in Lean 4 that Romik's sofa is optimal and, up to congruence, the only optimal shape.
  - Every ambidextrous sofa, in the sense of the [definitions](definitions.md#ambidextrous-sofas), has area at most
    `M = 1 + 4Y² + arctan Y = 1.64495…`, where `Y` is the positive root of `4Y³ + 3Y = 1`.
  - An ambidextrous sofa of area `M` is a rotated and translated copy of Romik's sofa, and each of its two motions
    makes a full quarter turn (`quarter_turns`).
- After a rigid normalization that puts a sofa in the strip `0 ≤ y ≤ 1`, the proof splits its convex hull into two
  caps, one for each hallway, and bounds the area of the sofa by the sum of their scores.
  - The score of each cap is at most `M/2`, with equality only for a full quarter turn and a translate of Romik's
    cap.
  - When the area is `M`, both caps are Romik's, and an exact identity for the deficit recovers the sofa from them.
- Two steps of the proof use the bound `22199/10000` that Baek's theorem, with a bound on the area of Gerver's
  sofa, gives for the ordinary problem. The Lean formalization of Baek's theorem comes from
  [lean4-moving-sofa](https://github.com/vltanh/lean4-moving-sofa) and is copied into
  [`MovingSofaOptimality/`](../MovingSofaOptimality/README.md).
- ChatGPT Pro 6 found the proof in October 2026 and wrote an uncompiled Lean draft of it, which Claude Opus 5.5
  made compile. No person has checked the proofs; Lean's kernel checks all of them.
- The [archive](archive/README.md) keeps the manuscript that ChatGPT Pro 6's research notes ended with, as a record
  of where the proof came from, and says where the notes are.
