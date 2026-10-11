# Prior work

[Back to the README](../README.md)

The sources below come from a search on 10 October 2026 of arXiv, journal and publisher pages, GitHub
repositories and issue trackers, the Palomar registry, and press and blog coverage, for work on the moving
sofa problem and its ambidextrous variant, on computer-assisted and formally verified proofs, and on
AI-assisted mathematics.

## The moving sofa problem

Leo Moser posed the moving sofa problem as Problem 66-11, *Moving furniture through a hallway*, SIAM Review 8
(1966), 381 ([doi:10.1137/1008074](https://doi.org/10.1137/1008074)). In Dan Romik's words it asks for "the
planar shape of maximal area that can be moved around a right-angled corner in a hallway of unit width"
([Romik 2018](https://arxiv.org/abs/1606.08111), §1.1). J. M. Hammersley set it as Problem 8 in Appendix IV of
*On the enfeeblement of mathematical skills by "Modern Mathematics" and by similar soft intellectual trash in
schools and universities*, Bulletin of the Institute of Mathematics and its Applications 4 (1968), 66-85
([scan](https://archive.org/details/hammersley1968)). The solver is asked to prove that the area is less than
2√2 and to show that a suitable shape of area π/2 + 2/π ≈ 2.2074 can be moved around the corner, and the
problem ends: "Is this the largest possible value for A?" Hammersley's shape consists of two quarter-discs of
radius 1 separated by a 4/π × 1 block, with a half-disc of radius 2/π removed. Romik reports that shapes of
slightly larger area were found later (R. K. Guy, American Mathematical Monthly 84 (1977),
[doi:10.1080/00029890.1977.11994487](https://doi.org/10.1080/00029890.1977.11994487)), and 2√2 ≈ 2.83 remained
the best upper bound until Kallus and Romik's 2.37 (below). SIAM Review printed two follow-ups to Moser's
problem, by Michael Goldberg (1969, [doi:10.1137/1011013](https://doi.org/10.1137/1011013)) and James D.
Sebastian (1970, [doi:10.1137/1012114](https://doi.org/10.1137/1012114)), and W. E. Howden searched by
computer for the largest rectangle of a given width that can turn the corner (The Computer Journal 11 (1968),
299-301, [doi:10.1093/comjnl/11.3.299](https://doi.org/10.1093/comjnl/11.3.299)).

Joseph Gerver, *On moving a sofa around a corner*, Geometriae Dedicata 42 (1992), 267-283
([doi:10.1007/BF02414066](https://doi.org/10.1007/BF02414066)), constructed a shape of area 2.21953166… whose
boundary consists of 3 line segments and 15 curved pieces, and conjectured that it has maximal area. He
derived it from a local condition: he proved that a sofa of maximal area is a limit of polygons that he calls
balanced, and showed that his shape satisfies the same condition. The shape depends on four constants that are
defined only implicitly, by four nonlinear equations, and neither the shape nor its area has a known closed
form ([Romik 2018](https://arxiv.org/abs/1606.08111), §1.1). Gerver also proved that the motion of a sofa of
maximal area can be taken to rotate it monotonically from 0 to an angle between π/3 and π/2
([Kallus and Romik 2018](https://arxiv.org/abs/1706.06630), §1). Baek later pointed out that Gerver's argument
does not address the connectedness of the sofa, and reproved the balance condition
([Baek 2024](https://arxiv.org/abs/2411.19826), §1.1). Romik attributes the existence of a sofa of maximal
area to Conway and M. Guy and knows of no printed proof of it other than Gerver's; he also recounts, after
Stewart, that B. F. Logan had found Gerver's shape in 1976 without publishing it. The problem appears in H. T.
Croft, K. J. Falconer and R. K. Guy, *Unsolved Problems in Geometry* (Springer, 1991), pp. 171-172
([doi:10.1007/978-1-4612-0963-8](https://doi.org/10.1007/978-1-4612-0963-8)), in S. R. Finch, *Mathematical
Constants* (Cambridge University Press, 2003), §8.12, and in I. Stewart, *Another Fine Math You've Got Me
Into…* (W. H. Freeman, 1992; Dover, 2004).

## The ambidextrous variant and early computations

Romik's account of the variant (§1.2) rests on Stewart's book. Around the time the problem was posed, John H.
Conway, G. C. Shephard (Shepard in Romik's paper) and several other mathematicians "were said to have worked
on the problem during a geometry conference, as well as on several other variants of the problem, each of
which was apparently assigned to one member of the group". Their rough guesses at the solution were nicknamed
the "Conway car" and the "Shepard piano", and Croft, Falconer and Guy draw a shape that they call the Conway
car. One variant, which Romik calls the ambidextrous moving sofa problem, "asks for the planar shape of
maximal area that can negotiate right-angled turns both to the right and to the left in a hallway of width 1";
another asks for the largest shape that can turn around in a T-junction, and Romik remarks that "the answer to
both versions may be the same". Philip Gibbs, also citing Stewart, places the meeting in Copenhagen in the
late 1960s.

Kiyoshi Maruyama computed polygonal approximations by a heuristic tree search over what he called angularly
simple polygons, for Moser's hallway and for several other hallways, among them one with a left and a right
turn (technical report UIUCDCS-R-71-489, University of Illinois, 1971,
[scan](https://digital.library.unt.edu/ark:/67531/metadc1032476/m2/1/high_res_d/4717606.pdf); *An
approximation method for solving the sofa problem*, International Journal of Computer and Information Sciences
2 (1973), 29-48, [doi:10.1007/BF00987151](https://doi.org/10.1007/BF00987151)). For Moser's hallway his shapes
reached about 90% of the area of Hammersley's. Gibbs, in an unrefereed note, *A computational study of sofas
and cars* ([viXra:1411.0038](https://vixra.org/abs/1411.0038), November 2014), fixed the sofa, intersected it
with N rotated and translated copies of the hallway, and optimized their positions numerically. For the
ordinary problem his extrapolated areas agree with Gerver's "to nearly eight significant figures". For the
left-and-right problem he intersected the shape with copies rotated through angles in [0°, 90°] and in
[270°, 360°], so that both turns start from the same placement, found a shape with a four-fold symmetry that
he had not imposed, which he nicknamed "the bikini", and computed its area as 1.64495. He expected its curves
to be given by Gerver's equations with other constants, and wrote that his computations support the conjecture
that the same shape is optimal for the T-junction problem.

## Romik's ambidextrous sofa

Dan Romik, *Differential equations and exact solutions in the moving sofa problem*, Experimental Mathematics
27 (2018), 316-330 ([doi:10.1080/10586458.2016.1270858](https://doi.org/10.1080/10586458.2016.1270858);
[arXiv:1606.08111](https://arxiv.org/abs/1606.08111), June 2016, revised July 2016). Extending Gerver's
method, Romik derives six differential equations from the maximality of the area, recovers Gerver's sofa from
them, and constructs a shape "that we propose as a possible solution to the ambidextrous moving sofa problem"
(abstract). He restricts to motions that rotate the shape monotonically from 0 to π/2, and makes assumptions
on the rotation path, among them symmetry, smoothness, and three phases of contact separated at a critical
angle β. The shape, `Σ = S_x ∩ ρ(S_x)`, intersects the shape `S_x` of a rotation path `x` with its image under
the reflection `ρ` in the line `y = 1/2`. His Theorem 5 states that Σ can move around corners both to the left
and to the right, and that `x` is the unique rotation path that satisfies his assumptions and the necessary
conditions of his differential equations at every angle other than β and π/2 − β. The boundary of Σ consists
of 18 curves, pieces of circles and of sextic curves, and its area is

  `∛(3 + 2√2) + ∛(3 − 2√2) − 1 + arctan(½(∛(√2 + 1) − ∛(√2 − 1))) ≈ 1.644955218425440`,

which he also writes `X + arctan Y`, with `x²(x + 3) = 8` and `x(4x² + 3) = 1`; the arctan term is the
critical angle β. Romik notes that the shape looks the same as Gibbs's numerical one and that its area agrees
with Gibbs's 1.64495. He calls it "a plausible candidate to be the solution" (§1.2) and "a highly plausible
candidate to be the solution" (§5). Problem 1 of his open problems (§7) asks to prove that Gerver's sofa and Σ
are local maxima of the area in their problems; he does not conjecture global optimality. A Mathematica
package, MovingSofas, accompanies the paper for checking some of its computations
([Romik's page](https://www.math.ucdavis.edu/~romik/movingsofa/)).

## Upper bounds and the optimality of Gerver's sofa

Yoav Kallus and Dan Romik, *Improved upper bounds in the moving sofa problem*, Advances in Mathematics 340
(2018), 960-982 ([doi:10.1016/j.aim.2018.10.022](https://doi.org/10.1016/j.aim.2018.10.022);
[arXiv:1706.06630](https://arxiv.org/abs/1706.06630)), prove with computer assistance that every moving sofa
has area at most 2.37 and that a sofa of maximal area rotates by at least arcsin(84/85) ≈ 81.2°; they
conjecture that it rotates by π/2. They note that Romik's constant is a lower bound for the ambidextrous
problem and that "any upper bound for the original problem is also an upper bound for the ambidextrous variant
of the problem, which establishes 2.37 as a valid upper bound for that problem", and they suggest extending
their method to the ambidextrous problem. Kuangdai Leng, Jia Bi, Jaehoon Cha, Samuel Pinilla and Jeyan
Thiyagalingam (Symmetry 16 (2024), 1388, [doi:10.3390/sym16101388](https://doi.org/10.3390/sym16101388))
recomputed these relaxations in double precision: with 2,100 angles the values come within 0.01% of Gerver's
area, and for the five angles of the bound 2.37 their results "suggest a tighter upper bound of 2.3337".
Jineon Baek proved without computer assistance the bound 1 + π²/8 ≈ 2.2337 for sofas that satisfy an
"injectivity condition", which Gerver's sofa satisfies, in a preprint that he withdrew in December 2024 as
superseded ([arXiv:2406.10725](https://arxiv.org/abs/2406.10725)). The abstract of a talk he gave in February
2024 announced a computer-assisted bound of 2.32
([abstract](https://www.mathematics.pitt.edu/content/moving-sofa-problem)); the search found no paper with
that bound.

Jineon Baek, *Optimality of Gerver's sofa*, [arXiv:2411.19826](https://arxiv.org/abs/2411.19826) (preprint,
submitted 29 November 2024, 119 pages), proves that Gerver's sofa has maximal area. He defines a moving sofa
as a translate of a nonempty, connected, closed subset of the horizontal arm `(−∞, 1] × [0, 1]` that a
continuous rigid motion inside the hallway moves into the vertical arm `[0, 1] × (−∞, 1]`. The proof shows
that a sofa of maximal area can be taken to be monotone and balanced and to rotate by π/2; proves an
injectivity condition, that the path of the hallway's inner corner, seen from the sofa, has no self-loops,
with a differential inequality inspired by an equation of Romik; and bounds the area of every sofa with that
condition by a quadratic functional of a triple of convex bodies, written with Green's theorem and
Brunn-Minkowski mixed areas. Mamikon's theorem shows that the functional is concave, Romik's local-optimality
equations show that its directional derivatives at Gerver's sofa are at most 0, and the functional equals the
area at Gerver's sofa. The proof "does not require computer assistance, except for numerical computations that
can be done on a scientific calculator"; an earlier, computer-assisted version of it used the program
[sofa-designer](https://github.com/jcpaik/sofa-designer). The paper does not mention the ambidextrous variant.
Together with Kallus and Romik's remark, Baek's theorem bounds the area of every ambidextrous sofa by Gerver's
area 2.2195….

On 10 October 2026 the paper is a preprint. arXiv lists one version and no journal reference, the list of
forthcoming papers of the Annals of Mathematics does not include it
([list](https://annals.math.princeton.edu/toappear)), and press reports of January 2026 said that it was under
review there ([Korea Herald](https://www.koreaherald.com/article/10648326)). Romik's page says that the
problem was "solved by Jineon Baek in 2024" and lists the paper as a preprint
([Romik's page](https://danromik.com/pages/sofas.html)); Georgiev, Gómez-Serrano, Tao and Wagner write that
Baek "showed that this bound was sharp" ([arXiv:2511.02864](https://arxiv.org/abs/2511.02864)); Quanta
Magazine reported in February 2025 that the proof was "still being peer-reviewed"
([Quanta](https://www.quantamagazine.org/the-largest-sofa-you-can-move-around-a-corner-20250214/)). Three Lean
formalizations of the theorem were posted in September and October 2026
([below](#formalizations-of-the-moving-sofa-problem)).

## The ambidextrous problem as an open problem

John Baez wrote in December 2016 that "Nobody has proved his solution is optimal. We're not even sure that
it's locally optimal" (blog post,
[AMS Visual Insight](https://blogs.ams.org/visualinsight/2016/12/15/romiks-ambidextrous-sofa/)). Zhipeng
Deng's preprint *Solving moving sofa problem using calculus of variations*
([arXiv:2407.02587](https://arxiv.org/abs/2407.02587), July 2024) assumes that the trajectories and envelopes
are convex and states that Gerver's sofa and "Romik's car" satisfy the Euler-Lagrange equations, a necessary
condition for maximal area. Its concluding section says that it addressed Romik's question of local
maximality, and also that "We need to calculate the second variation". Romik called the shape "a good
candidate to be a solution" in a talk in 2024
([slides](https://sites.lsa.umich.edu/speyer/wp-content/uploads/sites/1332/2024/08/Romik.pdf)), and his page
describes its area as one "which may be the largest possible area"
([Romik's page](https://danromik.com/pages/sofas.html)).

Bogdan Georgiev, Javier Gómez-Serrano, Terence Tao and Adam Zsolt Wagner, *Mathematical exploration and
discovery at scale*, [arXiv:2511.02864](https://arxiv.org/abs/2511.02864) (version 3, December 2025,
preprint), list it as Problem 6.63 ("Ambidextrous sofa (Conway's car)"): the largest area of a connected shape
that can pass a left-turning and a right-turning corner of unit width. They write that "Romik introduced the
'Romik sofa' that produced a lower bound 1.6449… . It remains open whether this bound is sharp." Their
statement does not say that the two passages start in the same orientation; without that condition the answer
would be Gerver's area, since Gerver's sofa, which is symmetric in a vertical line, passes the left-turning
hallway after a half turn ([Definitions](definitions.md#ambidextrous-sofas)). The paper reports that
AlphaEvolve found Romik's sofa "up to a very small error", within 1.5%, when the experiments stopped
([below](#computer-assisted-bounds-and-their-certificates)).

On 19 September 2026 an issue and a pull request proposed adding the problem to Google DeepMind's
formal-conjectures repository
([issue #6423](https://github.com/google-deepmind/formal-conjectures/issues/6423);
[pull request #6424](https://github.com/google-deepmind/formal-conjectures/pull/6424)); both were open on 10
October 2026. The pull request defines an ambidextrous sofa as a set that is a moving sofa, in the sense of
the repository's statement of the ordinary problem ([below](#formalizations-of-the-moving-sofa-problem)), and
whose reflection in the line `y = 1/2` is also a moving sofa; since both motions start at the identity, the
two passages start from the same placement. It defines Romik's area as `X + arctan Y`, without defining his
shape, states the lower bound as solved and leaves its proof as `sorry`, states the equality as open ("Even
its local optimality is open"), and proves that the ambidextrous constant is at most the ordinary one. Its
author writes: "AI was used to draft this proof, but we hand-edited it."

Three repositories give upper bounds or partial results for the ambidextrous problem; none reports a peer
review. Devin O'Keefe's [ambidextrous-sofa-bounds](https://github.com/devinokeefe/ambidextrous-sofa-bounds),
which contains a paper, states: "We prove with computer assistance that every ambidextrous sofa has area at
most 353/200 = 1.765, and give a computer-free proof of the bound 2√2 − 1 = 1.8284…". The bound 2√2 − 1 is
proved in Lean. For 353/200, a Lean theorem says that the bound holds if a checker written in Lean accepts a
certificate, and the compiled checker accepted a certificate of 1.7 GB with 436,160,442 leaves in about 13
minutes on 28 September 2026. The paper lists what this route trusts: the Lean kernel, the Lean compiler and
runtime, including the C compiler, the few unverified lines that read the certificate file, and the formal
definitions, which are copied from formal-conjectures and from pull request #6424. It states that Claude Opus
5.5 and GPT-6 Pro helped develop the arguments and write the programs, the Lean formalization and the paper.
The repository [larskarbo/ambidextrous-sofa-174](https://github.com/larskarbo/ambidextrous-sofa-174), created
on 10 October 2026, claims the bound 1.74, obtained by adding a test to O'Keefe's C checker; it states that an
AI agent, Claude, did the work and that the result is "not peer reviewed, and not formalised in Lean". Vico
Bonfioli's [moving-sofa-local-max](https://github.com/ElVec1o/moving-sofa-local-max)
([Zenodo](https://doi.org/10.5281/zenodo.20434287)), *The ambidextrous moving sofa problem: separation,
constants, and obstructions*, describes itself as "Not a claim of a solved problem" and lists the optimality
of Romik's sofa as open. Some of its lemmas, on the two niches of the shape and on connectedness, are checked
in Lean; its C²-local main theorem and its upper bound 2√2 − 1, proved by hand with a ball certificate, are
not.

Other variants have numerical results and conjectures. Gibbs and Romik suggest that the T-junction problem has
the same answer as the ambidextrous one. Xingyi He computed locally optimal areas for corridors whose corner
has an angle between 15° and 150° ([arXiv:2608.11206](https://arxiv.org/abs/2608.11206), 2026, preprint).
Hammersley suggested a three-dimensional version in 1968, and Georgiev, Gómez-Serrano, Tao and Wagner treat a
corridor that turns in two perpendicular planes (Problem 6.64, below). For hallways of unequal widths, results
exist for rectangles and boxes (Oleg Mushkarov and Nikolai Nikolov,
[arXiv:2604.01174](https://arxiv.org/abs/2604.01174), 2026, preprint).

## Computer-assisted bounds and their certificates

Kallus and Romik bound the sofa constant by relaxations with finitely many angles. For given angles they
maximize, over the positions of the hallway at these angles, the area of the largest connected component of
the intersection of the horizontal arm with the rotated and translated hallways and with a "butterfly set"
that contains the vertical arm at every final angle in a given range. These maxima bound the area of a sofa
from above and, for equally spaced angles, converge to the sofa constant. A geometric branch and bound
computes them. A lemma gives a box of positions that contains a maximizer; the program splits it into
sub-boxes, bounds the area on each sub-box by replacing each hallway with the union of its translates over the
sub-box, evaluates the area at midpoints, and discards a sub-box once its bound falls below the best value
found. The program, SofaBounds ([repository](https://github.com/ykallus/SofaBounds), C++, MIT license),
computes with CGAL's Nef polygons in exact rational arithmetic, so the angles must have rational sines and
cosines and are entered as Pythagorean triples; 45°, for instance, is replaced by the angle of the triple
(119, 120, 169), about 44.76°. The bound 2.37, for five angles, took 480 hours and 7,724,162 iterations on one
core. Three inequalities with bound 2.21, from which the rotation bound of 81.2° follows, took between 2
minutes and 6 hours 23 minutes.

The certificate is the run itself: the paper names the program and four parameter files, which contain only
the angles and options, and the program prints each bound as an exact rational. The bounds rest on the
program, on CGAL and GMP, and on the lemmas that set up the search. In July 2019 a user reported in the
repository's issue tracker that the a priori box was too small in the case of final angle π/2, the case of the
2.37 run, in the code and in the paper ("This seems to be a mistake in the paper"), and the authors corrected
the code in September 2019 ([issue #1](https://github.com/ykallus/SofaBounds/issues/1);
[pull request #2](https://github.com/ykallus/SofaBounds/pull/2)). The issue thread records no later run of the
2.37 computation with the corrected box. The three inequalities behind the rotation bound have final angles
below π/2 and do not use that case, and Baek's theorem, if it holds, implies the bound 2.37 without the
computation.

Baek's [sofa-designer](https://github.com/jcpaik/sofa-designer), which its README describes as still in
development, takes the same approach with a custom geometric branch and bound and CGAL's exact rational
quadratic-programming solver. For hallways at finitely many angles with rational cosines and sines it
enumerates the possible intersections and proves lower and upper bounds on linear functionals of the hallway
positions, and it can also bound the area of any sofa that rotates by 90°. Leng et al.'s values come from
gradient-based optimization in double precision and carry no certificate. Maruyama's and Gibbs's computations
are heuristic searches, as are the numerical studies of Michał Batsch (Symmetry 14 (2022), 1409,
[doi:10.3390/sym14071409](https://doi.org/10.3390/sym14071409)) and of He, which reproduce Gerver's sofa.

AlphaEvolve, in the work of Georgiev, Gómez-Serrano, Tao and Wagner, evolves programs that propose a path of
translations and rotations; evaluation code then computes the largest sofa that fits along the path, as an
intersection of hallway polygons computed with the Python library shapely. It found Gerver's sofa within 0.02%
and Romik's within 1.5%, and the paper reports no larger shape. The public notebook says that the sofas may
"clip into the wall slightly" because of the discrete steps and that "none of the final intersection values
should be taken as rigorous lower bounds"
([notebook](https://github.com/google-deepmind/alphaevolve_repository_of_problems/blob/main/experiments/the_2d_moving_sofa/the_2d_moving_sofa.ipynb));
its runs for the ambidextrous problem include a T-junction corridor, with area 1.6226, and a corridor that
turns twice, with area 1.5995. For the three-dimensional sofa of Problem 6.64 the paper gives the volume 1.81
as a rigorous lower bound, with an estimate of 1.84.

Bounds for several other extremal problems in plane geometry have been proved the same way, with finitely many
test shapes and a subdivision of their placements, and their certificates range from a recomputation in high
precision to a proof checked by a kernel. Baez, Bagdasaryan and Gibbs lowered the upper bound for Lebesgue's
universal covering problem to 0.8441153 with a double-precision computation that Greg Egan rechecked with
2000-digit arithmetic in Mathematica (Journal of Computational Geometry 6 (2015), 288-299,
[arXiv:1502.01251](https://arxiv.org/abs/1502.01251)). Xie's 2026 preprint proves the lower bound 0.833 for
convex covers from records in outward-rounded interval arithmetic
([arXiv:2606.04458](https://arxiv.org/abs/2606.04458)), and Markót proved the optimality of packings of 31, 32
and 33 equal circles in a square by interval branch and bound (Journal of Global Optimization 81 (2021),
773-803, [open access](https://pmc.ncbi.nlm.nih.gov/articles/PMC8550790/)). For Moser's worm problem, Keller
proved 0.239 ≤ α ≤ 0.24633… for convex covers of all unit arcs
([arXiv:2609.21968](https://arxiv.org/abs/2609.21968), September 2026, preprint). His search programs, in
floating point, produce rational certificates that are exported as Lean declarations and checked by the kernel
with `decide +kernel`, so the correctness of the search programs is not assumed; the certificate for the lower
bound is a tree of about a million nodes in 24,287 generated Lean modules, checked in about four hours on 64
CPUs ([repository](https://github.com/ethan-keller/moser-worm-improved-bounds)). In Kallus and Romik's proof
the run of an exact-arithmetic program is the certificate; in Keller's the kernel checks the certificate and
the lemmas that reduce the problem to it.

## Formalizations of the moving sofa problem

Google DeepMind's formal-conjectures repository, a collection of Lean statements of open and solved problems,
states the moving sofa problem in
[`FormalConjectures/Wikipedia/MovingSofa.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/MovingSofa.lean),
added in March 2026. A moving sofa is a closed connected subset of the horizontal arm `(−∞, 1] × [0, 1]` with
a continuous path of rigid motions, starting at the identity, that keeps it in the hallway and ends with it in
the vertical arm `[0, 1] × (−∞, 1]`. `sofaConstant` is the supremum of the areas of moving sofas, and
`gerversSofa` is built from the unique solution of the four equations for Gerver's constants, as Romik writes
them. The file was corrected twice in 2026: the uniqueness of Gerver's sofa was restated up to a rigid motion
in August ([pull request #4852](https://github.com/google-deepmind/formal-conjectures/pull/4852)), and the
order of translation and rotation in a motion was fixed in September
([pull request #5827](https://github.com/google-deepmind/formal-conjectures/pull/5827)). On 10 October 2026
the file marks `sofaConstant = volume gerversSofa` as solved, with links to two formal proofs, and the
uniqueness of Gerver's sofa up to congruence as open; it has no ambidextrous statement.

The formal proofs below are in unreviewed repositories. Dawid Trela's
[GerverSofaLean](https://github.com/dawidmtrela-dotcom/GerverSofaLean) proves that Gerver's constants exist
and are unique (release v1.0.0, 4 September 2026), with 8,713 interval obligations closed by `decide +kernel`
through the LeanCert library, and that Gerver's sofa is a moving sofa (v1.1.0, 13 September 2026). Two
formalizations of Baek's theorem followed in the same month, and both prove
`sofaConstant = volume gerversSofa` with only the axioms `propext`, `Classical.choice` and `Quot.sound`. Dean
Cureton's [MovingSofa](https://github.com/deancureton/MovingSofa) (release v1.0.0, 20 September 2026) has
about 66,000 lines "written in about four days by AI coding agents (OpenAI Codex and Claude Code), directed by
Dean Cureton". Its README reports that Comparator accepts it with the NanoDa kernel, that formalizing the
paper turned up 11 small errors or gaps and 33 misprints, none of which breaks the main theorem, and that the
area of Gerver's sofa is proved to be at least 11/5 without its value 2.2195… being checked; its metadata
states that "No human expert has reviewed the mathematics". It builds on Trela's library, and Lean Pool, an
archive of formalized mathematics maintained by AI agents, imported it on 29 September 2026. Ruifeng Cao's
[sofa-formal](https://github.com/RuifengCao/sofa-formal) (v1.0.0, 23 September 2026) also proves the existence
and uniqueness of Gerver's constants with kernel interval arithmetic, that Gerver's sofa is a moving sofa, and
Hammersley's bounds π/2 + 2/π ≤ `sofaConstant` ≤ 2√2. It replaces the paper's uses of Green's theorem and of
the Jordan curve theorem by explicit area computations, and it records the uniqueness of Gerver's sofa as
open. formal-conjectures links both
([pull request #6440](https://github.com/google-deepmind/formal-conjectures/pull/6440);
[pull request #6526](https://github.com/google-deepmind/formal-conjectures/pull/6526)).

[lean4-moving-sofa](https://github.com/vltanh/lean4-moving-sofa) (from 2 October 2026), by the maintainer of
this repository, formalizes Baek's theorem together with the results from the literature that it uses and the
structure of Gerver's sofa, which the paper states without proof, and encloses the area of Gerver's sofa
between 2.2192 and 2.2199. It also proves that Gerver's sofa is the only optimal sofa up to rigid motions,
which Baek's paper does not claim, and that a moving sofa whose area is ε less than the maximum is, after a
translation, within Hausdorff distance C√ε of Gerver's sofa, where the exponent 1/2 cannot be improved. Claude
Opus 5.5 wrote the formalization, and ChatGPT Pro 6 wrote the uniqueness argument and drafts of several of the
proofs; the README states that "No person has reviewed the proofs, the statements or the definitions". It
lists errors in Baek's paper that the formalization found, among them a definition that uses a parallelogram
where a fan is meant, which makes a proposition and a lemma false as written, and a theorem stated without
proof, and it states that "Every result holds in its intended form, the main theorem included". The Palomar
registry ([below](#formally-verified-computations-and-certified-numerics)) registered it as
[PALOMAR-2026-10-02-000008](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-02-000008), in five
versions from 2 to 8 October 2026. A pull request that would link it from formal-conjectures and mark the
uniqueness as solved was open on 10 October 2026
([pull request #6808](https://github.com/google-deepmind/formal-conjectures/pull/6808)).

The three formalizations of Baek's theorem prove the same formal statement from the same definitions
(lean4-moving-sofa proves that its own definitions agree with them), and a reader still has to compare those
definitions with the problem. Smaller repositories state the problem or prove that simple shapes, such as the
unit square, the half-disc and Hammersley's sofa, are moving sofas
([abobreshov/moving-sofa-lean](https://github.com/abobreshov/moving-sofa-lean)). Searches of GitHub and the
web found no formalization of the problem in Isabelle, Coq/Rocq or HOL. The Lean work on the ambidextrous
problem is described [above](#the-ambidextrous-problem-as-an-open-problem).

## Formally verified computations and certified numerics

Large computer-assisted proofs have been checked in proof assistants by separating an untrusted search from a
trusted check of what it produces. Gonthier and Werner checked the proof of the Four Colour Theorem in Coq in
2005, its computations included ([report](https://www.cl.cam.ac.uk/~lp15/Pages/4colproof.pdf); Notices of the
AMS 55 (2008), 1382-1393). The Flyspeck project checked Hales's proof of the Kepler conjecture in HOL Light
and Isabelle (Forum of Mathematics, Pi 5 (2017), e2,
[doi:10.1017/fmp.2017.1](https://doi.org/10.1017/fmp.2017.1)). It verified more than 23,000 nonlinear
inequalities with formal Taylor interval arithmetic in about 5,000 processor-hours, and 43,078 linear programs
through dual solutions that an external solver found and HOL Light repaired and checked. Immler's verified ODE
solver in Isabelle/HOL certified the computations in Tucker's proof of chaos for the Lorenz attractor (Journal
of Automated Reasoning 61 (2018), 73-111,
[doi:10.1007/s10817-017-9448-y](https://doi.org/10.1007/s10817-017-9448-y)).

SAT solvers settled the Boolean Pythagorean triples problem
([arXiv:1605.00723](https://arxiv.org/abs/1605.00723)), Schur number five
([arXiv:1711.08076](https://arxiv.org/abs/1711.08076)) and Keller's conjecture in dimension 7
([arXiv:1910.03740](https://arxiv.org/abs/1910.03740)), with proofs of up to two petabytes that formally
verified checkers in Coq or ACL2 accepted; the encoding into SAT was later verified in Coq for the Pythagorean
triples and was left unformalized for the other two. For the empty hexagon theorem, h(6) = 30, the geometric
reduction and the encoding were verified in Lean, and the unsatisfiability, checked by the verified checker
cake_lpr, was added as an axiom
([ITP 2024](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2024.35)). Recent results checked
in proof assistants include R(4,5) = 25 in HOL4 ([arXiv:2404.01761](https://arxiv.org/abs/2404.01761), ITP
2024), the fifth Busy Beaver value in Coq ([arXiv:2509.12337](https://arxiv.org/abs/2509.12337), preprint),
and the Noperthedron, a convex polyhedron without Rupert's property
([arXiv:2508.18475](https://arxiv.org/abs/2508.18475), preprint), whose case analysis has a Lean proof that
uses only the kernel and the three standard axioms ([repository](https://github.com/jcreedcmu/Noperthedron)).

Checked bounds on real numbers have had dedicated tools for more than a decade: CoqInterval in Coq/Rocq
(Melquiond, IJCAR 2008, [doi:10.1007/978-3-540-71070-7_2](https://doi.org/10.1007/978-3-540-71070-7_2)), the
`approximation` method of Isabelle/HOL (Hölzl, 2009) with libraries of affine arithmetic, Taylor models and
ODE enclosures in the Archive of Formal Proofs, and the Taylor interval verifier written in HOL Light for
Flyspeck (Solovyev and Hales, NFM 2013,
[doi:10.1007/978-3-642-38088-4_26](https://doi.org/10.1007/978-3-642-38088-4_26)). Lean 4 has
[girving/interval](https://github.com/girving/interval), conservative interval arithmetic on software floating
point, and [LeanCert](https://github.com/alerad/leancert), which turns numerical certificates into theorems
either with the kernel alone (`decide +kernel`) or, by default, by trusting the compiler (`native_decide`);
Trela's and Cureton's formalizations use it with the kernel. Since September 2026 Mathlib has had the
`inclusion` and `dyadic_interval` tactics for interval arithmetic
([pull request #42850](https://github.com/leanprover-community/mathlib4/pull/42850)), besides `norm_num`
extensions and fixed numerical bounds such as those on π. Kernel checking costs more: the Noperthedron proof
takes about 15 core-hours with the kernel alone and about 40 core-minutes with `native_decide`.

For Lean proofs written by others, including AI systems, the Lean FRO's
[Comparator](https://github.com/leanprover/comparator) builds a trusted file of statements, the Challenge, and
an untrusted Solution in sandboxes, and checks that the Solution proves the same statements, uses only
permitted axioms, and passes Lean's kernel and, optionally, external kernels such as
[NanoDa](https://github.com/ammkrn/nanoda_lib), an independent type checker written in Rust. In July 2026 an
AI-assisted "disproof" of the Collatz conjecture exploited a soundness bug in Lean's kernel, which was fixed
about an hour after the report. It also passed an older NanoDa because of a separate bug, and the Lean FRO's
postmortem notes that passing both kernels required two distinct bugs
([postmortem](https://leodemoura.github.io/blog/2026-8-1-postmortem-for-kernel-soundness-bug-14576/)). The
Palomar registry, incubated by the Lean FRO and ICARM and open since August 2026, registers a pinned commit of
a Lean formalization after three automated checks: Comparator, with only the axioms `propext`, `Quot.sound`
and `Classical.choice` and with replay by Lean's kernel and the independent kernels NanoDa and con-ron; a
language model's judgement that the formal statement renders the mathematical claim fairly; and a check of the
metadata in `formalization.yaml` ([about](https://palomar-registry.org/about);
[announcement](https://terrytao.wordpress.com/2026/08/18/palomar-a-registry-of-lean-verified-mathematics/)).
It adds no human editorial step and states that it is not peer review. Since `native_decide` adds an axiom of
its own, the computations in a Palomar entry have to be checked by the kernel.

## AI-assisted proofs and formalization

Google DeepMind announced in July 2024 that AlphaProof, which searches for proofs in Lean, and AlphaGeometry 2
solved four of the six problems of IMO 2024, a score of 28 of 42, from statements translated into formal
language by hand, taking up to three days on some problems
([announcement](https://deepmind.google/discover/blog/ai-solves-imo-problems-at-silver-medal-level/)).
AlphaProof's method was published in Nature in November 2025
([doi:10.1038/s41586-025-09833-y](https://doi.org/10.1038/s41586-025-09833-y)). At IMO 2025, Gemini Deep
Think, graded by IMO coordinators
([announcement](https://deepmind.google/discover/blog/advanced-version-of-gemini-with-deep-think-officially-achieves-gold-medal-standard-at-the-international-mathematical-olympiad/)),
and an experimental OpenAI model, graded by former medalists whom OpenAI engaged
([news](https://www.techrepublic.com/article/news-openai-model-math-olympiad/)), each reported a score of 35
of 42 with proofs in natural language. Preprints on Harmonic's Aristotle
([arXiv:2510.01346](https://arxiv.org/abs/2510.01346)) and ByteDance's Seed-Prover
([arXiv:2507.23726](https://arxiv.org/abs/2507.23726)) report Lean proofs of five of the six problems,
Aristotle's from formal statements written by hand.

Math Inc. reports that its agent Gauss completed the formalization of the strong prime number theorem in Lean,
about 25,000 lines in three weeks, on scaffolding written by people
([announcement](https://www.math.inc/gauss)). The Lean formalization of Viazovska's sphere packing theorem in
dimension 8, a project that a team of mathematicians began in March 2024, was finished in February 2026 with
Gauss doing the final stages; its authors write that the correspondence between the autoformalization and the
intended proof "is still being investigated" ([arXiv:2604.23468](https://arxiv.org/abs/2604.23468), preprint),
and Math Inc. reports a formalization of dimension 24 as well
([announcement](https://www.math.inc/sphere-packing)).

From late 2025, AI systems contributed solutions to problems from Erdős's collection, usually with a Lean
proof, often written by Aristotle. The community wiki that tracked them, with data to 30 June 2026, also lists
incorrect claims, misformalized statements and solutions later found in the literature
([wiki](https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erd%C5%91s-problems)). Preprints of
2026 report Lean proofs found by AI systems for Fel's conjecture on numerical semigroups
([arXiv:2602.03716](https://arxiv.org/abs/2602.03716), revised after referee reports) and for 9 of 353 open
Erdős problems and 44 of 492 OEIS conjectures ([arXiv:2605.22763](https://arxiv.org/abs/2605.22763)). OpenAI
announced ten results with Lean certificates in August 2026, without peer review
([The Next Web](https://thenextweb.com/news/openai-astra-model-ten-math-proofs-non-sofic-groups)); a preprint
notes that for one of them, on Connes's rigidity conjecture, the community has not been able to determine
whether the formalization means what it claims ([arXiv:2608.28997](https://arxiv.org/abs/2608.28997)).
OpenAI's claim in September 2026 of a Lean-formalized blowup for the Navier-Stokes equations was still
described as unverified on 5 October 2026 ([IEEE Spectrum](https://spectrum.ieee.org/millennium-prize-ai)).
formal-conjectures, with 2,615 Lean statements in May 2026, 1,029 of them open conjectures
([arXiv:2605.13171](https://arxiv.org/abs/2605.13171), preprint), supplies the statements of many of these
proofs.

For the moving sofa problem, AI work up to 2025 was numerical (AlphaEvolve, above). The formalizations of
Baek's theorem by Cureton and in lean4-moving-sofa, the formal-conjectures statement of the ambidextrous
problem, and the ambidextrous bounds of O'Keefe and of larskarbo/ambidextrous-sofa-174 were written by AI
systems or with their help, as their authors state.

## This repository

This repository proves in Lean 4 that Romik's sofa is optimal and, up to congruence, the only optimal shape.
Every ambidextrous sofa, in the sense of the [definitions](definitions.md#ambidextrous-sofas), has area at
most `M = 1 + 4Y² + arctan Y = 1.64495…`, where `Y` is the positive root of `4Y³ + 3Y = 1`, and an
ambidextrous sofa of area `M` is a rotated and translated copy of Romik's sofa. After a rigid normalization
that puts a sofa in the strip `0 ≤ y ≤ 1`, the proof splits its convex hull into two caps, one for each
hallway, and bounds the area of the sofa by the sum of their scores. The score of each cap is at most `M/2`,
with equality only for a full quarter turn and a translate of Romik's cap; when the area is `M`, both caps are
Romik's, and an exact identity for the deficit recovers the sofa from them. Two steps of the proof use the
bound `22199/10000` that Baek's theorem, with a bound on the area of Gerver's sofa, gives for the ordinary
problem. The Lean formalization of Baek's theorem comes from
[lean4-moving-sofa](https://github.com/vltanh/lean4-moving-sofa) and is copied into
[`MovingSofaOptimality/`](../MovingSofaOptimality/README.md). ChatGPT Pro 6 found the proof in October 2026
and wrote an uncompiled Lean draft of it, which Claude Opus 5.5 made compile; no person has checked the
proofs, and Lean's kernel checks all of them. The [archive](archive/README.md) keeps the manuscript that
ChatGPT Pro 6's research notes ended with, as a record of where the proof came from, and says where the notes
are.
