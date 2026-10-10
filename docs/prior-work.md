# Prior work

[Back to the README](../README.md)

From a search on 10 October 2026 of arXiv, the publishers' pages and the papers below.

## The problem

- Leo Moser, *Problem 66-11, Moving furniture through a hallway*, SIAM Review 8 (1966), 381, posed the moving
  sofa problem for a hallway that turns once.
- Romik attributes the ambidextrous variant to John Conway, G. C. Shephard and others, who worked on several
  variants of the problem soon after it was posed ("Conway car", "Shepard piano"). Maruyama (1973) and Gibbs
  (2014) computed approximate polygonal solutions numerically, Gibbs's of area about `1.64495`
  ([Romik 2018](https://arxiv.org/abs/1606.08111), §1.2 and Fig. 3).

## Romik's ambidextrous sofa

Dan Romik, *Differential equations and exact solutions in the moving sofa problem*, Experimental Mathematics
27 (2018), 316-330 ([arXiv:1606.08111](https://arxiv.org/abs/1606.08111), July 2016). Romik derives six
differential equations from Gerver's balance conditions, recovers Gerver's sofa from them, and constructs "a new
shape that we propose as a possible solution to the ambidextrous moving sofa problem" (abstract). The shape,
`Σ = S_x ∩ ρ(S_x)`, intersects the shape of a rotation path with its reflection in `y = 1/2`. Its boundary is
made of 18 pieces of algebraic curves, and its area is

  `∛(3 + 2√2) + ∛(3 − 2√2) − 1 + arctan(½(∛(√2 + 1) − ∛(√2 − 1))) ≈ 1.644955218425440`,

which he also writes `X + arctan Y`, with `x²(x + 3) = 8` and `x(4x² + 3) = 1`. He calls the shape "a highly
plausible candidate to be the solution" (§5). The first of his open problems (§7) asks to prove that Gerver's
sofa and `Σ` are local maxima of the area in their problems; he does not conjecture global optimality.

## Upper bounds and the ordinary problem

- Yoav Kallus and Dan Romik, *Improved upper bounds in the moving sofa problem*, Advances in Mathematics 340
  (2018), 960-982 ([arXiv:1706.06630](https://arxiv.org/abs/1706.06630)), prove the computer-assisted upper
  bound 2.37 for the moving sofa constant. They note that every upper bound for the ordinary problem bounds the
  ambidextrous one too, so the ambidextrous constant lies between `1.64495…` and `2.37`, and they propose to
  extend their method to the ambidextrous problem.
- Jineon Baek, *Optimality of Gerver's sofa*, [arXiv:2411.19826](https://arxiv.org/abs/2411.19826) (December
  2024, preprint), proves that Gerver's sofa, of area `2.21953…`, is optimal for the ordinary problem. The
  proof here uses this result in the form "every moving sofa has area at most `22199/10000`". Its formalization
  in [lean4-moving-sofa](https://github.com/vltanh/lean4-moving-sofa), registered in Palomar as
  [PALOMAR-2026-10-02-000008](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-02-000008), is copied
  into this repository ([`MovingSofaOptimality/`](../MovingSofaOptimality/README.md)).

## The ambidextrous problem as an open problem

Bogdan Georgiev, Javier Gómez-Serrano, Terence Tao and Adam Zsolt Wagner, *Mathematical exploration and
discovery at scale*, [arXiv:2511.02864](https://arxiv.org/abs/2511.02864) (version 3, December 2025), list it as
Problem 6.63 ("Ambidextrous sofa (Conway's car)"): the largest area of a connected shape that can pass a
left-turning and a right-turning corner of unit width. They write that "Romik introduced the 'Romik sofa' that
produced a lower bound 1.6449… . It remains open whether this bound is sharp." Their statement does not say
that the two passages start in the same orientation; without that condition the answer would be Gerver's area
([Definitions](definitions.md#ambidextrous-sofas)).

## This repository

This repository proves that Romik's sofa is optimal and, up to congruence, the only optimal shape. ChatGPT Pro 6
found the proof in October 2026 ([archive](archive/README.md)). The other Lean formalizations of the moving sofa
problem that we know of ([lean4-moving-sofa](https://github.com/vltanh/lean4-moving-sofa),
[deancureton/MovingSofa](https://github.com/deancureton/MovingSofa),
[RuifengCao/sofa-formal](https://github.com/RuifengCao/sofa-formal), and Google DeepMind's
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/MovingSofa.lean))
treat the ordinary problem.
