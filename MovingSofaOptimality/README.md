# MovingSofaOptimality

A copy of the library `MovingSofaOptimality` of
[lean4-moving-sofa](https://github.com/vltanh/lean4-moving-sofa), at commit
[`1174c5c`](https://github.com/vltanh/lean4-moving-sofa/tree/1174c5c25c1c66b807e368446d6682e8d0276759/MovingSofaOptimality),
by the same maintainer and under the same license (Apache-2.0). It formalizes Jineon Baek's *Optimality of
Gerver's sofa* ([arXiv:2411.19826](https://arxiv.org/abs/2411.19826)), and lean4-moving-sofa documents it; its
Palomar entry is [PALOMAR-2026-10-02-000008](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-02-000008).

The proof of the ambidextrous sofa uses its Theorem 1.1.1, `MovingSofaOptimality.gm_area_le` (no moving sofa
has a larger area than Gerver's sofa), the bound `MovingSofaOptimality.gerverSofa_area_mem` on the area of
Gerver's sofa, and its library of convex bodies (support functions, surface area measures).

It is copied into this repository so that the repository can follow Mathlib on its own schedule. The copy is
adapted to Mathlib `v4.35.0-rc4` by one line: `Basic/Plane.lean` imports `Mathlib.Analysis.Calculus.Deriv.Pow`,
which newer Mathlib no longer brings in through the derivatives of the trigonometric functions. Nothing else
differs.
