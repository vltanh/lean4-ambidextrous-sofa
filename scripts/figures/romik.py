#!/usr/bin/env python3
"""Romik's ambidextrous sofa, computed from the definitions of the Challenge (ChallengeDefs.lean).

The support function of the hull is, for t in [0, π/2], h(t) = f(t) and h(t + π/2) = g(t) on the
upper half of the circle, in three phases separated by β = arctan Y and π/2 - β (`supportF`,
`supportG`), and its reflection in the line y = 1/2 on the lower half. The niche n(x) is the
supremum over θ in (0, π/2) of min((f(θ) - 1 - x cos θ)/sin θ, (g(θ) - 1 + x sin θ)/cos θ), clipped
at 0 (`niche`); the sofa is the hull without {y < n(x)} and {1 - y < n(x)} (`referenceSofa`).

The motion that the figures show is the library's `lowerReferencePath`: at the angle φ of the turn
the sofa is turned clockwise by φ and translated by (1 - f(φ), 1 - g(φ)), so that it touches both
outer walls of the hallway that turns right. Its mirror image in y = 1/2 turns left.
"""
import math

import numpy as np

PI = math.pi

# The positive root of 4Y³ + 3Y = 1, and the parameters of the support function (MS.1, MS.11).
Y = float(next(r.real for r in np.roots([4, 0, 3, -1]) if abs(r.imag) < 1e-12 and r.real > 0))
BETA = math.atan(Y)
A = 1 / (4 * math.sin(BETA))
K = 1 - 4 / 3 * A
R = math.cos(BETA) / math.cos(1.5 * (PI / 4 - BETA))
M = 1 + 4 * Y ** 2 + BETA


def f(t):
    if t <= BETA:
        return math.cos(t) + 0.5 * math.sin(t)
    if t <= PI / 2 - BETA:
        return R * math.cos(t / 2 + PI / 8) + K * math.cos(t) + 0.5 * math.sin(t)
    return (1 - 2 / 3 * A) * math.cos(t) + 0.5 * math.sin(t) + 0.5


def g(t):
    if t <= BETA:
        return (2 * A - 1) * math.sin(t) + 0.5 * math.cos(t) + 0.5
    if t <= PI / 2 - BETA:
        return R * math.sin(t / 2 + PI / 8) - K * math.sin(t) + 0.5 * math.cos(t)
    return (8 / 3 * A - 1) * math.sin(t) + 0.5 * math.cos(t)


def fD(t):
    if t <= BETA:
        return -math.sin(t) + 0.5 * math.cos(t)
    if t <= PI / 2 - BETA:
        return -R / 2 * math.sin(t / 2 + PI / 8) - K * math.sin(t) + 0.5 * math.cos(t)
    return -(1 - 2 / 3 * A) * math.sin(t) + 0.5 * math.cos(t)


def gD(t):
    if t <= BETA:
        return (2 * A - 1) * math.cos(t) - 0.5 * math.sin(t)
    if t <= PI / 2 - BETA:
        return R / 2 * math.cos(t / 2 + PI / 8) - K * math.cos(t) - 0.5 * math.sin(t)
    return (8 / 3 * A - 1) * math.cos(t) - 0.5 * math.sin(t)


def upper_boundary(n=1500):
    """The upper half of the hull's boundary, from (1, 1/2) to (1 - 8A/3, 1/2): for each upward normal
    the point where the hull touches its supporting line; the gap at the top normal is the top face."""
    ts = np.linspace(0, PI / 2, n)
    first = [(f(t) * math.cos(t) - fD(t) * math.sin(t), f(t) * math.sin(t) + fD(t) * math.cos(t))
             for t in ts]
    second = [(-g(t) * math.sin(t) - gD(t) * math.cos(t), g(t) * math.cos(t) - gD(t) * math.sin(t))
              for t in ts]
    return first + second


def hull(n=1500):
    """The hull, counterclockwise from its rightmost point (1, 1/2)."""
    up = upper_boundary(n)
    return up + [(x, 1 - y) for x, y in reversed(up)]


LEFT, RIGHT = 1 - 8 * A / 3, 1.0
J = (1 - 2 * A, 1 - 2 * A / 3)          # the middle half of the projection, also the top face


def niche(xs, m=6000):
    """The niche n(x) of the hull, swept by the inner corner of the hallway that turns right."""
    th = np.linspace(1e-6, PI / 2 - 1e-6, m)
    fv = np.array([f(t) for t in th])
    gv = np.array([g(t) for t in th])
    c, s = np.cos(th), np.sin(th)
    out = []
    for x in xs:
        w = np.minimum((fv - 1 - x * c) / s, (gv - 1 + x * s) / c)
        out.append(max(w.max(), 0.0))
    return np.array(out)


def corner(phi):
    """The inner corner of the hallway turned by φ about the hull, in the sofa's frame (MS corner)."""
    return ((f(phi) - 1) * math.cos(phi) - (g(phi) - 1) * math.sin(phi),
            (f(phi) - 1) * math.sin(phi) + (g(phi) - 1) * math.cos(phi))


def fibers(n=2400):
    """The abscissas, the hull's lower and upper boundaries, and the niche."""
    up = np.array(upper_boundary(3000))
    order = np.argsort(up[:, 0])
    xs = np.linspace(LEFT, RIGHT, n)
    top = np.interp(xs, up[order, 0], up[order, 1])
    return xs, 1 - top, top, niche(xs)


def sofa(n=2400):
    """The outline of Romik's ambidextrous sofa: the upper boundary from left to right, then the lower
    boundary back, sampled on n abscissas."""
    xs, lo, hi, nv = fibers(n)
    upper = np.minimum(hi, 1 - nv)
    lower = np.maximum(lo, nv)
    assert np.all(upper >= lower - 1e-9)
    return [(x, y) for x, y in zip(xs, upper)] + [(x, y) for x, y in zip(xs[::-1], lower[::-1])]


def area(n=20000):
    xs, lo, hi, nv = fibers(n)
    return float(np.trapezoid(np.minimum(hi, 1 - nv) - np.maximum(lo, nv), xs))


def rot(a, p):
    c, s = math.cos(a), math.sin(a)
    return (c * p[0] - s * p[1], s * p[0] + c * p[1])


def place(phi, pts):
    """The sofa turned clockwise by φ and pushed against both outer walls of the hallway that turns
    right: q ↦ R_{-φ} q + (1 - f(φ), 1 - g(φ))."""
    cx, cy = 1 - f(phi), 1 - g(phi)
    out = []
    for q in pts:
        x, y = rot(-phi, q)
        out.append((x + cx, y + cy))
    return out


def in_lower_hallway(p, eps=1e-6):
    x, y = p
    return x <= 1 + eps and y <= 1 + eps and (x >= -eps or y >= -eps)


if __name__ == '__main__':
    print(f'Y = {Y:.12f}, beta = {BETA:.12f}, A = {A:.12f}, k = {K:.12f}, R = {R:.12f}')
    print(f'M = {M:.12f}, area of the computed sofa = {area():.9f}')
    pts = sofa(1200)
    bad = [(phi, p) for phi in np.linspace(0, PI / 2, 91) for p in place(phi, pts)
           if not in_lower_hallway(p, 1e-3)]
    print('points outside the hallway during the turn:', len(bad))
