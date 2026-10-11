#!/usr/bin/env python3
"""Draw the figures of the paper, as PDF files in docs/paper/figures/.

    python3 docs/paper/figures/make_figures.py

Every figure is computed from the definitions of the formalization: the hallways of
Geometry/Plane.lean, the motion of Reference/Body.lean, the caps of Geometry/Caps.lean and
Geometry/Reflection.lean, the walls, niche and barrier of Geometry/Barriers.lean and the score of
Measure/CapScore.lean. Romik's sofa comes from scripts/figures/romik.py, which computes its support
function, hull, niche and motion from the definitions of the Challenge. The facts that a caption
states are checked by `assert`s.
"""
import logging
import math
import sys
from pathlib import Path

import numpy as np
import matplotlib

matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.colors import to_rgba
from matplotlib.patches import Polygon, Arc, FancyArrowPatch

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True  # leave scripts/figures/ as it is
sys.path.insert(0, str(HERE.parents[2] / 'scripts' / 'figures'))
import romik  # noqa: E402

PI = math.pi
INK, FAINT, WALL = '#1f2937', '#9ca3af', '#374151'
BLUE, ORANGE, GREEN, PURPLE, TEAL = '#2563eb', '#ea580c', '#16a34a', '#9333ea', '#0d9488'
BLUE_F, ORANGE_F, GREY_F, GREEN_F, PURPLE_F, TEAL_F = '#dbeafe', '#fed7aa', '#e5e7eb', '#dcfce7', '#f3e8ff', '#ccfbf1'
FLOOR = '#f3f4f6'

# Matplotlib's Computer Modern fonts carry old timestamps, which fontTools reports while subsetting them.
logging.getLogger('fontTools').setLevel(logging.ERROR)

plt.rcParams.update({
    'font.family': 'serif', 'mathtext.fontset': 'cm', 'font.size': 8.5, 'pdf.fonttype': 42,
    'axes.linewidth': 0.6, 'savefig.bbox': 'tight', 'savefig.pad_inches': 0.02,
})


# ---- drawing helpers ---------------------------------------------------------------------------

def panels(boxes, scale, gap=0.0):
    """A figure with one frameless axes for each data box (xmin, xmax, ymin, ymax), side by side, `gap`
    inches apart and vertically centred, each drawn at `scale` inches per unit."""
    ws = [(b[1] - b[0]) * scale for b in boxes]
    hs = [(b[3] - b[2]) * scale for b in boxes]
    W, H = sum(ws) + gap * (len(boxes) - 1), max(hs)
    fig = plt.figure(figsize=(W, H))
    axes, x = [], 0.0
    for b, w, h in zip(boxes, ws, hs):
        axes.append(frame(fig.add_axes((x / W, (H - h) / 2 / H, w / W, h / H)), b))
        x += w + gap
    return fig, axes


def frame(ax, box):
    ax.set_xlim(box[0], box[1])
    ax.set_ylim(box[2], box[3])
    ax.set_aspect('equal')
    ax.axis('off')
    return ax


def poly(ax, pts, fc='none', ec=INK, lw=1.0, ls='-', alpha=None, z=2):
    ax.add_patch(Polygon(list(pts), closed=True, fc=fc, ec=ec, lw=lw, ls=ls, alpha=alpha, zorder=z,
                         joinstyle='round'))


def line(ax, pts, color=INK, lw=1.0, ls='-', z=3, cap='round', clip=True):
    xs, ys = zip(*pts)
    ax.plot(xs, ys, color=color, lw=lw, ls=ls, zorder=z, solid_capstyle=cap, dash_capstyle=cap,
            clip_on=clip)


def arrow(ax, a, b, color=INK, lw=1.0, z=5, style='-|>', ms=6, both=False):
    ax.annotate('', xy=b, xytext=a, zorder=z,
                arrowprops=dict(arrowstyle='<|-|>' if both else style, color=color, lw=lw,
                                shrinkA=0, shrinkB=0, mutation_scale=ms))


def text(ax, xy, s, color=INK, ha='center', va='center', size=8.5, z=6, **kw):
    ax.text(xy[0], xy[1], s, color=color, ha=ha, va=va, fontsize=size, zorder=z, **kw)


def dot(ax, p, r=2.2, color=INK, z=6):
    ax.plot([p[0]], [p[1]], 'o', ms=r * 2, color=color, zorder=z, mec='none')


def angle_mark(ax, c, r, t0, t1, label, color=INK, lw=0.7, size=8, dr=0.1):
    """An arc of radius r about c from the angle t0 to the angle t1 (radians), labelled at its middle."""
    ax.add_patch(Arc(c, 2 * r, 2 * r, theta1=math.degrees(t0), theta2=math.degrees(t1), color=color,
                     lw=lw, zorder=6))
    text(ax, add(c, mul(r + dr, uvec((t0 + t1) / 2))), label, color=color, size=size)


def bracket(ax, x0, x1, y, color=INK, lw=0.8, tick=0.035):
    """The interval [x0, x1] drawn at height y, with end ticks."""
    line(ax, [(x0, y), (x1, y)], color=color, lw=lw, z=5, cap='butt')
    for x in (x0, x1):
        line(ax, [(x, y - tick), (x, y + tick)], color=color, lw=lw, z=5, cap='butt')


def save(fig, name):
    path = HERE / f'{name}.pdf'
    fig.savefig(path)
    plt.close(fig)
    print('wrote', path.relative_to(HERE.parents[2]))


def uvec(t):
    return (math.cos(t), math.sin(t))


def vvec(t):
    return (-math.sin(t), math.cos(t))


def add(*ps):
    return (sum(p[0] for p in ps), sum(p[1] for p in ps))


def mul(c, p):
    return (c * p[0], c * p[1])


def dotp(p, q):
    return p[0] * q[0] + p[1] * q[1]


def rho(pts):
    """The reflection (x, y) -> (x, 1 - y) in the line y = 1/2 (`reflect`)."""
    return [(x, 1 - y) for x, y in pts]


def shoelace(pts):
    return 0.5 * abs(sum(p[0] * q[1] - q[0] * p[1] for p, q in zip(pts, pts[1:] + pts[:1])))


def graph_region(xs, ys, eps=1e-12):
    """The region between y = 0 and the graph of ys over xs, where ys > eps, as a polygon (one piece:
    the abscissas from the first to the last where ys > eps)."""
    xs, ys = np.asarray(xs), np.asarray(ys)
    k = np.nonzero(ys > eps)[0]
    xs, ys = xs[k[0]:k[-1] + 1], ys[k[0]:k[-1] + 1]
    return [(xs[0], 0.0)] + list(zip(xs, ys)) + [(xs[-1], 0.0)]


# ---- caps, walls, niches, barriers and scores (Geometry/Barriers.lean, Measure/CapScore.lean) ----

def hull_chains(pts):
    """The lower and the upper chain of the convex hull of the points, both from left to right
    (Andrew's monotone chain)."""
    pts = sorted(set((float(x), float(y)) for x, y in pts))

    def turn(o, a, b):
        return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])

    lower, upper = [], []
    for p in pts:
        while len(lower) >= 2 and turn(lower[-2], lower[-1], p) <= 0:
            lower.pop()
        lower.append(p)
    for p in reversed(pts):
        while len(upper) >= 2 and turn(upper[-2], upper[-1], p) <= 0:
            upper.pop()
        upper.append(p)
    return lower, upper[::-1]


def cap_of(upper):
    """The cap (`upperCap`) of a convex set in the strip whose upper chain, from left to right, is
    `upper`: the region between y = 0 and the chain, counterclockwise from (l, 0)."""
    return [(upper[0][0], 0.0), (upper[-1][0], 0.0)] + list(upper[::-1])


def roof_of(upper):
    """The roof f_U (`capRoof`) of the cap with upper chain `upper`, on its projection."""
    xs, ys = zip(*upper)
    return lambda x: np.interp(x, xs, ys)


def polygon_support(pts):
    """The support function t -> h(t) = max_p <p, u(t)> of a polygon (`angleSupport`)."""
    P = np.asarray(pts, dtype=float)

    def h(ts):
        ts = np.atleast_1d(np.asarray(ts, dtype=float))
        out = np.empty(len(ts))
        for k in range(0, len(ts), 256):
            t = ts[k:k + 256]
            out[k:k + 256] = (np.outer(P[:, 0], np.cos(t)) + np.outer(P[:, 1], np.sin(t))).max(axis=0)
        return out

    return h


def romik_support(ts):
    """The support function of Romik's cap K_R on [0, π]: f on [0, π/2] and g(t - π/2) on [π/2, π]
    (romik.py; the cap has the upward support values of the hull)."""
    return np.array([romik.f(t) if t <= PI / 2 else romik.g(t - PI / 2) for t in np.atleast_1d(ts)])


def first_wall(h, t):
    """x -> a_t(x) = (h(t) - 1 - x cos t) / sin t (`firstWall`)."""
    h1 = float(h([t])[0])
    return lambda x: (h1 - 1 - np.asarray(x, dtype=float) * math.cos(t)) / math.sin(t)


def second_wall(h, t):
    """x -> b_t(x) = (h(t + π/2) - 1 + x sin t) / cos t (`secondWall`)."""
    h2 = float(h([t + PI / 2])[0])
    return lambda x: (h2 - 1 + np.asarray(x, dtype=float) * math.sin(t)) / math.cos(t)


def inner_corner(h, t):
    """The inner corner (h(t) - 1) u(t) + (h(t + π/2) - 1) u⊥(t) of the hallway L_- turned by t and
    moved so that its outer walls touch the cap: the common point of the lines y = a_t(x), y = b_t(x)."""
    h1, h2 = float(h([t])[0]), float(h([t + PI / 2])[0])
    return add(mul(h1 - 1, uvec(t)), mul(h2 - 1, vvec(t)))


def hall_frame(h, t, pts):
    """Points given in the coordinates of the hallway L_- (inner corner at the origin), placed in the
    frame of the cap: turned by t and moved so that both outer walls touch the cap. This inverts the
    placement p -> (<p, u(t)> + 1 - h(t), <p, u⊥(t)> + 1 - h(t + π/2)) (`canonicalPlacement`)."""
    c = inner_corner(h, t)
    return [add(c, mul(p[0], uvec(t)), mul(p[1], vvec(t))) for p in pts]


def swept_niche(h, alpha, xs, step=PI / 2 / 4000):
    """x -> n_alpha(x) = max(sup_{0 < t < alpha} min(a_t(x), b_t(x)), 0) (`sweptNiche`), the supremum
    taken over the multiples of `step` in the open interval (nested for different alpha)."""
    xs = np.asarray(xs, dtype=float)
    ts = step * np.arange(1, math.ceil(alpha / step - 1e-9))
    h1, h2 = h(ts) - 1, h(ts + PI / 2) - 1
    best = np.full(len(xs), -np.inf)
    for k in range(0, len(ts), 200):
        t = ts[k:k + 200, None]
        a = (h1[k:k + 200, None] - xs * np.cos(t)) / np.sin(t)
        b = (h2[k:k + 200, None] + xs * np.sin(t)) / np.cos(t)
        best = np.maximum(best, np.minimum(a, b).max(axis=0))
    return np.maximum(best, 0.0)


def partial_barrier(h, alpha, xs):
    """x -> N_alpha(x) = max(n_alpha(x), a_alpha(x)) (`partialBarrier`)."""
    return np.maximum(swept_niche(h, alpha, xs), first_wall(h, alpha)(xs))


def middle_half(l, r):
    """The middle half J = [l + w/4, r - w/4] of [l, r], w = r - l (`middleHalfInterval`)."""
    return l + (r - l) / 4, r - (r - l) / 4


def cap_score(roof, l, r, h, alpha, n=2001):
    """P_alpha(U) = ∫ f_U over [l, r] minus J  -  ∫ N_alpha over J (`capScore`), by the trapezoidal
    rule."""
    j0, j1 = middle_half(l, r)
    xa, xb, xj = np.linspace(l, j0, n), np.linspace(j1, r, n), np.linspace(j0, j1, n)
    outer = np.trapezoid(roof(xa), xa) + np.trapezoid(roof(xb), xb)
    return outer - np.trapezoid(partial_barrier(h, alpha, xj), xj)


# ---- Romik's sofa and its cap (romik.py) --------------------------------------------------------

L_R, R_R = romik.LEFT, romik.RIGHT
J_R = romik.J
UPPER_R = romik.upper_boundary(1500)[::-1]           # the hull's upper boundary, left to right
CAP_R = cap_of(UPPER_R)                              # Romik's cap K_R
ROOF_R = roof_of(UPPER_R)
SOFA_R = romik.sofa(2400)                            # for the checks
SOFA_DRAW = romik.sofa(700)                          # for the drawings


def check_romik():
    """Romik's cap from romik.py against the definitions: the polygon K_R has the support values f
    and g, the niche of Barriers.lean is romik.niche, J is the middle half of the projection, and the
    score of K_R at π/2 is M/2."""
    ts = np.linspace(0, PI, 721)
    assert np.max(np.abs(polygon_support(CAP_R)(ts) - romik_support(ts))) < 1e-6
    xs = np.linspace(L_R, R_R, 301)
    assert np.max(np.abs(swept_niche(romik_support, PI / 2, xs) - romik.niche(xs))) < 1e-3
    assert max(abs(a - b) for a, b in zip(J_R, middle_half(L_R, R_R))) < 1e-12
    p = cap_score(ROOF_R, L_R, R_R, romik_support, PI / 2)
    assert abs(p - romik.M / 2) < 1e-3, p
    return p


# ---- Figure 1: the two hallways ---------------------------------------------------------------

def placed(phi, pts, turn):
    """The sofa at the angle phi of its motion through L_- (turn = -1: `lowerReferencePath`,
    q -> R_{-phi} q + (1 - f(phi), 1 - g(phi))) or through L_+ (turn = +1: `upperReferencePath`, the
    mirror image of the first in the line y = 1/2)."""
    if turn < 0:
        return romik.place(phi, pts)
    return rho(romik.place(phi, rho(pts)))


def in_hall(p, turn, eps=1e-3):
    """p lies in L_- = H ∪ V_- (turn = -1) or in L_+ = H ∪ V_+ (turn = +1)."""
    x, y = p
    if turn < 0:
        return x <= 1 + eps and y <= 1 + eps and (y >= -eps or x >= -eps)
    return x <= 1 + eps and y >= -eps and (y <= 1 + eps or x >= -eps)


def fig_intro():
    """Romik's sofa moving through the hallway L_- that turns right (left) and through the hallway L_+
    that turns left (right), from the same placement in H: at the times t = 0, 1/2, 1 of the motions of
    the proof, which turn it at constant speed by -π/2 and by π/2."""
    pts = SOFA_R
    # Both motions start from the same placement, the sofa itself, which lies in H.
    for turn in (-1, 1):
        assert max(math.dist(p, q) for p, q in zip(placed(0.0, pts, turn), pts)) < 1e-12
    assert all(x <= 1 + 1e-9 and -1e-9 <= y <= 1 + 1e-9 for x, y in pts)
    # Each placement along the way lies in its hallway, and the last one in the outgoing arm.
    for turn in (-1, 1):
        for phi in np.linspace(0, PI / 2, 91):
            assert all(in_hall(q, turn) for q in placed(phi, pts[::3], turn)), (turn, phi)
    assert all(-1e-9 <= x <= 1 + 1e-9 and y <= 1 + 1e-9 for x, y in placed(PI / 2, pts, -1))   # in V_-
    assert all(-1e-9 <= x <= 1 + 1e-9 and y >= -1e-9 for x, y in placed(PI / 2, pts, 1))      # in V_+
    far = 1.5
    box_m, box_p = (-far, 1.12, -far, 1.12), (-far, 1.12, -0.12, 1 + far)
    fig, (a1, a2) = panels([box_m, box_p], 0.58, gap=0.42)
    stages = ((0.0, GREEN, GREEN_F, 4, r'$t=0$', 0.9), (PI / 2, PURPLE, PURPLE_F, 5, r'$t=1$', 0.9),
              (PI / 4, BLUE, BLUE_F, 6, r'$t=1/2$', 1.1))
    for ax, turn in ((a1, -1), (a2, 1)):
        def m(p):                          # L_+ is the mirror image of L_-
            return p if turn < 0 else (p[0], 1 - p[1])
        floor = [(-far, 0), (0, 0), (0, -far), (1, -far), (1, 1), (-far, 1)]
        poly(ax, [m(p) for p in floor], fc=FLOOR, ec='none', z=0)
        line(ax, [m(p) for p in [(-far, 1), (1, 1), (1, -far)]], color=WALL, lw=1.6, cap='butt')
        line(ax, [m(p) for p in [(-far, 0), (0, 0), (0, -far)]], color=WALL, lw=1.6, cap='butt')
        for phi, ec, fc, z, _, lw in stages:
            poly(ax, placed(phi, SOFA_DRAW, turn), fc=to_rgba(fc, 0.45), ec=ec, lw=lw, z=z)
        text(ax, m((-far - 0.07, 0.5)), r'$H$', ha='right')
        text(ax, m((0.5, -far - 0.08)), r'$V_-$' if turn < 0 else r'$V_+$',
             va='top' if turn < 0 else 'bottom')
        text(ax, m((-0.95, -1.05)), r'$L_-$' if turn < 0 else r'$L_+$', size=10.5)
        # The times of the three placements.
        text(ax, m((-0.75, 1.05)), stages[0][4], color=GREEN, size=7.5, va='bottom' if turn < 0 else 'top')
        text(ax, m((1.07, -0.75)), stages[1][4], color=PURPLE, size=7.5, ha='left')
        target = placed(PI / 4, [(L_R + 0.55, 0.5)], turn)[0]
        label = m((-0.62, -0.42))
        text(ax, label, stages[2][4], color=BLUE, size=7.5, ha='right')
        arrow(ax, add(label, (0.03, 0.04 * (1 if turn < 0 else -1))), target, color=BLUE, lw=0.6, ms=4, z=8)
    save(fig, 'fig-intro')


# ---- Figure 2: Romik's sofa -------------------------------------------------------------------

def fig_sofa():
    """Romik's sofa S_R between the lines y = 0 and y = 1: its hull (dashed) without the region below
    n_R and its mirror image above 1 - n_R (orange), over the middle half J of its projection."""
    xs, lo, hi, nv = romik.fibers(2400)
    j0, j1 = J_R
    # The sofa has area M; the hull lies in the strip, and its roof is 1 exactly over J.
    assert abs(romik.area() - romik.M) < 1e-4
    assert lo.min() >= -1e-12 and hi.max() <= 1 + 1e-12
    inside = (xs > j0 + 1e-3) & (xs < j1 - 1e-3)
    outside = (xs < j0 - 1e-3) | (xs > j1 + 1e-3)
    assert np.all(np.abs(hi[inside] - 1) < 1e-9) and np.all(hi[outside] < 1 - 1e-6)
    # J is the middle half of the projection; the niche is positive exactly over J, and below 1/2, so
    # that the two niches are disjoint.
    assert max(abs(a - b) for a, b in zip(J_R, middle_half(L_R, R_R))) < 1e-12
    assert np.all(nv[inside] > 0) and np.all(nv[outside] == 0) and nv.max() < 0.5
    xl, xr = L_R - 0.1, R_R + 0.1
    fig, (ax,) = panels([(xl, xr, -0.3, 1.06)], 1.15)
    for y in (0, 1):
        line(ax, [(xl, y), (xr, y)], color=FAINT, lw=0.6, z=1)
    text(ax, (xr + 0.04, 1), r'$y=1$', color=FAINT, size=7.5, ha='left')
    text(ax, (xr + 0.04, 0), r'$y=0$', color=FAINT, size=7.5, ha='left')
    lower = graph_region(xs[::3], nv[::3])
    for region in (lower, rho(lower)):
        poly(ax, region, fc=ORANGE_F, ec='none', z=1.2)
    poly(ax, romik.hull(500), ec=INK, lw=0.8, ls=(0, (4, 3)), z=1.5)
    poly(ax, SOFA_DRAW, fc=BLUE_F, ec=BLUE, lw=1.1, z=2)
    for x in (j0, j1):
        line(ax, [(x, -0.15), (x, 1.06)], color=FAINT, lw=0.6, ls=(0, (2, 2)), z=1)
    bracket(ax, L_R, R_R, -0.15, color=FAINT, lw=0.6)
    bracket(ax, j0, j1, -0.15, lw=1.1)
    text(ax, ((j0 + j1) / 2, -0.21), r'$J$', va='top')
    text(ax, (-1.0, 0.5), r'$S_{\mathrm{R}}$', color=BLUE, size=10.5)
    k = (j0 + j1) / 2
    text(ax, (k, 0.13), r'$n_{\mathrm{R}}$', color=ORANGE, size=8)
    text(ax, (k, 0.87), r'$1-n_{\mathrm{R}}$', color=ORANGE, size=8)
    save(fig, 'fig-sofa')


# ---- Figure 3: the walls of a turned hallway ----------------------------------------------------

def fig_walls():
    """Romik's cap K_R and the hallway L_- turned by θ = π/5 and moved so that both outer walls touch it.
    Its inner walls lie on the lines y = a_θ(x) and y = b_θ(x), which meet at the inner corner (dot).
    As θ runs over (0, π/2) the inner corner traces the dashed path, and the region below
    c_θ = min(a_θ, b_θ) (darker) sweeps the niche below n_R (orange)."""
    t = PI / 5
    h = romik_support
    a, b = first_wall(h, t), second_wall(h, t)
    c = inner_corner(h, t)
    # The outer walls touch the cap: the polygon K_R attains the support values f(θ) and g(θ).
    hp = polygon_support(CAP_R)
    assert abs(hp([t])[0] - romik.f(t)) < 1e-6 and abs(hp([t + PI / 2])[0] - romik.g(t)) < 1e-6
    # The placement sends the line y = a_θ(x) to the inner wall x = 0 of V_-, the line y = b_θ(x) to
    # the floor y = 0 of H, and the inner corner to the origin.
    for x in np.linspace(-1.5, 1.5, 7):
        assert abs(dotp((x, float(a(x))), uvec(t)) + 1 - romik.f(t)) < 1e-12
        assert abs(dotp((x, float(b(x))), vvec(t)) + 1 - romik.g(t)) < 1e-12
    assert abs(a(c[0]) - c[1]) < 1e-12 and abs(b(c[0]) - c[1]) < 1e-12
    assert math.dist(c, romik.corner(t)) < 1e-12
    # The region below c_θ lies in the niche; the path of the corner lies in the closed niche and
    # reaches its top.
    xs = np.linspace(L_R, R_R, 1201)
    nv = romik.niche(xs)
    assert np.all(np.minimum(a(xs), b(xs)) <= nv + 1e-6)
    path = [romik.corner(s) for s in np.linspace(0, PI / 2, 721)]
    assert all(q[1] <= np.interp(q[0], xs, nv) + 2e-3 for q in path)
    assert abs(max(q[1] for q in path) - nv.max()) < 1e-3
    box = (-1.62, 1.62, -0.72, 1.92)
    fig, (ax,) = panels([box], 1.0)
    big = 3.5
    poly(ax, hall_frame(h, t, [(-big, 0), (0, 0), (0, -big), (1, -big), (1, 1), (-big, 1)]),
         fc=FLOOR, ec='none', z=0)
    poly(ax, CAP_R, fc=BLUE_F, ec=BLUE, lw=1.1, z=2)
    poly(ax, graph_region(xs, nv), fc=ORANGE_F, ec=ORANGE, lw=0.7, z=3)
    poly(ax, graph_region(xs, np.minimum(a(xs), b(xs))), fc=ORANGE, ec='none', alpha=0.3, z=3.2)
    line(ax, path, color=ORANGE, lw=1.0, ls=(0, (3, 1.5)), z=4)
    # The walls: the outer ones, then the inner ones on the two lines, drawn on to the edges.
    line(ax, hall_frame(h, t, [(-big, 1), (1, 1), (1, -big)]), color=WALL, lw=1.6, z=5)
    line(ax, hall_frame(h, t, [(0, 0), (0, -big)]), color=PURPLE, lw=1.6, z=5)
    line(ax, hall_frame(h, t, [(0, 0), (-big, 0)]), color=TEAL, lw=1.6, z=5)
    line(ax, hall_frame(h, t, [(0, 0), (0, big)]), color=PURPLE, lw=0.7, ls=(0, (4, 2)), z=5)
    line(ax, hall_frame(h, t, [(0, 0), (big, 0)]), color=TEAL, lw=0.7, ls=(0, (4, 2)), z=5)
    dot(ax, c, 2.2, INK, z=7)
    td = math.degrees(t)
    pa = hall_frame(h, t, [(0, 1.62)])[0]
    text(ax, add(pa, mul(-0.1, uvec(t))), r'$y=a_\theta(x)$', color=PURPLE, size=7.5, rotation=td - 90,
         rotation_mode='anchor', ha='left', va='center')
    pb = hall_frame(h, t, [(1.25, 0)])[0]
    text(ax, add(pb, mul(0.1, vvec(t))), r'$y=b_\theta(x)$', color=TEAL, size=7.5, rotation=td,
         rotation_mode='anchor', ha='left', va='center')
    # The angle of the turn, at the outer corner.
    oc = hall_frame(h, t, [(1, 1)])[0]
    line(ax, [oc, add(oc, (-0.72, 0))], color=FAINT, lw=0.6, ls=(0, (2, 2)), z=5)
    angle_mark(ax, oc, 0.5, PI, PI + t, r'$\theta$', size=8, dr=0.12)
    text(ax, (-1.0, 0.62), r'$K_{\mathrm{R}}$', color=BLUE, size=10.5)
    text(ax, (0.36, 0.2), r'$n_{\mathrm{R}}$', color=ORANGE, size=8)
    save(fig, 'fig-walls')


# ---- the body T of Figure 5, its hull and its two caps ------------------------------------------

def blob(n=900, a=1.12, p=2.4, tilt=0.05, top_dent=(0.30, -0.25, 0.30), bottom_dent=(0.30, 0.40, 0.28)):
    """A compact connected body in the strip that is not convex: the region between the graphs of bot
    and top over [-a, a], a rounded box with a dent in its top and one in its bottom, scaled to touch
    y = 0 and y = 1. Returns the abscissas and the two graphs."""
    xs = a * np.sin(np.linspace(-PI / 2, PI / 2, n))
    e = 0.5 * np.maximum(1 - np.abs(xs / a) ** p, 0) ** (1 / p)
    c = 0.5 + tilt * xs
    (dt, xt, wt), (db, xb, wb) = top_dent, bottom_dent
    top = c + e - dt * np.exp(-((xs - xt) / wt) ** 2) * (2 * e)
    bot = c - e + db * np.exp(-((xs - xb) / wb) ** 2) * (2 * e)
    lo, hi = bot.min(), top.max()
    return xs, (bot - lo) / (hi - lo), (top - lo) / (hi - lo)


BX, BBOT, BTOP = blob()
T_BODY = list(zip(BX, BTOP)) + list(zip(BX[::-1], BBOT[::-1]))
T_LOWER, T_UPPER = hull_chains(T_BODY)
T_HULL = T_LOWER + T_UPPER[::-1][1:-1]
CAP_U = cap_of(T_UPPER)                   # U = (conv T)^↓
CAP_V = cap_of(rho(T_LOWER))              # V = (ρ(conv T))^↓
ROOF_U, ROOF_V = roof_of(T_UPPER), roof_of(rho(T_LOWER))
H_U = polygon_support(CAP_U)
L_U, R_U = T_UPPER[0][0], T_UPPER[-1][0]


def in_convex(poly_pts, p, tol):
    """1 if p lies in the counterclockwise convex polygon at distance more than tol from its boundary,
    -1 if it lies outside at distance more than tol, 0 otherwise."""
    worst = min(((q[0] - p0[0]) * (p[1] - p0[1]) - (q[1] - p0[1]) * (p[0] - p0[0])) / math.dist(p0, q)
                for p0, q in zip(poly_pts, poly_pts[1:] + poly_pts[:1]) if math.dist(p0, q) > 0)
    return 1 if worst > tol else (-1 if worst < -tol else 0)


def fig_reduction():
    """A compact connected body T in the strip Σ that is not convex; its hull conv T adds the hatched
    regions. The upper boundary of the hull (blue) is the roof of the cap U = (conv T)^↓, and its lower
    boundary (purple), reflected in y = 1/2, is the roof of the cap V = (ρ(conv T))^↓, the reflection
    of the lower cap of the hull. The hull is U ∩ ρ(V)."""
    # T lies in the strip and touches both lines; it is connected (its vertical fibers are intervals,
    # over an interval) and not convex.
    assert abs(BBOT.min()) < 1e-12 and abs(BTOP.max() - 1) < 1e-12
    assert np.all(BTOP[1:-1] > BBOT[1:-1])
    area_t, area_hull = np.trapezoid(BTOP - BBOT, BX), shoelace(T_HULL)
    assert area_hull - area_t > 0.1
    # U and V have the projection of T, and conv T = U ∩ ρ(V): a point of the strip lies in the hull
    # exactly when it lies under the roof of U and its reflection lies under the roof of V.
    assert abs(L_U - BX.min()) < 1e-12 and abs(R_U - BX.max()) < 1e-12
    assert CAP_V[0][0] == CAP_U[0][0] and CAP_V[1][0] == CAP_U[1][0]
    hits = 0
    for x in np.linspace(L_U + 1e-3, R_U - 1e-3, 61):
        for y in np.linspace(0.0, 1.0, 41):
            inside = in_convex(T_HULL, (x, y), 1e-6)
            if inside:
                assert (y <= ROOF_U(x) and 1 - y <= ROOF_V(x)) == (inside > 0), (x, y)
                hits += inside > 0
    assert hits > 500
    # Hence the hull has area ∫ (f_U + f_V - 1) over the projection.
    xs = np.linspace(L_U, R_U, 4001)
    assert abs(np.trapezoid(ROOF_U(xs) + ROOF_V(xs) - 1, xs) - area_hull) < 1e-4
    scale, gap, vgap = 0.6, 0.5, 0.26
    box = (L_U - 0.12, R_U + 0.12, -0.06, 1.06)
    w, h = (box[1] - box[0]) * scale, (box[3] - box[2]) * scale
    W, H = 2 * w + gap, 2 * h + vgap
    fig = plt.figure(figsize=(W, H))
    a1 = frame(fig.add_axes((0, (H - h) / 2 / H, w / W, h / H)), box)
    a2 = frame(fig.add_axes(((w + gap) / W, (h + vgap) / H, w / W, h / H)), box)
    a3 = frame(fig.add_axes(((w + gap) / W, 0, w / W, h / H)), box)
    for ax in (a1, a2, a3):
        for y in (0, 1):
            line(ax, [(box[0], y), (box[1], y)], color=FAINT, lw=0.6, z=1)
    a1.add_patch(Polygon(T_HULL, closed=True, fc='none', ec=FAINT, lw=0, hatch='//////', zorder=1.5))
    poly(a1, T_BODY, fc=GREY_F, ec=INK, lw=0.9, z=2)
    line(a1, T_UPPER, color=BLUE, lw=1.5, z=4)
    line(a1, T_LOWER, color=PURPLE, lw=1.5, z=4)
    text(a1, (-0.62, 0.5), r'$T$', size=10.5)
    xb = -0.1
    text(a1, (0.42, 1.3), r'$\mathrm{conv}\,T$', size=8, ha='left')
    line(a1, [(0.38, 1.27), (xb, float(ROOF_U(xb)) + 0.03)], color=INK, lw=0.5, z=6, clip=False)
    text(a1, (box[1] + 0.04, 1), r'$\Sigma$', color=FAINT, size=8.5, ha='left')
    poly(a2, CAP_U, fc=BLUE_F, ec=BLUE, lw=0.9, z=2)
    line(a2, T_UPPER, color=BLUE, lw=1.5, z=4)
    poly(a2, T_BODY, ec=FAINT, lw=0.5, z=3)
    text(a2, (box[1] + 0.05, 0.5), r'$U$', color=BLUE, size=10.5, ha='left')
    poly(a3, CAP_V, fc=PURPLE_F, ec=PURPLE, lw=0.9, z=2)
    line(a3, rho(T_LOWER), color=PURPLE, lw=1.5, z=4)
    poly(a3, rho(T_BODY), ec=FAINT, lw=0.5, z=3)
    text(a3, (box[1] + 0.05, 0.5), r'$V$', color=PURPLE, size=10.5, ha='left')
    for ax_to in (a2, a3):
        start = fig.transFigure.inverted().transform(a1.transData.transform((box[1] + 0.05, 0.5)))
        end = fig.transFigure.inverted().transform(ax_to.transData.transform((box[0] - 0.05, 0.5)))
        fig.add_artist(FancyArrowPatch(start, end, transform=fig.transFigure, arrowstyle='-|>',
                                       mutation_scale=6, color=FAINT, lw=0.7, shrinkA=0, shrinkB=0))
    save(fig, 'fig-reduction')


# ---- Figure 4: the score of a cap ---------------------------------------------------------------

def fig_score():
    """The score of the cap U of Figure 5 for α = π/2: the area under its roof f_U over the two outer
    quarters of its projection [l_U, r_U] (green) minus the area under the barrier N_{π/2}(U), which is
    the niche, over the middle half J_U (orange). The rest of U does not count."""
    j0, j1 = middle_half(L_U, R_U)
    w = R_U - L_U
    # The outer quarters have the length of J_U, half the width.
    assert abs((j1 - j0) - w / 2) < 1e-12 and abs((j0 - L_U) + (R_U - j1) - w / 2) < 1e-12
    xs = np.linspace(j0, j1, 1201)
    N = partial_barrier(H_U, PI / 2, xs)
    # At the full turn the terminal wall a_{π/2} = h_U(π/2) - 1 = 0 is redundant: the barrier is the
    # niche.
    assert abs(float(first_wall(H_U, PI / 2)(0.0))) < 1e-12
    assert np.max(np.abs(N - swept_niche(H_U, PI / 2, xs))) < 1e-12
    # The barrier lies inside U, and the score is below M/2, the score of Romik's cap (check_romik).
    assert np.all(N <= ROOF_U(xs) + 1e-9)
    p = cap_score(ROOF_U, L_U, R_U, H_U, PI / 2)
    assert p < romik.M / 2 - 0.02 and p <= w / 2
    xl, xr = L_U - 0.1, R_U + 0.1
    fig, (ax,) = panels([(xl, xr, -0.36, 1.06)], 1.25)
    line(ax, [(xl, 0), (xr, 0)], color=FAINT, lw=0.6, z=1)
    line(ax, [(xl, 1), (xr, 1)], color=FAINT, lw=0.6, z=1)
    poly(ax, CAP_U, fc=BLUE_F, ec='none', z=1.5)
    for x0, x1 in ((L_U, j0), (j1, R_U)):
        q = np.linspace(x0, x1, 300)
        poly(ax, graph_region(q, ROOF_U(q)), fc=GREEN_F, ec='none', z=2)
        line(ax, list(zip(q, ROOF_U(q))), color=GREEN, lw=1.5, z=4)
    q = np.linspace(j0, j1, 400)
    line(ax, list(zip(q, ROOF_U(q))), color=BLUE, lw=0.9, z=4)
    for x in (L_U, R_U):
        line(ax, [(x, 0), (x, float(ROOF_U(x)))], color=GREEN, lw=1.5, z=4)
    poly(ax, graph_region(xs, N), fc=ORANGE_F, ec=ORANGE, lw=0.9, z=3)
    for x in (j0, j1):
        line(ax, [(x, -0.15), (x, 1.06)], color=FAINT, lw=0.6, ls=(0, (2, 2)), z=3.5)
    bracket(ax, L_U, R_U, -0.15, color=INK, lw=0.6)
    bracket(ax, j0, j1, -0.15, lw=1.1)
    text(ax, ((j0 + j1) / 2, -0.21), r'$J_U$', va='top')
    text(ax, (L_U, -0.21), r'$l_U$', va='top')
    text(ax, (R_U, -0.21), r'$r_U$', va='top')
    text(ax, (-0.3, 0.7), r'$U$', color=BLUE, size=10.5)
    text(ax, (L_U + 0.2, 0.62), r'$f_U$', color=GREEN, size=9)
    text(ax, (0.06, 0.48), r'$N_{\pi/2}(U)$', color=ORANGE, size=8)
    save(fig, 'fig-score')
    return p


# ---- Figure 6: the barrier of a partial turn ----------------------------------------------------

def fig_barrier():
    """The barrier of the cap U of Figure 5 for a turn that stops at α = 3π/8: the niche n_α swept by
    the inner corner up to α (orange; the corner's path dashed), the first inner wall y = a_α(x) of the
    final placement (purple; the hallway there in grey), and their maximum N_α over the middle half J_U
    (black). Left of the final inner corner the wall is higher, right of it the niche."""
    al = 3 * PI / 8
    j0, j1 = middle_half(L_U, R_U)
    xs = np.linspace(L_U, R_U, 1601)
    n_al, n_full = swept_niche(H_U, al, xs), swept_niche(H_U, PI / 2, xs)
    a = first_wall(H_U, al)
    N = np.maximum(n_al, a(xs))
    mid = (xs >= j0) & (xs <= j1)
    c = inner_corner(H_U, al)
    # The wall passes through the final inner corner, the niche grows with the angle, and over J_U the
    # barrier is the wall left of the corner and the niche right of it; the partial turn scores less.
    assert abs(float(a(c[0])) - c[1]) < 1e-12
    assert np.all(n_al <= n_full)
    left, right = mid & (xs < c[0] - 0.01), mid & (xs > c[0] + 0.01)
    assert np.all(a(xs)[left] > n_al[left]) and np.all(n_al[right] >= a(xs)[right] - 2e-3)
    assert np.max((a(xs) - n_al)[mid]) > 0.2 and np.max((n_al - a(xs))[mid]) > 0.05
    p_al = cap_score(ROOF_U, L_U, R_U, H_U, al)
    p_full = cap_score(ROOF_U, L_U, R_U, H_U, PI / 2)
    assert p_al < p_full - 0.05
    box = (L_U - 0.12, R_U + 0.12, -0.42, 1.12)
    fig, (ax,) = panels([box], 1.25)
    big = 3.5
    poly(ax, hall_frame(H_U, al, [(-big, 0), (0, 0), (0, -big), (1, -big), (1, 1), (-big, 1)]),
         fc=FLOOR, ec='none', z=0)
    line(ax, hall_frame(H_U, al, [(-big, 1), (1, 1), (1, -big)]), color=FAINT, lw=0.9, z=1)
    line(ax, hall_frame(H_U, al, [(0, 0), (-big, 0)]), color=FAINT, lw=0.9, z=1)
    poly(ax, CAP_U, fc=BLUE_F, ec=BLUE, lw=1.0, z=2)
    poly(ax, graph_region(xs, n_al), fc=ORANGE_F, ec=ORANGE, lw=0.7, z=3)
    qx = xs[left]
    poly(ax, list(zip(qx, a(qx))) + list(zip(qx[::-1], n_al[left][::-1])), fc=PURPLE_F, ec='none', z=2.8)
    path = [inner_corner(H_U, s) for s in np.linspace(1e-4, al, 300)]
    line(ax, path, color=ORANGE, lw=1.0, ls=(0, (3, 1.5)), z=4)
    line(ax, hall_frame(H_U, al, [(0, -big), (0, big)]), color=PURPLE, lw=0.8, z=4.5)
    line(ax, list(zip(xs[mid], N[mid])), color=INK, lw=1.6, z=5)
    for x in (j0, j1):
        line(ax, [(x, -0.15), (x, 1.06)], color=FAINT, lw=0.6, ls=(0, (2, 2)), z=3.5)
    bracket(ax, j0, j1, -0.15, lw=1.1)
    text(ax, ((j0 + j1) / 2, -0.21), r'$J_U$', va='top')
    dot(ax, c, 2.2, INK, z=7)
    text(ax, (0.75, 0.62), r'$U$', color=BLUE, size=10.5)
    text(ax, (0.78, 0.3), r'$n_\alpha$', color=ORANGE, size=8.5)
    line(ax, [(0.7, 0.27), (0.36, 0.05)], color=ORANGE, lw=0.5, z=6)
    xn = j0 + 0.2
    text(ax, (xn, float(a(xn)) + 0.1), r'$N_\alpha$', size=8.5)
    xa = R_U - 0.28
    text(ax, (xa, float(a(xa)) - 0.1), r'$y=a_\alpha(x)$', color=PURPLE, size=7.5, ha='left', va='top',
         rotation=math.degrees(al) - 90, rotation_mode='anchor')
    save(fig, 'fig-barrier')
    return p_al, p_full


def main():
    p_r = check_romik()
    fig_intro()
    fig_sofa()
    fig_walls()
    p_u = fig_score()
    fig_reduction()
    p_al, _ = fig_barrier()
    print(f'scores: K_R at π/2 {p_r:.4f} (M/2 = {romik.M / 2:.4f}), U at π/2 {p_u:.4f}, U at 3π/8 {p_al:.4f}')


if __name__ == '__main__':
    main()
