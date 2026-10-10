#!/usr/bin/env python3
"""The figures of the README and of docs/, written to docs/figures/:

- romik-sofa.svg: Romik's ambidextrous sofa, its hull and the two niches;
- supporting-hallway.svg: the sofa in the hallway that turns right, turned by π/4 about it;
- cap-score.svg: the cap of the hull and its score, the quantity that the proof bounds;
- ambidextrous-moving.gif: the sofa in one hallway that turns right, then left.

    python3 scripts/figures/make_figures.py

Every figure is computed from the definitions of the Challenge (romik.py).
"""
import math

import numpy as np

import romik
from sofa_figures import Figure, OUT, FAINT, WALL, FLOOR, COLORS, FILLS, INK

PI = math.pi
BLUE, ORANGE, GREEN = COLORS[0], COLORS[1], COLORS[2]


def niche_regions(n=1200):
    """The two niches as polygons: below n(x) and above 1 - n(x), inside the hull, on J."""
    xs, lo, hi, nv = romik.fibers(n)
    keep = nv > lo + 1e-9
    xs, lo, hi, nv = xs[keep], lo[keep], hi[keep], nv[keep]
    lower = [(x, y) for x, y in zip(xs, nv)] + [(x, y) for x, y in zip(xs[::-1], lo[::-1])]
    upper = [(x, 1 - y) for x, y in lower]
    return lower, upper


def romik_sofa():
    """The sofa, its hull (dashed) and the two niches, between the lines y = 0 and y = 1."""
    left, right = romik.LEFT, romik.RIGHT
    f = Figure(left - 0.25, right + 0.35, -0.42, 1.3, 210)
    f.line((left - 0.2, 0), (right + 0.15, 0), stroke=FAINT, width=1)
    f.line((left - 0.2, 1), (right + 0.15, 1), stroke=FAINT, width=1)
    f.text((right + 0.2, 1), '1', size=14, italic=False, anchor='start', color=FAINT)
    f.text((right + 0.2, 0), '0', size=14, italic=False, anchor='start', color=FAINT)
    f.polygon(romik.sofa(1600), fill=FILLS[0], stroke=BLUE, width=2.2)
    lower, upper = niche_regions()
    for region in (lower, upper):
        f.polygon(region, fill=FILLS[1], stroke=ORANGE, width=1.4, opacity=0.9)
    f.polygon(romik.hull(), stroke=INK, width=1.1, dash='5 4')
    # The path of the inner corner of the hallway that turns right, and its mirror image.
    path = [romik.corner(t) for t in np.linspace(0, PI / 2, 400)]
    vis = [p for p in path if romik.LEFT - 0.05 <= p[0] <= right and p[1] >= -0.25]
    f.polyline(vis, stroke=ORANGE, width=1.3, dash='2 3')
    f.polyline([(x, 1 - y) for x, y in vis], stroke=ORANGE, width=1.3, dash='2 3')
    a, b = romik.J
    for x in (a, b):
        f.line((x, -0.12), (x, 1.12), stroke=FAINT, width=1, dash='3 3')
    f.line((a, -0.2), (b, -0.2), stroke=INK, width=1.2)
    f.text(((a + b) / 2, -0.2), 'J', size=15, dy=13)
    f.text((-0.95, 0.5), 'Σ', size=20, color=BLUE)
    f.text(((a + b) / 2, 0.16), 'n', size=15, color=ORANGE)
    f.text(((a + b) / 2, 0.84), '1 − n', size=15, color=ORANGE)
    return f.save('romik-sofa',
                  "Romik's ambidextrous sofa (blue) between the lines y = 0 and y = 1: its convex "
                  "hull (dashed) without the two niches (orange) that the inner corners of the two "
                  "hallways sweep over the middle half J of its projection")


def supporting_hallway(phi=PI / 4):
    """The sofa in its frame, inside the hallway that turns right, turned by φ about it."""
    xmin, xmax, ymin, ymax = -2.45, 1.75, -1.55, 2.35
    f = Figure(xmin, xmax, ymin, ymax, 120)
    c = (1 - romik.f(phi), 1 - romik.g(phi))

    def frame(q):
        return romik.rot(phi, (q[0] - c[0], q[1] - c[1]))

    far = 9
    f.polygon([frame(q) for q in [(-far, 0), (0, 0), (0, -far), (1, -far), (1, 1), (-far, 1)]],
              fill=FLOOR, stroke='none', width=0)
    pts = romik.sofa(1400)
    for q in romik.place(phi, pts[::5]):
        assert romik.in_lower_hallway(q, 1e-3), q
    f.polygon(pts, fill=FILLS[0], stroke=BLUE, width=2.0)
    lower, upper = niche_regions()
    f.polygon(lower, fill=FILLS[1], stroke=ORANGE, width=1.2, opacity=0.9)
    f.polyline([frame(q) for q in [(-far, 1), (1, 1), (1, -far)]], stroke=WALL, width=2.6)
    f.polyline([frame(q) for q in [(-far, 0), (0, 0), (0, -far)]], stroke=WALL, width=2.6)
    path = [romik.corner(t) for t in np.linspace(0, PI / 2, 400)]
    f.polyline(path, stroke=ORANGE, width=1.8)
    x = romik.corner(phi)
    f.dot(x, r=3.6, fill=ORANGE)
    f.text((x[0] + 0.32, x[1] + 0.2), 'x(π/4)', size=15, color=ORANGE, anchor='start')
    f.text((-0.95, 0.5), 'Σ', size=19, color=BLUE)
    return f.save('supporting-hallway',
                  "Romik's ambidextrous sofa in its own frame, inside the hallway that turns right, "
                  "turned by π/4 about it with its outer walls touching the sofa's hull: the inner "
                  "corner x(π/4) lies on the orange path that the corner traces during the turn, "
                  "which bounds the niche")


def cap_score():
    """The upper cap of the hull and its score: the roof over the two outer quarters of the
    projection, minus the niche over the middle half J."""
    left, right = romik.LEFT, romik.RIGHT
    f = Figure(left - 0.3, right + 0.3, -0.5, 1.25, 210)
    xs, lo, hi, nv = romik.fibers(1600)
    a, b = romik.J
    for piece in (xs <= a, xs >= b):
        px, ph = xs[piece], hi[piece]
        f.polygon([(px[0], 0)] + list(zip(px, ph)) + [(px[-1], 0)], fill=FILLS[2], stroke='none',
                  width=0)
    mid = (xs >= a) & (xs <= b)
    f.polygon([(a, 0)] + list(zip(xs[mid], hi[mid])) + [(b, 0)], fill='#f9fafb', stroke='none',
              width=0)
    mx, mn = xs[mid], nv[mid]
    f.polygon([(mx[0], 0)] + list(zip(mx, mn)) + [(mx[-1], 0)], fill=FILLS[1], stroke=ORANGE,
              width=1.4)
    f.polyline(list(zip(xs, hi)), stroke=GREEN, width=2.2)
    f.line((left, 0), (right, 0), stroke=INK, width=1.6)
    for x in (a, b):
        f.line((x, 0), (x, 1.08), stroke=FAINT, width=1, dash='3 3')
    f.line((left, -0.2), (right, -0.2), stroke=INK, width=1.2)
    f.text(((left + right) / 2, -0.2), 'I', size=15, dy=13)
    f.line((a, -0.34), (b, -0.34), stroke=INK, width=1.2)
    f.text(((a + b) / 2, -0.34), 'J', size=15, dy=13)
    f.text((left + 0.35, 0.28), 'A', size=17, color=GREEN)
    f.text(((a + b) / 2, 0.2), 'N', size=17, color=ORANGE)
    f.text(((a + b) / 2, 0.62), 'U', size=18, color=INK)
    return f.save('cap-score',
                  "The upper cap U of the hull of Romik's sofa, with its roof A over its projection "
                  "I: the score of U is the area under the roof over the two outer quarters of I "
                  "(green) minus the area of the niche N over the middle half J (orange); for "
                  "Romik's cap it is M/2")


def animation(name='ambidextrous-moving.gif', width=760, frames=(18, 56, 26, 56, 18), D=2.0):
    """One hallway with two corners: it turns right, then left. The sofa slides in, turns right
    (clockwise) at the first corner, slides down the middle corridor, turns left (counterclockwise) at
    the second corner, and leaves. Near each corner the hallway is the hallway that turns right, or
    the one that turns left, rotated by a quarter turn; the sofa makes the two turns of the
    definition, the second starting in the same orientation relative to its corridor as the first."""
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    from matplotlib.patches import Polygon
    from PIL import Image

    pts = romik.sofa(900)

    def second(q):
        # The left turn of the reference motion, carried to the second corner: the mirror image in
        # y = 1/2, then a clockwise quarter turn and a translation that puts the inner corner at
        # (1, -D).
        return [(1 - y, -x - D) for x, y in q]

    def in_hallway(q, eps=1e-3):
        x, y = q
        incoming = x <= 1 + eps and -eps <= y <= 1 + eps
        middle = -eps <= x <= 1 + eps and -D - 1 - eps <= y <= 1 + eps
        outgoing = x >= -eps and -D - 1 - eps <= y <= -D + eps
        return incoming or middle or outgoing

    slide_in, slide_out = 1.25, 1.35
    gap = D + 2 - 8 * romik.A / 3          # from the end of the first turn to the second corner
    n_in, n_turn1, n_mid, n_turn2, n_out = frames
    poses = []
    for k in range(n_in):
        s = slide_in * (1 - k / n_in)
        poses.append([(x - s, y) for x, y in romik.place(0, pts)])
    for k in range(n_turn1 + 1):
        poses.append(romik.place(PI / 2 * k / n_turn1, pts))
    end1 = romik.place(PI / 2, pts)
    for k in range(1, n_mid):
        s = gap * k / n_mid
        poses.append([(x, y - s) for x, y in end1])
    for k in range(n_turn2 + 1):
        poses.append(second(romik.place(PI / 2 * k / n_turn2, pts)))
    end2 = second(romik.place(PI / 2, pts))
    for k in range(1, n_out + 1):
        s = slide_out * k / n_out
        poses.append([(x + s, y) for x, y in end2])
    for q in poses:
        for p in q[::4]:
            assert in_hallway(p), p
    xs = [x for q in poses for x, _ in q]
    xmin, xmax = min(xs) - 0.35, max(xs) + 0.35
    ymin, ymax = -D - 1.3, 1.3
    w_in = width / 100
    h_in = w_in * (ymax - ymin) / (xmax - xmin)
    floor = [(xmin, 1), (1, 1), (1, -D), (xmax, -D), (xmax, -D - 1), (0, -D - 1), (0, 0), (xmin, 0)]
    images = []
    for q in poses:
        fig = plt.figure(figsize=(w_in, h_in), dpi=100)
        ax = fig.add_axes([0, 0, 1, 1])
        ax.set_xlim(xmin, xmax)
        ax.set_ylim(ymin, ymax)
        ax.set_aspect('equal')
        ax.axis('off')
        ax.add_patch(Polygon(floor, closed=True, facecolor=FLOOR, edgecolor='none'))
        ax.plot([xmin, 1, 1, xmax], [1, 1, -D, -D], color=WALL, lw=2.6, solid_capstyle='butt')
        ax.plot([xmin, 0, 0, xmax], [0, 0, -D - 1, -D - 1], color=WALL, lw=2.6,
                solid_capstyle='butt')
        ax.add_patch(Polygon(q, closed=True, facecolor=FILLS[0], edgecolor=BLUE, lw=1.6))
        fig.canvas.draw()
        rgba = np.asarray(fig.canvas.buffer_rgba())
        images.append(Image.fromarray(rgba[:, :, :3].copy()))
        plt.close(fig)
    durations = [45] * len(images)
    durations[0] = durations[-1] = 800
    pal = images[len(images) // 2].quantize(colors=48, method=Image.Quantize.MEDIANCUT)
    frames_q = [im.quantize(palette=pal, dither=Image.Dither.NONE) for im in images]
    path = OUT / name
    path.parent.mkdir(parents=True, exist_ok=True)
    frames_q[0].save(path, save_all=True, append_images=frames_q[1:], duration=durations,
                     loop=0, optimize=True, disposal=1)
    return path


def main():
    print(f'area of the computed sofa: {romik.area():.7f} (M = {romik.M:.7f})')
    for p in (romik_sofa(), supporting_hallway(), cap_score(), animation()):
        print(f'wrote {p.relative_to(OUT.parents[1])} ({p.stat().st_size // 1024} KiB)')


if __name__ == '__main__':
    main()
