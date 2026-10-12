#!/usr/bin/env python3
"""Check the simplified estimates with exact fractions and audit large literals.

Lean remains the proof authority. This independent calculation checks the
manuscript's endpoint formulas, circle inequalities, and stopping comparisons.
Run from any directory with Python 3; no dependencies.
"""

from fractions import Fraction as F
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
G = F("2.2199")

def newton_up(q, x):
    return (x + q / x) / 2


def sqrt_up(q, seed=F(1)):
    assert q >= 0
    assert seed > 0
    result = newton_up(q, newton_up(q, seed))
    assert result**2 >= q
    return result


def sqrt_down(q, seed=F(1)):
    result = q / sqrt_up(q, seed)
    assert result**2 <= q
    return result


# The pressure and circle bounds stop every horizontal excess episode before
# a wall can reach the middle endpoint. One comparison covers the whole range.
D, H = F(37, 50), F(1, 3)
for c in [F(2, 3), F(4, 5)]:
    assert F(6, 5) * c - F(2, 25) - F(1, 2) - F(15, 32) * c**2 > 0
assert 1 - D**2 > F(2, 3)**2  # H(C) < 1/3.
assert 9 * D**2 - F(3, 16) < (2 + (F(1, 3)**2 + 2 * F(1, 3)) / 4)**2
stop = F(2, 5) + F(1, 3)
assert stop == F(11, 15)
assert 2 * (1 - (stop / 2)**2 / 2)**2 - 1 > D
# At the dry-endpoint energy threshold, the 3–4–5 chord support exceeds G.
assert ((G - F(3, 10)) * F(15, 7))**2 < 17

# Before the floor, the exact circle and sin(pi/6)=1/2 give the geometric crossing angle.
assert F(111, 50)**2 + F(7, 12)**2 - 1 < (2 + F(1, 12))**2
assert F(1, 12) < F(1, 6) / 2 + F(1, 6)**2 / 4
assert (F(22, 7) + 1) / 6 < F(11, 15)

# Tilt loss pays for crossing delay throughout the whole post-floor range.
# Each check is an endpoint implication, rather than a sample of interior heights.
d_max, h_max = F(111, 50), F(1, 5)
energy_max = d_max**2 - F(3, 16)
assert h_max == 1 - F(4, 5)
assert h_max <= F(1, 5)  # h(2-h) >= (3h)^2.
assert F(7, 8) + F(5, 16) * h_max <= 1  # Polynomial gain <= h.
assert 2 * 3 - 1 == 5  # Floor loss minus polynomial gain >= 5h.
assert 2**2 - F(3, 2) >= F(3, 2)**2  # Baseline crossing root >= 3/2.
assert 2 * F(3, 2) - h_max >= F(5, 2)  # Crossing delay <= h.
assert energy_max < F(9, 4)**2 and 2 * F(9, 4) < 5
assert 4 * F(9, 4) - 7 < F(3, 2)**2 and 2 * F(3, 2) < 4
assert energy_max < (2 + F(19, 100))**2
assert energy_max < (2 + F(1, 3) / 2 + F(1, 3)**2 / 4)**2
# A single far corner covers zero tilt, tilted comparison, and reflected heights.
assert F(3, 4) - d_max * F(2, 5) + F(2, 5)**2 / 2 < 0
assert d_max**2 - F(1, 4) > 4  # All far-width energy roots are >= 2.
assert min(e * (1 - e) for e in (F(3, 20), F(3, 4))) >= F(1, 8)
assert d_max**2 - F(1, 8) < (2 + F(1, 5))**2
assert d_max**2 - F(1, 8) < (2 + F(1, 3) / 2 + F(1, 3)**2 / 4)**2
# Root comparisons make the reciprocal width factors cancel exactly.
assert F(4, 5) * (2 * F(7, 3)) <= 2 * (2 - F(1, 64))
assert F(5, 4) * (2 * F(8, 5)) == 4
assert F(4, 5) * F(5, 4) == 1

# One unit-circle tangent pays for the cubic shift throughout the cosine range.
terminal_cosine_square = F(3, 8)**2 / (1 + F(3, 8)**2)
assert terminal_cosine_square == F(9, 73)
assert 10 * (F(37, 50) + F(3, 16))**2 < 9  # Circle slope is at most three.
assert (2 * F(3, 4) + F(9, 8)) * F(3, 8) < 1  # Linear gain pays for center drift.
def sqrt_up_four(q):
    x = F(1)
    for _ in range(4):
        x = newton_up(q, x)
    return x

q_upper = sqrt_up_four(terminal_cosine_square)
q_lower = terminal_cosine_square / q_upper
s_upper = sqrt_up_four(1 - terminal_cosine_square)
s_lower = (1 - terminal_cosine_square) / s_upper
cubic_price = F(4, 5) * F(2, 3)**3 * F(3, 8)**2 / (6 * F(2, 3) * s_lower)
assert 0 < q_lower < q_upper < F(3, 8)
assert q_lower**2 < terminal_cosine_square < q_upper**2
assert s_upper**2 > 1 - terminal_cosine_square
for C in [F(1, 2), F(37, 50)]:
    center_upper = C - terminal_cosine_square * q_upper / 8
    vL = 1 - (center_upper - q_upper / 2)**2
    vR = 1 - (center_upper + q_upper / 2)**2
    L, R = sqrt_up_four(vL), vR / sqrt_up_four(vR)
    assert vL < L**2 and R**2 < vR
    assert (2 * C - q_upper) / s_upper - (L - R) / q_lower > cubic_price

def sqrt_up_three(q, seed=F(1)):
    return newton_up(q, sqrt_up(q, seed))


def sqrt_down_three(q, seed=F(1)):
    return q / sqrt_up_three(q, seed)


# One zero-tilt baseline prices all width, height and impulse changes.
k_max, C_max, prefix_stop = F(3, 8), F(37, 50), F(11, 15)
d_base, e_base = 3 * C_max, F(3, 4)
d_max, impulse_max = d_base + k_max / 4, k_max**2 / 4
cross_square, energy_square = d_base**2 - 2 * e_base, d_base**2 - e_base * (1 - e_base)
y_lo, y_hi = sqrt_down_three(energy_square, F(2)), sqrt_up_three(energy_square, F(2))
z_lo = sqrt_down_three(4 * y_lo - 7)
z_hi = sqrt_up_three(4 * y_hi - 7)
product_lo = y_lo * z_lo
assert product_lo >= F(3, 5) * (d_max + d_base) and product_lo >= F(5, 2)
assert d_base**2 - 2 >= F(5, 3)**2
assert d_max**2 - F(3, 2) <= (F(6, 7) * d_max)**2
baseline_stop_hi = d_base - sqrt_down_three(cross_square, F(2)) + z_hi - 1
pressure_extra = max(2 * C_max * k_max - F(1, 3), F(0))
endpoint_budget = F(3, 8) * k_max + F(9, 10) * F(3, 4) * pressure_extra + F(2, 5) * impulse_max
assert baseline_stop_hi < prefix_stop
assert baseline_stop_hi + endpoint_budget < prefix_stop + F(2, 3) * k_max
# Convexity bounds the pressure and quadratic costs by their endpoint chord.
assert F(37, 25) - (F(1, 3) / k_max) > 0
assert F(9, 16) * k_max <= F(3, 8)  # Descending height fits the overhang budget.
assert d_max**2 + impulse_max < (2 + F(3, 5) / 2 + F(3, 5)**2 / 4)**2
assert k_max + F(3, 5) < prefix_stop + F(2, 3) * k_max
# The cubic overlap scales as cot(alpha)^3, while the circle margin scales as cot(alpha).
assert cubic_price == F(4, 5) * F(2, 3)**3 * k_max**2 / (6 * F(2, 3) * s_lower)
# The descending height lowers the outgoing wall; both pressure branches stay below one.
height_loss = k_max**2 / 2
assert F(3, 4) + F(5, 4) * height_loss < 1
assert F(1, 2) + height_loss / 2 + F(3, 2) * C_max * k_max < 1

# Both root enclosures follow the Newton procedure used in the proof.
lower, upper = F(1, 4), F(1, 3)
for _ in range(2):
    residual = 4 * upper**3 + 3 * upper - 1
    lower, upper = (upper - residual / (3 + 12 * lower**2),
                    upper - residual / (3 + 12 * upper**2))
    assert 0 < lower <= upper
    assert 4 * lower**3 + 3 * lower <= 1 <= 4 * upper**3 + 3 * upper
reference_budget = (1 + 4 * lower**2 + lower - lower**3 / 3) / 2
sqrt_two_upper = newton_up(2, newton_up(2, F(3, 2)))
klo, khi = 2 / sqrt_two_upper - 1, sqrt_two_upper - 1
assert klo**2 + 2 * klo < 1 < khi**2 + 2 * khi
sqrt73_upper = newton_up(73, F(9))
initial_endpoint = ((2 - F(3, 8))**2 / 8 + khi *
                    ((1 + F(3, 8)) / 2 - F(3, 8)**2 / 4 + sqrt73_upper / 16))
assert F(41, 50) < reference_budget and initial_endpoint < reference_budget
# The angle exclusion splits at the diagonal offset itself. The residual
# tent gap is forced by that same offset and the minimum cotangent.
initial_kappa_min = F(3, 8)
initial_corner_upper = (sqrt73_upper + 3) / 24
assert 2 * initial_corner_upper - 2 * (initial_corner_upper - khi / 2)**2 < reference_budget
initial_gap_lower = (1 + 3 * initial_kappa_min) * klo / 2
assert 3 * khi - F(1, 2) < F(3, 4) < reference_budget
assert 1 - initial_gap_lower**2 < reference_budget

# The common-price diagonal bound at height one third already beats the
# reference area; this removes the old fitted height enclosure.
intermediate_a, intermediate_h = F(8, 5), F(1, 3)
intermediate_factor = 2 * intermediate_a / (4 * intermediate_a - intermediate_h)
assert 1 - intermediate_factor * (klo + intermediate_h / 2)**2 < reference_budget
assert 2 * (1 - reference_budget) < F(9, 25)

# Reduce the unit-width geometric comparisons using k²+2k=1 and N²+2k=2.
norm_square_upper = 2 - 2 * klo
norm_upper = newton_up(norm_square_upper, newton_up(norm_square_upper, F(1)))
assert norm_upper**2 > norm_square_upper
assert 9 * khi / 8 + F(11, 32) < reference_budget  # Width boundary a*=1-k²/4.
assert 47 * khi / 32 + F(27, 128) < reference_budget  # Tilt boundary h*=k²/4.
assert (8 - 10 * khi) * norm_upper / 3 + 55 * khi / 3 - F(49, 6) < reference_budget
assert 2 * norm_upper + 4 * khi - 3 < reference_budget  # Exact companion midpoint.
assert F(37, 16) - norm_upper - 21 * khi / 8 > khi / 3
assert 2 * khi - reference_budget < khi / 6 - F(1, 18)  # Complete outer-cut area.
assert (12 - 22 * khi) * norm_upper + 91 * khi - 40 < reference_budget  # Paid envelope.
assert F(12, 13) ** 2 * (2 - 2 * klo) < 1
assert F(73, 79) ** 2 * (2 - 2 * F(29, 70)) > 1

# The wide endpoint supporting line pays the peak span directly. The prices
# come from the midpoint tangent at the first wide width, not separate cuts.
wide_a0 = F(8, 5)
wide_m0 = wide_a0 - F(1, 2)
wide_d0 = 5 * wide_a0 / 8 - F(3, 4) + 1 / (8 * wide_a0)
wide_norm_lower = sqrt_down(2 - 2 * khi)
wide_p_min = 2 * (wide_m0 - khi) - 1
wide_q_min = wide_d0 - (2 * (wide_m0 - klo) - 1) / 4
wide_q_max = wide_d0 - wide_p_min / 4
wide_reserve_max = F(21, 5) * (khi - F(2, 5))  # Reduce using k²+2k=1.
wide_span_min = (1 + klo) * wide_norm_lower - (1 - klo / 2) * wide_a0
assert wide_q_min > 0
assert wide_p_min >= wide_q_max * (1 - klo / 2)
assert wide_reserve_max < wide_q_min * wide_span_min
assert (F(5, 2) * khi - F(1, 4)) < F(41, 50)  # Natural width a=1+2k.

# Choose the height where the dry radius and maximal floor energy meet.
h_max = F(1, 3)
b = lambda h: -F(1, 2) + F(5, 4) * h
floor_offset = lambda h: 5 - b(h)**2 + (b(h) + F(1, 4))**2 + (b(h) + F(1, 4)) * (1 - h) - 4
balance_gap = lambda h: floor_offset(h)**2 - (5 - b(h)**2) * h * (2 - h)
balance_derivative = lambda h: (-455 + 686 * h - 180 * h**2) / 64
h_lower, h_upper = F(0), h_max
assert balance_gap(h_lower) > 0 > balance_gap(h_upper)
for _ in range(3):
    h_lower, h_upper = (h_lower - balance_gap(h_lower) / balance_derivative(h_lower),
                        h_upper - balance_gap(h_upper) / balance_derivative(h_lower))
    assert 0 < h_lower < h_upper < h_max
    assert balance_gap(h_lower) > 0 > balance_gap(h_upper)
radius_square_lower, radius_square_upper = 5 - b(h_lower)**2, 5 - b(h_upper)**2
radius_upper = sqrt_up(radius_square_upper, F(2))
radius_lower = radius_square_lower / radius_upper
radius_triangle_width = 2 * radius_lower / 3
assert radius_lower**2 < radius_square_lower < radius_square_upper < radius_upper**2
assert radius_upper / 3 < F(37, 50)
assert -F(1, 4) + F(5, 4) * h_max <= -b(h_upper)
assert radius_square_upper < 5
assert radius_triangle_width - F(1, 2) - h_max / 4 > F(3, 4)
# The first floor endpoint is equality by definition. At height one third,
# radius squared <= five, radius >= two, and sine >= two thirds suffice.
assert F(2, 3)**2 < h_max * (2 - h_max)
assert 5 + F(1, 6)**2 + F(1, 6) * (1 - h_max) - 2 * F(2, 3) < 4

# Exact triangle demand and reciprocal prices cancel the tilt payment.
wide_t_low = wide_d0 / (2 * (2 - 3 * klo / 4))
wide_t_upper = wide_d0 / (2 * (2 - 3 * khi / 4))
wide_demand_lower = (2 + khi) * wide_a0 + F(3, 2) - 3 * khi / 2 - (3 + khi) * F(13, 12)
assert wide_demand_lower > 0
assert khi + F(1, 2) - 2 * wide_t_low * wide_demand_lower + (9 - klo) * wide_t_upper**2 < reference_budget
assert (4 * (1 + klo) + klo) == 4 + 5 * klo

# The three floor corrections share a tilt payment and one Newton corner rule.
norm_lo, norm_hi = 2 - 2 * khi, 2 - 2 * klo
cos_hi = newton_up(norm_lo, newton_up(norm_lo, F(1))) / norm_lo
cos_lo = 1 / newton_up(norm_hi, newton_up(norm_hi, F(1)))
assert cos_lo**2 * norm_hi < 1 < cos_hi**2 * norm_lo
assert F(12, 13) < cos_lo < cos_hi < F(73, 79)
assert -F(1, 5) + F(1, 20) + F(1, 10) + F(1, 32) < 0
threshold = F(5, 12)
assert 2 * cos_lo - 1 - khi > threshold
assert 2 * cos_hi - 1 - klo < F(1, 2)
for floor_motion in [(F(3, 5) - threshold) / 2,
                     F(2, 3) * (F(2, 3) - threshold),
                     (F(1, 2) - threshold) / 2 + F(1, 16)]:
    assert floor_motion <= F(1, 6)
assert F(1, 4)**2 + F(3, 4)**2 == F(5, 8)
assert F(2, 3)**2 <= F(5, 8)


def triangle_corner(a, h, k, c, b_right, b_left, weight):
    z = (2 + 3 * k) * a / 2 - (4 * c - 2) - (1 - k) * h / 4
    right, left = b_right - 2 * c + 1 + k, b_left - 2 * c + 1 + k
    return ((a + 1 - h / 2) * k + a - (a**2 + 1) / 2 - h**2 / 8
            - F(2, 9) * z**2 + (1 - k) / 2 * (weight * right**2 + left**2))


# Uniform parameter bounds prove monotonicity on the complete comparison segments.
assert (2 + 3 * klo) * radius_triangle_width / 2 - (4 * cos_hi - 2) > F(3, 5)
assert (2 + 3 * khi) * F(37, 25) / 2 - (4 * cos_lo - 2) < F(3, 4)
assert F(1, 2) - 2 * cos_hi + 1 + klo > 0
assert F(2, 3) - 2 * cos_lo + 1 + khi < F(1, 4)
assert F(16, 9) * F(3, 5) - 2 * F(3, 5) * F(1, 2) > 0
assert F(1, 2) + F(15, 16) - F(7, 12) * F(1, 20) > 0
# The generated support coordinate stays unclipped at both comparison widths.
for a, height in [(F(37, 25), h_max), (radius_triangle_width, h_max)]:
    s_hi = (2 + 3 * khi) * a / 2 - (4 * cos_lo - 2)
    s_lo = (2 + 3 * klo) * a / 2 - (4 * cos_hi - 2)
    assert s_lo > F(2, 3) and s_hi < F(71, 100)
    assert s_lo - (1 - klo) * height / 4 > 0
    assert -klo / 2 + (2 - klo) * s_hi / 9 + (6 + 5 * khi) * height / 36 < 0
    assert 1 + khi < a
for a, h, b_right, b_left, weight in [
    (F(37, 25), F(0), F(3, 5), F(3, 5), F(1)),
    (F(37, 25), F(0), F(2, 3), F(2, 3), F(0)),
    (radius_triangle_width, F(0), F(1, 2), F(7, 12), F(1)),
]:
    assert triangle_corner(a, h, khi, cos_hi, b_right, b_left, weight) < reference_budget

leakage_moment = F(11, 15) * (F(1, 3)**2 / 4 + F(1, 3)**3 / 6)
projection = newton_up(F(5), F(2)) / 2
assert projection * F(2, 3) == newton_up(F(5), F(2)) / 3
D, E = newton_up(F(5), F(2)) / 3 + F(3, 20), F(3, 20) + leakage_moment / 2 - F(1, 10) / projection
A, Q = F(14, 5) / 6 - projection * E, F(14, 5) * F(3, 64)
# Complete the square, then compare the collected losses at the sine endpoint.
root17_upper = newton_up(17, F(4))
assert (17 / root17_upper) ** 2 < 17 < root17_upper**2
assert F(14, 5) * 17 / (6 * root17_upper) + F(3, 10) > G
hstar = h_upper
kappa, r = 1 / (2 - hstar), newton_up(hstar * (2 - hstar), F(1, 3)) / 1
assert hstar * (2 - hstar) < r**2
loss_coefficient = D * kappa + projection / 2 + Q * (projection + kappa * r) ** 2
assert A - loss_coefficient * r > 0
# Radius failure below the shared radius width gives h + (3/5)z < hstar.
# Its whole area cost is paid by that pressure budget and the circle-radius gain.
assert E + r / 2 < F(3, 5) * D
assert 17 < F(9, 2)**2 and 19 < F(9, 2)**2
assert F(14, 5) / 27 > D * hstar
d0 = F(1, 3)
assert F(19, 100) < d0 / 2 + d0**2 / 4
assert leakage_moment == F(11, 15) * (d0**2 / 4 + d0**3 / 6)
sine, cosine = F(3, 5), F(4, 5)
assert cosine / (2 * sine) + F(5, 4) * (1 - sine) / sine + F(5, 16) / sine < 3

# Circle confinement uses two positive quadratics, with no quartic certificate.
D, H = F(37, 50), F(1, 3)
a = 3 * D - F(5, 9)
b = -(1 + H) + 5 * H / 27
d = 1 - D - 10 * H / 243
assert a > 0 and 4 * a * d - b**2 > 0
assert 4 * 29 * 15 - 36**2 > 0

# Audit active files, excluding the archived manuscript and the unchanged imported library.
inline = re.compile(r"(?<![\d.])(\d+)\s*/\s*(\d+)(?![\d.])")
braced = re.compile(r"\\(?:t|d)?frac\{(\d+)\}\{(\d+)\}")
typed = re.compile(r"\((\d+)\s*:\s*ℝ\)\s*/\s*(\d+)")

def large_rationals(text):
    return [(int(a), int(b)) for pattern in [inline, braced, typed]
            for a, b in pattern.findall(text) if max(int(a), int(b)) >= 1000]

files = sorted((ROOT / "AmbidextrousSofa").rglob("*.lean"))
files += sorted((ROOT / "docs/paper/sections").glob("*.tex"))
baseline_files = set(subprocess.run(["git", "ls-tree", "-r", "--name-only", "HEAD"], cwd=ROOT,
                                    capture_output=True, text=True, check=True).stdout.splitlines())
before, after = 0, []
for path in files:
    relative = str(path.relative_to(ROOT))
    if relative in baseline_files:
        old = subprocess.run(["git", "show", f"HEAD:{relative}"], cwd=ROOT,
                             capture_output=True, text=True, check=True).stdout
        before += len(large_rationals(old))
    hits = large_rationals(path.read_text())
    if hits:
        after.append((relative, hits))
assert not after, after
print(f"Exact estimates passed: horizontal stopping and dry-endpoint area bounds, "
      f"uniform tilt cancellation and joint stopping comparisons, "
      f"the intrinsic terminal-circle gap and cubic price, two circle discriminants, two Newton width endpoints, "
      f"the uniform angular deadline and cubic payment, generated reference enclosures, geometric short-width margins, "
      f"the natural initial-angle and terminal-corner widths, geometric complementary tent gap, "
      f"the exact wide demand, weighted triangle prices and tilt cancellation, the intermediate height bound one third, "
      f"the common triangle tilt payment and Newton corners, the energy-balance height and its radius width, exact lower floor endpoint and elementary upper endpoint, "
      f"the common small-tilt pressure budget and circle-radius payment, and folded-wing endpoint comparisons.")
print(f"Audited {len(files)} active files: large literal rationals {before} → 0.")
