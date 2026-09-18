"""Generator-side lower checker. Lean checks every emitted certificate again."""

from functools import lru_cache

from interval import Interval, ONE, PI, PI2_LO, UNIT, ZERO, sincos, sincos_point


def det(a, b):
    return a[0] * b[1] - a[1] * b[0]


def rotate(s, c, v):
    return c * v[0] - s * v[1], s * v[0] + c * v[1]


@lru_cache(maxsize=1)
def bodies():
    r = Interval.ratio(3).sqrt()
    t = (
        (Interval.ratio(-1, 4), -(r * Interval.ratio(1, 12))),
        (Interval.ratio(1, 4), -(r * Interval.ratio(1, 12))),
        (ZERO, r * Interval.ratio(1, 6)),
    )
    s, c = sincos(PI * Interval.ratio(11, 24))
    s2, c2 = sincos(PI * Interval.ratio(11, 12))
    k, two, three = Interval.ratio(1, 12), Interval.ratio(2), Interval.ratio(3)
    u = (
        (-(three + two * c + c2) * k, -(two * s + s2) * k),
        ((UNIT - two * c - c2) * k, -(two * s + s2) * k),
        ((UNIT + two * c - c2) * k, (two * s - s2) * k),
        ((UNIT + two * c + three * c2) * k, (two * s + three * s2) * k),
    )
    y = Interval.ratio(8745).sqrt() * Interval.ratio(1, 1024)
    crown = (
        (Interval.ratio(-7, 16), ZERO),
        (Interval.ratio(49, 128), -y),
        (Interval.ratio(7, 16), ZERO),
        (Interval.ratio(-49, 128), y),
    )
    return t, u, crown


def c_header():
    """Serialize the fixed vertices for native generators."""
    vertices = [(-1, (Interval.ratio(-1, 2), ZERO)), (-1, (Interval.ratio(1, 2), ZERO))]
    vertices.extend((i, vertex) for i, body in enumerate(bodies()) for vertex in body)
    rows = (
        f"    {{{{{x.lo}LL, {x.hi}LL}}, {{{y.lo}LL, {y.hi}LL}}, {i}}},\n" for i, (x, y) in vertices
    )
    return "static const Vertex base_vertices[13] = {\n" + "".join(rows) + "};\n"


def root_box():
    x, y = Interval.ratio(603894, 1000000).hi, Interval.ratio(478, 1000).hi
    return (
        Interval(0, (PI * Interval.ratio(1, 3)).hi),
        Interval(0, (PI * Interval.ratio(2)).hi),
        Interval(0, PI.hi),
        *(Interval(-r, r) for _ in range(3) for r in (x, y)),
    )


@lru_cache(maxsize=32768)
def rotated_body(body, midpoint):
    s, c = sincos_point(midpoint)
    return tuple((body, rotate(s, c, v)) for v in bodies()[body])


def box_data(box):
    points = [(-1, (Interval.ratio(-1, 2), ZERO)), (-1, (Interval.ratio(1, 2), ZERO))]
    variables = []
    for i in range(3):
        mid, radius = box[i].midpoint(), box[i].radius()
        if not (-64 * ONE <= mid <= 64 * ONE and 0 <= radius <= PI2_LO):
            return None
        points.extend(rotated_body(i, mid))
        s, c = sincos_point(radius)
        variables.extend(
            (box[3 + 2 * i], box[4 + 2 * i], Interval(c.lo, ONE), Interval(-s.hi, s.hi))
        )
    return points, variables


def scale(a, polynomial):
    return [(s, a * c) for s, c in polynomial]


def multiply(p, q):
    return [(s + t, a * b) for s, a in p for t, b in q]


def coordinate(i):
    return [((i,), UNIT)]


def xy_polynomials(body, vertex):
    x, y = vertex
    tx, ty, c, s = range(4 * body, 4 * body + 4)
    return (
        coordinate(tx) + scale(x, coordinate(c)) + scale(-y, coordinate(s)),
        coordinate(ty) + scale(y, coordinate(c)) + scale(x, coordinate(s)),
    )


def edge(a, b):
    i, v = a
    j, w = b
    if i < 0 and j < 0:
        return [((), det(v, w))]
    if i < 0:
        x, y = xy_polynomials(j, w)
        return scale(v[0], y) + scale(-v[1], x)
    if j < 0:
        x, y = xy_polynomials(i, v)
        return scale(w[1], x) + scale(-w[0], y)
    if i == j:
        tx, ty, c, s = range(4 * i, 4 * i + 4)
        return [
            ((), det(v, w)),
            ((tx, c), w[1] - v[1]),
            ((tx, s), w[0] - v[0]),
            ((ty, c), v[0] - w[0]),
            ((ty, s), w[1] - v[1]),
        ]
    vx, vy = xy_polynomials(i, v)
    wx, wy = xy_polynomials(j, w)
    return multiply(vx, wy) + scale(Interval.ratio(-1), multiply(vy, wx))


def fan(a, b, c):
    return edge(a, b) + edge(b, c) + edge(c, a)


def shoelace(points):
    terms = [
        term
        for i, point in enumerate(points)
        for term in edge(point, points[(i + 1) % len(points)])
    ]
    return scale(Interval.ratio(1, 2), terms)


def centered_coefficients(polynomial, variables):
    affine = [
        [((), Interval.point(a.midpoint())), ((i,), Interval.point(a.radius()))]
        for i, a in enumerate(variables)
    ]
    coefficients = {}
    for support, coefficient in polynomial:
        terms = [((), UNIT)]
        for i in reversed(support):
            terms = multiply(affine[i], terms)
        for support2, coefficient2 in scale(coefficient, terms):
            key = tuple(sorted(support2))
            coefficients[key] = coefficients.get(key, ZERO) + coefficient2
    return coefficients


def lower_bound(polynomial, variables):
    coefficients = centered_coefficients(polynomial, variables)
    return sum(a.lo if not support else -a.magnitude() for support, a in coefficients.items())


def fan_margins(points, variables):
    if len(points) < 3:
        return []
    return [
        (lower_bound(fan(points[0], points[1], points[i]), variables), (1, i))
        for i in range(2, len(points))
    ] + [
        (lower_bound(fan(points[0], points[i], points[i + 1]), variables), (i, i + 1))
        for i in range(2, len(points) - 1)
    ]


def check_leaf(box, leaf):
    data = box_data(box)
    if data is None or any(a.lo > a.hi for a in box):
        return False
    points, variables = data
    if sum(weight for weight, _ in leaf) > ONE:
        return False
    polynomial = []
    for weight, labels in leaf:
        if weight < 0 or len(labels) < 3 or len(set(labels)) != len(labels):
            return False
        if any(i < 0 or i >= 13 for i in labels):
            return False
        selected = [points[i] for i in labels]
        if len(selected) > 5 and min(m for m, _ in fan_margins(selected, variables)) <= 0:
            return False
        polynomial.extend(scale(Interval.point(weight), shoelace(selected)))
    return 239 * ONE <= 1000 * lower_bound(polynomial, variables)


def split_box(box, axis):
    midpoint = box[axis].midpoint()
    left, right = list(box), list(box)
    left[axis] = Interval(box[axis].lo, midpoint)
    right[axis] = Interval(midpoint, box[axis].hi)
    return tuple(left), tuple(right)


def split_axis(box):
    return max(range(9), key=lambda i: (45 if i < 3 else 100) * (box[i].hi - box[i].lo))
