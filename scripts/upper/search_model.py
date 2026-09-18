"""Numerical proposals for the fixed upper problem; exact.py accepts each leaf."""

from fractions import Fraction
from functools import lru_cache
from math import cos, gcd, isfinite, radians

import cvxpy as cp
import numpy as np
from scipy import sparse

from exact import Geometry, H, T

SUPPORT_ANGLE_DEGREES = 90.0
ANGLE_TOLERANCE_DEGREES = 1e-9
PLACEMENT_TOLERANCE = 1e-9
BISECTION_IMPROVEMENT = 1e-4
CANDIDATE_TOLERANCE = 1e-6
COEFFICIENT_DROP = 1e-10
ROUNDING_DIGITS = 22
SOLVE_SECONDS = 30.0
MAX_ITERATIONS = 300
TIGHT_MAX_ITERATIONS = 50000


def partition(rect, right, left):
    def intervals(lo, hi, cuts):
        endpoints = [lo, *(i + 1 for i in sorted(set(cuts)) if lo <= i < hi), hi + 1]
        return [(a, b - 1) for a, b in zip(endpoints, endpoints[1:])]

    return [
        (a, b, c, d)
        for a, b in intervals(rect[0], rect[1], right)
        for c, d in intervals(rect[2], rect[3], left)
    ]


class Model:
    def __init__(self, header):
        if (
            type(header.get("schema")) is not int
            or header["schema"] != 1
            or any(type(header.get(k)) is not int or header[k] < 0 for k in ("kR", "kL"))
        ):
            raise ValueError("unsupported upper header")
        if list(map(Fraction, header["t"])) != T or list(map(Fraction, header["h"])) != H:
            raise ValueError("unexpected upper quadrilateral")
        self.geometry = g = Geometry(header["specs"])
        if (g.kR, g.kL) != (header["kR"], header["kL"]):
            raise ValueError("header label counts disagree with its placements")
        self.normals = np.array(g.normals, dtype=float)
        self.static_keys = []
        threshold = cos(radians(SUPPORT_ANGLE_DEGREES + ANGLE_TOLERANCE_DEGREES))
        for d in range(g.n):
            for p in range(g.n):
                if d != p and self.normals[d] @ self.normals[p] >= threshold:
                    self.static_keys.append(d * g.n + p)
        self.static_keys.append(g.n**2)
        self.keys = self.static_keys + [g.n**2 + 1 + i for i in range(len(g.erows))]
        rows = [g.row(k) for k in self.keys]
        self.row_labels = [set(i for i, _ in terms) for terms, _ in rows]
        self.mx, self.my = self.coefficient_matrices(rows)
        self.constants = np.array([float(b) for _, b in rows])
        # Every term is a nonnegative multiple of its named unit normal.
        fit_rows, fit_cols, fit_values = [], [], []
        for r, (terms, bound) in enumerate(g.erows):
            for label, v in terms:
                weight = sum(a * b for a, b in zip(v, g.normals[label]))
                if weight < 0:
                    raise ValueError("negative support expansion")
                fit_rows.append(r)
                fit_cols.append(label)
                fit_values.append(float(weight / -bound))
        self.fit = sparse.csr_matrix((fit_values, (fit_rows, fit_cols)), shape=(len(g.erows), g.n))
        self.cumulative = []
        for count, offset in ((g.kL, 3 + g.kR), (g.kR, 3)):
            rows, cols = [], []
            for j in range(count + 1):
                for i in range(j):
                    rows.append(j)
                    cols.append(offset + i)
            self.cumulative.append(
                sparse.csr_matrix((np.ones(len(rows)), (rows, cols)), shape=(count + 1, g.n))
            )

    def coefficient_matrices(self, rows):
        ri, ci, xs, ys = [], [], [], []
        for j, (terms, _) in enumerate(rows):
            for i, (x, y) in terms:
                ri.append(i)
                ci.append(j)
                xs.append(float(x))
                ys.append(float(y))
        shape = (self.geometry.n, len(rows))
        return (
            sparse.csr_matrix((xs, (ri, ci)), shape=shape),
            sparse.csr_matrix((ys, (ri, ci)), shape=shape),
        )

    @lru_cache(maxsize=64)
    def family_matrix(self, rect):
        """Four prefix families, using explicit left/right cumulative variables."""
        g = self.geometry
        a, b = g.n, g.n + g.kL + 1
        lo, hi, qlo, qhi = rect
        rows, cols, values = [], [], []
        count = 0

        def add(entries):
            nonlocal count
            for col, value in entries:
                rows.append(count)
                cols.append(col)
                values.append(value)
            count += 1

        for i in range(qlo, g.kL):
            for j in range(i + 1, g.kL + 1):
                add([(a + j, 1), (a + i, -1)])
        for j in range(qhi + 1):
            add([(a + g.kL, 1), (a + j, -1), (0, 1)])
        for j in range(lo, g.kR + 1):
            add([(a + g.kL, 1), (0, 1), (2, 1), (b + g.kR, 1), (b + j, -1)])
        for i in range(hi + 1):
            for j in range(i, hi + 1):
                add([(a + g.kL, 1), (0, 1), (2, 1), (1, 1), (b + i, 1), (b + g.kR, 1), (b + j, -1)])
        return sparse.csr_matrix((values, (rows, cols)), shape=(count, g.n + g.kL + g.kR + 2))

    def solver_options(self, tight=False):
        tolerance = 1e-11 if tight else 1e-8
        iterations = TIGHT_MAX_ITERATIONS if tight else MAX_ITERATIONS
        base = dict(
            max_iter=iterations,
            time_limit=SOLVE_SECONDS,
            max_threads=1,
            direct_solve_method="qdldl",
            tol_gap_abs=tolerance,
            tol_gap_rel=tolerance,
            tol_feas=tolerance,
        )
        if tight:
            base["tol_ktratio"] = 1e-10
        return [
            base,
            {**base, "static_regularization_constant": 1e-7},
            {**base, "static_regularization_constant": 1e-6, "equilibrate_enable": False},
        ]

    def solve(self, assigned, rect, *, tight=False, all_rows=False):
        g = self.geometry
        escapes = [len(self.static_keys) + 2 * m + ray for m, ray in assigned]
        involved = set().union(*(self.row_labels[i] for i in escapes))
        selected = [
            i
            for i, key in enumerate(self.static_keys)
            if all_rows or key == g.n**2 or self.row_labels[i] & involved
        ] + escapes
        mu = cp.Variable(len(selected), nonneg=True)
        wx, wy = [cp.Variable(g.n + g.kL + g.kR + 2) for _ in range(2)]
        eqx, eqy = wx[: g.n] == self.mx[:, selected] @ mu, wy[: g.n] == self.my[:, selected] @ mu
        constraints = [eqx, eqy]
        for w in (wx, wy):
            constraints.extend(
                [
                    w[g.n : g.n + g.kL + 1] == self.cumulative[0] @ w[: g.n],
                    w[g.n + g.kL + 1 :] == self.cumulative[1] @ w[: g.n],
                ]
            )
        family = self.family_matrix(tuple(rect))
        constraints.append(cp.norm(cp.vstack([family @ wx, family @ wy]), 2, axis=0) <= 1)
        problem = cp.Problem(cp.Maximize(-self.constants[selected] @ mu), constraints)
        for settings in self.solver_options(tight):
            try:
                value = problem.solve(solver="CLARABEL", **settings)
                if (
                    value is None
                    or not isfinite(value)
                    or mu.value is None
                    or eqx.dual_value is None
                    or eqy.dual_value is None
                ):
                    raise cp.error.SolverError("no finite solution")
                points = -np.column_stack([eqx.dual_value, eqy.dual_value])
                if not np.isfinite(points).all() or not np.isfinite(mu.value).all():
                    raise cp.error.SolverError("nonfinite proposal")
                return float(value), mu.value, points, [self.keys[i] for i in selected]
            except cp.error.SolverError:
                pass
        return None

    def exact_leaf(self, proposal, rect):
        if proposal is None or proposal[0] < 1 - CANDIDATE_TOLERANCE:
            return None
        _, values, _, keys = proposal
        items = [
            (key, Fraction(str(float(v)))) for key, v in zip(keys, values) if v > COEFFICIENT_DROP
        ]
        if not items:
            return None
        keys, values = zip(*items)
        rows = self.geometry.integer_rows(keys)
        for digits in range(2, ROUNDING_DIGITS + 1):
            weights = [round(v * 10**digits) for v in values]
            if self.geometry.valid(weights, rows, rect):
                bound = -sum(w * self.geometry.row(k)[1] for k, w in zip(keys, weights))
                nums = [w * bound.denominator for w in weights]
                den = bound.numerator
                common = den
                for n in nums:
                    common = gcd(common, n)
                return [den // common, [[k, n // common] for k, n in zip(keys, nums) if n]]
        return None

    def best_placement(self, assigned, points):
        support = (points @ self.normals.T).max(axis=0)
        values = np.asarray(self.fit @ support).reshape(-1, 2).max(axis=1)
        for m, _ in assigned:
            values[m] = np.inf
        index = int(values.argmin())
        return index if values[index] <= 1 + PLACEMENT_TOLERANCE else None

    def new_labels(self, assigned, placement, ray):
        offset = len(self.static_keys)
        involved = set().union(*(self.row_labels[offset + 2 * m + r] for m, r in assigned))
        new = self.row_labels[offset + 2 * placement + ray] - involved
        right = sorted(i - 3 for i in new if 3 <= i < 3 + self.geometry.kR)
        left = sorted(i - 3 - self.geometry.kR for i in new if i >= 3 + self.geometry.kR)
        return right, left

    def expand(self, state):
        """Return a leaf, a covering split, a placement branch, or an unresolved node."""
        assigned, rect, right, left = state
        proposal = self.solve(assigned, rect)
        leaf = self.exact_leaf(proposal, rect)
        if leaf is None and proposal is not None and proposal[0] >= 1 - CANDIDATE_TOLERANCE:
            for kw in ({"tight": True}, {"all_rows": True}):
                leaf = self.exact_leaf(self.solve(assigned, rect, **kw), rect)
                if leaf is not None:
                    break
        if leaf is not None:
            return ["l", *leaf]
        cells = partition(rect, right, [])
        if len(cells) > 1:
            return ["s", [[cell, [assigned, cell, [], left]] for cell in cells]]
        cells = partition(rect, [], left)
        if len(cells) > 1:
            return ["s", [[cell, [assigned, cell, [], []]] for cell in cells]]
        if proposal is None:
            return ["unresolved", "solver"]
        placement = self.best_placement(assigned, proposal[2])
        if placement is None:
            for axis in sorted((0, 2), key=lambda i: rect[i] - rect[i + 1]):
                if rect[axis] == rect[axis + 1]:
                    continue
                a, b = list(rect), list(rect)
                mid = (rect[axis] + rect[axis + 1]) // 2
                a[axis + 1], b[axis] = mid, mid + 1
                trials = [self.solve(assigned, cell) for cell in (a, b)]
                if any(
                    p is not None and p[0] > proposal[0] + BISECTION_IMPROVEMENT for p in trials
                ):
                    return ["s", [[cell, [assigned, cell, [], []]] for cell in (a, b)]]
            return ["unresolved", "no excluding placement"]
        children = []
        for ray in range(2):
            rnew, lnew = self.new_labels(assigned, placement, ray)
            children.append([assigned + [[placement, ray]], rect, rnew, lnew])
        return ["p", placement, *children]
