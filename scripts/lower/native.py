"""Build and call the three process-local pruning libraries."""

import ctypes
from itertools import zip_longest
import os
from pathlib import Path
import signal
import subprocess

import chord
from chord_prune_core import checked_box
from checker import c_header
from interval import ONE

HERE = Path(__file__).resolve().parent
FLAGS = [
    "-O3",
    "-std=c11",
    "-ffp-contract=off",
    "-Wall",
    "-Wextra",
    "-Werror",
    "-fPIC",
    "-shared",
    "-Wl,-z,defs",
    "-fvisibility=hidden",
]


def build(directory: Path, kind: str) -> Path:
    stem = {"accept": "accept", "geometry": "chord_oracle", "lp": "chord_lp"}[kind]
    work = Path(directory).resolve() / stem
    work.mkdir()
    (work / "data.h").write_text(c_header())
    library = work / (stem + ".so")
    command = [
        "gcc",
        *FLAGS,
        "-I",
        str(work),
        str(HERE / (stem + ".c")),
        "-lm",
        "-o",
        str(library),
    ]
    with (work / "compile.log").open("wb") as log:
        process = subprocess.Popen(
            command, stdout=log, stderr=subprocess.STDOUT, start_new_session=True
        )
        try:
            if process.wait(timeout=120):
                raise RuntimeError("native compilation failed:\n" + Path(log.name).read_text())
        except BaseException:
            # GCC's children belong to this invocation's process group.
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.wait()
            raise
    return library


def prepare(function, box):
    values = [value for bounds in checked_box(box) for value in bounds]
    if any(not -(1 << 63) <= value < (1 << 63) for value in values):
        raise ValueError("box mantissa outside signed 64-bit range")
    result = function((ctypes.c_int64 * 18)(*values))
    if result not in (0, 1):
        raise ValueError("invalid native prepare result")
    return bool(result)


def decode(output, size):
    if size == 0:
        return None
    if not 1 <= size <= len(output) or not 1 <= output[0] <= 24:
        raise ValueError("invalid native output size")
    at, fans = 1, []
    for _ in range(output[0]):
        if at + 2 > size:
            raise ValueError("truncated native member")
        weight, length = output[at], output[at + 1]
        if not 3 <= length <= 13 or at + 2 + length > size:
            raise ValueError("invalid native polygon length")
        fans.append(chord.Fan(weight, tuple(output[at + 2 : at + 2 + length])))
        at += length + 2
    if at != size:
        raise ValueError("trailing native output")
    result = tuple(fans)
    chord.validate_fans(result)
    return result


class Acceptor:
    def __init__(self, library):
        self.lib = ctypes.CDLL(str(Path(library).resolve()))
        pointer = ctypes.POINTER(ctypes.c_int64)
        self.lib.lower_accept_prepare.argtypes = [pointer]
        self.lib.lower_accept_prepare.restype = ctypes.c_int
        self.lib.lower_accept_try.argtypes = [ctypes.c_int, pointer, pointer]
        self.lib.lower_accept_try.restype = ctypes.c_int
        self.lib.lower_accept_mix.argtypes = [ctypes.c_int, pointer, pointer]
        self.lib.lower_accept_mix.restype = ctypes.c_int
        self.output = (ctypes.c_int64 * 361)()
        self.prepared = False

    def prepare(self, box):
        self.prepared = False
        self.prepared = prepare(self.lib.lower_accept_prepare, [(a.lo, a.hi) for a in box])
        return self.prepared

    def check(self, witness):
        if not self.prepared:
            raise ValueError("acceptance box is not prepared")
        return self._decode(self.lib.lower_accept_try(len(witness.leaf), witness.raw, self.output))

    def mix(self, pool):
        if not self.prepared or len(pool) > 16:
            raise ValueError("unprepared box or oversized candidate pool")
        cycles, seen = [], set()
        for members in zip_longest(*(w.leaf for w in pool)):
            for member in members:
                if member is not None:
                    key = tuple(member[1])
                    if key not in seen:
                        seen.add(key)
                        cycles.append(key)
        if not cycles:
            return None
        values = [v for cycle in cycles for v in (len(cycle), *cycle)]
        raw = (ctypes.c_int64 * len(values))(*values)
        return self._decode(self.lib.lower_accept_mix(len(cycles), raw, self.output))

    def _decode(self, size):
        fans = decode(self.output, size)
        return None if fans is None else [(fan.weight, list(fan.labels)) for fan in fans]


class PrimitiveOracle:
    def __init__(self, library):
        self.lib = ctypes.CDLL(str(Path(library).resolve()))
        self.lib.lower_accept_prepare.argtypes = [ctypes.POINTER(ctypes.c_int64)]
        self.lib.lower_accept_prepare.restype = ctypes.c_int
        self.lib.lower_chord_area_sized.argtypes = [
            ctypes.c_int,
            ctypes.POINTER(ctypes.c_int64),
            ctypes.c_size_t,
        ]
        self.lib.lower_chord_area_sized.restype = ctypes.c_int64
        self.lib.lower_chord_fan.argtypes = [ctypes.c_int, ctypes.c_int, ctypes.c_int]
        self.lib.lower_chord_fan.restype = ctypes.c_int64
        self.lib.lower_chord_nonzero.argtypes = [ctypes.c_int, ctypes.c_int]
        self.lib.lower_chord_nonzero.restype = ctypes.c_int
        self.prepared = False

    @staticmethod
    def boolean(value):
        if type(value) is not int or value not in (0, 1):
            raise ValueError("invalid oracle Boolean result")
        return bool(value)

    @staticmethod
    def label(value):
        if type(value) is not int or not 0 <= value < 13:
            raise ValueError("invalid oracle label")
        return value

    @staticmethod
    def bound(value):
        if type(value) is not int or not -(1 << 63) < value < (1 << 63):
            raise ValueError("oracle error sentinel or invalid lower bound")
        return value

    def require_prepared(self):
        if not self.prepared:
            raise ValueError("oracle box is not prepared")

    def prepare(self, box):
        self.prepared = False
        self.prepared = prepare(self.lib.lower_accept_prepare, box)
        return self.prepared

    def area_lower_bound(self, fans):
        self.require_prepared()
        chord.validate_fans(fans)
        values = [value for fan in fans for value in (fan.weight, len(fan.labels), *fan.labels)]
        raw = (ctypes.c_int64 * len(values))(*values)
        return self.bound(self.lib.lower_chord_area_sized(len(fans), raw, len(values)))

    def fan_lower_bound(self, a, b, c):
        self.require_prepared()
        return self.bound(self.lib.lower_chord_fan(self.label(a), self.label(b), self.label(c)))

    def coordinate_nonzero(self, a, b):
        self.require_prepared()
        return self.boolean(self.lib.lower_chord_nonzero(self.label(a), self.label(b)))


class ChordLPOracle:
    def __init__(self, library):
        self.lib = ctypes.CDLL(str(Path(library).resolve()))
        pointer = ctypes.POINTER(ctypes.c_int64)
        self.lib.lower_chord_lp_mode.argtypes = []
        self.lib.lower_chord_lp_mode.restype = ctypes.c_int
        if self.lib.lower_chord_lp_mode() != 1:
            raise ValueError("not a chord LP proposal library")
        self.lib.lower_chord_lp_full_first.argtypes = []
        self.lib.lower_chord_lp_full_first.restype = ctypes.c_int
        if self.lib.lower_chord_lp_full_first() != 0:
            raise ValueError("LP library must use the default coefficient policy")
        self.lib.lower_chord_lp_prepare.argtypes = [pointer]
        self.lib.lower_chord_lp_prepare.restype = ctypes.c_int
        self.lib.lower_chord_lp_propose.argtypes = [
            ctypes.c_int,
            pointer,
            ctypes.c_size_t,
            pointer,
            ctypes.c_size_t,
        ]
        self.lib.lower_chord_lp_propose.restype = ctypes.c_int
        self.lib.lower_chord_lp_reset.argtypes = []
        self.lib.lower_chord_lp_reset.restype = None
        self.lib.lower_chord_lp_stats.argtypes = [ctypes.POINTER(ctypes.c_uint64)]
        self.lib.lower_chord_lp_stats.restype = None
        self.lib.lower_chord_lp_reset()
        self.output = (ctypes.c_int64 * 361)()
        self.prepared = False

    def prepare(self, box):
        self.prepared = False
        self.prepared = prepare(self.lib.lower_chord_lp_prepare, box)
        return self.prepared

    def stats(self):
        values = (ctypes.c_uint64 * 5)()
        self.lib.lower_chord_lp_stats(values)
        return dict(zip(("attempts", "pools", "solves", "accepted", "pivots"), values))

    def propose(self, cycles):
        if not self.prepared:
            raise ValueError("LP box is not prepared")
        if not isinstance(cycles, (list, tuple)) or not 2 <= len(cycles) <= 24:
            raise ValueError("LP requires 2..24 parent-certified cycles")
        for labels in cycles:
            chord.validate_fans((chord.Fan(ONE, tuple(labels)),))
        values = [v for labels in cycles for v in (len(labels), *labels)]
        packed = (ctypes.c_int64 * len(values))(*values)
        before = self.stats()
        size = self.lib.lower_chord_lp_propose(
            len(cycles), packed, len(values), self.output, len(self.output)
        )
        if self.stats()["solves"] - before["solves"] > 1:
            raise ValueError("LP exceeded the one-solve budget")
        fans = decode(self.output, size)
        if fans is None:
            return None
        allowed = {tuple(labels) for labels in cycles}
        if (
            any(f.weight <= 0 or f.labels not in allowed for f in fans)
            or sum(f.weight for f in fans) != ONE
        ):
            raise ValueError("invalid LP weights or uncertified cycle")
        return fans
