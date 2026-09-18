"""Versioned lower-certificate tree codec; parsing is not geometric acceptance."""

from dataclasses import dataclass, field
import io
from typing import Optional

import certificate as plain_codec
from interval import ONE

MAGIC = b"MWLC\x02"
V2_ID = "moser-lower-mixed-chord-v2"
LOWER_CHORD_ENCODING = V2_ID
ANNOTATED_TAG = 30
PLAIN_TAGS = frozenset([16, *range(19, 30)])


class CodecError(ValueError):
    pass


@dataclass(frozen=True)
class Limits:
    tree_depth: int = 256
    tree_nodes: int = 64_000_000
    witness_depth: int = 64
    witness_nodes: int = 512  # per member, including rotations and terminals
    annotation_bytes: int = 1 << 20
    input_bytes: int = 1 << 30

    def __post_init__(self):
        for name in self.__dataclass_fields__:
            if type(getattr(self, name)) is not int or getattr(self, name) < 1:
                raise CodecError("limits must be positive integers")
        if self.tree_depth > 256 or self.witness_depth > 256:
            raise CodecError("recursive depth limit exceeds implementation bound")


@dataclass(frozen=True)
class Fan:
    weight: int
    labels: tuple


@dataclass(frozen=True)
class PlainLeaf:
    fans: tuple
    # Retain valid noncanonical v1 payload bytes, e.g. a singleton mixture.
    wire: Optional[bytes] = field(default=None, compare=False, repr=False)


@dataclass(frozen=True)
class Terminal:
    pass


@dataclass(frozen=True)
class Rotate:
    offset: int
    child: object


@dataclass(frozen=True)
class Coordinate:
    pass


@dataclass(frozen=True)
class Side:
    label: int
    reversed: bool


@dataclass(frozen=True)
class Cut:
    i: int
    j: int
    positive_right: bool
    nonzero: object
    left: object
    right: object


@dataclass(frozen=True)
class AnnotatedFan:
    fan: Fan
    witness: object


@dataclass(frozen=True)
class AnnotatedLeaf:
    members: tuple
    wire: Optional[bytes] = field(default=None, compare=False, repr=False)


@dataclass(frozen=True)
class Split:
    axis: int
    left: object
    right: object


def integer(value, low, high, name):
    if type(value) is not int or not low <= value <= high:
        raise CodecError(f"invalid {name}")
    return value


def flag(value, name):
    if type(value) is not bool:
        raise CodecError(f"invalid {name} flag")
    return int(value)


def validate_fans(fans):
    if type(fans) is not tuple or not 1 <= len(fans) <= 24:
        raise CodecError("invalid fan count")
    total = 0
    for f in fans:
        if type(f) is not Fan:
            raise CodecError("invalid fan")
        total += integer(f.weight, 0, ONE, "weight")
        if type(f.labels) is not tuple or not 3 <= len(f.labels) <= 13:
            raise CodecError("invalid polygon length")
        for k in f.labels:
            integer(k, 0, 12, "label")
        if len(set(f.labels)) != len(f.labels):
            raise CodecError("duplicate label")
    if total > ONE:
        raise CodecError("weight sum exceeds ONE")


def arcs(labels, i, j):
    integer(i, 0, len(labels) - 1, "cut index i")
    integer(j, 0, len(labels) - 1, "cut index j")
    if not i < j or not 2 <= j - i <= len(labels) - 2:
        raise CodecError("invalid cut arcs")
    return labels[i : j + 1], labels[j:] + labels[: i + 1]


def rotate_labels(labels, offset):
    integer(offset, 0, len(labels) - 1, "rotation")
    return labels[offset:] + labels[:offset]


class Reader:
    def __init__(self, data, limits):
        if type(data) is not bytes or len(data) > limits.input_bytes:
            raise CodecError("invalid or oversized byte input")
        self.stream = io.BytesIO(data)
        self.data = data
        self.limits = limits
        self.nodes = 0

    def read(self, n):
        try:
            return plain_codec.read_exact(self.stream, n)
        except ValueError as e:
            raise CodecError(str(e)) from e

    def byte(self):
        return self.read(1)[0]

    def boolean(self):
        value = self.byte()
        if value not in (0, 1):
            raise CodecError("nonbinary flag")
        return bool(value)

    def finish(self):
        if self.stream.tell() != len(self.data):
            raise CodecError("trailing or extra data")

    def plain(self, tag):
        if tag not in PLAIN_TAGS:
            raise CodecError("invalid plain-leaf tag")
        start = self.stream.tell() - 1
        try:
            entries = plain_codec.read_leaf(self.stream, tag)
        except (ValueError, IndexError) as e:
            raise CodecError(str(e)) from e
        fans = tuple(Fan(w, tuple(labels)) for w, labels in entries)
        validate_fans(fans)
        return PlainLeaf(fans, self.data[start : self.stream.tell()])

    def witness(self, labels, depth=0, budget=None):
        if budget is None:
            budget = [0]
        budget[0] += 1
        if depth > self.limits.witness_depth or budget[0] > self.limits.witness_nodes:
            raise CodecError("witness recursion/node limit")
        tag = self.byte()
        if tag == 0:
            return Terminal()
        if tag == 1:
            offset = self.byte()
            child_labels = rotate_labels(labels, offset)
            return Rotate(offset, self.witness(child_labels, depth + 1, budget))
        if tag != 2:
            raise CodecError("unknown witness tag")
        i, j, positive = self.byte(), self.byte(), self.boolean()
        left, right = arcs(labels, i, j)
        nz_tag = self.byte()
        if nz_tag == 0:
            nz = Coordinate()
        elif nz_tag == 1:
            label = integer(self.byte(), 0, 12, "nonzero label")
            nz = Side(label, self.boolean())
        else:
            raise CodecError("unknown nonzero-witness tag")
        left_witness = self.witness(left, depth + 1, budget)
        right_witness = self.witness(right, depth + 1, budget)
        return Cut(i, j, positive, nz, left_witness, right_witness)

    def tree(self, version, depth=0):
        self.nodes += 1
        if depth > self.limits.tree_depth or self.nodes > self.limits.tree_nodes:
            raise CodecError("tree recursion/node limit")
        tag = self.byte()
        if 0 <= tag < 9:
            left = self.tree(version, depth + 1)
            return Split(tag, left, self.tree(version, depth + 1))
        return self.leaf_tag(tag, version)

    def leaf_tag(self, tag, version):
        if tag in PLAIN_TAGS:
            return self.plain(tag)
        if version != 2 or tag != ANNOTATED_TAG:
            raise CodecError("unknown tree tag for this version")
        size = int.from_bytes(self.read(4), "little")
        if not 1 <= size <= self.limits.annotation_bytes:
            raise CodecError("annotation frame length")
        frame = Reader(self.read(size), self.limits)
        payload = frame.plain(frame.byte())
        members = tuple(AnnotatedFan(f, frame.witness(f.labels)) for f in payload.fans)
        frame.finish()  # exactly one witness per decoded payload member
        return AnnotatedLeaf(members, payload.wire)


class StreamReader(Reader):
    """Incremental full-grammar reader; no seek, read-all, or whole-tree buffer.

    read_node() returns an axis integer or a PlainLeaf/AnnotatedLeaf.
    read_tree() materializes only the next pending subtree.
    finish() is required after consuming the root, even when all leaves were used.
    """

    def __init__(self, stream, *, version, limits=Limits()):
        if type(version) is not int or version not in (1, 2):
            raise CodecError("unsupported format version")
        if not callable(getattr(stream, "read", None)):
            raise CodecError("expected a binary readable stream")
        self.stream = stream
        self.version = version
        self.limits = limits
        self.nodes = 0
        self.offset = 0
        self._capture = None
        self._pending = [0]
        self._failed = False
        self._finished = False
        if version == 2 and self.read(len(MAGIC)) != MAGIC:
            raise CodecError("wrong v2 magic/version")

    @property
    def tree_complete(self):
        return not self._failed and not self._pending

    @property
    def remaining_subtrees(self):
        return len(self._pending)

    def read(self, n):
        integer(n, 0, self.limits.input_bytes, "read size")
        if self.offset + n > self.limits.input_bytes:
            raise CodecError("stream byte limit")
        chunks = []
        remaining = n
        while remaining:
            chunk = self.stream.read(remaining)
            if type(chunk) is not bytes:
                raise CodecError("expected binary stream bytes")
            if not chunk:
                raise CodecError("truncated certificate")
            if len(chunk) > remaining:
                raise CodecError("stream returned too many bytes")
            chunks.append(chunk)
            self.offset += len(chunk)
            remaining -= len(chunk)
        data = b"".join(chunks)
        if self._capture is not None:
            self._capture.append(data)
        return data

    def plain(self, tag):
        if tag not in PLAIN_TAGS:
            raise CodecError("invalid plain-leaf tag")
        self._capture = [bytes([tag])]
        try:
            entries = plain_codec.read_leaf(self, tag)
            wire = b"".join(self._capture)
        except (ValueError, IndexError) as e:
            raise CodecError(str(e)) from e
        finally:
            self._capture = None
        fans = tuple(Fan(w, tuple(labels)) for w, labels in entries)
        validate_fans(fans)
        return PlainLeaf(fans, wire)

    def read_node(self):
        if self._failed or self._finished or not self._pending:
            raise CodecError("reader failed, finished, or root already consumed")
        try:
            depth = self._pending.pop()
            self.nodes += 1
            if depth > self.limits.tree_depth or self.nodes > self.limits.tree_nodes:
                raise CodecError("tree recursion/node limit")
            tag = self.byte()
            if 0 <= tag < 9:
                self._pending.extend((depth + 1, depth + 1))
                return tag
            return self.leaf_tag(tag, self.version)
        except Exception:
            self._failed = True
            raise

    def read_tree(self):
        node = self.read_node()
        if type(node) is int:
            left = self.read_tree()
            return Split(node, left, self.read_tree())
        return node

    def finish(self):
        if self._failed or self._pending:
            raise CodecError("failed or incomplete tree")
        if self._finished:
            return
        try:
            extra = self.stream.read(1)
            if type(extra) is not bytes or extra:
                raise CodecError("trailing or nonbinary data")
        except Exception:
            self._failed = True
            raise
        self._finished = True


def _plain_bytes(fans, wire):
    validate_fans(fans)
    if wire is not None:
        reader = Reader(wire, Limits())
        decoded = reader.plain(reader.byte())
        reader.finish()
        if decoded.fans != fans:
            raise CodecError("preserved payload disagrees with fan values")
        return wire
    # The shared existing writer is used verbatim on the plain payload.
    return plain_codec.encode_tree([(f.weight, list(f.labels)) for f in fans])


def _witness_bytes(w, labels, limits, depth=0, budget=None):
    if budget is None:
        budget = [0]
    budget[0] += 1
    if depth > limits.witness_depth or budget[0] > limits.witness_nodes:
        raise CodecError("witness recursion/node limit")
    if type(w) is Terminal:
        return b"\x00"
    if type(w) is Rotate:
        child_labels = rotate_labels(labels, w.offset)
        return bytes((1, w.offset)) + _witness_bytes(
            w.child, child_labels, limits, depth + 1, budget
        )
    if type(w) is not Cut:
        raise CodecError("unknown witness value")
    left, right = arcs(labels, w.i, w.j)
    positive = flag(w.positive_right, "positiveRight")
    if type(w.nonzero) is Coordinate:
        nz = b"\x00"
    elif type(w.nonzero) is Side:
        nz = bytes(
            (
                1,
                integer(w.nonzero.label, 0, 12, "nonzero label"),
                flag(w.nonzero.reversed, "reversed"),
            )
        )
    else:
        raise CodecError("unknown nonzero witness")
    return (
        bytes((2, w.i, w.j, positive))
        + nz
        + _witness_bytes(w.left, left, limits, depth + 1, budget)
        + _witness_bytes(w.right, right, limits, depth + 1, budget)
    )


def _encode(tree, version, limits):
    out = bytearray(MAGIC if version == 2 else b"")
    pending = [(tree, 0)]
    nodes = 0
    while pending:
        node, depth = pending.pop()
        nodes += 1
        if depth > limits.tree_depth or nodes > limits.tree_nodes:
            raise CodecError("tree recursion/node limit")
        if type(node) is Split:
            out.append(integer(node.axis, 0, 8, "split axis"))
            pending.extend(((node.right, depth + 1), (node.left, depth + 1)))
        elif type(node) is PlainLeaf:
            out.extend(_plain_bytes(node.fans, node.wire))
        elif version == 2 and type(node) is AnnotatedLeaf:
            if type(node.members) is not tuple or any(
                type(m) is not AnnotatedFan for m in node.members
            ):
                raise CodecError("invalid paired annotated members")
            fans = tuple(m.fan for m in node.members)
            frame = bytearray(_plain_bytes(fans, node.wire))
            for m in node.members:
                frame.extend(_witness_bytes(m.witness, m.fan.labels, limits))
            if not 1 <= len(frame) <= limits.annotation_bytes:
                raise CodecError("annotation frame length")
            out.append(ANNOTATED_TAG)
            out.extend(len(frame).to_bytes(4, "little"))
            out.extend(frame)
        else:
            raise CodecError("node is not supported by this version")
        if len(out) > limits.input_bytes:
            raise CodecError("encoded byte limit")
    return bytes(out)


def encode_v1(tree, limits=Limits()):
    return _encode(tree, 1, limits)


def encode_v2(tree, limits=Limits()):
    return _encode(tree, 2, limits)


def decode_v1(data, limits=Limits()):
    reader = Reader(data, limits)
    tree = reader.tree(1)
    reader.finish()
    return tree


def decode_v2(data, limits=Limits()):
    reader = Reader(data, limits)
    if reader.read(len(MAGIC)) != MAGIC:
        raise CodecError("wrong v2 magic/version")
    tree = reader.tree(2)
    reader.finish()
    return tree


def read_tree(data, *, version, limits=Limits()):
    """Decode one complete stream. No trailing bytes or implicit version choice."""
    if type(version) is not int or version not in (1, 2):
        raise CodecError("unsupported format version")
    return decode_v1(data, limits) if version == 1 else decode_v2(data, limits)


def write_tree(tree, *, version, limits=Limits()):
    """Encode one complete stream; v1 rejects every annotated leaf."""
    if type(version) is not int or version not in (1, 2):
        raise CodecError("unsupported format version")
    return encode_v1(tree, limits) if version == 1 else encode_v2(tree, limits)


def read_leaf(data, *, version, limits=Limits()):
    """Decode a complete single-leaf stream with the version's usual header."""
    leaf = read_tree(data, version=version, limits=limits)
    if type(leaf) not in (PlainLeaf, AnnotatedLeaf):
        raise CodecError("expected a leaf, received a split tree")
    return leaf


def write_leaf(leaf, *, version, limits=Limits()):
    if type(leaf) not in (PlainLeaf, AnnotatedLeaf):
        raise CodecError("expected a leaf")
    return write_tree(leaf, version=version, limits=limits)
