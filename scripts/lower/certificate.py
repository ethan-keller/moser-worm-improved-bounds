"""Read lower certificate manifests and binary trees; Lean checks the mathematics."""

import hashlib
import json
from pathlib import Path

from common import certificate_file, checked_hash, fingerprint
from interval import ONE


def inputs(directory):
    """Check a complete frontier and bind its manifest to every payload."""
    directory = Path(directory)
    raw = (directory / "manifest.json").read_bytes()
    manifest = json.loads(raw)
    if not isinstance(manifest, dict):
        raise ValueError("invalid lower manifest")
    depth, version = manifest.get("frontier_depth"), manifest.get("format")
    if (
        type(version) is not int
        or version != 2
        or manifest.get("complete") is not True
        or type(depth) is not int
        or not 0 <= depth <= 16
    ):
        raise ValueError("invalid or incomplete lower manifest")
    if manifest.get("encoding") != "moser-lower-mixed-chord-v2":
        raise ValueError("unknown lower encoding")
    parts = manifest.get("parts")
    if not isinstance(parts, list) or any(not isinstance(p, dict) for p in parts):
        raise ValueError("invalid lower parts")
    ids = [p.get("id") for p in parts]
    if (
        any(type(i) is not int for i in ids)
        or len(ids) != 1 << depth
        or set(ids) != set(range(1 << depth))
    ):
        raise ValueError("lower manifest does not cover its entire frontier")
    hashes = {"manifest.json": hashlib.sha256(raw).hexdigest()}
    for part in parts:
        if (
            part.get("complete") is not True
            or type(part.get("format")) is not int
            or part["format"] != 2
        ):
            raise ValueError("invalid or incomplete lower part")
        name = part.get("file")
        path = certificate_file(directory, name)
        if name in hashes:
            raise ValueError("duplicate lower input filename")
        hashes[name] = checked_hash(path, part.get("sha256"))
    return fingerprint(hashes), manifest


def read_exact(stream, count):
    data = stream.read(count)
    if len(data) != count:
        raise ValueError("truncated certificate")
    return data


def read_labels(stream, count):
    if not 3 <= count <= 13:
        raise ValueError("invalid polygon length")
    labels = list(read_exact(stream, count))
    if len(set(labels)) != count or any(i >= 13 for i in labels):
        raise ValueError("invalid vertex labels")
    return labels


def read_leaf(stream, tag):
    if tag != 16:
        return [(ONE, read_labels(stream, tag - 16))]
    count = read_exact(stream, 1)[0]
    if not 1 <= count <= 24:
        raise ValueError("invalid mixture length")
    leaf = []
    for _ in range(count):
        weight = int.from_bytes(read_exact(stream, 8), "little")
        labels = read_labels(stream, read_exact(stream, 1)[0])
        leaf.append((weight, labels))
    if sum(weight for weight, _ in leaf) > ONE:
        raise ValueError("invalid mixture weight")
    return leaf


def encode_tree(tree):
    out, pending = bytearray(), [tree]
    while pending:
        node = pending.pop()
        if isinstance(node, list):
            if len(node) == 1 and node[0][0] == ONE:
                labels = node[0][1]
                out.extend([16 + len(labels), *labels])
            else:
                out.extend([16, len(node)])
                for weight, labels in node:
                    out.extend(weight.to_bytes(8, "little"))
                    out.extend([len(labels), *labels])
        else:
            axis, left, right = node
            out.append(axis)
            pending.extend((right, left))
    return bytes(out)
