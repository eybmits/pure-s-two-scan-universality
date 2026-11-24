#!/usr/bin/env python3
"""Reference seed encoder, raw S evaluator, whole-tree observer and output decoder.

python3 pure_s_reference.py                    runs finite reference checks
python3 pure_s_reference.py --encode spec.json 01   prints a ground seed as a DAG
python3 pure_s_reference.py --run spec.json 01 --rounds 4  checks rounds 0 through 4
Omitting --rounds from --run executes the semidecision until its first hit.

A spec can contain conventional instructions: {"transitions":[["s","$","!",0,"h"]]}.
For the conventional frontend see compile_tm. Alternatively supply the finite
radius-one presentation of a fixed transducer. Required JSON
keys: colors (ordered strings), heads (head-decorated colors), allowed (list of
[l,c,r,d] transitions). The conventions are #, <, >, [, 0, 1, $, _, m0, m1,
s0, s1, s$, h!. The three start colors are indexed by the first symbol, and h!
is the canonical halting head and closing output delimiter. The optional key
vocabulary is a fixed list of quadruples for a sparse test profile. When absent,
the alphabet of tiles is the full fourth Cartesian power. In either case the
permission mask is literal data in the term. Fix colors, heads and vocabulary
once for a transducer family. Seed construction never runs the transducer.

An accepted empty output is the empty string. None denotes rejection at this
round. The finite replay tests run the real S rule after isolating candidate
shells and separately exercise genuine shell launches from encoded input seeds.
They do not search a universal machine's unbounded orbit to a first accepting hit.
"""

import argparse
from functools import lru_cache
import json
from pathlib import Path
from itertools import product


class Trees:
    def __init__(self):
        self.children = [None]
        self.ids = {}
        self.normal = [True]
        self.arity = [0]
        self.next = {0: 0}

    def app(self, a, b):
        key = (a, b)
        if key not in self.ids:
            self.ids[key] = len(self.children)
            self.children.append(key)
            self.arity.append(min(3, self.arity[a] + 1))
            self.normal.append(self.normal[a] and self.normal[b] and self.arity[a] < 2)
        return self.ids[key]

    def cat(self, x, *xs):
        for y in xs:
            x = self.app(x, y)
        return x

    def step(self, root):
        # Every redex is classified on the input tree, with disjoint contractions.
        pending = [root]
        while pending:
            x = pending[-1]
            if x in self.next:
                pending.pop()
                continue
            left, right = self.children[x]
            if self.normal[x]:
                self.next[x] = x
            elif self.normal[left] and self.arity[left] == 2 and self.normal[right]:
                sx, y = self.children[left]
                _, a = self.children[sx]
                self.next[x] = self.app(self.app(a, right), self.app(y, right))
            elif left in self.next and right in self.next:
                self.next[x] = self.app(self.next[left], self.next[right])
            else:
                pending.extend(c for c in (right, left) if c not in self.next)
        return self.next[root]

    def advance(self, root, rounds):
        for _ in range(rounds):
            root = self.step(root)
        return root


class Palette:
    def __init__(self, colors, heads, vocabulary=None):
        self.colors = tuple(colors)
        self.heads = frozenset(heads)
        self.ci = {c: i for i, c in enumerate(colors)}
        wanted = {
            "#",
            "<",
            ">",
            "[",
            "0",
            "1",
            "$",
            "_",
            "m0",
            "m1",
            "s0",
            "s1",
            "s$",
            "h!",
        }
        if len(self.ci) != len(colors) or not wanted <= self.ci.keys():
            raise ValueError("missing or repeated cell colors")
        if not {"s0", "s1", "s$", "h!"} <= self.heads <= self.ci.keys():
            raise ValueError("invalid set of head colors")
        self.vocabulary = None if vocabulary is None else tuple(map(tuple, vocabulary))
        self.vi = (
            {}
            if self.vocabulary is None
            else {q: i for i, q in enumerate(self.vocabulary)}
        )
        if self.vocabulary is not None and (
            len(self.vi) != len(self.vocabulary)
            or any(len(q) != 4 or not set(q) <= self.ci.keys() for q in self.vocabulary)
        ):
            raise ValueError("invalid tile vocabulary")
        self.k = (
            len(self.colors) ** 4 if self.vocabulary is None else len(self.vocabulary)
        )
        self.width = 2 + (3 + len(self.colors) + 2 * self.k).bit_length()

    def qi(self, quad):
        if self.vocabulary is not None:
            return self.vi[tuple(quad)]
        i = 0
        for c in quad:
            i = i * len(self.colors) + self.ci[c]
        return i

    def quad(self, i):
        if self.vocabulary is not None:
            return self.vocabulary[i]
        q = []
        for _ in range(4):
            i, j = divmod(i, len(self.colors))
            q.append(self.colors[j])
        return tuple(reversed(q))

    def block(self, value):
        return (
            "A"
            + format(value, f"0{self.width - 2}b").translate(str.maketrans("01", "AB"))
            + "B"
        )

    def label(self, block):
        if len(block) != self.width or block[0] != "A" or block[-1] != "B":
            return None
        return int(block[1:-1].translate(str.maketrans("AB", "01")), 2)

    def tile(self, q, terminal):
        return 4 + len(self.colors) + 2 * self.qi(q) + int(terminal)

    def local(self, label):
        if (
            label is None
            or not 4 + len(self.colors) <= label < 4 + len(self.colors) + 2 * self.k
        ):
            return None
        i, f = divmod(label - 4 - len(self.colors), 2)
        return self.quad(i), bool(f), i

    def mask(self, allowed):
        slots = bytearray(b"A" * self.k)
        for q in allowed:
            slots[self.qi(q)] = ord("B")
        return slots.decode("ascii")

    def prefix(self, data):
        if any(c not in "01" for c in data):
            raise ValueError("binary input expected")
        return ["<", "["] + (["s" + data[0], *data[1:], "$"] if data else ["s$"])

    def suffix(self, data, allowed):
        return (
            "".join(self.block(4 + self.ci[c]) for c in reversed(self.prefix(data)))
            + self.block(3)
            + self.mask(allowed)
        )


class Reference:
    def __init__(self, palette):
        self.p = palette
        self.t = Trees()
        c = self.t.cat
        s = 0
        self.a = c(s, s)
        self.b = c(s, self.a)
        a, b = self.a, self.b
        da = c(s, c(s, a, s), a)
        db = c(s, c(s, b, s), b)
        e = c(s, c(s, a, a), a)
        self.launch = c(s, c(s, s, s), s)
        u = c(s, c(s, self.launch), c(s, s, c(s, e)))
        self.tag = s
        for _ in range(21):
            self.tag = c(s, self.tag)
        self.g = c(s, da, c(s, db, c(s, c(s, self.tag, self.launch), u)))
        self.base = c(s, self.g)
        self.word_ok = {self.base: True, 0: False}
        self.scan_cache = {}
        self.static_cache = {}
        self.route_cache = {}

    def word(self, data):
        p = self.base
        for c in reversed(data):
            p = self.t.app(self.a if c == "A" else self.b, p)
        return p

    def seed(self, data, allowed):
        return self.t.app(self.g, self.word(self.p.suffix(data, allowed)))

    def is_word(self, x):
        trail = []
        while x not in self.word_ok:
            trail.append(x)
            op, x = self.t.children[x]
            if op not in (self.a, self.b):
                for node in trail:
                    self.word_ok[node] = False
                return False
        ans = self.word_ok[x]
        for node in trail:
            self.word_ok[node] = ans
        return ans

    def word_str(self, x):
        bits = []
        while x != self.base:
            op, x = self.t.children[x]
            bits.append("A" if op == self.a else "B")
        return "".join(bits)

    def unary_word(self, x):
        return (
            x != 0
            and self.t.children[x][0] == 0
            and self.is_word(self.t.children[x][1])
        )

    @lru_cache(None)
    def is_v(self, x):
        return x != 0 and all(self.unary_word(y) for y in self.t.children[x])

    def scan(self, x):
        # A suffix pointer is only a representation aid. Its users inspect a
        # fixed-width block, and test a fixed-size footer at the calibration bit.
        trail = []
        while x not in self.scan_cache:
            trail.append(x)
            if x == 0:
                break
            f, right = self.t.children[x]
            if f == 0:
                break
            h, a = self.t.children[f]
            if h in (self.a, self.b) and self.is_word(a) and self.is_v(right):
                self.scan_cache[x] = f
                break
            if h not in (0, self.a) or not self.is_v(a):
                break
            x = right
        result = self.scan_cache.get(x)
        for node in trail:
            self.scan_cache[node] = result
        return result

    @lru_cache(None)
    def scan_label(self, x):
        s = self.scan(x)
        if s is None:
            return None, False
        bits = []
        for _ in range(self.p.width):
            if s == self.base:
                return None, False
            a, s = self.t.children[s]
            bits.append("A" if a == self.a else "B")
        z = self.p.label("".join(bits))
        if z != 3:
            return z, False
        for _ in range(self.p.k):
            if s == self.base:
                return z, False
            _, s = self.t.children[s]
        return z, s == self.base

    def slot(self, x, delayed):
        if x == 0:
            return None
        left, right = self.t.children[x]
        normal = self.t.normal
        if normal[left] and not normal[right] and left != 0:
            q, v = self.t.children[left]
            if self.unary_word(q) and self.is_v(v):
                return "A", right, None
        elif not normal[left] and not normal[right]:
            scanner, slow = self.t.children[right]
            if not normal[slow]:
                return "B", slow if delayed else left, scanner
        return None

    @lru_cache(None)
    def block_at(self, x):
        bits = []
        for _ in range(self.p.width):
            entry = self.slot(x, False)
            if entry is None:
                return None
            ch, x, scanner = entry
            bits.append(ch)
        if scanner is None:
            return None
        return self.p.label("".join(bits)), x, scanner

    def route(self, root, delayed):
        # Memoization keys use one of finitely many control states per node.
        # Each block has fixed length, and the two checks never zip distant lists.
        state = "header"
        trail = []
        rem = 0
        saw = False
        while (root, delayed, state, rem, saw) not in self.route_cache:
            trail.append((root, delayed, state, rem, saw))
            if state == "header":
                entry = self.slot(root, delayed)
                if entry is None:
                    break
                ch, root, _ = entry
                if ch == "B":
                    rem = (rem + 1) % self.p.width
                    saw = True
                    continue
                if not saw or rem:
                    break
                state = "begin"
                continue
            entry = self.block_at(root)
            if entry is None:
                break
            label, root, scanner = entry
            observed, calibrated = self.scan_label(scanner)
            if state == "begin":
                if label != 0 or (not delayed and not calibrated):
                    break
                state = "cells"
                continue
            if label == 1:
                answer = delayed or observed == 2
                for key in trail:
                    self.route_cache[key] = answer
                return answer
            tile = self.p.local(label)
            if tile is None:
                break
            (left, c, right, d), last, _ = tile
            if delayed:
                if last and observed is not None and 4 <= observed < 4 + len(self.p.colors):
                    break
                if not last and observed != 4 + self.p.ci[d]:
                    break
            elif observed != 4 + self.p.ci[c]:
                break
        else:
            answer = self.route_cache[(root, delayed, state, rem, saw)]
            for key in trail:
                self.route_cache[key] = answer
            return answer
        for key in trail:
            self.route_cache[key] = False
        return False

    def payload(self, p):
        if p in self.static_cache:
            return self.static_cache[p]
        answer = self._payload(p)
        self.static_cache[p] = answer
        return answer

    def _payload(self, p):
        if not self.is_word(p):
            return None
        text = self.word_str(p)
        fmt = self.p
        if len(text) <= fmt.k:
            return None
        body, mask = text[: -fmt.k], text[-fmt.k :]
        h = body.find("A")
        if h <= 0 or h % fmt.width or (len(body) - h - 1) % fmt.width:
            return None
        labels = [
            fmt.label(body[i : i + fmt.width])
            for i in range(h + 1, len(body), fmt.width)
        ]
        if not labels or labels[0] != 0 or labels[-1] != 3 or 1 not in labels:
            return None
        e = labels.index(1)
        if labels[e + 1 : e + 2] != [2] or not all(
            v is not None and 4 <= v < 4 + len(fmt.colors) for v in labels[e + 2 : -1]
        ):
            return None
        # Horizontal neighborhood and output checks on the immutable U word.
        # Lists improve readability here; all acceptance constraints need only
        # one prior tile, finite row-state flags and a fixed-size table mask.
        rows = []
        row = []
        for label in labels[1:e]:
            tile = fmt.local(label)
            if tile is None:
                return None
            (left, c, right, d), last, idx = tile
            if not last and (
                mask[idx] != "B"
                or any((c == wall) != (d == wall) for wall in ("<", ">"))
            ):
                return None
            row.append(tile)
            if c == ">":
                rows.append(row)
                row = []
        if row or len(rows) < 2:
            return None
        for j, row in enumerate(rows):
            cells = [q[1] for q, last, i in row]
            final = j == len(rows) - 1
            if (
                len(row) < 4
                or cells[:2] != ["<", "["]
                or any(c in ("#", "<", ">", "[") for c in cells[2:-1])
            ):
                return None
            if sum(c in fmt.heads for c in cells) != 1:
                return None
            padded = ["#", *cells, "#"]
            for (q, last, i), left, right in zip(row, padded, padded[2:]):
                if last != final or left != q[0] or right != q[2]:
                    return None
            if j == 0:
                if cells[2] not in ("s0", "s1", "s$"):
                    return None
                initial = [cells[2][1:]] + cells[3:-1]
                if "$" not in initial:
                    return None
                stop = initial.index("$")
                if not all(c in ("0", "1") for c in initial[:stop]) or any(
                    c != "_" for c in initial[stop + 1 :]
                ):
                    return None
            if final:
                if "h!" not in cells:
                    return None
                stop = cells.index("h!")
                if any(c not in ("m0", "m1") for c in cells[2:stop]) or any(
                    c != "_" for c in cells[stop + 1 : -1]
                ):
                    return None
                return "".join(c[1] for c in cells[2:stop])
            if "h!" in cells:
                return None
        raise AssertionError("unreachable")

    def decode(self, root):
        # Preorder with left child first. Identical ground subtrees have identical
        # acceptance, so skipping their later DAG occurrences preserves selection.
        seen = set()
        stack = [root]
        while stack:
            x = stack.pop()
            if self.t.normal[x] or x in seen:
                continue
            seen.add(x)
            left, right = self.t.children[x]
            if left != 0:
                tag, p = self.t.children[left]
                if (
                    tag == self.tag
                    and self.route(right, False)
                    and self.route(right, True)
                ):
                    output = self.payload(p)
                    if output is not None:
                        return output
            stack.extend((right, left))
        return None


def compile_tm(desc):
    """Compile finite one-tape instructions to the fixed radius-one presentation.

    `tape` lists extra work symbols. An instruction is [state, read, write,
    move, successor]. State s starts on the first bit or $. State h may occur
    only on !. Directions are -1, 0, +1. The symbols <, [, > are immovable
    walls. The intended transducer finishes with [ m0/m1* h! and trailing blanks.
    """
    reserved = {"#", "<", "[", ">"}
    tape = list(
        dict.fromkeys(["0", "1", "$", "_", "m0", "m1", "!", *desc.get("tape", [])])
    )
    if reserved.intersection(tape) or not all(isinstance(x, str) for x in tape):
        raise ValueError("invalid tape symbols")
    delta = {}
    states = {"s", "h"}
    for q, read, write, direction, nxt in desc["transitions"]:
        if (
            not isinstance(q, str)
            or not isinstance(nxt, str)
            or q == "h"
            or read not in tape
            or write not in tape
            or direction not in (-1, 0, 1)
        ):
            raise ValueError("invalid transition")
        if (q, read) in delta:
            raise ValueError("nondeterministic transition")
        delta[q, read] = (write, direction, nxt)
        states.update((q, nxt))
    decorated = {("h", "!"): "h!"}
    for i, q in enumerate(sorted(states - {"h"})):
        for j, x in enumerate(tape):
            decorated[q, x] = (
                "s" + x if q == "s" and x in ("0", "1", "$") else f"@{i}/{j}"
            )
    if set(decorated.values()) & (set(tape) | reserved):
        raise ValueError("head color collision")
    undecorate = {c: pair for pair, c in decorated.items()}
    colors = ["#", "<", "[", ">", *tape, *undecorate]

    def local(left, cur, right):
        if cur == "#":
            return None
        if cur in undecorate:
            step = delta.get(undecorate[cur])
            if step is None:
                return None
            write, direction, nxt = step
            if direction == 0:
                return decorated.get((nxt, write))
            if (left if direction < 0 else right) in reserved:
                return None
            return write
        arrivals = []
        for neigh, incoming in ((left, 1), (right, -1)):
            if neigh in undecorate:
                action = delta.get(undecorate[neigh])
                if action is not None and action[1] == incoming:
                    arrivals.append(action[2])
        if len(arrivals) > 1:
            return None
        if arrivals:
            return decorated.get((arrivals[0], cur))
        return cur

    allowed = set()
    for left, c, right in product(colors, repeat=3):
        # Neighborhoods with multiple heads never occur in a well-formed row.
        if sum(x in undecorate for x in (left, c, right)) > 1:
            continue
        d = local(left, c, right)
        if d is not None:
            allowed.add((left, c, right, d))
    return Palette(colors, undecorate), allowed


def machine_check():
    desc = {
        "transitions": [
            ["s", "0", "m1", 1, "s"],
            ["s", "1", "m0", 1, "s"],
            ["s", "$", "!", 0, "h"],
        ]
    }
    fmt, allowed = compile_tm(desc)
    expected = [
        ["<", "[", "s0", "1", "$", "_", ">"],
        ["<", "[", "m1", "s1", "$", "_", ">"],
        ["<", "[", "m1", "m0", "s$", "_", ">"],
        ["<", "[", "m1", "m0", "h!", "_", ">"],
    ]
    for before, after in zip(expected, expected[1:]):
        padded = ["#", *before, "#"]
        for left, c, right, d in zip(padded, padded[1:], padded[2:], after):
            assert {out for out in fmt.colors if (left, c, right, out) in allowed} == {
                d
            }
    raw = Reference(fmt)
    seed = raw.seed("01", allowed)
    assert raw.t.children[seed][0] == raw.g
    assert raw.is_word(raw.t.children[seed][1])
    return dict(
        colors=len(fmt.colors),
        allowed_quads=len(allowed),
        dense_mask_bits=fmt.k,
        seed_nodes=len(raw.t.children),
        native_TM_instructions=len(desc["transitions"]),
    )


COLORS = ("#", "<", ">", "[", "0", "1", "$", "_", "m0", "m1", "s0", "s1", "s$", "h!")
HEADS = ("s0", "s1", "s$", "h!")


def tile_rows(rows):
    result = []
    for i, row in enumerate(rows):
        padded = ["#", *row, "#"]
        last = i == len(rows) - 1
        result.append(
            [
                ((left, c, right, "_" if last else rows[i + 1][j]), last)
                for j, (left, c, right) in enumerate(
                    zip(padded, padded[1:], padded[2:])
                )
            ]
        )
    return result


def history(data):
    if data == "":
        return [["<", "[", "s$", ">"], ["<", "[", "h!", ">"]]
    return [
        ["<", "[", "s" + data, "$", ">"],
        ["<", "[", "m" + str(1 - int(data)), "h!", ">"],
    ]


def full_word(palette, rows, allowed, wrong_v=False):
    pairs = [tile for row in tile_rows(rows) for tile in row]
    labels = [palette.tile(q, f) for q, f in pairs]
    v = [q[1] for q, f in pairs]
    if wrong_v:
        v[0] = ">"
    end = [2, *[4 + palette.ci[c] for c in reversed(v)], 3]
    bits = "".join(palette.block(t) for t in [0, *labels, 1, *end])
    header = len(rows[0]) * palette.width
    return "B" * header + "A" + bits + palette.mask(allowed), header


def isolated(raw, data, allowed, expected, wrong_v=False):
    fmt = raw.p
    t = raw.t
    text, header = full_word(fmt, history(data), allowed, wrong_v)
    p = raw.word(text)
    # Begin at the one native contraction that creates the protected shell.
    job = t.cat(0, raw.tag, raw.launch, p)
    first_probe = header + fmt.width
    last_v = len(text) - fmt.k - fmt.width
    preparation = (
        1 + 2 + 1 + text.count("A") + 2 * text.count("B")
    )  # Qp→shell, Lp→²C0, preparation
    age = preparation + first_probe + last_v + 2
    root = t.advance(job, age - 1)
    assert raw.decode(root) is None
    hit = t.step(root)
    assert raw.decode(hit) == expected, (data, age, expected, raw.decode(hit))
    assert raw.decode(t.step(hit)) is None
    return hit, age


def self_test():
    rows = [tile_rows(history(data)) for data in ("", "0", "1")]
    vocabulary = sorted({q for rowset in rows for row in rowset for q, f in row})
    allowed = {q for rowset in rows for row in rowset for q, f in row if not f}
    fmt = Palette(COLORS, HEADS, vocabulary)
    raw = Reference(fmt)
    t = raw.t
    good_one, a1 = isolated(raw, "0", allowed, "1")
    good_empty, a0 = isolated(raw, "", allowed, "")
    wrong_rule, a2 = isolated(raw, "0", allowed - {("#", "<", "[", "<")}, None)
    wrong_copy, a3 = isolated(raw, "0", allowed, None, wrong_v=True)
    assert raw.decode(t.cat(0, wrong_rule, good_one)) == "1"
    assert raw.decode(t.cat(0, wrong_copy, good_empty)) == ""
    assert raw.decode(t.cat(0, good_empty, good_one)) == ""
    assert raw.decode(t.cat(0, good_one, good_empty)) == "1"
    assert raw.decode(t.cat(0, wrong_rule, wrong_copy)) is None
    # A real short run from the full seed does launch the unsolved input suffix.
    actual = raw.seed("0", allowed)
    p0 = raw.word(fmt.suffix("0", allowed))
    target = t.app(t.app(raw.tag, p0), t.app(raw.launch, p0))
    found = False
    for age in range(9):
        todo = [actual]
        seen = set()
        while todo:
            x = todo.pop()
            if x == target:
                found = True
                break
            if x and x not in seen:
                seen.add(x)
                todo.extend(t.children[x])
        if found:
            break
        actual = t.step(actual)
    assert found and raw.decode(actual) is None
    # The canonical dense encoder is exercised independently of sparse raw fixtures.
    # Its ground seed contains a 14^4-bit literal mask for this alphabet.
    dense = Reference(Palette(COLORS, HEADS))
    dense_seed = dense.seed("010", allowed)
    assert dense.t.children[dense_seed][0] == dense.g
    dense_payload = dense.t.children[dense_seed][1]
    assert dense.is_word(dense_payload)
    assert dense.word_str(dense_payload) == dense.p.suffix("010", allowed)
    return dict(
        sparse_quads=fmt.k,
        block_width=fmt.width,
        genuine_suffix_launch_round=age,
        raw_Qp_sample_ages=[a1, a0, a2, a3],
        decoded=["1", "", None, None],
        combined_trees=5,
        sparse_generated_DAG_nodes=len(t.children),
        dense_mask_bits=dense.p.k,
        dense_encoded_seed_DAG_nodes=len(dense.t.children),
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--encode", nargs=2, metavar=("SPEC", "BINARY_INPUT"))
    mode.add_argument("--run", nargs=2, metavar=("SPEC", "BINARY_INPUT"))
    parser.add_argument("--rounds", type=int, default=None)
    args = parser.parse_args()
    if args.rounds is not None and (args.run is None or args.rounds < 0):
        parser.error("--rounds requires --run and a nonnegative integer")
    if args.encode is None and args.run is None:
        result = self_test()
        result["compiled_tm"] = machine_check()
        print(json.dumps(result, indent=2))
        return
    path, data = args.encode or args.run
    spec = json.loads(Path(path).read_text())
    if "transitions" in spec:
        fmt, allowed = compile_tm(spec)
    else:
        fmt = Palette(spec["colors"], spec["heads"], spec.get("vocabulary"))
        allowed = spec["allowed"]
    raw = Reference(fmt)
    seed = raw.seed(data, allowed)
    if args.run is not None:
        root = seed
        age = 0
        while True:
            output = raw.decode(root)
            if output is not None:
                print(
                    json.dumps({"status": "accepted", "round": age, "output": output})
                )
                return
            if args.rounds is not None and age == args.rounds:
                print(
                    json.dumps(
                        {"status": "no_hit_in_checked_prefix", "through_round": age}
                    )
                )
                return
            root = raw.t.step(root)
            age += 1
    print(
        json.dumps(
            {"leaf": 0, "children": raw.t.children, "root": seed}, separators=(",", ":")
        )
    )


if __name__ == "__main__":
    main()
