#!/usr/bin/env python3
"""Replay a ground pure-S packet containing a two-cell, two-row example.

Run `python3 pure_s_two_cell.py`. The only dependency is pure_s_reference.py
from the same archive. A fixed two-cell machine writes 1 and moves right from
state R into H, leaving the second bit unchanged. `R0` is a head in state R
reading 0; similarly for `H1`. Each packed row has stride 3, including `#`.

We start at Q<W>, the application that launches the candidate's tagged packet.
Its finite alphabet is a compact instance of the paper's block format. The
universal seed's search for this packet is proved separately in Lean.

Encode: TwoCellPalette.encode writes the packed candidate as a binary word.
Reference.word turns it into a ground S-term. Its 7-letter cell alphabet and
20 local record labels use 7 wrappers per block and 134 wrappers per word.
Reduce: Trees.step contracts all innermost redexes in the input snapshot.
Detect: PacketReader._payload tests the local records, and Reference.route
reads the fast and delayed scans from the evolved term's structure.
Decode: Reference.decode finds the first passing tagged packet in preorder
and returns both rows. The valid packet first passes at round 364. The forged
packet fails its delayed scan at its own calibration round, 362.
"""

from itertools import product

from pure_s_reference import Palette, Reference


class TwoCellPalette:
    colors = ("#", "0", "1", "R0", "R1", "H0", "H1")
    ci = {symbol: index for index, symbol in enumerate(colors)}
    k = 0  # The transition rule is fixed. No optional mask follows the footer.
    block = Palette.block
    label = Palette.label

    def __init__(self):
        self.records = []
        for left, right in product("01", repeat=2):
            before = ("#", "R" + left, right)
            successor = ("#", "1", "H" + right)
            self.records.extend(self.row_records(before, successor))
            self.records.extend(self.row_records(("#", left, "H" + right)))
        self.records = tuple(dict.fromkeys(self.records))
        self.offset = 4 + len(self.colors)
        self.width = 2 + (self.offset + len(self.records) - 1).bit_length()

    @staticmethod
    def row_records(row, successor=None):
        bordered = ("|", *row, "|")
        return [(tuple(bordered[j:j + 3]) + (successor[j] if successor else None,),
                 successor is None) for j in range(len(row))]

    def local(self, label):
        if label is None or not self.offset <= label < self.offset + len(self.records):
            return None
        idx = label - self.offset
        quad, final = self.records[idx]
        return quad, final, idx

    def encode(self, before, after):
        # Only the proposed update is computed by the toy transition table.
        predicted = ("#", "1", "H" + before[-1])
        records = self.row_records(before, predicted) + self.row_records(after)
        codes = [self.offset + self.records.index(record) for record in records]
        colors = [4 + self.ci[c] for c in reversed(before + after)]
        header = "B" * (3 * self.width) + "A"
        return header + "".join(self.block(x) for x in [0, *codes, 1, 2, *colors, 3])


class PacketReader(Reference):
    def _payload(self, node):
        # Finite static test of the tagged word. Vertical agreement is reserved
        # for the two native scans inherited from Reference.route.
        if not self.is_word(node):
            return None
        text = self.word_str(node)
        width = self.p.width
        header = "B" * (3 * width) + "A"
        if not text.startswith(header) or len(text) != len(header) + 16 * width:
            return None
        labels = [self.p.label(text[i:i + width]) for i in range(len(header), len(text), width)]
        if (labels[0], labels[7], labels[8], labels[15]) != (0, 1, 2, 3):
            return None
        if not all(c is not None and 4 <= c < self.p.offset for c in labels[9:15]):
            return None
        records = [self.p.local(x) for x in labels[1:7]]
        if any(r is None for r in records):
            return None
        rows = []
        for terminal, group in ((False, records[:3]), (True, records[3:])):
            row = tuple(q[1] for q, _, _ in group)
            bordered = ("|", *row, "|")
            if any(final != terminal or q[:3] != bordered[j:j + 3]
                   for j, (q, final, _) in enumerate(group)):
                return None
            rows.append(row)
        return tuple(rows)


def replay(forged):
    palette = TwoCellPalette()
    raw = PacketReader(palette)
    before = ("#", "R0", "1")
    after = ("#", "0" if forged else "1", "H1")
    word = palette.encode(before, after)
    root = raw.t.cat(0, raw.tag, raw.launch, raw.word(word))
    first_probe = 3 * palette.width + palette.width
    final_boundary = len(word) - palette.width
    preparation = 4 + word.count("A") + 2 * word.count("B")  # includes the Q launch
    calibrated = preparation + first_probe + final_boundary + 2
    for age in range(calibrated):
        if raw.decode(root) is not None:
            raise AssertionError(f"unexpected earlier acceptance at round {age}")
        root = raw.t.step(root)
    tag_word, body = raw.t.children[root]
    tag, payload = raw.t.children[tag_word]
    if tag != raw.tag:
        raise AssertionError("tag lost during the native evolution")
    static = raw.payload(payload)
    fast, delayed = raw.route(body, False), raw.route(body, True)
    result = raw.decode(root)
    following = raw.decode(raw.t.step(root))
    if following is not None:
        raise AssertionError("packet unexpectedly remained readable on the next round")
    if static != (before, after) or not fast or delayed == forged:
        raise AssertionError((static, fast, delayed))
    if result != (None if forged else (before, after)):
        raise AssertionError(result)
    print(f"{'forged' if forged else 'valid'}: round {calibrated} | static=pass | "
          f"fast=pass | delayed={'pass' if delayed else 'fail'}")
    if result is None:
        print("  rejected")
    else:
        for index, row in enumerate(result):
            print(f"  row {index}: {' '.join(row[1:])}")
        print(f"  output tape: {result[-1][1]}{result[-1][2][-1]}")


if __name__ == "__main__":
    replay(False)
    replay(True)
