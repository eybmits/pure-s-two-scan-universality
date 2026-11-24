"""Single-terminal-row output tableau and fixed decoder checks (Python 3.10+).

This checks encoded wrapper words. It does not perform S reductions. The rule
table is a fixed-length bit mask in the encoded seed suffix. The toy machine
and its honest histories are fixtures. The verifier reads its transition
quadruples from the mask and never calls the toy transition function. The
fixture scans a binary input left to right and writes its bitwise complement,
using output-marked symbols distinct from the input alphabet.
"""

from dataclasses import dataclass
from itertools import product
import json


SYMBOLS = ("#", "<", ">", "[", "0", "1", "$", "_", "s0", "s1", "s$", "m0", "m1", "h!")
S = len(SYMBOLS)
MASK_LEN = S**4
DIGITS = (4 + S + 2 * MASK_LEN - 1).bit_length()
L = DIGITS + 2
INDEX = {c: i for i, c in enumerate(SYMBOLS)}
UB, UE, VE, VB = range(4)


@dataclass(frozen=True)
class Tile:
    left: str
    center: str
    right: str
    following: str
    terminal: bool

    def quad(self):
        return self.left, self.center, self.right, self.following


def quad_id(quad):
    i = 0
    for c in quad:
        i = S*i + INDEX[c]
    return i


def quad_value(i):
    out = []
    for _ in range(4):
        out.append(SYMBOLS[i % S])
        i //= S
    return tuple(reversed(out))


def code(n):
    return "A" + format(n, f"0{DIGITS}b").translate(str.maketrans("01", "AB")) + "B"


def value(bits):
    if len(bits) != L or bits[0] != "A" or bits[-1] != "B":
        return None
    return int(bits[1:-1].translate(str.maketrans("AB", "01")), 2)


def encode_u(tile):
    return code(4 + S + 2*quad_id(tile.quad()) + int(tile.terminal))


def decode_u(i):
    if i is None or not 4+S <= i < 4+S+2*MASK_LEN:
        return None
    q, last = divmod(i-4-S, 2)
    return Tile(*quad_value(q), bool(last))


def v_id(symbol):
    return 4+INDEX[symbol]


def make_mask(table):
    bits = ["A"] * MASK_LEN
    for quad in table:
        bits[quad_id(quad)] = "B"
    return "".join(bits)


def input_prefix(data):
    if any(c not in "01" for c in data):
        raise ValueError("binary input expected")
    return ["<", "[", "s"+data[0]] + list(data[1:]) + ["$"] if data else ["<", "[", "s$"]


def fixed_suffix(data, table):
    return "".join(code(v_id(c)) for c in reversed(input_prefix(data))) + code(VB) + make_mask(table)


def wrapper_word(tiles, reverse_symbols, width, table):
    return ("B"*(L*width) + "A" + code(UB) + "".join(map(encode_u, tiles))
            + code(UE) + code(VE) + "".join(code(v_id(c)) for c in reverse_symbols)
            + code(VB) + make_mask(table))


def row_language(tiles):
    # All checks are regular. The lists below make the row invariants legible.
    rows = []
    terminal_seen = False
    start = 0
    for j, tile in enumerate(tiles):
        if tile.center != ">":
            continue
        row = tiles[start:j+1]
        cells = [x.center for x in row]
        if len(row) < 5 or cells[:2] != ["<", "["] or terminal_seen:
            return False
        if "[" in cells[2:]:
            return False
        if any(c in ("#", "<", ">") for c in cells[1:-1]):
            return False
        padded = ["#"] + cells + ["#"]
        for x, l, r in zip(row, padded, padded[2:]):
            if x.left != l or x.right != r or x.terminal != row[0].terminal:
                return False
        heads = [c for c in cells if c.startswith(("s", "h"))]
        if len(heads) != 1:
            return False
        if row[0].terminal:
            terminal_seen = True
            if "h!" not in cells:
                return False
            stop = cells.index("h!")
            if any(c not in ("m0", "m1") for c in cells[2:stop]):
                return False
            if any(c != "_" for c in cells[stop+1:-1]):
                return False
        elif heads[0] not in ("s0", "s1", "s$"):
            return False
        rows.append(cells)
        start = j+1
    if not rows or start != len(tiles) or not terminal_seen or tiles[0].terminal:
        return False
    first = rows[0]
    if first[2] not in ("s0", "s1", "s$"):
        return False
    data = [first[2][1:]] + first[3:-1]
    if "$" not in data:
        return False
    end = data.index("$")
    return all(c in ("0", "1") for c in data[:end]) and all(c=="_" for c in data[end+1:])


def regular_observation(word, age_error=0):
    """Source-level mirror observer, including the fixed-column seed mask."""
    if len(word) <= MASK_LEN or any(c not in "AB" for c in word):
        return False
    body, mask = word[:-MASK_LEN], word[-MASK_LEN:]
    k = len(body) - len(body.lstrip("B"))
    if k == 0 or k % L or body[k:k+1] != "A":
        return False
    h = k+1
    if (len(body)-h) % L:
        return False
    blocks = [value(body[i:i+L]) for i in range(h, len(body), L)]
    if not blocks or blocks[0] != UB or blocks[-1] != VB or UE not in blocks:
        return False
    stop = blocks.index(UE)
    if blocks[stop+1:stop+2] != [VE]:
        return False
    if not all(i is not None and 4 <= i < 4+S for i in blocks[stop+2:-1]):
        return False
    tiles = [decode_u(i) for i in blocks[1:stop]]
    if None in tiles or not row_language(tiles):
        return False

    def probe(j):
        return h+(j+1)*L-1

    def read(age, j, shift):
        y = age-probe(j)-2-shift
        if not 0 <= y < len(word):
            return None
        return value(word[y:y+L])

    # The UB probe requires the entire residual word to be VB plus the
    # fixed-length mask. This gives a unique age even for non-self-sync codes.
    age = probe(0)+2+len(body)-L+age_error
    if age-probe(0)-2 != len(body)-L:
        return False
    if read(age, 0, 0) != VB or read(age, stop, 0) != VE:
        return False
    for j, tile in enumerate(tiles, 1):
        if read(age, j, 0) != v_id(tile.center):
            return False
        nxt = read(age, j, k)
        available = nxt is not None and 4 <= nxt < 4+S
        if tile.terminal == available:
            return False
        if available:
            if nxt != v_id(tile.following) or mask[quad_id(tile.quad())] != "B":
                return False
            if any((tile.center == b) != (tile.following == b) for b in ("<", ">")):
                return False
    return True


def accepted_seed_candidate(word, data, table, age_error=0):
    # The anchoring lemma on S terms supplies this suffix restriction. A
    # The same observer handles every binary input and allowed rule table.
    return word.endswith(fixed_suffix(data, table)) and regular_observation(word, age_error)


def toy_next(l, c, r):
    if c in ("<", ">", "["):
        return c
    if c == "s$":
        return "h!"
    if c in ("s0", "s1"):
        return "m1" if c == "s0" else "m0"
    if c.startswith(("s", "h")):
        return None
    if l in ("s0", "s1"):
        return "s"+c if "s"+c in INDEX else None
    return c


def honest(data):
    cells = input_prefix(data) + ["_", "_", ">"]
    out = []
    while True:
        terminal = "h!" in cells
        padded = ["#"] + cells + ["#"]
        triples = list(zip(padded, padded[1:], padded[2:]))
        next_cells = ["_"]*len(cells) if terminal else [toy_next(*t) for t in triples]
        out.append([Tile(*t, new, terminal) for t, new in zip(triples, next_cells)])
        if terminal:
            return out
        cells = next_cells


def decode_authenticated_word(word):
    """Output after authentication. One scan, O(|word|) time and O(output) space."""
    start = word.find("A")
    if start < 0 or word[start+1:start+1+L] != code(UB):
        raise ValueError("invalid header")
    current = start+1+L
    result = []
    reading = False
    while current+L <= len(word):
        label = value(word[current:current+L])
        current += L
        if label == UE:
            return "".join(result)
        tile = decode_u(label)
        if tile is None:
            raise ValueError("invalid U block")
        if tile.terminal:
            if tile.center == "[":
                reading = True
            elif tile.center == "h!":  # Accept-head decoration on the closing delimiter.
                reading = False
            elif reading:
                result.append(tile.center[1])
    raise ValueError("missing end of U track")


def check_and_read(word, data, table):
    if not accepted_seed_candidate(word, data, table):
        raise ValueError("unauthenticated tableau")
    return decode_authenticated_word(word)


def encoded_rows(rows, width, table):
    flat = [x for row in rows for x in row]
    return wrapper_word(flat, [t.center for t in reversed(flat)], width, table)


def forged_row(cells, following, terminal):
    pad = ["#"] + cells + ["#"]
    return [Tile(l,c,r,new,terminal) for l,c,r,new in zip(pad,pad[1:],pad[2:],following)]


def self_test():
    table = {(l,c,r,new) for l,c,r in product(SYMBOLS, repeat=3)
             if (new := toy_next(l,c,r)) in INDEX}
    assert set(("m0", "m1", "h!")).isdisjoint(("0", "1", "$", "_", "s0", "s1", "s$"))
    examples = ["".join(cs) for n in range(4) for cs in product("01", repeat=n)]
    examples.extend(("1001", "00101"))
    summary = []
    negatives = 0
    for data in examples:
        rows = honest(data)
        flat = sum(rows, [])
        rev = [x.center for x in reversed(flat)]
        width = len(rows[0])
        good = wrapper_word(flat, rev, width, table)
        want = data.translate(str.maketrans("01", "10"))
        assert check_and_read(good, data, table) == want
        assert check_and_read(good, data, table) != want+"0"
        for d in (-L,-1,1,L):
            assert not accepted_seed_candidate(good,data,table,d)
            negatives += 1
        assert not accepted_seed_candidate(good,data+"0",table)
        negatives += 1
        for badwidth in [width-1, width+1]:
            assert not regular_observation(wrapper_word(flat,rev,badwidth,table))
            negatives += 1
        for badrev in [rev[1:], rev[:1]+rev]:
            assert not regular_observation(wrapper_word(flat,badrev,width,table))
            negatives += 1
        truncated = rows[0] + rows[-1]
        if len(rows) > 2:
            assert not regular_observation(wrapper_word(truncated,
                [x.center for x in reversed(truncated)],width,table))
            negatives += 1
        bad_table = table - {flat[1].quad()}
        assert not regular_observation(wrapper_word(flat,rev,width,bad_table))
        negatives += 1
        for damaged, stride in ((rows+[rows[-1]], width), (rows+[rows[0]], width),
                                ([row for r in rows for row in (r,r)], 2*width)):
            assert not regular_observation(encoded_rows(damaged, stride, table))
            negatives += 1

        # Forge an internally well-formed terminal row and the previous row's
        # claimed next symbols together. Both mirrors now agree on the false
        # answer. Only the machine table can reject the forged transition.
        actual = [x.center for x in rows[-1]]
        if data:
            wrong = actual[:]
            wrong[2] = "m1" if actual[2] == "m0" else "m0"
        else:
            wrong = ["<", "[", "m0", "h!", "_", ">"]
        assert len(wrong) == width
        penultimate = forged_row([x.center for x in rows[-2]], wrong, False)
        bad_final = forged_row(wrong, ["_"]*width, True)
        fake_rows = rows[:-2] + [penultimate,bad_final]
        forged = encoded_rows(fake_rows,width,table)
        assert row_language([t for r in fake_rows for t in r])
        assert decode_authenticated_word(forged) != want
        assert not accepted_seed_candidate(forged, data, table)
        negatives += 1

        # Copy a literal input digit into the final output field. This violates
        # the finite final-row grammar independently of the transition check.
        # Also reject missing and repeated delimiters.
        for index, bad in [(2,"0"), (1,"_"), (2,"["), (wrong.index("h!"),"_"),
                           (wrong.index("h!")+1,"h!")]:
            malformed = wrong[:]
            malformed[index] = bad
            raw_final = forged_row(malformed, ["_"]*width, True)
            assert not regular_observation(encoded_rows(rows[:-1]+[raw_final],width,table))
            negatives += 1
        summary.append(dict(input=data, output=want, rows=len(rows), width=width,
                            tiles=len(flat), wrappers=len(good)))
    print(json.dumps(dict(block_width=L, mask_length=MASK_LEN, examples=len(summary),
                          negative_checks=negatives, cases=summary), indent=2))


if __name__ == "__main__":
    self_test()
