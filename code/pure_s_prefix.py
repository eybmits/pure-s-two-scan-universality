"""Finite-prefix corollary fixtures on binary S wrapper words (Python 3.10+).

Run beside pure_s_output.py. The suffix, tile alphabet, clocks and mirror
offsets are the output construction's. The final row only marks the end of
the proposed prefix. It can be the initial row, or a live machine state.
"""
from itertools import product
import json

import pure_s_output as o


def prefix_grammar(tiles):
    starts = 0
    terminal_seen = False
    start = 0
    for j,tile in enumerate(tiles):
        if tile.center != ">":
            continue
        if terminal_seen:
            return False
        section = tiles[start:j+1]
        cells = [x.center for x in section]
        if len(cells) < 5 or cells[:2] != ["<","["]:
            return False
        if any(c in ("<",">","[","#") for c in cells[2:-1]):
            return False
        decorated = [c for c in cells if c in ("s0","s1","s$","h!")]
        if len(decorated) != 1:
            return False
        padded = ["#"] + cells + ["#"]
        terminal_seen = section[0].terminal
        if any(t.left != l or t.right != r or t.terminal != terminal_seen
               for t,l,r in zip(section,padded,padded[2:])):
            return False
        if starts == 0:
            if cells[2] not in ("s0","s1","s$"):
                return False
            input_tape = [cells[2][1:]] + cells[3:-1]
            if "$" not in input_tape:
                return False
            end = input_tape.index("$")
            if any(c not in ("0","1") for c in input_tape[:end]):
                return False
            if any(c != "_" for c in input_tape[end+1:]):
                return False
        starts += 1
        start = j+1
    return starts > 0 and start == len(tiles) and terminal_seen


def prefix_observation(word, age_error=0):
    if len(word) <= o.MASK_LEN or set(word) - {"A","B"}:
        return False
    body, mask = word[:-o.MASK_LEN], word[-o.MASK_LEN:]
    k = len(body) - len(body.lstrip("B"))
    h = k+1
    if not k or k % o.L or body[k:h] != "A" or (len(body)-h) % o.L:
        return False
    blocks = [o.value(body[i:i+o.L]) for i in range(h,len(body),o.L)]
    if not blocks or blocks[0] != o.UB or blocks[-1] != o.VB or o.UE not in blocks:
        return False
    stop = blocks.index(o.UE)
    if blocks[stop+1:stop+2] != [o.VE]:
        return False
    if any(v is None or not 4 <= v < 4+o.S for v in blocks[stop+2:-1]):
        return False
    tiles = [o.decode_u(v) for v in blocks[1:stop]]
    if None in tiles or not prefix_grammar(tiles):
        return False
    def probe(j):
        return h+(j+1)*o.L-1
    age = probe(0)+2+len(body)-o.L+age_error
    def read(j,shift):
        y = age-probe(j)-2-shift
        return o.value(word[y:y+o.L]) if 0 <= y < len(word) else None
    if age-probe(0)-2 != len(body)-o.L or read(0,0) != o.VB or read(stop,0) != o.VE:
        return False
    for j,t in enumerate(tiles,1):
        if read(j,0) != o.v_id(t.center):
            return False
        v = read(j,k)
        present = v is not None and 4 <= v < 4+o.S
        if present == t.terminal:
            return False
        if present:
            if v != o.v_id(t.following) or mask[o.quad_id(t.quad())] != "B":
                return False
            if any((t.center == b) != (t.following == b) for b in ("<",">")):
                return False
    return True


def right_walker(l,c,r):
    """This machine moves right forever on the unbounded blank tape."""
    if c in ("<",">","["):
        return c
    if c in ("s0","s1"):
        return c[1]
    if c == "s$":
        return "m0"
    if c == "h!":
        return None
    if l in ("s0","s1","s$"):
        return {"0":"s0", "1":"s1", "$":"s$", "_":"s$"}.get(c)
    return c


def rule_table(rule):
    return {(l,c,r,nxt) for l,c,r in product(o.SYMBOLS,repeat=3)
            if (nxt:=rule(l,c,r)) in o.INDEX}


def prefix_rows(data, rule, n, blanks):
    cells = o.input_prefix(data)+["_"]*blanks+[">"]
    history = []
    for t in range(n+1):
        end = t==n
        padded = ["#"]+cells+["#"]
        next_cells = ["_"]*len(cells) if end else [
            rule(l,c,r) for l,c,r in zip(padded,padded[1:],padded[2:])]
        assert all(c in o.INDEX for c in next_cells)
        history.append(o.forged_row(cells,next_cells,end))
        cells = next_cells
    return history


def check():
    positives = negatives = singletons = 0
    largest = 0
    for rule, data, horizon in ((right_walker,"",12), (right_walker,"01",10),
                                 (right_walker,"101",7), (o.toy_next,"",1),
                                 (o.toy_next,"001",4)):
        table = rule_table(rule)
        seed_suffix = o.fixed_suffix(data,table)
        for n in range(horizon+1):
            rows = prefix_rows(data,rule,n,horizon+3)
            width = len(rows[0])
            word = o.encoded_rows(rows,width,table)
            assert word.endswith(seed_suffix)
            assert prefix_observation(word)
            positives += 1
            largest = max(largest,len(word))
            singletons += int(n==0)
            for error in (-o.L,-1,1,o.L):
                assert not prefix_observation(word,error)
                negatives += 1
            doubled = [r for r in rows for _ in range(2)]
            assert not prefix_observation(o.encoded_rows(doubled,2*width,table))
            negatives += 1
            if n:
                # Coherent bad successor: alter the last tape square in the
                # final row AND the preceding row's prediction. Both mirror
                # tracks and all within-row triples agree on the false value.
                wrong = [x.center for x in rows[-1]]
                wrong[-2] = "1"
                fake = rows[:-2]+[
                    o.forged_row([x.center for x in rows[-2]],wrong,False),
                    o.forged_row(wrong,["_"]*width,True)]
                assert prefix_grammar([t for row in fake for t in row])
                bad = o.encoded_rows(fake,width,table)
                assert bad.endswith(seed_suffix)
                assert not prefix_observation(bad)
                negatives += 1
    print(json.dumps(dict(accepted_prefixes=positives, singleton_prefixes=singletons,
                          rejected_cases=negatives, longest_steps=12,
                          largest_wrapper_word=largest),indent=2))


if __name__ == "__main__":
    check()
