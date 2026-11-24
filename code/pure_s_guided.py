#!/usr/bin/env python3
"""Replay a protected witness lineage starting from the actual g p0 input seed.

This is a certificate check on the fixed maximal parallel-innermost evolution.
The candidate word supplies the choice of a descendant to inspect. It never
replaces a term with the proposed payload. Each renewed payload is extracted
from native S steps. Untaken siblings are omitted using the proved innermost
barrier. Normalization of a mixed-word call uses the checked induction below.
This reports the global round of one verified accepting *subtree*, without
materializing the whole round or establishing the earliest accepting round.
"""

import json
from pure_s_reference import (
    COLORS,
    HEADS,
    Palette,
    Reference,
    full_word,
    history,
    tile_rows,
)


def normalize_mixed(raw, x, tester, statistics):
    """Exact result, duration, and intermediate frame data for x tester.

    The tester is unary and normal. In an A or B peel the enclosing frame
    waits for the designated suffix call to become normal. At B there is
    exactly one more contraction, and its tester/result subcall is normal.
    """
    tree = raw.t
    letters = []
    suffix = x
    while suffix != raw.base:
        opcode, shorter = tree.children[suffix]
        assert opcode in (raw.a, raw.b)
        letters.append((suffix, opcode, shorter))
        suffix = shorter
    result = tree.app(raw.base, tester)
    assert tree.normal[result]
    frames = []
    duration = 0
    for word, opcode, shorter in reversed(letters):
        shorter_call = tree.app(shorter, tester)
        peel = tree.step(tree.app(word, tester))
        frames.append((opcode, result))
        if opcode == raw.a:
            assert peel == tree.cat(0, tester, shorter_call)
            result = tree.cat(0, tester, result)
            duration += 1
        else:
            pending = tree.app(raw.a, tester)
            assert peel == tree.app(pending, shorter_call)
            output = tree.step(tree.app(pending, result))
            assert output == tree.cat(0, result, tree.app(tester, result))
            result = output
            duration += 2
        assert tree.normal[result]
        statistics["normal_frame_instances"] += 1
    return result, duration, reversed(frames)


def extend(raw, g_call, next_letter, statistics):
    tree = raw.t
    g, previous = tree.children[g_call]
    assert g == raw.g and raw.is_word(previous)
    selected = 0 if next_letter == "A" else 1
    first = tree.step(g_call)
    branch = tree.children[first][selected]
    assert not tree.normal[branch]
    if selected:
        branch = tree.children[tree.step(branch)][0]
        assert not tree.normal[branch]
    code_age = 1 + selected
    # The actual two-step D_theta computation generates and duplicates x.
    intermediate = tree.step(branch)
    assert not tree.normal[intermediate]
    extraction = tree.step(intermediate)
    pair, x = tree.children[extraction]
    also_x, tester = tree.children[pair]
    assert x == also_x and x == tree.app(raw.a if not selected else raw.b, previous)
    assert tester == tree.app(0, previous)
    result, preparation, frames = normalize_mixed(raw, x, tester, statistics)
    # Before the left call is normal, the parent cannot contract. At exactly
    # preparation rounds it is (result x); this right x is the actual operand.
    cursor = tree.app(result, x)
    descended = 0
    for opcode, tail_result in frames:
        assert not tree.normal[cursor]
        node = tree.step(cursor)
        cursor = tree.children[node][1 if opcode == raw.a else 0]
        assert cursor == tree.app(tail_result, x) and not tree.normal[cursor]
        descended += 1
        statistics["native_descent_edges"] += 1
    base_pair = tree.step(cursor)
    final = tree.children[base_pair][0]
    assert final == tree.app(raw.g, x) and not tree.normal[final]
    return final, code_age + 2 + preparation + descended + 1


def replay(data):
    rows = [tile_rows(history(item)) for item in ("", "0", "1")]
    vocabulary = sorted({q for rowset in rows for row in rowset for q, _ in row})
    allowed = {q for rowset in rows for row in rowset for q, final in row if not final}
    fmt = Palette(COLORS, HEADS, vocabulary)
    raw = Reference(fmt)
    tree = raw.t
    actual = raw.seed(data, allowed)
    initial_payload = tree.children[actual][1]
    suffix = raw.word_str(initial_payload)
    candidate, header = full_word(fmt, history(data), allowed)
    assert candidate.endswith(suffix)
    additional = candidate[: -len(suffix)]
    global_age = 0
    statistics = dict(normal_frame_instances=0, native_descent_edges=0)
    for letter in reversed(additional):
        actual, elapsed = extend(raw, actual, letter, statistics)
        global_age += elapsed
    # This check is diagnostic. The positive replay below uses actual, not a
    # reconstructed candidate, and no metalevel word becomes a runtime seed.
    assert raw.word_str(tree.children[actual][1]) == candidate
    # The fixed generator's three forks expose genuine Qp along R,R,L.
    for direction in (1, 1, 0):
        actual = tree.children[tree.step(actual)][direction]
        assert not tree.normal[actual]
        global_age += 1
    tagger = tree.cat(0, raw.tag, raw.launch)
    q, p = tree.children[actual]
    assert q == tagger
    local_prep = 4 + candidate.count("A") + 2 * candidate.count("B")
    first_probe = header + fmt.width
    last_v = len(candidate) - fmt.k - fmt.width
    local_age = local_prep + first_probe + last_v + 2
    # Genuine raw Qp now receives every full synchronous round of its orbit.
    # The enclosing process is nonnormal throughout, so its ancestors stay fixed.
    for _ in range(local_age):
        assert not tree.normal[actual]
        actual = tree.step(actual)
    out = raw.decode(actual)
    assert out == ("" if data == "" else str(1 - int(data)))
    return dict(
        input=data,
        decoded_output=out,
        initial_suffix_letters=len(suffix),
        candidate_letters=len(candidate),
        actual_renewals=len(additional),
        Qp_birth_global_round=global_age,
        isolated_Qp_age=local_age,
        certified_subtree_global_round=global_age + local_age,
        **statistics,
    )


def check_early_global_paths():
    # On short generic seeds it is feasible to materialize the entire global
    # orbit. Independently inspect every branch word of up to three letters.
    fmt = Palette(COLORS, HEADS, [("#", "<", "[", "<")])
    raw = Reference(fmt)
    tree = raw.t
    initial = tree.app(raw.g, raw.base)
    pending = [(initial, 0, "", "")]
    checks = {}
    while pending:
        call, age, path, word = pending.pop()
        checks.setdefault(age, []).append((path, call))
        tagger = tree.cat(0, raw.tag, raw.launch)
        checks.setdefault(age + 3, []).append(
            (path + "RRL", tree.app(tagger, tree.children[call][1]))
        )
        if len(word) == 3:
            continue
        for letter in "AB":
            renewed, elapsed = extend(
                raw,
                call,
                letter,
                dict(normal_frame_instances=0, native_descent_edges=0),
            )
            nextword = letter + word
            suffix_path = "".join("R" if c == "A" else "L" for c in nextword) + "L"
            address = path + ("L" if letter == "A" else "RL") + suffix_path
            pending.append((renewed, age + elapsed, address, nextword))
    root = initial
    for age in range(max(checks) + 1):
        for path, expected in checks.get(age, []):
            x = root
            for ch in path:
                x = tree.children[x][ch == "R"]
            assert x == expected
        root = tree.step(root)
    return dict(
        whole_global_rounds=max(checks) + 1,
        designated_occurrences=sum(map(len, checks.values())),
    )


if __name__ == "__main__":
    print(
        json.dumps(
            dict(
                short_whole_tree_crosscheck=check_early_global_paths(),
                guided_input_runs=[replay(""), replay("0")],
            ),
            indent=2,
        )
    )
