#!/usr/bin/env python3
"""Self-contained finite checks for the pure-S two-mirror construction.

Run with Python 3. Only the standard library is required. The small test alphabet
contains two data symbols and four boundary symbols. This checks term reductions,
scanner phases, mirror arithmetic, tag syntax, and a tiny raw-S masked tableau.
It does not implement the
universal tile palette or supply a formal verification of the general theorem.
"""
from functools import lru_cache
from itertools import product
import json


class Trees:
    """Immutable binary trees, sharing identical subtrees. Node zero is S."""
    def __init__(self):
        self.nodes = [None]
        self.index = {}

    def app(self, left, right):
        pair = (left, right)
        if pair not in self.index:
            self.index[pair] = len(self.nodes)
            self.nodes.append(pair)
        return self.index[pair]

    def cat(self, left, *args):
        for arg in args:
            left = self.app(left, arg)
        return left

    @lru_cache(None)
    def arity(self, node):
        if node == 0:
            return 0
        return 1 + self.arity(self.nodes[node][0])

    @lru_cache(None)
    def normal(self, node):
        if node == 0:
            return True
        left, right = self.nodes[node]
        return self.arity(left) < 2 and self.normal(left) and self.normal(right)

    @lru_cache(None)
    def step(self, node):
        if self.normal(node):
            return node
        left, z = self.nodes[node]
        if self.arity(left) == 2 and self.normal(left) and self.normal(z):
            sx, y = self.nodes[left]
            _, x = self.nodes[sx]
            return self.app(self.app(x, z), self.app(y, z))
        return self.app(self.step(left), self.step(z))

    @lru_cache(None)
    def leaves(self, node):
        if node == 0:
            return 1
        return sum(self.leaves(child) for child in self.nodes[node])

    def subterms(self, root):
        pending, seen = [root], set()
        while pending:
            node = pending.pop()
            if node in seen:
                continue
            seen.add(node)
            if node:
                pending.extend(self.nodes[node])
        return seen


LABELS = {'AAAAB': '<U', 'AAABB': 'U>', 'AABAB': '<V',
          'AABBB': 'V>', 'ABAAB': '0', 'ABABB': '1'}
BLOCKS = {label: word for word, label in LABELS.items()}
LENGTH = 5


class Verifier:
    def __init__(self):
        self.tree = Trees()
        cat = self.tree.cat
        s = 0
        self.a = cat(s, s)
        self.b = cat(s, self.a)
        a, b = self.a, self.b
        ea = cat(s, cat(s, a, s), a)
        eb = cat(s, cat(s, b, s), b)
        e = cat(s, cat(s, a, a), a)
        launch = self.launch = cat(s, cat(s, s, s), s)
        p_e = cat(s, s, cat(s, e))
        u = cat(s, cat(s, launch), p_e)
        self.tag = s
        for _ in range(2 + max(map(self.tree.leaves, (ea, eb, u, launch)))):
            self.tag = cat(s, self.tag)
        self.prefix = cat(s, self.tag)
        self.tagger = cat(s, self.tag, launch)
        self.g = cat(s, ea, cat(s, eb, cat(s, self.tagger, u)))
        self.base = cat(s, self.g)
        assert all(self.tree.normal(c) for c in (a, b, ea, eb, e, launch, p_e,
                                                  u, self.tag, self.g, self.base))

    def word(self, text):
        node = self.base
        for letter in reversed(text):
            node = self.tree.app(self.a if letter == 'A' else self.b, node)
        return node

    @lru_cache(None)
    def is_word(self, node):
        if node == self.base:
            return True
        if node == 0:
            return False
        code, rest = self.tree.nodes[node]
        return code in (self.a, self.b) and self.is_word(rest)

    @lru_cache(None)
    def unary_word(self, node):
        return (node != 0 and self.tree.nodes[node][0] == 0
                and self.is_word(self.tree.nodes[node][1]))

    @lru_cache(None)
    def scan_operand(self, node):
        return node != 0 and all(self.unary_word(c) for c in self.tree.nodes[node])

    @lru_cache(None)
    def scan_state(self, node):
        """Find the unpeeled right-spine suffix, or the final-B end pulse."""
        if node == 0:
            return None, False
        left, right = self.tree.nodes[node]
        if left == 0:
            return None, False
        op, arg = self.tree.nodes[left]
        if op in (self.a, self.b) and self.is_word(arg) and self.scan_operand(right):
            return left, False
        if op in (0, self.a) and self.scan_operand(arg):
            if op == self.a and right != 0:
                head, last = self.tree.nodes[right]
                if head == self.base and self.scan_operand(last):
                    return None, True
            return self.scan_state(right)
        return None, False

    def scan_symbol(self, scanner):
        suffix, _ = self.scan_state(scanner)
        if suffix is None:
            return None
        bits = []
        for _ in range(LENGTH):
            if suffix == self.base:
                return None
            op, suffix = self.tree.nodes[suffix]
            bits.append('A' if op == self.a else 'B')
        result = LABELS.get(''.join(bits))
        # The <V calibration must be the entire last block, including the base.
        if result == '<V' and suffix != self.base:
            return None
        return result

    def slot(self, node, slow):
        """One true A/B extraction frame. Only current syntactic normality is used."""
        if node == 0:
            return None
        normal = self.tree.normal
        left, right = self.tree.nodes[node]
        if normal(left) and not normal(right) and left != 0:
            q, v = self.tree.nodes[left]
            if self.unary_word(q) and self.scan_operand(v):
                return 'A', right, None
        if not normal(left) and not normal(right):
            scanner, delayed = self.tree.nodes[right]
            if not normal(delayed):
                return 'B', delayed if slow else left, scanner
        return None

    def observe(self, root, slow_header):
        # Only fixed-width fields and a finite-state header loop are needed.
        # The list is the replay diagnostic. A DFA can check pairs as they arrive.
        while True:
            entry = self.slot(root, slow_header)
            if entry is None:
                return None
            letter, root, _ = entry
            if letter == 'A':
                break
        pairs = []
        while True:
            block, scanner = [], None
            for _ in range(LENGTH):
                entry = self.slot(root, False)
                if entry is None:
                    return None
                letter, root, scanner = entry
                block.append(letter)
            label = LABELS.get(''.join(block))
            if label is None or scanner is None:
                return None
            pairs.append((label, self.scan_symbol(scanner)))
            if label == 'U>':
                return pairs

    def check_seed_prefix(self, seed, anchor):
        assert self.tree.normal(anchor)
        assert self.tree.leaves(self.prefix) < self.tree.leaves(anchor)
        for node in self.tree.subterms(seed) - {0}:
            left, right = self.tree.nodes[node]
            assert right != self.prefix
            assert right != self.tag or node == self.prefix
            assert left != self.prefix or node == self.tagger
            assert left != self.tag
            if not self.tree.normal(node):
                assert anchor in self.tree.subterms(right)


def scanner_checks(native):
    tree = native.tree
    cases = states = 0
    for length in range(1, 8):
        for letters in product('AB', repeat=length):
            word = ''.join(letters)
            p = native.word(word)
            q = tree.app(0, p)
            scanner = tree.app(p, tree.app(q, q))
            for age in range(length + 20):
                suffix, end = native.scan_state(scanner)
                if age < length:
                    assert suffix == native.word(word[age:]) and not end
                else:
                    assert suffix is None
                    assert end == (age == length and word.endswith('B'))
                scanner = tree.step(scanner)
                states += 1
            cases += 1
    return cases, states


def mirror_case(native, top, bottom, width):
    tree = native.tree
    upper = ['<U', *top, 'U>']
    lower = ['V>', *reversed(bottom), '<V']
    header = LENGTH * width
    text = 'B' * header + 'A' + ''.join(BLOCKS[c] for c in upper + lower)
    payload = native.word(text)
    q = tree.app(0, payload)
    root = tree.cat(q, q, q)
    preparation = 1 + text.count('A') + 2 * text.count('B')
    index = header + LENGTH  # last letter of first U block, zero based
    mirror = header + 1 + (len(upper) + len(lower) - 1) * LENGTH
    target = preparation + index + mirror + 2
    matches, pairs = [], 0
    for age in range(target + 3):
        fast = native.observe(root, False)
        if fast and fast[0] == ('<U', '<V') and fast[-1] == ('U>', 'V>'):
            matches.append(age)
            assert fast == list(zip(upper, ['<V', *bottom, 'V>']))
            slow = native.observe(root, True)
            whole = upper + lower
            expected = [(u, whole[len(whole) - 1 - i - width]) for i,u in enumerate(upper)]
            assert slow == expected
            pairs += len(fast) + len(slow)
        root = tree.step(root)
    assert matches == ([target] if len(top) == len(bottom) else [])
    return target + 3, pairs


def tag_checks(native):
    tree = native.tree
    states = shells = 0
    for initial in ('', 'B', 'AB', 'BA'):
        anchor = native.word(initial)
        seed = tree.app(native.g, anchor)
        native.check_seed_prefix(seed, anchor)
        # Found shells must have a payload retaining the initial encoded suffix.
        # Verify their exact right-hand orbit, not only its visible readout.
        root = seed
        right_orbits = {}
        found = False
        for age in range(26):
            for node in tree.subterms(root) - {0}:
                tagged, active = tree.nodes[node]
                if tagged == 0:
                    continue
                token, payload = tree.nodes[tagged]
                if token != native.tag or not native.is_word(payload):
                    continue
                found = True
                assert anchor in tree.subterms(payload)
                if payload not in right_orbits:
                    job = tree.app(native.launch, payload)
                    orbit = set()
                    for _ in range(26):
                        orbit.add(job)
                        job = tree.step(job)
                    right_orbits[payload] = orbit
                assert active in right_orbits[payload]
                shells += 1
            states += 1
            root = tree.step(root)
        assert found
    return states, shells


class TinyTableau(Verifier):
    """A two-bit tape, with one encoded transition mask for both tape cells."""
    width = 6
    ub, ue, ve, vb = range(4)

    @staticmethod
    def block(label):
        return 'A' + format(label, '04b').translate(str.maketrans('01', 'AB')) + 'B'

    def scan_small(self, scanner):
        suffix, _ = self.scan_state(scanner)
        if suffix is None:
            return None, None
        bits = []
        for _ in range(self.width):
            if suffix == self.base:
                return None, None
            op, suffix = self.tree.nodes[suffix]
            bits.append('A' if op == self.a else 'B')
        if bits[0] != 'A' or bits[-1] != 'B':
            return None, None
        label = int(''.join(bits[1:-1]).translate(str.maketrans('AB', '01')), 2)
        if label != self.vb:
            return label, None
        # The actual residual suffix must be VB, exactly four table bits, then Sg.
        mask = []
        for _ in range(4):
            if suffix == self.base:
                return None, None
            op, suffix = self.tree.nodes[suffix]
            mask.append(op == self.b)
        if suffix != self.base:
            return None, None
        return label, tuple(mask)

    def tiny_route(self, root, delayed):
        # Test exactly two cells of header in this fixed-width toy example.
        for _ in range(2 * self.width):
            entry = self.slot(root, delayed)
            if entry is None or entry[0] != 'B':
                return None
            root = entry[1]
        entry = self.slot(root, delayed)
        if entry is None or entry[0] != 'A':
            return None
        root = entry[1]
        out = []
        while True:
            bits = []
            for _ in range(self.width):
                entry = self.slot(root, False)
                if entry is None:
                    return None
                letter, root, scanner = entry
                bits.append(letter)
            if bits[0] != 'A' or bits[-1] != 'B' or scanner is None:
                return None
            label = int(''.join(bits[1:-1]).translate(str.maketrans('AB', '01')), 2)
            value, table = self.scan_small(scanner)
            out.append((label, value, table))
            if label == self.ue:
                return out

    def tiny_hit(self, root):
        fast = self.tiny_route(root, False)
        if not fast or fast[0][:2] != (self.ub, self.vb) or fast[-1][:2] != (self.ue, self.ve):
            return False
        mask = fast[0][2]
        slow = self.tiny_route(root, True)
        if not slow or len(slow) != len(fast):
            return False
        # Run this finite pair check per cell. The lists expose diagnostics only.
        for (tile, here, _), (_, other, _) in zip(fast[1:-1], slow[1:-1]):
            if not 6 <= tile < 14:
                return False
            pair, terminal = divmod(tile-6, 2)
            current, following = divmod(pair, 2)
            if here != 4 + current:
                return False
            available = other in (4, 5)
            if available == bool(terminal):
                return False
            if available and (other != 4 + following or not mask[pair]):
                return False
        return True

    def tiny_case(self, rows, footer, mirror_values=None, tamper=None):
        # Whole word is the isolated packet's actual runtime datum for this test.
        # In the full construction generation is certified by the suffix/tag lemma.
        tiles = []
        for i, row in enumerate(rows):
            for j, bit in enumerate(row):
                terminal = i == len(rows)-1
                following = 0 if terminal else int(rows[i+1][j])
                tiles.append(6 + 2*(2*int(bit) + following) + int(terminal))
        if tamper is not None:
            tiles[tamper] = 6 + ((tiles[tamper] - 6) ^ 2)  # change only the proposed following value
        centres = ''.join(rows) if mirror_values is None else mirror_values
        body = ''.join(self.block(c) for c in [self.ub, *tiles, self.ue, self.ve,
                                                *[4+int(b) for b in reversed(centres)], self.vb])
        header = 2*self.width
        text = 'B'*header + 'A' + body + footer
        p = self.word(text)
        q = self.tree.app(0, p)
        root = self.tree.cat(q, q, q)
        preparation = 1 + text.count('A') + 2*text.count('B')
        probe = header + self.width
        vb_index = len(text) - 4 - self.width
        target = preparation + probe + vb_index + 2
        hits = []
        for age in range(target + 4):
            if self.tiny_hit(root):
                hits.append(age)
            root = self.tree.step(root)
        return target, hits, target + 4


def tiny_tableau_checks():
    tiny = TinyTableau()
    # Mask order is 00,01,10,11. B means the encoded transition is allowed.
    cases = [(['01','10','01'], 'ABBA', None, None, True),
             (['01','01','01'], 'BAAB', None, None, True),
             (['01','10','01'], 'BAAB', None, None, False),
             (['01','11','01'], 'ABBA', None, None, False),
             (['01','10','01'], 'ABBA', '011011', None, False),
             (['01','10','01'], 'ABBA', None, 1, False)]
    states, positives = 0, []
    for rows, mask, mirrored, tamper, should_hit in cases:
        target, hits, count = tiny.tiny_case(rows, mask, mirrored, tamper)
        assert hits == ([target] if should_hit else []), (rows, mask, hits)
        if should_hit:
            positives.append(target)
        states += count
    return len(cases), states, positives


def main():
    native = Verifier()
    words, scan_states = scanner_checks(native)
    samples = [('0','1',1), ('1','0',1), ('01','11',1), ('10','01',1),
               ('10','01',2), ('011','101',2), ('101','100',3),
               ('0','10',1), ('001','11',2)]
    rows = [mirror_case(native, *row) for row in samples]
    tag_states, sampled_shells = tag_checks(native)
    tiny_cases, tiny_states, tiny_positives = tiny_tableau_checks()
    print(json.dumps(dict(tiny_masked_tableaus=tiny_cases, tiny_tableau_states=tiny_states,
                          tiny_positive_ages=tiny_positives, scanner_words=words, scanner_states=scan_states,
                          mirror_cases=len(rows), mirror_states=sum(r[0] for r in rows),
                          mirrored_pairs=sum(r[1] for r in rows), tag_seed_cases=4,
                          tag_states=tag_states, sampled_shells=sampled_shells,
                          generator_leaves=native.tree.leaves(native.g)), indent=2))


if __name__ == '__main__':
    main()
