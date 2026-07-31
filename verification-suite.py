"""Verification suite for:
      dim_VC(NFA'(3) cap B_4) = 9  >  8 = dim_VC(NFA'(3) cap B_5),
where NFA'(q) is the class of languages over {0,1} accepted by NFAs with
q states, one initial and one accepting state.

Requires numpy. Full run: ~30-60 min, single core, <2 GB RAM.
Expected output appears in a comment at the bottom of this file.
"""
import numpy as np

# ---------- acceptance profiles ------------------------------------------
def profiles(q, n):
    """Sorted array of the distinct acceptance profiles over B_n of all
    q-state NFAs with initial state 0 (no loss of generality, by relabeling
    states) and exactly one accepting state f in {0,...,q-1}.  Bit w of a
    profile (0 <= w < 2^n) is the acceptance of the word given by the
    binary expansion of w, most significant bit = first letter."""
    nm = 1 << (q * q)                    # Boolean q x q matrices, row j of
    trans = np.zeros((nm, 1 << q), dtype=np.uint8)   # M in bits qj..qj+q-1
    for m in range(nm):
        rows = [(m >> (q * j)) & ((1 << q) - 1) for j in range(q)]
        for v in range(1 << q):          # v = subset of states, as bitmask
            u = 0
            for j in range(q):
                if (v >> j) & 1:
                    u |= rows[j]
            trans[m, v] = u              # u = image of v under M
    N = nm * nm                          # enumerate all pairs (M_0, M_1)
    T = [trans[np.repeat(np.arange(nm), nm)],
         trans[np.tile(np.arange(nm), nm)]]
    idx, leaves = np.arange(N), {}
    def rec(v, depth, w):                # walk the binary tree of words
        if depth == n:
            leaves[w] = v
            return
        for a in (0, 1):
            rec(T[a][idx, v], depth + 1, (w << 1) | a)
    rec(np.full(N, 1, dtype=np.uint8), 0, 0)         # initial state set {0}
    profs = []
    for f in range(q):
        p = np.zeros(N, dtype=np.uint64)
        for w, v in leaves.items():
            p |= (((v >> f) & 1) != 0).astype(np.uint64) << np.uint64(w)
        profs.append(p)
    return np.unique(np.concatenate(profs))

# ---------- shattering ----------------------------------------------------
def shattered(P, S):
    """Naive predicate: S (bitmask of words) is shattered by profile set P."""
    return np.unique(P & np.uint64(S)).size == 1 << bin(S).count("1")

def make_ext_mask(P, nbits):
    """Fast kernel.  For shattered S, ext_mask(S) is the bitmask of all x
    such that S u {x} is shattered: sort profiles by their trace on S; a
    trace class blocks x iff its members all agree on bit x; so x is good
    iff every class has OR-bit x = 1 and AND-bit x = 0."""
    P = P.astype(np.uint64)
    full = np.uint64((1 << nbits) - 1)
    def ext_mask(S):
        cls = P & np.uint64(S)
        order = np.argsort(cls)
        ps, sc = P[order], cls[order]
        bnd = np.flatnonzero(np.r_[True, sc[1:] != sc[:-1]])
        good = np.bitwise_and.reduce(np.bitwise_or.reduceat(ps, bnd)) \
             & (full ^ np.bitwise_or.reduce(np.bitwise_and.reduceat(ps, bnd)))
        return int(good) & ~S & int(full)
    return ext_mask

# ---------- exhaustive BFS, no symmetry -----------------------------------
def bfs_plain(P, n, verbose=False):
    """Levels of shattered sets; each set generated exactly once via the
    increasing-maximum rule (valid since shattered sets are closed under
    subsets).  Returns (vc_dim, last_nonempty_level, level_sizes)."""
    ext = make_ext_mask(P, 1 << n)
    level, k, sizes = [0], 0, []
    while True:
        nxt = []
        for S in level:
            m = ext(S) & -(1 << S.bit_length())      # bits above max(S) only
            while m:
                b = m & -m
                nxt.append(S | b)
                m ^= b
        if not nxt:
            return k, level, sizes
        k, level = k + 1, nxt
        sizes.append(len(level))
        if verbose:
            print(f"  level {k}: {len(level)} shattered sets", flush=True)

# ---------- symmetry-reduced BFS ------------------------------------------
def sym_perms(n):
    """Induced action on word indices of: identity, word reversal,
    the letter swap 0 <-> 1, and their composition."""
    nb, fmt = 1 << n, f"0{n}b"
    rev = [int(format(i, fmt)[::-1], 2) for i in range(nb)]
    comp = [nb - 1 - i for i in range(nb)]
    return [list(range(nb)), rev, comp, [comp[rev[i]] for i in range(nb)]]

def apply_perm(S, perm):
    out = 0
    while S:
        b = S & -S
        out |= 1 << perm[b.bit_length() - 1]
        S ^= b
    return out

def check_symmetry(P, n):
    """The profile set must be invariant under the induced group action."""
    for perm in sym_perms(n):
        img = np.zeros_like(P)
        for i in range(1 << n):
            img |= (((P >> np.uint64(i)) & np.uint64(1))
                    << np.uint64(perm[i]))
        assert np.array_equal(np.unique(img), P)
    print("  profile set invariant under the symmetry group: OK")

def bfs_sym(P, n, verbose=False):
    """BFS over canonical representatives (minimum of the orbit).  Complete:
    if S is canonical shattered and e in S, and g canonicalizes S \\ {e},
    then S is the canonical form of the one-element extension
    g(S \\ {e}) u {g(e)} of a canonical set of the previous level."""
    perms = sym_perms(n)
    canon = lambda S: min(apply_perm(S, p) for p in perms)
    osize = lambda S: len({apply_perm(S, p) for p in perms})
    ext = make_ext_mask(P, 1 << n)
    level, k, sizes = {0}, 0, []
    while True:
        nxt = set()
        for S in level:
            m = ext(S)
            while m:
                b = m & -m
                nxt.add(canon(S | b))
                m ^= b
        if not nxt:
            return k, level, sizes
        k, level = k + 1, nxt
        sizes.append((len(level), sum(osize(S) for S in level)))
        if verbose:
            print(f"  level {k}: {len(level)} canonical, "
                  f"{sizes[-1][1]} total", flush=True)

# ---------- main ----------------------------------------------------------
def words(S, n):
    return [format(i, f"0{n}b") for i in range(1 << n) if (S >> i) & 1]

def main():
    print("q=2 baseline (resolved in prior work):")
    for n in range(1, 7):
        P = profiles(2, n)
        d, _, _ = bfs_plain(P, n)
        print(f"  n={n}: {P.size:4d} profiles, VC dim = {d}")

    print("q=3, small n:")
    for n in range(1, 4):
        P = profiles(3, n)
        d, _, _ = bfs_plain(P, n)
        print(f"  n={n}: {P.size:4d} profiles, VC dim = {d}")

    print("q=3, n=4:")
    P4 = profiles(3, 4)
    print(f"  {P4.size} profiles")
    d4, tops, sizes = bfs_plain(P4, 4, verbose=True)
    assert d4 == 9 and sizes == [16, 120, 560, 1820, 4368, 7898, 8730, 886, 2]
    for S in tops:                       # independent check of the extrema
        assert shattered(P4, S)
        assert not any(shattered(P4, S | (1 << x))
                       for x in range(16) if not (S >> x) & 1)
        print("  extremal 9-set:", words(S, 4))
    print("  d_3(4) = 9, certified")

    print("q=3, n=5:")
    P5 = profiles(3, 5)
    print(f"  {P5.size} profiles")
    check_symmetry(P5, 5)
    d5s, _, ssizes = bfs_sym(P5, 5, verbose=True)
    d5p, eights, psizes = bfs_plain(P5, 5, verbose=True)
    assert d5s == d5p == 8
    assert [t for (_, t) in ssizes] == psizes     # two runs must agree
    print("  final independent pass: extending all shattered 8-sets "
          "with the naive predicate...")
    for S in eights:                     # every 9-set would contain one
        assert not any(shattered(P5, S | (1 << x))
                       for x in range(32) if not (S >> x) & 1)
    print("  d_3(5) = 8, certified")
    print("CONCLUSION: d_3(4) = 9 > 8 = d_3(5); "
          "monotonicity in n fails for NFA'(3).")

if __name__ == "__main__":
    main()

# Expected output ----------------------------------------------------------
# q=2 baseline (resolved in prior work):
#   n=1:    4 profiles, VC dim = 2
#   n=2:   16 profiles, VC dim = 4
#   n=3:   86 profiles, VC dim = 5
#   n=4:  116 profiles, VC dim = 5
#   n=5:  122 profiles, VC dim = 5
#   n=6:  122 profiles, VC dim = 5
# q=3, small n:
#   n=1:    4 profiles, VC dim = 2
#   n=2:   16 profiles, VC dim = 4
#   n=3:  256 profiles, VC dim = 8
# q=3, n=4:
#   5423 profiles
#   level 1: 16 ... level 9: 2 shattered sets
#     (16, 120, 560, 1820, 4368, 7898, 8730, 886, 2)
#   extremal 9-set: 0000 0010 0100 0101 0110 1001 1011 1101 1111
#   extremal 9-set: 0000 0010 0100 0110 1001 1010 1011 1101 1111
#   d_3(4) = 9, certified
# q=3, n=5:
#   14773 profiles
#   profile set invariant under the symmetry group: OK
#   canonical: 10, 142, 1278, 9168, 50645, 221149, 493205, 36709
#   total:     32, 496, 4960, 35960, 201324, 880636, 1968732, 145801
#   d_3(5) = 8, certified
# CONCLUSION: d_3(4) = 9 > 8 = d_3(5); monotonicity in n fails for NFA'(3).
