# POJ 3278 · Catch That Cow — O(log) Solution, Machine-Verified

**English** | [简体中文](README.zh-CN.md)

> An **O(log k) closed-form solution** to POJ 3278 "Catch That Cow", with correctness
> machine-verified along two independent routes: exhaustive checking against BFS in C++
> (up to 6.87 × 10¹⁰ pairs, all consistent), and a **complete Lean 4 formal proof**
> (core library only, no Mathlib, zero `sorry`).

## The Problem

Farmer John stands at position `n` on a number line; the cow stands at `k`
(`0 ≤ n, k ≤ 100000`). Each step he may move to `n − 1`, `n + 1`, or `2n`
(`−1` and `×2` require the current position to be positive). Find the minimum number
of steps to reach the cow.

Sample: `n = 5, k = 17` → answer `4`, via 5 → 4 → 8 → 16 → 17 (`−1, ×2, ×2, +1`).

## The Solution

The standard approach is BFS in O(range). This repository gives a direct
**O(log k)** solution `solve()`. An optimal strategy can always be written in three
segments:

1. perform `d` doublings (from position 0, first take one step to 1);
2. take `q` whole `±1` steps at the original scale — folded into a distance of
   `2^d · q` after doubling;
3. cover the remaining gap `r < 2^d` in a **signed binary representation (NAF,
   non-adjacent form)**, at a cost equal to the NAF weight of `r`
   (its number of nonzero terms).

The total cost is `d + q + naf(r)`. Only two candidates for `d` matter — the minimum
`d` with `n · 2^d ≥ k`, and `d − 1` — compared against walking straight `|n − k|` with
no doubling at all. The implementation is [`poj3278.cpp`](poj3278.cpp)
(~100 lines, including the BFS reference implementation).

## Machine Verification

### 1. Exhaustive checking (C++)

[`verify.cpp`](verify.cpp) includes `poj3278.cpp` verbatim (after renaming its `main`
away with a macro), so the code under test is not touched, and compares `solve()` pair
by pair against a BFS reference — exhaustively, on 20 threads:

| Stage | Exhaustive range | Pairs | Result |
| --- | --- | --- | --- |
| B | [0, 4096]² | 16,785,409 | ✅ all consistent (~5 s) |
| C | [0, 100000]² (full problem range) | 10,000,200,001 | ✅ all consistent (~10 s) |
| E | [0, 262144]² (~2.6× the range) | 68,720,001,025 | ✅ all consistent (~220 s) |

Additional small-range pairwise checks, random cross-binding against a second BFS,
and wide-boundary self-checks are included; see the full log in
[`verify_out.txt`](verify_out.txt).

### 2. Formal proof (Lean 4)

[`Poj3278.lean`](Poj3278.lean) formalizes the solution from scratch in Lean 4 using
**only the core library (no Mathlib)**: the move rules `Step`, the inductive relation
`Reach n k s` ("`k` is reachable from `n` in exactly `s` steps"), a rigorous definition
of the minimum `dist`, and a proof that the O(log) recursive solution `f` — and the
implementation mirroring the C++ `solve()` — indeed compute it. Key theorems:

```lean
/-- Full characterization of the minimum: f n k steps do reach k,
    and no path can be shorter. -/
theorem f_is_minimal (n k : Nat) :
    Reach n k (f n k) ∧ ∀ s, Reach n k s → f n k ≤ s

/-- The O(log) recursive solution f outputs exactly the minimum. -/
theorem f_eq_dist (n k : Nat) : f n k = dist n k

/-- The implementation mirroring C++ solve() (min over d, d − 1, and walking
    straight) equals the minimum. -/
theorem solve_eq_dist (start target : Nat) : solve start target = dist start target
```

The `#print axioms` block at the end of the file confirms that the key theorems depend
only on Lean's three standard logical axioms (`propext`, `Classical.choice`,
`Quot.sound`) — **no custom axioms, no `sorry`**.

## Repository Layout

| File | Description |
| --- | --- |
| [`poj3278.cpp`](poj3278.cpp) | C++ solution: BFS reference + O(log) `solve()`, the POJ entry point |
| [`verify.cpp`](verify.cpp) | Exhaustive verifier (includes the code under test verbatim) |
| [`verify_out.txt`](verify_out.txt) | Log of the latest full verification run |
| [`Poj3278.lean`](Poj3278.lean) | Complete Lean 4 formal proof + axiom check |
| `lean-toolchain` | Lean toolchain version (v4.34.1, picked up automatically by elan) |

## Build & Run

**C++ solution**

```bash
g++ -O2 -o poj3278 poj3278.cpp
echo "5 17" | ./poj3278        # prints 4
```

**Exhaustive verification** (20 threads, ~4 minutes total)

```bash
g++ -O2 -o verify verify.cpp
./verify
```

**Lean proof** (with [elan](https://github.com/leanprover/elan) installed, the
`lean-toolchain` file pins v4.34.1 automatically; Mathlib is not required)

```bash
lean Poj3278.lean
```

## License

[MIT](LICENSE)
