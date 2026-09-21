# A Lean counterexample to the Fejér-gap variant of Erdős Problem 516

This repository gives an explicit counterexample to the **Fejér-gap variant**
registered in
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/61696dbe1a5c4ee31550b61a9f1ecac320c02f9d/FormalConjectures/ErdosProblems/516.lean).
The answer to the yes/no question is `False`: there is an entire lacunary series
with strictly increasing exponents and summable reciprocal exponents for which
the registered minimum/maximum-modulus ratio does not have limsup `1`.

**Try it in Lean4Web:**
[open the standalone proof](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Ferdos-516-fejer-counterexample%2Frefs%2Fheads%2Fmain%2Flean4web%2FErdos516FejerLean4Web.lean)

## Formal Conjectures target

The file in `lean/` imports the target declaration and proves it with the explicit
answer `False`:

```lean
theorem erdos_516_fejer_gap_variant_solved :
    answer(False) ↔
      ∀ {f : ℂ → ℂ} {n : ℕ → ℕ} (_hn : HasFejerGaps n) {a : ℕ → ℂ}
        (_ha : ∀ n, a n ≠ 0)
        (_hfn : ∀ z, HasSum (fun k => a k * z ^ n k) (f z)),
        limsup (fun r => Erdos516.ratio r f) atTop = 1
```

Thus
`Erdos516.erdos_516.variants.limsup_ratio_eq_one_of_hasFejerGaps`
can be changed from `research open` to `research solved` by replacing
`answer(sorry)` with `answer(False)` and supplying this proof.

## Mathematical Explanation (AI generated)

Write

```text
m_f(r) = inf { |f(z)| : |z| = r },
M_f(r) = sup { |f(z)| : |z| = r }.
```

The Formal Conjectures question asks whether every entire Fejér-gap series must
satisfy

```text
limsup_(r → ∞) log(m_f(r)) / log(M_f(r)) = 1.
```

To disprove this, it is enough to construct one entire Fejér-gap series for
which the quotient is at most `1/2` at every sufficiently large radius.

The main idea is to build `f` from polynomial blocks. A block contains the
factor

```text
(1 - z/R)^m.
```

Near the positive point `z = R` this factor is very small. At the opposite
point `z = -R` it becomes `(1 + |z|/R)^m` and is large. Thus the same circle has
a point where `f` is small and another point where `f` is large. Carefully
separating the blocks makes this happen on every sufficiently large circle,
rather than only on a chosen sequence of circles.

For `j ≥ 16`, define

```text
b_j = floor(log₂ j),                 N_j = 2^(j²),
q_j = ceil(8 N_j / (j b_j²)),        m_j = 2 q_j,
δ_j = 1 / (j b_j),                   A_j = N_j δ_j.
```

The very fast growth of `N_j` separates the frequency blocks. The resulting
entire function has the form

```text
P_k(z) = c_k z^(N_(k+16)) (1 - z/R_k)^(m_(k+16)),
f(z)   = Σ_(k ≥ 0) P_k(z),
```

where the positive constants `R_k` select the important radii and `c_k`
normalize the heights of the blocks.

Expanding one block gives the consecutive exponents

```text
N_j, N_j + 1, ..., N_j + m_j.
```

The proof shows `m_j ≤ N_j/2` and `2N_j ≤ N_(j+1)`, so different exponent
intervals do not overlap. Every coefficient in the binomial expansion is
nonzero. Consequently, after enumerating the union of these intervals in
increasing order, all coefficients of the resulting power series are nonzero
and its exponent sequence is strictly increasing.

There are about `m_j` exponents in the `j`-th block, and each is at least
`N_j`. Hence its contribution to the reciprocal exponent sum is bounded by a
constant multiple of

```text
m_j / N_j ≤ 1 / (j (floor(log₂ j))²).
```

The series

```text
Σ_(j ≥ 16) 1 / (j (floor(log₂ j))²)
```

converges by grouping `j` into dyadic intervals. This proves the
`HasFejerGaps` hypothesis. The same separation estimates make the future
blocks geometrically small on every fixed disk. Therefore the sum converges
locally uniformly, and `f` is entire.

It remains to compare the minimum and maximum modulus. Put `r = exp(u)`. The
chosen logarithmic radii divide every sufficiently large `u` into intervals

```text
s_(p+2) ≤ u ≤ s_(p+3).
```

On such an interval, estimates for the old blocks, the three nearby blocks,
and the geometrically small tail give

```text
|f(r)| ≤ (p + 5) exp(5 A_(p+16)).
```

At the negative point of the same circle, all terms of each expanded block
have the same sign. One nearby block therefore gives

```text
|f(-r)| ≥ exp(A_(p+17)).
```

Since `r` and `-r` lie on the circle of radius `r`,

```text
m_f(r) ≤ |f(r)|,                 M_f(r) ≥ |f(-r)|.
```

After taking logarithms, the growth of `A_j` yields

```text
log(m_f(r)) / log(M_f(r))
    ≤ (5 A_(p+16) + log(p + 5)) / A_(p+17)
    ≤ 1/2.
```

The Lean proof also handles the case `m_f(r) = 0` directly, using the total
real logarithm appearing in the registered definition. Thus

```text
∀ᶠ r in atTop, Erdos516.ratio r f ≤ 1/2,
```

and therefore its limsup cannot equal `1`. This explicit `f`, together with
its enumerated exponents and coefficients, is the required counterexample.

## Status boundary

This repository settles the Fejér-gap yes/no variant above. It does not alter
the finite-order/Fabry-gap theorem `Erdos516.erdos_516`, nor the separate growth
variant already recorded in Formal Conjectures. The formalization proves the
inequality needed for the counterexample, `limsup ≠ 1`; it does not formalize
the stronger paper-level claim that this limsup is `0`.

## Files

| Directory | Lean version | Purpose |
|---|---:|---|
| `lean/` | `v4.33.1` | Imports the Formal Conjectures target pinned at commit `61696dbe...` |
| `lean4web/` | `v4.35.0-rc2` | Standalone mathlib-only proof for Lean4Web |

Each directory contains one proof file, `lakefile.toml`, `lean-toolchain`, and
the generated `lake-manifest.json`.

## Verification

Formal Conjectures version:

```bash
cd lean
lake update
lake build
```

Standalone mathlib/Lean4Web version:

```bash
cd lean4web
lake update
lake build
```

Both builds are kernel checked. The proof files contain no `sorry`, `admit`,
custom axiom, `native_decide`, or `unsafe` theorem. Their final `#print axioms`
commands report only Lean's standard axioms:

```text
[propext, Classical.choice, Quot.sound]
```

## Sources

- [Erdős Problem 516](https://www.erdosproblems.com/516)
- [Formal Conjectures: `ErdosProblems/516.lean`](https://github.com/google-deepmind/formal-conjectures/blob/61696dbe1a5c4ee31550b61a9f1ecac320c02f9d/FormalConjectures/ErdosProblems/516.lean)
- [Repository layout used as a model](https://github.com/KitaKen1/erdos-361-asymptotic)

## AI usage disclosure

This formalization and repository packaging were developed by Kenta Kitamura
([KitaKen1 on GitHub](https://github.com/KitaKen1)), with assistance from
ChatGPT and OpenAI Codex using GPT-6 Astra.
