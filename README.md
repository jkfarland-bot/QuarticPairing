# QuarticPairing

Lean 4 / Mathlib formalization of the pairing of the twists `ℓ = 0` and `ℓ = 1` in Conjecture 1.2 of
C. David, A. Dunn, A. Hamieh and H. Lin, *Quartic Gauss sums over primes and metaplectic theta
functions* (arXiv:2306.11875, to appear in Algebra & Number Theory).

The conjecture says that the sums

  `S_β(X; ℓ) = ∑_{N(c) ≤ X, c ≡ β (mod 4)} g̃(c) (c̄/|c|)^ℓ Λ(c)`

of normalized quartic Gauss sums over primary `c ∈ ℤ[i]`, weighted by the von Mangoldt function, are `b_β X^{3/4} + O(X^{1/2+ε})` with
`b_β ≠ 0` when `ℓ = 0`, and `O(X^{1/2+ε})` when `ℓ ≠ 0`. Their identity (1.2), whose symbol factors
evaluate to 1 at primary primes, gives `g̃(c)² = -c/|c|`, so `g̃(c) (c̄/|c|) = -conj g̃(c)` and
`S_β(X; 1) = -conj S_β(X; 0)` exactly. The cases `ℓ = 0` and `ℓ = 1` are therefore incompatible.
The relation is already contained in DDHL (1.2) at `k = -1`. This repository proves:

- **The pointwise pairing**: if `g = 0` or `g² = -κ c/|c|` with `|κ| = 1`, then
  `g (c̄/|c|) = -κ ḡ` (`pointwise_pairing`).
- **The pairing of the twists**: `S_β(X; 1) = -κ conj S_β(X; 0)` when the identity holds on the
  support of `Λ` (`pairing_of_twists`), and in general
  `|S_β(X; 1) + κ conj S_β(X; 0)| ≤ 2 ∑_{c ∈ E} |g(c)| |Λ(c)|` off an exceptional set `E`
  (`pairing_of_twists_defect`).
- **The pairing identities** for the twisted moments: `A(ν³, -m) = -κ conj A(ν, m)`
  (`pairing_identities`).
- **The inconsistency**: under the identity on the support of `Λ`, or off a set of weight
  `O(X^{1/2+ε})`, Conjecture 1.2 fails for every class `β` (`conjecture12_inconsistent`,
  `conjecture12_inconsistent_of_defect`).
- **Why quartic**: if `|g| = 1` and `g^k = ξ`, then `ḡ = g^{k-1} ξ̄` (`why_quartic`); conjugation
  returns to the first moment only when `k = 2`, the quartic case.

Toolchain: `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`.

```
lake exe cache get
lake build
```

No `sorry`, no `native_decide`. Every result depends only on `propext`, `Classical.choice` and
`Quot.sound`.

## Scope and what is cited

Mathlib has no quartic residue symbol and no primary primes of `ℤ[i]`, and the formulation does not
need them. The quartic Gauss sum `g̃` and the von Mangoldt function `Λ` of `ℤ[i]` are arbitrary
functions `g : GaussianInt → ℂ` and `Λ : GaussianInt → ℝ`, and every result assumes of them only
the identity `g(c)² = -κ c/|c|`, with `κ` a fixed unit, on the support of `Λ` or off an exceptional
set of small weight, so the Lean theorems are conditional. The unconditional statement, that
Conjecture 1.2 is false for the quartic Gauss sum, rests on Lemma 2.2 of the companion paper, which is
proved there and not formalized:

- the quartic Gauss sum satisfies the identity with `κ = 1` at every primary prime (DDHL (1.2) at
  `k = 2`, equivalently (3.11), with its symbol factors evaluated, and DDHL (3.8) at the primes of
  degree two), and vanishes at higher prime powers (DDHL (3.7));
- `conj (ν/c)₄ = (ν³/c)₄`, used to read `pairing_identities` as `A(ν³, -m) = -conj A(ν, m)`.

The conjecture is stated along integer `X`; since the conjecture for real `X` implies it along the
integers, refuting the latter refutes the former. `check/pairing.py` recomputes `g̃(c)` from the
definition of DDHL at every primary prime of degree one with norm at most 6000 and checks the
identity, the pairing and `S_β(X; 1) = -conj S_β(X; 0)` to `10⁻¹³`.

## Sources

- The companion paper: J. S. Farland, *The twists ℓ = 0 and ℓ = 1 in a conjecture on quartic Gauss
  sums, formalized in Lean* (preprint, Zenodo, 2026).
- The manuscript: J. S. Farland, *A note on Conjecture 1.2 of David, Dunn, Hamieh and Lin: the
  pairing of the twists, Suzuki's vanishing law, and a repair* (Paper IX of the author's series),
  whose Section 3 is formalized here.

## Authorship, AI assistance and licence

The mathematics and the manuscript are by Joseph S. Farland. The Lean code was drafted and repaired
by Claude (Anthropic); the formulation with an abstract Gauss sum was proposed by Claude and adopted
by the author. The code is released under the Apache License 2.0 (`LICENSE`); the paper is CC BY 4.0.

## Layout for the Palomar registry

- `Challenge.lean` is the statement surface to audit. It restates the definitions exactly as the
  development has them and states the seven results with `sorry`.
- `Solution.lean` proves the same declarations from the development in `QuarticPairing/`.
- `comparator.json` lists the compared theorems and definitions and the permitted axioms.
- `formalization.yaml` records authorship, sources, AI assistance, scope and fidelity.
- `scripts/` holds Palomar's checks, copied from the Palomar starter template.

```
python3 scripts/check-lean-sources.py
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh      # needs bubblewrap (bwrap)
```

| Paper | Challenge declaration |
|---|---|
| Lemma 3.1 | `pointwise_pairing` |
| Theorem 3.2 | `pairing_of_twists` |
| Theorem 3.3 | `pairing_of_twists_defect` |
| Proposition 3.4 | `pairing_identities` |
| **Theorem 4.1** | `conjecture12_inconsistent` |
| **Theorem 4.2** | `conjecture12_inconsistent_of_defect` |
| Proposition 5.1 | `why_quartic` |

| File | Contents |
|---|---|
| `Defs` | `unitDir`, `normBall`, `twistedSum`, `Conjecture12`, `defectSum`, `twistedAvg` |
| `Pairing` | the pointwise pairing, the pairing of the twists, the pairing identities, why quartic |
| `Inconsistency` | the two inconsistency theorems |
