# Lean 4 proofs of three OEIS conjectures

This repository contains complete Lean 4 / Mathlib proofs of conjectures stated in the
[OEIS](https://oeis.org/). The proofs use no `sorry` and no `native_decide`.
Each main theorem depends only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

| OEIS | Conjecture | Lean theorem |
|---|---|---|
| [A008578](https://oeis.org/A008578) | Gerasimova (2013): `k ≥ 1` is `1` or a prime iff `σ(k) > k·Ω(k)` | `OeisProofs.Gerasimova.gerasimova` |
| [A400194](https://oeis.org/A400194), [A400195](https://oeis.org/A400195) | Pol (2026): `A400194(n) = A001511(n) · A400195(n)` | `OeisProofs.TwoDense.maxBlock_eq` |
| [A384222](https://oeis.org/A384222) | Pol (2026): `T(n,k) = A384225(n,k) · A001511(n)` | `OeisProofs.TwoDense.card_block` |
| [A384222](https://oeis.org/A384222) | Pol (2025), Conjecture 1: each row is palindromic | `OeisProofs.TwoDense.block_div`, `card_block_div` |

## Statements of formal-conjectures

`OeisProofs/FC/` restates the conjectures exactly as in the
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) files
`FormalConjectures/OEIS/8578.lean`, `400194.lean` and `384222.lean`, and proves them.
These files use the OEIS definition directly: the increasing list of divisors is split with
`List.splitBy` between consecutive divisors `d < d'` with `d' > 2 * d`.

| Statement | Lean theorem |
|---|---|
| A008578 | `OeisA8578.conjecture` |
| A400194 | `OeisA400194.conjecture` |
| A384222, Conjecture 1 | `OeisA384222.conjecture_1` |
| A384222, formula of T(n,k) | `OeisA384222.conjecture_formula` |

## Definitions

A *2-dense sublist* of the divisors of `n` is a maximal run of consecutive divisors in which each
divisor is at most twice the previous one. In `OeisProofs/TwoDense.lean`, `block n d` is the
sublist that contains `d`. The file checks with `#guard` that the definitions reproduce the
first 100 terms of A400194 and A400195.

For A384222, the file proves that `d ↦ n / d` maps the sublist of `d` onto the sublist of `n / d`.
Because this map reverses the order of the divisors, the row of sublist lengths is a palindrome.

## Proof ideas

* **A400194, A400195, A384222.** If `d` and `2d` both divide `n`, then they lie in the same sublist.
  So every sublist is a union of sets `{o, 2o, 4o, …, 2^v o}`, where `o` is odd and `v = ν₂(n)`.
  Each such set contains exactly one odd number.
* **A008578.** `σ` is submultiplicative, and `σ(k) < k·P` for the largest prime factor `P` of `k`.
  If `P + 2 ≤ Ω(k)`, this gives `σ(k) ≤ k·Ω(k)` at once. Otherwise write `k = P·m` and use induction on `m`.

## Build

```
lake exe cache get
lake build
```

The project pins Lean `v4.33.1` and the Mathlib revision used by
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures).

## AI disclosure

The proofs were found and written with the help of an AI assistant (Claude, Anthropic).
Lean checked every proof. The definitions are tested against OEIS data with `#guard`.
