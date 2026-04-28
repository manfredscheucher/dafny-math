# Formal Proof: √2 is Irrational (Dafny)

A machine-verified proof that √2 is irrational, written in [Dafny](https://dafny.org/).

## What is proved

```
∀ p q : ℕ, q > 0 → p² ≠ 2·q²
```

This is equivalent to saying √2 is irrational: if √2 = p/q, then p² = 2·q², which the proof shows is impossible.

## Proof strategy: infinite descent

Assume p² = 2·q² for some natural numbers p, q with q > 0. Then:

1. p² is even → p is even → p = 2h
2. Substituting: 4h² = 2q² → q² = 2h²
3. q² is even → q is even → q = 2g
4. Substituting: 4g² = 2h² → h² = 2g²
5. (h, g) is a strictly smaller solution with 0 < g < q

This is a contradiction: q cannot decrease indefinitely. Dafny verifies termination via `decreases q`.

## Structure

| Lemma | Purpose |
|---|---|
| `OddSquareIsOdd` | If n = 2k+1, then n² ≡ 1 (mod 2) |
| `SquareEvenImpliesEven` | n² even → n even (contrapositive of above) |
| `EvenSquareWitness` | Gives Dafny an explicit witness that p² = 2·q·q is even |
| `EvenDivision` | n even → n = 2·(n/2) |
| `Sqrt2Irrational` | Main lemma: infinite descent on q |
| `Sqrt2IsIrrational` | Top-level theorem (universal quantifier) |

## Running the proof

```bash
dafny verify sqrt2irrational.dfy
# Dafny program verifier finished with 12 verified, 0 errors
```
