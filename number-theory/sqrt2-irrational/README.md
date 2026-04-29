# Proof: √2 is Irrational

**Theorem:** For all naturals a, b with b > 0: a² ≠ 2·b²

Two versions are provided:

## v1 — Standalone (parity-based)

`sqrt2irrational_v1.dfy` — no dependencies, self-contained.

Uses parity-specific lemmas (`OddSquareIsOdd`, `SquareEvenImpliesEven`).

| Lemma | Purpose |
|---|---|
| `OddSquareIsOdd` | n = 2k+1 → n² ≡ 1 (mod 2) |
| `SquareEvenImpliesEven` | n² even → n even |
| `EvenSquareWitness` | witness that p² = 2·q² is even |
| `EvenDivision` | n even → n = 2·(n/2) |
| `Sqrt2Irrational` | main infinite descent |
| `Sqrt2IsIrrational` | top-level ∀ statement |

```bash
dafny verify sqrt2irrational_v1.dfy
# 12 verified, 0 errors
```

## v2 — Uses shared lib/Divisibility.dfy

`sqrt2irrational_v2.dfy` — depends on `../../lib/Divisibility.dfy`.

Treats 2 as an ordinary divisor and reuses the `Dvd` infrastructure from the prime
proof. Same proof strategy, more uniform with the rest of the project.

| Lemma | Purpose |
|---|---|
| `OddSquareIsOdd` | n = 2k+1 → n² ≡ 1 (mod 2) |
| `SquareEvenImpliesEven` | n² even → n even |
| `TwoDividesSquareImpliesTwo` | Dvd(2, n²) → Dvd(2, n) |
| `SquareHalve2` | a=2h, a²=2b² → b²=2h² |
| `Sqrt2Irrational` | main infinite descent |
| `Sqrt2IsIrrational` | top-level ∀ statement |

```bash
dafny verify sqrt2irrational_v2.dfy
# 9 verified, 0 errors
```

## Proof strategy: infinite descent

Assume a² = 2b² for some naturals a, b with b > 0. Then:

1. 2 | a² → 2 | a → a = 2h
2. 4h² = 2b² → b² = 2h²
3. 2 | b² → 2 | b → b = 2g
4. 4g² = 2h² → h² = 2g²
5. (h, g) is a strictly smaller solution with 0 < g < b — contradiction.
