# Proof: √p is Irrational for any Prime p

**Theorem:** For any prime p and all naturals a, b with b > 0: a² ≠ p·b²

`sqrt_prime_irrational.dfy` — depends on `../../lib/Divisibility.dfy`.

```bash
dafny verify sqrt_prime_irrational.dfy
# 24 verified, 0 errors
```

## Proof strategy

Same infinite descent as the √2 proof, but "p | a² → p | a" requires
**Euclid's Lemma**, which in turn requires **Bézout's identity**.

### Infinite descent

Assume a² = p·b² for some prime p and naturals a, b with b > 0. Then:

1. p | a² → p | a (Euclid's Lemma) → a = p·h
2. p²h² = p·b² → b² = p·h²
3. p | b² → p | b → b = p·g
4. p²g² = p·h² → h² = p·g²
5. (h, g) is a strictly smaller solution with 0 < g < b — contradiction.

### Euclid's Lemma

**Lemma:** prime p | a·b → p | a or p | b

**Proof:** If p ∤ a, then gcd(p, a) = 1 (since p is prime). By Bézout's identity,
there exist naturals s, t such that either s·p = t·a + 1 or t·a = s·p + 1.
Multiplying by b and using p | a·b gives p | b.

### Bézout's identity (nat-only formulation)

The extended Euclidean algorithm is encoded as a nat-only datatype:

```dafny
datatype Bez = Bez(g: nat, s: nat, t: nat, pos: bool)
// pos=true:  s*a == t*b + g
// pos=false: t*b == s*a + g
```

Using `pos: bool` to track which side is larger avoids negative numbers entirely,
which is crucial since Dafny's `%` on negative integers is non-standard.

## Lemma structure

| Lemma | Purpose |
|---|---|
| `IsPrime`, `PrimeDivisor` | Primality: divisors of p are only 1 and p |
| `ExtGcd`, `ExtGcdBezout` | Extended Euclidean algorithm + Bézout correctness |
| `ExtGcdDvd` | gcd divides both arguments |
| `PrimeGcdOne` | p prime, p∤a → gcd(p,a) = 1 |
| `EuclidPos`, `EuclidNeg` | Bézout × b → p\|b (two cases) |
| `EuclidLemma` | p prime, p\|a·b → p\|a or p\|b |
| `PrimeDividesSquare` | p\|n² → p\|n |
| `SquareHalve`, `SquareHalve2` | Nonlinear arithmetic helpers |
| `SqrtPrimeIrrational` | Main infinite descent |
| `SqrtOfPrimeIsIrrational` | Top-level ∀ statement |
