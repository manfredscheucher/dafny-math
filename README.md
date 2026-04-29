# dafny-math

Machine-verified mathematical proofs in [Dafny](https://dafny.org/).

All proofs are fully verified by Dafny's SMT backend (Z3), with the exception of one
documented axiom (`DvdFromWitness` in `lib/Divisibility.dfy` — see below).

---

## Proof index

### Number Theory (`number-theory/`)

| Theorem | File | Lemmas | Notes |
|---|---|---|---|
| √2 is irrational | `sqrt2-irrational/sqrt2irrational_v1.dfy` | 12 | Standalone, parity-based |
| √2 is irrational | `sqrt2-irrational/sqrt2irrational_v2.dfy` | 9 | Uses `lib/Divisibility.dfy` |
| √p is irrational (p prime) | `sqrt-prime-irrational/sqrt_prime_irrational.dfy` | 24 | Euclid's Lemma via Bézout |

---

## Proof strategies

### √2 is irrational

**Theorem:** ∀ a b : ℕ, b > 0 → a² ≠ 2·b²

**Proof (v1, parity-based):** By infinite descent. If a² = 2b², then a² is even → a
is even → a = 2h. Substituting: 4h² = 2b² → b² = 2h². Then b is even → b = 2g, giving
h² = 2g² — a strictly smaller solution. Contradiction.

The key lemma (`n² even → n even`) is proved via the contrapositive: if n is odd, n² is odd.

**Proof (v2):** Same descent, but parity is handled via the shared `Dvd` predicate
(treating 2 as an ordinary divisor). More uniform with the prime proof.

### √p is irrational for any prime p

**Theorem:** ∀ prime p, ∀ a b : ℕ, b > 0 → a² ≠ p·b²

**Proof:** Same infinite descent structure, but "p | a² → p | a" requires
**Euclid's Lemma**: prime p | a·b → p | a or p | b.

Euclid's Lemma is proved via **Bézout's identity**: if gcd(p, a) = 1, there exist
naturals s, t with s·p = t·a + 1 (or vice versa). Multiplying by b and using p | a·b
gives p | b. The extended Euclidean algorithm computes Bézout coefficients as a
nat-only datatype, avoiding negative numbers entirely.

---

## Shared library

`lib/Divisibility.dfy` provides:

| Name | Type | Description |
|---|---|---|
| `Dvd(d, n)` | predicate | d divides n (d > 0, both nat) |
| `DvdWitness` | lemma | `Dvd(d,n) → ∃ k, n == d*k` |
| `DvdFromWitness` | **axiom** | `n == d*k → Dvd(d,n)` |
| `DvdAdd` | lemma | `Dvd(d,x) ∧ Dvd(d,y) → Dvd(d,x+y)` |
| `DvdMul` | lemma | `Dvd(d,x) → Dvd(d, c*x)` |

`DvdFromWitness` is marked `{:axiom}` because Dafny's Z3 backend cannot prove
`(d*k) % d == 0` (nonlinear arithmetic). It is mathematically sound.
See `LESSONS_LEARNED.md` for a full explanation.

---

## Running the proofs

```bash
dafny verify number-theory/sqrt2-irrational/sqrt2irrational_v1.dfy
dafny verify number-theory/sqrt2-irrational/sqrt2irrational_v2.dfy
dafny verify number-theory/sqrt-prime-irrational/sqrt_prime_irrational.dfy
```

Expected: `0 errors` for each file.

---

## Further reading

- `LESSONS_LEARNED.md` — what works and what doesn't in Dafny (Z3 limitations, failed approaches, proof patterns)
- `CLAUDE.md` — project conventions

---

## Planned

- **Number theory:** primality, fundamental theorem of arithmetic, infinitely many primes
- **Algebra:** group theory basics
- **Analysis:** real number properties
