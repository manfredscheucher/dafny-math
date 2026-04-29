// number-theory/sqrt2-irrational/sqrt2irrational_v2.dfy
//
// Proof that √2 is irrational — version 2, using shared lib/Divisibility.dfy.
//
// This is a refactored version of v1. The proof strategy changes slightly:
// instead of parity-specific helpers, we use the general Dvd infrastructure
// (same as sqrt-prime-irrational), with 2 treated as an ordinary divisor.
//
// See v1 (sqrt2irrational_v1.dfy) for the self-contained parity-based proof.

include "../../lib/Divisibility.dfy"

// ── Helper: odd squares are odd ───────────────────────────────────────────────

lemma OddSquareIsOdd(k: nat)
    ensures (2 * k + 1) * (2 * k + 1) % 2 == 1
{
    var m := 2 * k * k + 2 * k;
    assert (2 * k + 1) * (2 * k + 1) == 2 * m + 1;
}

// If n² is even, then n is even.
lemma SquareEvenImpliesEven(n: nat)
    ensures n * n % 2 == 0 ==> n % 2 == 0
{
    if n % 2 != 0 {
        OddSquareIsOdd(n / 2);
        assert n == 2 * (n / 2) + 1;
    }
}

// ── Dvd(2, n²) → Dvd(2, n) ────────────────────────────────────────────────────

lemma TwoDividesSquareImpliesTwo(n: nat)
    requires n > 0
    requires Dvd(2, n * n)
    ensures Dvd(2, n)
{
    SquareEvenImpliesEven(n);
    assert n % 2 == 0;
}

// ── Main lemma: infinite descent ─────────────────────────────────────────────

// Helper: a = 2*h and a*a = 2*b*b  →  b*b = 2*h*h
lemma SquareHalve2(a: nat, b: nat, h: nat)
    requires a == 2 * h
    requires a * a == 2 * b * b
    ensures b * b == 2 * h * h
{
    assert 2 * 2 * h * h == 2 * b * b;
    assert b * b == 2 * h * h;
}

// For all nat p, q with q > 0: p*p != 2*q*q.
lemma Sqrt2Irrational(p: nat, q: nat)
    requires q > 0
    ensures p * p != 2 * q * q
    decreases q
{
    if p * p == 2 * q * q {

        // 1. 2 | p²
        DvdFromWitness(2, p * p, q * q);

        // 2. 2 | p
        TwoDividesSquareImpliesTwo(p);
        DvdWitness(2, p); var h :| p == 2 * h;

        // 3. q² = 2 * h²
        SquareHalve2(p, q, h);
        assert q * q == 2 * h * h;

        // 4. 2 | q²
        DvdFromWitness(2, q * q, h * h);

        // 5. 2 | q
        TwoDividesSquareImpliesTwo(q);
        DvdWitness(2, q); var g :| q == 2 * g;

        // 6. g > 0
        assert g > 0;

        // 7. h² = 2 * g²
        SquareHalve2(q, h, g);
        assert h * h == 2 * g * g;

        // 8. Smaller solution — contradiction.
        Sqrt2Irrational(h, g);
    }
}

// Top-level theorem.
lemma Sqrt2IsIrrational()
    ensures forall p: nat, q: nat :: q > 0 ==> p * p != 2 * q * q
{
    forall p: nat, q: nat | q > 0
        ensures p * p != 2 * q * q
    {
        Sqrt2Irrational(p, q);
    }
}
