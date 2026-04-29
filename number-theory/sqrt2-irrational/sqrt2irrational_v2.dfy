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

// ── Dvd(2, n²) → Dvd(2, n) ────────────────────────────────────────────────────

// Mod(2*m+1, 2) == 1, by induction on m (subtracting 2 each step).
lemma OddModTwo(m: nat)
    ensures Mod(2 * m + 1, 2) == 1
    decreases m
{
    if m == 0 {
        // Mod(1, 2) == 1 since 1 < 2. Trivial.
    } else {
        OddModTwo(m - 1);
        // 2*m+1 = 2*(m-1)+1 + 2, so one ModShift step suffices.
        assert 2 * m + 1 == 2 * (m - 1) + 1 + 2;
        ModShift(2 * (m - 1) + 1, 2);
    }
}

// Dvd(2, n²) → Dvd(2, n)
lemma TwoDividesSquareImpliesTwo(n: nat)
    requires n > 0
    requires Dvd(2, n * n)
    ensures Dvd(2, n)
{
    // Contrapositive: if n is odd, n² is odd.
    if !Dvd(2, n) {
        // Mod(n, 2) != 0, so Mod(n, 2) == 1, i.e. n = 2k+1 for k = n/2.
        var k := n / 2;
        // n odd and Mod-based: show n == 2*k+1 via DvdWitnessHelper contrapositive
        assert Mod(n, 2) == 1 by { assert n >= 2 || n == 1; ModOddIsOne(n); }
        ModOddImpliesOdd(n);
        var j :| n == 2 * j + 1;
        // n² = (2j+1)² = 2*(2j²+2j) + 1, so Mod(n², 2) == 1
        assert n * n == 2 * (2 * j * j + 2 * j) + 1;
        OddModTwo(2 * j * j + 2 * j);
        assert Mod(n * n, 2) == 1;
        assert false; // contradicts Dvd(2, n*n)
    }
}

// If Mod(n, 2) != 0 then Mod(n, 2) == 1.
lemma ModOddIsOne(n: nat)
    requires Mod(n, 2) != 0
    ensures Mod(n, 2) == 1
{
    // Mod(n, 2) is either 0 or 1 (it's < 2 by definition of Mod).
    assert Mod(n, 2) < 2 by { ModBound(n, 2); }
}

lemma ModBound(a: nat, b: nat)
    requires b > 0
    ensures Mod(a, b) < b
    decreases a
{
    if a < b { } else { ModBound(a - b, b); }
}

// If Mod(n, 2) == 1, then n is odd: exists k, n == 2*k+1.
lemma ModOddImpliesOdd(n: nat)
    requires Mod(n, 2) == 1
    ensures exists k: nat :: n == 2 * k + 1
    decreases n
{
    if n == 1 {
        assert n == 2 * 0 + 1;
    } else {
        // n >= 2, so Mod(n, 2) == Mod(n-2, 2) == 1
        assert n >= 2;
        ModShift(n - 2, 2);
        // Mod(n, 2) == Mod(n-2+2, 2) == Mod(n-2, 2) == 1
        assert Mod(n - 2, 2) == 1;
        ModOddImpliesOdd(n - 2);
        var k :| n - 2 == 2 * k + 1;
        assert n == 2 * (k + 1) + 1;
    }
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
