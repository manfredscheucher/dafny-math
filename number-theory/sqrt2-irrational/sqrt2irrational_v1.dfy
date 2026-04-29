// Proof that sqrt(2) is irrational.
//
// We show: for all nat p, q with q > 0: p*p != 2*q*q.
// (Working with nat avoids Dafny's non-standard negative modulo.)
//
// Proof by infinite descent: any solution (p,q) produces a strictly
// smaller solution (h, g) with g < q — impossible for q : nat.

// ── Helper: even multiples ────────────────────────────────────────────────────

// 2*k is divisible by 2.
lemma TwoKEven(k: nat)
    ensures (2 * k) % 2 == 0
{}

// n % 2 == 0 implies n == 2 * (n/2).
lemma EvenDivision(n: nat)
    requires n % 2 == 0
    ensures n == 2 * (n / 2)
{
    assert n == 2 * (n / 2) + n % 2;
}

// If n^2 is divisible by 2, then n^2 = 2*something.
// We give Dafny the explicit witness.
lemma EvenSquareWitness(n: nat, q: nat)
    requires n * n == 2 * q * q
    ensures n * n % 2 == 0
{
    // 2*q*q is clearly even.
    assert n * n == 2 * (q * q);
}

// ── Helper: odd squares are odd ───────────────────────────────────────────────

// If n is odd (n = 2k+1), then n^2 mod 2 = 1.
lemma OddSquareIsOdd(k: nat)
    ensures (2 * k + 1) * (2 * k + 1) % 2 == 1
{
    var m := 2 * k * k + 2 * k;
    assert (2 * k + 1) * (2 * k + 1) == 2 * m + 1;
}

// If n^2 is even, then n must be even (contrapositive of odd → odd^2).
lemma SquareEvenImpliesEven(n: nat)
    ensures n * n % 2 == 0 ==> n % 2 == 0
{
    if n % 2 != 0 {
        OddSquareIsOdd(n / 2);
        assert n == 2 * (n / 2) + 1;
    }
}

// ── Main lemma: infinite descent ─────────────────────────────────────────────

// For all nat p, q with q > 0: p*p != 2*q*q.
lemma Sqrt2Irrational(p: nat, q: nat)
    requires q > 0
    ensures p * p != 2 * q * q
    decreases q
{
    if p * p == 2 * q * q {

        // 1. p^2 is even ⟹ p is even.
        EvenSquareWitness(p, q);        // p*p % 2 == 0
        SquareEvenImpliesEven(p);       // p % 2 == 0
        assert p % 2 == 0;
        EvenDivision(p);                // p == 2*(p/2)
        var h := p / 2;
        assert p == 2 * h;

        // 2. q^2 = 2 * h^2
        //    p^2 = 4*h^2 = 2*q^2  ⟹  q^2 = 2*h^2
        assert p * p == 4 * h * h;
        assert q * q == 2 * h * h;

        // 3. q^2 is even ⟹ q is even.
        EvenSquareWitness(q, h);        // q*q % 2 == 0
        SquareEvenImpliesEven(q);       // q % 2 == 0
        assert q % 2 == 0;
        EvenDivision(q);                // q == 2*(q/2)
        var g := q / 2;
        assert q == 2 * g;

        // 4. g > 0
        assert g > 0;

        // 5. h^2 = 2 * g^2
        //    q^2 = 4*g^2 = 2*h^2  ⟹  h^2 = 2*g^2
        assert q * q == 4 * g * g;
        assert h * h == 2 * g * g;

        // 6. Inductive step: 0 < g < q, contradiction.
        Sqrt2Irrational(h, g);
    }
}

// ── Top-level theorem ─────────────────────────────────────────────────────────

lemma Sqrt2IsIrrational()
    ensures forall p: nat, q: nat :: q > 0 ==> p * p != 2 * q * q
{
    forall p: nat, q: nat | q > 0
        ensures p * p != 2 * q * q
    {
        Sqrt2Irrational(p, q);
    }
}
