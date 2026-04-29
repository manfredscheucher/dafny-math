// number-theory/sqrt-prime-irrational/sqrt_prime_irrational.dfy
//
// Proof that √p is irrational for any prime p.
//
// Main theorem (SqrtOfPrimeIsIrrational):
//   For any prime p and naturals a, b with b > 0: a*a != p*b*b.
//
// Proof:
//   (1) Euclid's Lemma: prime p | a*b → p | a or p | b.
//       Proved via Bézout's identity from the extended Euclidean algorithm.
//   (2) Infinite descent: any solution (a,b) of a²=p·b² yields a smaller one.

include "../../lib/Divisibility.dfy"

// ── Primality ─────────────────────────────────────────────────────────────────

predicate IsPrime(p: nat) {
    p >= 2 && forall q: nat :: 2 <= q < p ==> !Dvd(q, p)
}

lemma PrimeNoDivisorInRange(p: nat, q: nat)
    requires IsPrime(p)
    requires 2 <= q < p
    ensures q > 0 && !Dvd(q, p)
{}

lemma PrimeDivisor(p: nat, d: nat)
    requires IsPrime(p)
    requires d > 0
    requires Dvd(d, p)
    ensures d == 1 || d == p
{
    if 2 <= d < p { PrimeNoDivisorInRange(p, d); }
    if d > p {
        assert p % d == p;
        assert false;
    }
}

// ── Extended Euclidean Algorithm ──────────────────────────────────────────────
// Bézout witness in nat only, avoiding negative subtraction.
// Invariant: pos=true  means  s*a == t*b + g
//            pos=false means  t*b == s*a + g

datatype Bez = Bez(g: nat, s: nat, t: nat, pos: bool)

function ExtGcd(a: nat, b: nat): Bez
    requires a > 0
    decreases b
{
    if b == 0 then Bez(a, 1, 0, true)
    else
        var q := a / b;
        var w := ExtGcd(b, a % b);
        if w.pos then Bez(w.g, w.t, w.s + w.t * q, false)
        else          Bez(w.g, w.t, w.s + w.t * q, true)
}

lemma ExtGcdBezout(a: nat, b: nat)
    requires a > 0
    ensures var w := ExtGcd(a, b);
            w.g > 0
            && (w.pos ==> w.s * a == w.t * b + w.g)
            && (!w.pos ==> w.t * b == w.s * a + w.g)
    decreases b
{
    if b == 0 { } else {
        var q := a / b;
        var r := a % b;
        assert a == q * b + r;
        ExtGcdBezout(b, r);
        var w' := ExtGcd(b, r);
        var w  := ExtGcd(a, b);
        if w'.pos {
            assert w == Bez(w'.g, w'.t, w'.s + w'.t * q, false);
            calc {
                (w'.s + w'.t * q) * b;
                == w'.s * b + w'.t * q * b;
                == (w'.t * r + w'.g) + w'.t * q * b;
                == w'.t * (r + q * b) + w'.g;
                == w'.t * a + w'.g;
            }
        } else {
            assert w == Bez(w'.g, w'.t, w'.s + w'.t * q, true);
            calc {
                w'.t * a;
                == w'.t * (q * b + r);
                == w'.t * q * b + w'.t * r;
                == w'.t * q * b + (w'.s * b + w'.g);
                == (w'.t * q + w'.s) * b + w'.g;
            }
        }
    }
}

lemma ExtGcdDvd(a: nat, b: nat)
    requires a > 0
    ensures var g := ExtGcd(a, b).g;
            g > 0 && Dvd(g, a) && (b == 0 || Dvd(g, b))
    decreases b
{
    var w := ExtGcd(a, b);
    if b == 0 {
        DvdFromWitness(a, a, 1);
    } else {
        var r := a % b;
        ExtGcdDvd(b, r);
        var w' := ExtGcd(b, r);
        assert w.g == w'.g;
        var g := w.g;
        assert Dvd(g, b);
        DvdWitness(g, b); var kb :| b == g * kb;
        if r == 0 {
            DvdFromWitness(g, a, (a / b) * kb);
        } else {
            assert Dvd(g, r);
            DvdWitness(g, r); var kr :| r == g * kr;
            DvdFromWitness(g, a, (a / b) * kb + kr);
        }
    }
}

// ── Euclid's Lemma ────────────────────────────────────────────────────────────

lemma PrimeGcdOne(p: nat, a: nat)
    requires IsPrime(p)
    requires a > 0
    requires !Dvd(p, a)
    ensures ExtGcd(p, a).g == 1
{
    ExtGcdDvd(p, a);
    var g := ExtGcd(p, a).g;
    assert Dvd(g, p);
    PrimeDivisor(p, g);
    if g == p { assert Dvd(p, a); assert false; }
}

// From  s*p == t*a + 1  and  a*b == p*kab,  derive  p | b.
lemma EuclidPos(p: nat, a: nat, b: nat, s: nat, t: nat, kab: nat)
    requires p >= 2
    requires a * b == p * kab
    requires s * p == t * a + 1
    ensures Dvd(p, b)
{
    assert s * p * b == t * (a * b) + b;
    assert s * p * b == t * p * kab + b;
    assert p * (s * b) == p * (t * kab) + b;
    assert s * b >= t * kab;
    assert b == p * (s * b - t * kab);
    DvdFromWitness(p, b, s * b - t * kab);
}

// From  t*a == s*p + 1  and  a*b == p*kab,  derive  p | b.
lemma EuclidNeg(p: nat, a: nat, b: nat, s: nat, t: nat, kab: nat)
    requires p >= 2
    requires a * b == p * kab
    requires t * a == s * p + 1
    ensures Dvd(p, b)
{
    assert t * (a * b) == s * p * b + b;
    assert t * p * kab == s * p * b + b;
    assert p * (t * kab) == p * (s * b) + b;
    assert t * kab >= s * b;
    assert b == p * (t * kab - s * b);
    DvdFromWitness(p, b, t * kab - s * b);
}

// Euclid's Lemma: prime p | a*b → p | a  or  p | b.
lemma EuclidLemma(p: nat, a: nat, b: nat)
    requires IsPrime(p)
    requires a > 0 && b > 0
    requires Dvd(p, a * b)
    ensures Dvd(p, a) || Dvd(p, b)
{
    if !Dvd(p, a) {
        PrimeGcdOne(p, a);
        ExtGcdBezout(p, a);
        var w := ExtGcd(p, a);
        assert w.g == 1;
        DvdWitness(p, a * b); var kab :| a * b == p * kab;
        if w.pos { EuclidPos(p, a, b, w.s, w.t, kab); }
        else      { EuclidNeg(p, a, b, w.s, w.t, kab); }
    }
}

// ── Irrationality of sqrt(p) ──────────────────────────────────────────────────

// p prime, p | n² → p | n.
lemma PrimeDividesSquare(p: nat, n: nat)
    requires IsPrime(p)
    requires n > 0
    requires Dvd(p, n * n)
    ensures Dvd(p, n)
{
    EuclidLemma(p, n, n);
}

// a = p*h and a² = p*b²  →  b² = p*h²
lemma SquareHalve(p: nat, a: nat, b: nat, h: nat)
    requires p > 0
    requires a == p * h
    requires a * a == p * b * b
    ensures b * b == p * h * h
{
    assert p * p * h * h == p * b * b;
    assert p * (p * h * h) == p * (b * b);
    assert p * h * h == b * b;
}

// b = p*g and b² = p*h²  →  h² = p*g²
lemma SquareHalve2(p: nat, b: nat, h: nat, g: nat)
    requires p > 0
    requires b == p * g
    requires b * b == p * h * h
    ensures h * h == p * g * g
{
    assert p * p * g * g == p * h * h;
    assert p * (p * g * g) == p * (h * h);
    assert p * g * g == h * h;
}

// Main lemma: for prime p, no naturals a, b with b > 0 satisfy a² = p·b².
lemma SqrtPrimeIrrational(p: nat, a: nat, b: nat)
    requires IsPrime(p)
    requires b > 0
    ensures a * a != p * b * b
    decreases b
{
    if a * a == p * b * b {
        // 1. p | a²
        DvdFromWitness(p, a * a, b * b);

        // 2. p | a
        PrimeDividesSquare(p, a);
        DvdWitness(p, a); var h :| a == p * h;

        // 3. b² = p * h²
        SquareHalve(p, a, b, h);

        // 4. p | b²
        DvdFromWitness(p, b * b, h * h);

        // 5. p | b
        PrimeDividesSquare(p, b);
        DvdWitness(p, b); var g :| b == p * g;

        // 6. g > 0
        assert g > 0;

        // 7. h² = p * g²
        SquareHalve2(p, b, h, g);

        // 8. Smaller solution — contradiction.
        SqrtPrimeIrrational(p, h, g);
    }
}

// Top-level: √p is irrational for every prime p.
lemma SqrtOfPrimeIsIrrational(p: nat)
    requires IsPrime(p)
    ensures forall a: nat, b: nat :: b > 0 ==> a * a != p * b * b
{
    forall a: nat, b: nat | b > 0
        ensures a * a != p * b * b
    {
        SqrtPrimeIrrational(p, a, b);
    }
}
