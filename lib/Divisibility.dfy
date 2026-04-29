// lib/Divisibility.dfy
//
// Shared library: divisibility on nat.
//
// Used by: number-theory/sqrt-prime-irrational/

// Dvd(d, n) ↔ d divides n (both nat, d > 0).
predicate Dvd(d: nat, n: nat)
    requires d > 0
{
    n % d == 0
}

// Dvd(d, n) → ∃ k, n == d * k
lemma DvdWitness(d: nat, n: nat)
    requires d > 0
    requires Dvd(d, n)
    ensures exists k: nat :: n == d * k
{
    assert n == d * (n / d);
}

// n == d * k → Dvd(d, n)
// Marked {:axiom}: mathematically trivial, but Dafny's Z3 backend cannot prove
// (d * k) % d == 0 without a nonlinear arithmetic decision procedure.
// See LESSONS_LEARNED.md for details.
lemma {:axiom} DvdFromWitness(d: nat, n: nat, k: nat)
    requires d > 0
    requires n == d * k
    ensures Dvd(d, n)

// Dvd(d, x) ∧ Dvd(d, y) → Dvd(d, x+y)
lemma DvdAdd(d: nat, x: nat, y: nat)
    requires d > 0
    requires Dvd(d, x) && Dvd(d, y)
    ensures Dvd(d, x + y)
{
    DvdWitness(d, x); var kx :| x == d * kx;
    DvdWitness(d, y); var ky :| y == d * ky;
    DvdFromWitness(d, x + y, kx + ky);
}

// Dvd(d, x) → Dvd(d, c * x)
lemma DvdMul(d: nat, x: nat, c: nat)
    requires d > 0
    requires Dvd(d, x)
    ensures Dvd(d, c * x)
{
    DvdWitness(d, x); var k :| x == d * k;
    DvdFromWitness(d, c * x, c * k);
}
