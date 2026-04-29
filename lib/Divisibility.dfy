// lib/Divisibility.dfy
//
// Shared library: divisibility on nat.
//
// We define modulo via repeated subtraction so that Dafny's verifier can
// reason about it inductively — Dafny's built-in % is opaque to Z3 for
// nonlinear terms like (d * k) % d.

// ── Custom modulo via repeated subtraction ────────────────────────────────────

function Mod(a: nat, b: nat): nat
    requires b > 0
    decreases a
{
    if a < b then a else Mod(a - b, b)
}

// Mod(a + b, b) == Mod(a, b)  — one subtraction step is neutral
lemma ModShift(a: nat, b: nat)
    requires b > 0
    ensures Mod(a + b, b) == Mod(a, b)
    decreases a
{
    if a < b {
        assert Mod(a + b, b) == Mod(a + b - b, b);
        assert a + b - b == a;
    } else {
        ModShift(a - b, b);
        assert Mod(a + b, b) == Mod(a + b - b, b);
        assert Mod(a, b) == Mod(a - b, b);
    }
}

// Mod(b * k, b) == 0  — key lemma, by induction on k
lemma ModMul(b: nat, k: nat)
    requires b > 0
    ensures Mod(b * k, b) == 0
    decreases k
{
    if k == 0 {
        assert b * 0 == 0;
    } else {
        ModMul(b, k - 1);
        assert b * k == b * (k - 1) + b;
        ModShift(b * (k - 1), b);
    }
}

// ── Divisibility predicate ────────────────────────────────────────────────────

// Dvd(d, n) ↔ d divides n (d > 0, both nat).
predicate Dvd(d: nat, n: nat)
    requires d > 0
{
    Mod(n, d) == 0
}

// Dvd(d, n) → ∃ k, n == d * k
lemma DvdWitness(d: nat, n: nat)
    requires d > 0
    requires Dvd(d, n)
    ensures exists k: nat :: n == d * k
{
    DvdWitnessHelper(d, n);
}

lemma DvdWitnessHelper(d: nat, n: nat)
    requires d > 0
    requires Mod(n, d) == 0
    ensures exists k: nat :: n == d * k
    decreases n
{
    if n < d {
        // Mod(n, d) == n == 0, so n == d * 0
        assert n == 0;
        assert n == d * 0;
    } else {
        // Mod(n, d) == Mod(n-d, d) == 0
        DvdWitnessHelper(d, n - d);
        var k :| n - d == d * k;
        assert n == d * (k + 1);
    }
}

// n == d * k → Dvd(d, n)
lemma DvdFromWitness(d: nat, n: nat, k: nat)
    requires d > 0
    requires n == d * k
    ensures Dvd(d, n)
{
    ModMul(d, k);
    assert Mod(d * k, d) == 0;
}

// Dvd(d, x) ∧ Dvd(d, y) → Dvd(d, x + y)
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
