# Formalization Plan: Lutz-Nagell via Division Polynomials (Project + mathlib)

## Summary (What We Will Prove)
Formalize the short **Lutz-Nagell** theorem from the PDF
`/Users/mcu22seu/Downloads/nagell-lutz, quickly.pdf` for the short Weierstrass model
`y^2 = x^3 + A*x + B` with `A B : ℤ`, `Δ = -16*(4*A^3 + 27*B^2) ≠ 0`, and a nonzero torsion point
`P ∈ E(ℚ)`:

1. `x(P), y(P) ∈ ℤ`
2. `y(P) = 0 ∨ y(P)^2 ∣ Δ`.

We will reuse (already in this repo / vendored mathlib):
- Division polynomials + congruences in project:
  - `/Users/mcu22seu/Documents/GitHub/Nagel--Lutz/LutzNagell/DivisionPolynomial.lean`
  - `/Users/mcu22seu/Documents/GitHub/Nagel--Lutz/LutzNagell/DivisionPolynomialOmega.lean`
- Multiplication formula in Jacobian coords:
  - `/Users/mcu22seu/Documents/GitHub/Nagel--Lutz/LutzNagell/ZSMul.lean` (`WeierstrassCurve.zsmul_eq_smulEval`)
- Rational root theorem (mathlib):
  - `/Users/mcu22seu/Documents/GitHub/Nagel--Lutz/.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/RationalRoot.lean`
- Nat “power equality with coprime exponents” lemma (mathlib):
  - `/Users/mcu22seu/Documents/GitHub/Nagel--Lutz/.lake/packages/mathlib/Mathlib/Data/Nat/Factorization/Basic.lean`
- Division polynomial degree facts in mathlib (template to port):
  - `/Users/mcu22seu/Documents/GitHub/Nagel--Lutz/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`

## High-Level Proof Structure (Matches the PDF)
We implement the PDF’s “denominator shape” lemma (Lemma 3.3 in the PDF), the prime-order torsion
integrality argument, and the “integral-multiple-backwards” lemma (Lemma 3.2 in the PDF),
all using the project’s division-polynomial framework.

1. **(Denominator shape)** If `y^2 = x^3 + A*x + B` with `x y : ℚ`, then the denominator of `x`
   is a square (and `y` a cube).
   Lean target: either
   - `∃ d a b : ℤ, x = (a : ℚ) / (d : ℚ)^2 ∧ y = (b : ℚ) / (d : ℚ)^3`, or
   - `∃ d : ℕ, Int.natAbs (IsFractionRing.den ℤ x : ℤ) = d^2` (and similarly for `y`).

2. **(Prime-order case)** If `P ≠ 0` and `p` is prime with `p • P = 0`, then `x(P), y(P) ∈ ℤ`.
   Key steps:
   - From `p • P = 0`, use `zsmul_eq_smulEval` to get `evalEval x y (ψ p) = 0`.
   - Use coordinate-ring congruences (`Affine.CoordinateRing.mk_ψ`, `mk_φ`, `mk_Ψ_sq`)
     to rewrite evaluation of `ψ p` into a univariate polynomial root statement for `preΨ p`.
   - Apply rational root theorem to `preΨ p` and combine with the “den(x) is a square” lemma
     to force `den(x)=1`, hence `x ∈ ℤ`, then `y ∈ ℤ` from the curve equation.

3. **(Integral-multiple-backwards, PDF Lemma 3.2)** If `n • P` is an *integral affine point*
   `(X,Y)` with `X Y : ℤ`, then `P` was integral.
   Use `x(n•P) = Φ_n(x(P)) / ΨSq_n(x(P))` plus degree/leading coefficient facts to show
   denominators cannot cancel unless `den(x(P))=1`.

4. **(General torsion → prime torsion)** For torsion `P ≠ 0`, set `m = addOrderOf P`, choose a
   prime `p ∣ m`, set `Q = (m/p) • P`. Show `Q ≠ 0` and `p • Q = 0`. Apply prime-order lemma to
   `Q` to get `Q` integral. Apply “integral-multiple-backwards” to deduce `P` integral.

5. **(Discriminant divisibility)** Once `x,y ∈ ℤ`, use integrality of `2•P` to show
   `y^2 = f(x) ∣ (3*x^2 + A)^2`. Then use an explicit integer identity to show `y^2 ∣ Δ`.
   The identity we will keep as a Lean lemma proved by `ring`:
   ```text
   let f := x^3 + A*x + B
   let g := 3*x^2 + A
   (432*x^3 + 432*A*x - 432*B) * f + (-48*x^2 - 64*A) * g^2 = -16*(4*A^3 + 27*B^2)
   ```

## Repo Additions (Files to Create)
We split into small files to enable parallel workers.

- `LutzNagell/LutzNagellTheorem/ShortWeierstrass.lean`
  - Defines the short curve over `ℤ` and its map/base-change to `ℚ`.
  - Proves simp lemmas for `Equation`, `Δ`, and short-form rewriting.
- `LutzNagell/DivisionPolynomialDegree.lean`
  - Port/copy-adapt of mathlib’s division-polynomial degree file, but importing
    `LutzNagell.DivisionPolynomial` (project copy) instead of mathlib’s Basic file.
- `LutzNagell/LutzNagellTheorem/EvalBridge.lean`
  - Lemmas that turn coordinate-ring congruences into equalities of `evalEval` at an on-curve point
    (ψ/Ψ, φ/Φ, ΨSq).
- `LutzNagell/LutzNagellTheorem/Denominators.lean`
  - Denominator-square/cube lemma (PDF Lemma 3.3).
- `LutzNagell/LutzNagellTheorem/PrimeOrder.lean`
  - Prime-order torsion integrality.
- `LutzNagell/LutzNagellTheorem/IntegralMultiple.lean`
  - Integral-multiple-backwards (PDF Lemma 3.2).
- `LutzNagell/LutzNagellTheorem/Main.lean`
  - Final theorem and corollaries; imports the above.

Also update the single-import entrypoint:
- `LutzNagell.lean` should eventually import `LutzNagell.LutzNagellTheorem.Main`.

## Ticketing + Progress System (Files)
AI workers will update:
- `docs/lutz_nagell/WORKBOARD.md` (single source of truth table)
- `docs/lutz_nagell/TICKETS/*.md` (one file per ticket, with acceptance criteria)

Recommended `WORKBOARD.md` columns:
`ID | Status | Owner | Depends | Files | Deliverable | Acceptance | Notes`

Status enum:
`TODO`, `IN_PROGRESS`, `BLOCKED`, `REVIEW`, `DONE`

Global “definition of done” for a ticket:
- The ticket’s deliverables are implemented with correct statements.
- No `sorry`.
- `lake build` succeeds.

## Tickets (Parallelizable Work Breakdown)
See `docs/lutz_nagell/WORKBOARD.md` and `docs/lutz_nagell/TICKETS/`.
