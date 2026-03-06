# LN-004: Denominator Is a Square/Cube (PDF Lemma 3.3)

Status: TODO  
Owner:  
Last updated: 2026-03-04

## Depends
LN-001.

## Files
- `LutzNagell/LutzNagellTheorem/Denominators.lean`

## Goal
On the short curve `y^2 = x^3 + A*x + B` over `ℚ`, prove the “denominators are square/cube” lemma
used to force integrality in the rational-root step.

## Deliverables
1. A lemma that clears denominators to a Nat power equality.
   - Suggested target (adapt as needed to available API):
     `Int.natAbs (IsFractionRing.den ℤ x : ℤ)^3 = Int.natAbs (IsFractionRing.den ℤ y : ℤ)^2`.
2. From that, deduce existence of a square/cube:
   - `∃ d : ℕ, Int.natAbs (IsFractionRing.den ℤ x : ℤ) = d^2`
   - similarly for `y` being a cube (optional if not needed later).
3. Use `Nat.exists_eq_pow_of_exponent_coprime_of_pow_eq_pow` with `coprime 3 2`.

## Acceptance
- No `sorry`.
- `lake build` succeeds.
- The result is reusable as a lemma in `PrimeOrder`.

## Notes / Pitfalls
- Be explicit about working with `Int.natAbs` to avoid sign issues.
- You’ll likely need helper lemmas about `IsFractionRing.num/den` in `ℚ` over `ℤ`.

