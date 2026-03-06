# LN-008: Discriminant Divisibility (Second Claim)

Status: TODO  
Owner:  
Last updated: 2026-03-04

## Depends
LN-007, LN-001.

## Files
- `LutzNagell/LutzNagellTheorem/Main.lean`

## Goal
For a nonzero torsion point `P` on the short curve over `ℚ` with integral coordinates, prove:
`y(P) = 0 ∨ y(P)^2 ∣ Δ`.

## Deliverables
1. Prove the explicit identity (over `ℤ`) using `ring`:
   ```text
   (432*x^3 + 432*A*x - 432*B) * (x^3 + A*x + B)
     + (-48*x^2 - 64*A) * (3*x^2 + A)^2
     = -16*(4*A^3 + 27*B^2)
   ```
2. Use the `n=2` case (doubling / division polynomials) plus integrality of `2•P` to prove:
   - `f(x) = x^3 + A*x + B = y^2` divides `(3*x^2 + A)^2`.
3. Combine with the identity to conclude `y^2 ∣ Δ`.

## Acceptance
- No `sorry`.
- `lake build` succeeds.
- Final theorem statement matches the PDF claim.

## Notes / Pitfalls
- Prove small arithmetic lemmas first:
  - `y^2 ∣ g^2` plus identity implies `y^2 ∣ Δ`.
- Keep the doubling step isolated; don’t mix group-law algebra with the final divisibility step.

## Partial Implementation Notes
- The identity in Deliverable (1) is already available as
  `LutzNagell.LutzNagellTheorem.delta_linear_combination` in:
  `LutzNagell/LutzNagellTheorem/Main.lean`
