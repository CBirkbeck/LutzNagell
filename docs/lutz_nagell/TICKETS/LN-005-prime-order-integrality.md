# LN-005: Prime-Order Integrality

Status: TODO  
Owner:  
Last updated: 2026-03-04

## Depends
LN-001, LN-002, LN-003, LN-004.

## Files
- `LutzNagell/LutzNagellTheorem/PrimeOrder.lean`

## Goal
If `P ≠ 0` is a torsion point of *prime* order on the short curve over `ℚ`, prove `x(P), y(P) ∈ ℤ`.

## Deliverables
1. A lemma:
   - assumptions: `p : ℕ` prime, `P` on the short curve over `ℚ`, `P ≠ 0`, and `p • P = 0`.
   - conclusion: affine coords of `P` are integers (use `IsInteger ℤ` or `∃ z : ℤ, x = (z:ℚ)`).
2. Use:
   - `WeierstrassCurve.zsmul_eq_smulEval` (project) to extract `ψ_p(x,y)=0` (in Jacobian coords).
   - LN-003 bridge to get `preΨ p` has root `x`.
   - `den_dvd_of_is_root` (mathlib RationalRoot) on `preΨ p` with `leadingCoeff = p` (from LN-002).
   - LN-004 denominator-square lemma to force `den(x)=1`.
   - Then get `y ∈ ℤ` from `y^2 = x^3 + A*x + B`.

## Acceptance
- No `sorry`.
- `lake build` succeeds.
- Used as a black box by the general torsion ticket.

## Notes / Pitfalls
- Separate odd prime `p` from `p=2` early; the “preΨ” reduction uses oddness.
- Be careful: `p • P = 0` in the *group* of points; extracting `ψ_p(x,y)=0` uses the `Z`-coordinate
  of the Jacobian representation.

