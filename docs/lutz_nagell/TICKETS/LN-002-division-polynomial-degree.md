# LN-002: Port Division Polynomial Degree Lemmas

Status: DONE  
Owner:  
Last updated: 2026-03-04

## Depends
None.

## Files
- `LutzNagell/DivisionPolynomialDegree.lean`

## Goal
Port/adapt mathlib’s degree/leading-coefficient results for division polynomials so they apply to
the project’s copy in `LutzNagell/DivisionPolynomial.lean` (to avoid importing
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` and getting name conflicts).

Template:
- `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`

## Deliverables
Minimum interface that downstream proofs should rely on:
1. `WeierstrassCurve.leadingCoeff_preΨ` (or a specialized lemma)
   - in particular, for odd `n` (or `n` prime), leading coeff is `n`.
2. `WeierstrassCurve.leadingCoeff_Φ` and `WeierstrassCurve.natDegree_Φ`.
3. `WeierstrassCurve.leadingCoeff_ΨSq` and `WeierstrassCurve.natDegree_ΨSq`.

## Acceptance
- No `sorry`.
- `lake build` succeeds.
- The file imports `LutzNagell.DivisionPolynomial` (project copy), not mathlib’s Basic file.

## Implementation Notes
Implemented in:
- `LutzNagell/DivisionPolynomialDegree.lean`

## Notes / Pitfalls
- Keep the lemma names identical to mathlib when possible; it makes later porting easier.
- If you need extra tactic imports, prefer mirroring the mathlib file (`Mathlib.Tactic.ComputeDegree`).
