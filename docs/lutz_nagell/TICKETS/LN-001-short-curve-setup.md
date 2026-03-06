# LN-001: Short Curve Setup (Short Weierstrass)

Status: DONE  
Owner:  
Last updated: 2026-03-04

## Depends
None.

## Files
- `LutzNagell/LutzNagellTheorem/ShortWeierstrass.lean`

## Goal
Define the short Weierstrass curve `y^2 = x^3 + A*x + B` over `ℤ` and its base-change to `ℚ`,
and prove basic simp/rewriting lemmas needed everywhere else.

## Deliverables
1. `def shortCurveZ (A B : ℤ) : WeierstrassCurve ℤ`
   - should set `a₁=a₂=a₃=0`, `a₄=A`, `a₆=B`.
2. `def shortCurveQ (A B : ℤ) : WeierstrassCurve ℚ`
   - preferably as `(shortCurveZ A B).map (algebraMap ℤ ℚ)` or `baseChange`.
3. A rewriting lemma for the affine equation:
   - `W.toAffine.Equation x y ↔ y^2 = x^3 + (A:ℚ)*x + (B:ℚ)`
   - be careful about the exact `Equation` definition in mathlib (`evalEval ... polynomial = 0`).
4. A discriminant lemma:
   - `(shortCurveZ A B).Δ = -16*(4*A^3 + 27*B^2)`
   - prove by `simp [WeierstrassCurve.Δ, WeierstrassCurve.b₂, ...]` then `ring`.

## Acceptance
- No `sorry`.
- `lake build` succeeds.
- Downstream files can use the simp lemmas without rewriting by hand.

## Implementation Notes
Implemented in:
- `LutzNagell/LutzNagellTheorem/ShortWeierstrass.lean`

## Notes / Pitfalls
- Keep the `ℤ` vs `ℚ` coercions explicit where needed; add helper lemmas with `(A : ℚ)` if it
  materially reduces friction.
- Do not assume `Δ ≠ 0` in this ticket; just define `Δ` and compute it.
