# LN-003: Eval Bridge Lemmas (Coordinate-Ring Congruence → `evalEval`)

Status: TODO  
Owner:  
Last updated: 2026-03-04

## Depends
LN-001 (for short-curve simp lemmas).

## Files
- `LutzNagell/LutzNagellTheorem/EvalBridge.lean`

## Goal
Turn coordinate-ring equalities (e.g. `Affine.CoordinateRing.mk_ψ`) into concrete equalities after
evaluating at an on-curve point `(x,y)`.

This is the glue needed for “torsion implies `ψ_p(x,y)=0`” to become “`preΨ_p(x)=0`”.

## Deliverables
1. Define a reusable evaluation map at an on-curve point:
   - something like `coordRingEval : W.CoordinateRing →+* F` (for a field `F`)
   - built from `W.toAffine.Equation x y` via `AdjoinRoot.lift`.
2. Lemmas (shape, not necessarily names):
   - From `Affine.CoordinateRing.mk_ψ (n)` derive:
     `evalEval x y (W.ψ n) = evalEval x y (W.Ψ n)` (or a version with `mk`-evaluations).
   - From `Affine.CoordinateRing.mk_Ψ_sq (n)` derive:
     `evalEval x y (W.Ψ n)^2 = (W.ΨSq n).eval x` (after coercions).
   - From `Affine.CoordinateRing.mk_φ (n)` derive:
     `evalEval x y (W.φ n) = (W.Φ n).eval x`.
3. A “odd n” specialization:
   - for odd `n`, `evalEval x y (W.ψ n) = (W.preΨ n).eval x` (the `Y` vanishes).

## Acceptance
- No `sorry`.
- `lake build` succeeds.
- Downstream `PrimeOrder` can go from `p • P = 0` to `IsRoot (W.preΨ p) x`.

## Notes / Pitfalls
- Keep coercions straight: `ψ n : R[X][Y]`, `Ψ n : R[X]`, `preΨ n : R[X]`.
- The mk-lemmas live in `LutzNagell/DivisionPolynomial.lean`:
  - `Affine.CoordinateRing.mk_ψ`
  - `Affine.CoordinateRing.mk_φ`
  - `Affine.CoordinateRing.mk_Ψ_sq`

