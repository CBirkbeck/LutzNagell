# LN-006: Integral Multiple Implies Integral Point (PDF Lemma 3.2)

Status: TODO  
Owner:  
Last updated: 2026-03-04

## Depends
LN-001, LN-002, LN-003.

## Files
- `LutzNagell/LutzNagellTheorem/IntegralMultiple.lean`

## Goal
If `n • P` is integral (affine coordinates in `ℤ`), show `P` is integral.

## Deliverables
1. Set up the coordinate formula:
   - `x(n•P) = Φ_n(x(P)) / ΨSq_n(x(P))` in `ℚ`
   - derive from the project’s `zsmul_eq_smulEval` plus LN-003 bridges.
2. Prove a denominator-cancellation lemma using degrees/monicity:
   - `Φ_n` is monic, degree `n^2`
   - `ΨSq_n` has degree `n^2 - 1`
   - if `Φ(x)/ΨSq(x)` is integral, then `x` must be integral.
3. Conclude `y` integral from the curve equation.

## Acceptance
- No `sorry`.
- `lake build` succeeds.
- The lemma is used by LN-007.

## Notes / Pitfalls
- Don’t try to do the full cancellation argument in one lemma; split it:
  - general “monic over ℤ, denominator is d>1 gives contradiction” lemma
  - specialize to `Φ`/`ΨSq`.
- Watch out for `n=0` and `n=±1` edge cases; keep a clean `n ≠ 0` / `0 < n` assumption.

