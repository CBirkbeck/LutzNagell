# LN-007: General Torsion Integrality (First Claim)

Status: TODO  
Owner:  
Last updated: 2026-03-04

## Depends
LN-005, LN-006.

## Files
- `LutzNagell/LutzNagellTheorem/Main.lean` (or split out a `Torsion.lean` if needed)

## Goal
For a nonzero torsion point `P` on the short curve over `ℚ`, prove `x(P), y(P) ∈ ℤ`.

## Deliverables
1. Let `m = addOrderOf P`. Choose prime `p ∣ m`.
2. Define `Q = (m/p) • P`. Prove:
   - `Q ≠ 0`
   - `p • Q = 0`
3. Apply LN-005 to get `Q` integral.
4. Apply LN-006 (“integral-multiple-backwards”) to deduce `P` integral.

## Acceptance
- No `sorry`.
- `lake build` succeeds.
- Exported lemma usable by LN-008.

## Notes / Pitfalls
- Keep group-theory lemmas small and reusable (`addOrderOf` facts, prime divisor extraction).
- Avoid re-proving generic group facts; check `Mathlib/GroupTheory/OrderOfElement` etc.

