# Lutz-Nagell Workboard

Single source of truth for work status. Update this file as tickets move.

Status enum: `TODO | IN_PROGRESS | BLOCKED | REVIEW | DONE`

Columns:
`ID | Status | Owner | Depends | Files | Deliverable | Acceptance | Notes`

| ID | Status | Owner | Depends | Files | Deliverable | Acceptance | Notes |
|---|---|---|---|---|---|---|---|
| LN-001 | DONE |  |  | `LutzNagell/LutzNagellTheorem/ShortWeierstrass.lean` | Short curve setup + `Δ` formula + simp lemmas | `lake build`; no `sorry` | Implemented. |
| LN-002 | DONE |  |  | `LutzNagell/DivisionPolynomialDegree.lean` | Port degree/leading-coeff lemmas for `preΨ`, `ΨSq`, `Φ` | `lake build`; no `sorry` | Implemented (ported from mathlib, imports project `DivisionPolynomial`). |
| LN-003 | TODO |  | LN-001 | `LutzNagell/LutzNagellTheorem/EvalBridge.lean` | Bridge coordinate-ring congruences to `evalEval` equalities | `lake build`; no `sorry` | Use existing `Affine.CoordinateRing.mk_*` lemmas |
| LN-004 | TODO |  | LN-001 | `LutzNagell/LutzNagellTheorem/Denominators.lean` | Denominator square/cube lemma (PDF Lemma 3.3) | `lake build`; no `sorry` | Use `Nat.exists_eq_pow_of_exponent_coprime_of_pow_eq_pow` |
| LN-005 | TODO |  | LN-001, LN-002, LN-003, LN-004 | `LutzNagell/LutzNagellTheorem/PrimeOrder.lean` | Prime-order torsion integrality lemma | `lake build`; no `sorry` | Use `den_dvd_of_is_root` |
| LN-006 | TODO |  | LN-001, LN-002, LN-003 | `LutzNagell/LutzNagellTheorem/IntegralMultiple.lean` | Integral-multiple-backwards (PDF Lemma 3.2) | `lake build`; no `sorry` | Needs degree facts for denominator-cancellation argument |
| LN-007 | TODO |  | LN-005, LN-006 | `LutzNagell/LutzNagellTheorem/Main.lean` | General torsion integrality (`x,y ∈ ℤ`) | `lake build`; no `sorry` | Reduce to prime torsion via `addOrderOf` |
| LN-008 | TODO |  | LN-007, LN-001 | `LutzNagell/LutzNagellTheorem/Main.lean` | Discriminant divisibility (`y=0 ∨ y^2 ∣ Δ`) | `lake build`; no `sorry` | Use explicit `ring` identity + doubling |
| LN-009 | TODO |  | LN-001..LN-008 | `LutzNagell.lean` | Single import for the theorem (`import LutzNagell`) | `lake build`; no `sorry` | Keep the public API stable |
