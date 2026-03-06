# LN-009: Packaging + Imports

Status: TODO  
Owner:  
Last updated: 2026-03-04

## Depends
LN-001..LN-008.

## Files
- `LutzNagell.lean`

## Goal
Expose a single stable import for the final theorem.

## Deliverables
1. Update `LutzNagell.lean` so that:
   - `import LutzNagell` provides the final theorem and main supporting lemmas.
2. Keep the project building with `lake build`.

## Acceptance
- No `sorry`.
- `lake build` succeeds.
- Public API docstrings / module docs point to the final theorem location.

