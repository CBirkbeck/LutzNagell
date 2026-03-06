import LutzNagell.LutzNagellTheorem.ShortWeierstrass
import LutzNagell.LutzNagellTheorem.GeneralMain
import LutzNagell.LutzNagellTheorem.GeneralDiscriminant

/-!
# The Lutz–Nagell Theorem

## Statement (Theorem 1.1 of "Nagell-Lutz, quickly")

Let `A, B ∈ ℤ` with `Δ_{A,B} := -16·(4A³ + 27B²) ≠ 0`.
Let `E` be the elliptic curve over `ℚ` given by `y² = x³ + Ax + B`.
If `(x, y)` is a nonidentity rational point of finite order on `E`, then:

1. `x, y ∈ ℤ`, and
2. either `y = 0` or `y² ∣ Δ_{A,B}`.

## References

* E. Lutz, *Sur l'équation y² = x³ − Ax − B dans les corps p-adiques*, 1937.
* T. Nagell, *Solution de quelques problèmes dans la théorie arithmétique des cubiques planes
  du premier genre*, 1935.
-/

namespace LutzNagell
namespace LutzNagellTheorem

open WeierstrassCurve

/-! ## The Lutz–Nagell theorem -/

/-- **Lutz–Nagell theorem, part 1: integrality of torsion points.**

If `(x, y)` is a nonzero torsion point on the short Weierstrass curve
`y² = x³ + Ax + B` over `ℚ` with nonzero discriminant, then `x` and `y` are integers. -/
theorem lutz_nagell_integrality (A B : ℤ) (hΔ : (shortCurveZ A B).Δ ≠ 0)
    {x y : ℚ} (hpt : (shortCurveQ A B).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some hpt)) :
    (∃ x₀ : ℤ, (x₀ : ℚ) = x) ∧ ∃ y₀ : ℤ, (y₀ : ℚ) = y :=
  lutz_nagell_integrality_short A B hpt htor

/-- **Lutz–Nagell theorem, part 2: discriminant divisibility.**

If `(x₀, y₀) ∈ ℤ²` is a nonzero torsion point on `y² = x³ + Ax + B` over `ℚ`,
then either `y₀ = 0` or `y₀² ∣ Δ_{A,B}`.

Derived from the general discriminant divisibility theorem by specializing
`κ₀ = 2y₀` (since `a₁ = a₃ = 0`) and observing `4y₀² | 4Δ → y₀² | Δ`. -/
theorem lutz_nagell_discriminant (A B : ℤ) (hΔ : (shortCurveZ A B).Δ ≠ 0)
    {x y : ℚ} (hpt : (shortCurveQ A B).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some hpt))
    {x₀ y₀ : ℤ} (hx : (x₀ : ℚ) = x) (hy : (y₀ : ℚ) = y) :
    y₀ = 0 ∨ y₀ ^ 2 ∣ (shortCurveZ A B).Δ := by
  -- Apply the general discriminant theorem to shortCurveZ
  rcases lutz_nagell_discriminant_general (shortCurveZ A B) hpt htor hx hy with hκ | hdvd
  · -- κ₀ = 2y₀ + 0·x₀ + 0 = 0 implies y₀ = 0
    simp only [shortCurveZ_a₁, shortCurveZ_a₃, zero_mul, add_zero] at hκ
    exact Or.inl (by omega)
  · -- κ₀² | 4Δ, i.e. (2y₀)² | 4Δ, i.e. 4y₀² | 4Δ, i.e. y₀² | Δ
    right
    simp only [shortCurveZ_a₁, shortCurveZ_a₃, zero_mul, add_zero] at hdvd
    -- hdvd : (2 * y₀) ^ 2 ∣ 4 * (shortCurveZ A B).Δ
    have h_eq : (2 * y₀) ^ 2 = 4 * y₀ ^ 2 := by ring
    rw [h_eq] at hdvd
    exact (mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0)).mp hdvd

/-- **The Lutz–Nagell theorem** (Theorem 1.1 of "Nagell-Lutz, quickly").

Let `A, B ∈ ℤ` with `Δ_{A,B} = -16·(4A³ + 27B²) ≠ 0`. Let `E : y² = x³ + Ax + B`.
If `(x, y)` is a nonidentity rational point of finite order on `E`, then there exist
`x₀, y₀ ∈ ℤ` with `x = x₀` and `y = y₀`, and either `y₀ = 0` or `y₀² ∣ Δ_{A,B}`. -/
theorem lutz_nagell (A B : ℤ) (hΔ : (shortCurveZ A B).Δ ≠ 0)
    {x y : ℚ} (hpt : (shortCurveQ A B).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some hpt)) :
    ∃ (x₀ y₀ : ℤ), (x₀ : ℚ) = x ∧ (y₀ : ℚ) = y ∧
      (y₀ = 0 ∨ y₀ ^ 2 ∣ (shortCurveZ A B).Δ) := by
  obtain ⟨⟨x₀, hx⟩, ⟨y₀, hy⟩⟩ := lutz_nagell_integrality A B hΔ hpt htor
  exact ⟨x₀, y₀, hx, hy, lutz_nagell_discriminant A B hΔ hpt htor hx hy⟩

end LutzNagellTheorem
end LutzNagell
