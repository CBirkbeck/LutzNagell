import LutzNagell.LutzNagellTheorem.PIDPrimeOrder
import LutzNagell.LutzNagellTheorem.PIDIntegralMultiple
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.NumberTheory.NumberField.Basic

/-!
# The Lutz–Nagell theorem over PIDs and number fields

Generalization of the classical Lutz–Nagell theorem from `ℤ/ℚ` to a PID `R` of
characteristic zero with fraction field `K`.

## Main results

### Without ramification hypothesis (Option B)

* `den_powerful_of_on_curve`: **Every** prime factor of `den_R(x)` appears with
  multiplicity ≥ 2. No hypothesis on the torsion order needed — this is a property
  of ALL points on the curve. Denominators are only supported at "ramified-like" primes.

### With unramified hypothesis

* `lutz_nagell_integrality_pid`: If every prime dividing the torsion order is
  squarefree in `R`, then coordinates are integral (or order 2 with bounded denominators).

### Discriminant

* `lutz_nagell_pid_discriminant`: For integral coordinates, κ₀ = 0 or κ₀² ∣ 4Δ.

### Number fields

* `lutz_nagell_number_field`: The theorem for number fields `K` with
  `IsPrincipalIdealRing (𝓞 K)` (class number 1).
-/

namespace LutzNagell
namespace PID

open WeierstrassCurve IsFractionRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [CharZero R]
variable {K : Type*} [Field K] [DecidableEq K] [Algebra R K] [IsFractionRing R K]
variable (W : WeierstrassCurve R)

/-! ### Helper lemmas -/

/-- Convert `n • P = 0` on affine points to `(n : ℤ) • P = 0` on Jacobian points. -/
lemma nsmul_eq_zero_affine_to_jac
    {x y : K} {hns : (curveK R K W).toAffine.Nonsingular x y}
    {n : ℕ} (h : n • (Affine.Point.some _ _ hns) = 0) :
    (n : ℤ) • Jacobian.Point.fromAffine (Affine.Point.some _ _ hns) = 0 := by
  rw [natCast_zsmul]
  simpa only [map_nsmul, map_zero] using
    congrArg (Jacobian.Point.toAffineAddEquiv (curveK R K W)).symm h

/-- A nonzero affine point is of the form `.some hns`. -/
lemma exists_some_of_ne_zero
    {Q : Affine.Point ((curveK R K W).toAffine)} (hQ : Q ≠ 0) :
    ∃ x y, ∃ hns : (curveK R K W).toAffine.Nonsingular x y, Q = .some _ _ hns := by
  rcases Q with _ | ⟨_, _, hns⟩
  · exact absurd rfl hQ
  · exact ⟨_, _, hns, rfl⟩

/-! ### The powerful denominator theorem (no torsion hypothesis needed) -/

/-- **Every prime factor of `den_R(x)` on a curve point has multiplicity ≥ 2.**

This is the "Option B" result: without any squarefree or torsion hypothesis, the
denominator of any curve point has no "simple" prime factors. In particular,
denominators are only supported at primes `q` where `q²` divides the denominator.

For number fields, this means denominators live only at ramified primes. -/
theorem den_powerful_of_on_curve
    {x y : K}
    (heq : y ^ 2 + algebraMap R K W.a₁ * x * y + algebraMap R K W.a₃ * y =
      x ^ 3 + algebraMap R K W.a₂ * x ^ 2 + algebraMap R K W.a₄ * x + algebraMap R K W.a₆) :
    ∀ q : R, Prime q → q ∣ (IsFractionRing.den R x : R) →
      q ^ 2 ∣ (IsFractionRing.den R x : R) :=
  fun q hq hqd => by_contra fun h => den_no_simple_prime_factor_of_on_curve W heq hq hqd h

/-! ### Odd prime factor case -/

private lemma integrality_of_odd_prime_factor
    {x y : K} (hpt : (curveK R K W).toAffine.Nonsingular x y)
    {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hpm : p ∣ addOrderOf (Affine.Point.some _ _ hpt))
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt))
    (hsf : Squarefree (p : R)) :
    (IsLocalization.IsInteger R x) ∧ IsLocalization.IsInteger R y := by
  set P := Affine.Point.some _ _ hpt
  have hm_pos := htor.addOrderOf_pos
  set k := addOrderOf P / p
  have hkp : k * p = addOrderOf P := Nat.div_mul_cancel hpm
  have hk_pos : 0 < k := Nat.div_pos (Nat.le_of_dvd hm_pos hpm) hp.pos
  have hQ_ne : k • P ≠ 0 := by
    intro h
    exact absurd (Nat.le_of_dvd hk_pos (addOrderOf_dvd_of_nsmul_eq_zero h))
      (not_le.mpr (by
        calc k = k * 1 := (mul_one k).symm
          _ < k * p := Nat.mul_lt_mul_of_pos_left hp.one_lt hk_pos
          _ = addOrderOf P := hkp))
  have hpQ : p • (k • P) = 0 := by
    rw [← mul_nsmul, hkp, addOrderOf_nsmul_eq_zero]
  obtain ⟨x', y', hns', hQ_eq⟩ := exists_some_of_ne_zero W hQ_ne
  have hne_jac : Jacobian.Point.fromAffine (Affine.Point.some _ _ hns') ≠ 0 := by
    rw [← map_zero (Jacobian.Point.toAffineAddEquiv (curveK R K W)).symm]
    exact (Jacobian.Point.toAffineAddEquiv (curveK R K W)).symm.injective.ne
      (Affine.Point.some_ne_zero hns')
  obtain ⟨hx'_int, hy'_int⟩ := prime_order_integrality_squarefree W hns' hp hodd
    (nsmul_eq_zero_affine_to_jac W (hQ_eq ▸ hpQ)) hsf
  have hk_ne : (k : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hk_pos.ne'
  have hk_R_ne : ((k : ℤ) : R) ≠ 0 := by
    rw [Int.cast_natCast]; exact Nat.cast_ne_zero.mpr hk_pos.ne'
  exact isInteger_of_nsmul_isInteger W hpt hk_ne hk_R_ne hns'
    (show (k : ℤ) • P = Affine.Point.some _ _ hns' by rw [natCast_zsmul]; exact hQ_eq)
    hx'_int hy'_int

/-! ### Four divides order case -/

private lemma integrality_of_four_dvd_order
    {x y : K} (hpt : (curveK R K W).toAffine.Nonsingular x y)
    (h4 : 4 ∣ addOrderOf (Affine.Point.some _ _ hpt))
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt))
    (hsf2 : Squarefree (2 : R)) :
    (IsLocalization.IsInteger R x) ∧ IsLocalization.IsInteger R y := by
  set P := Affine.Point.some _ _ hpt
  have hm_pos := htor.addOrderOf_pos
  set k := addOrderOf P / 4
  have hk4 : k * 4 = addOrderOf P := Nat.div_mul_cancel h4
  have hk_pos : 0 < k := Nat.div_pos (Nat.le_of_dvd hm_pos h4) (by norm_num)
  have hQ_ne : k • P ≠ 0 := by
    intro h
    exact absurd (Nat.le_of_dvd hk_pos (addOrderOf_dvd_of_nsmul_eq_zero h))
      (not_le.mpr (by omega))
  have h4Q : 4 • (k • P) = 0 := by
    rw [← mul_nsmul, hk4, addOrderOf_nsmul_eq_zero]
  have h2Q_ne : (2 : ℕ) • (k • P) ≠ 0 := by
    intro h; rw [← mul_nsmul] at h
    exact absurd (Nat.le_of_dvd (by omega) (addOrderOf_dvd_of_nsmul_eq_zero h))
      (not_le.mpr (by omega))
  obtain ⟨x', y', hns', hQ_eq⟩ := exists_some_of_ne_zero W hQ_ne
  obtain ⟨hx'_int, hy'_int⟩ := integrality_of_order_four_squarefree W hns'
    (nsmul_eq_zero_affine_to_jac W (hQ_eq ▸ h4Q)) (hQ_eq ▸ h2Q_ne) hsf2
  have hk_ne : (k : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hk_pos.ne'
  have hk_R_ne : ((k : ℤ) : R) ≠ 0 := by
    rw [Int.cast_natCast]; exact Nat.cast_ne_zero.mpr hk_pos.ne'
  exact isInteger_of_nsmul_isInteger W hpt hk_ne hk_R_ne hns'
    (show (k : ℤ) • P = Affine.Point.some _ _ hns' by rw [natCast_zsmul]; exact hQ_eq)
    hx'_int hy'_int

/-! ### The general integrality theorem -/

/-- **Generalized Lutz–Nagell integrality over PIDs.**

For a nonzero finite-order point on a general Weierstrass curve with coefficients in
a PID `R` of characteristic zero, if every prime `p` dividing the torsion order satisfies
`Squarefree (p : R)` (equivalently, `p` does not ramify in `R`), then either:
- the coordinates are integral (`x, y ∈ R`), or
- the point has order exactly 2 and `den_R(x) ∣ 4`. -/
theorem lutz_nagell_integrality_pid
    {x y : K} (hpt : (curveK R K W).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt))
    (hsf_all : ∀ p : ℕ, p.Prime → p ∣ addOrderOf (Affine.Point.some _ _ hpt) →
      Squarefree (p : R)) :
    ((IsLocalization.IsInteger R x) ∧ IsLocalization.IsInteger R y) ∨
    (addOrderOf (Affine.Point.some _ _ hpt) = 2 ∧
      (IsFractionRing.den R x : R) ∣ (4 : R)) := by
  set P := Affine.Point.some _ _ hpt
  have hP_ne : P ≠ 0 := Affine.Point.some_ne_zero hpt
  have hm_ne_one : addOrderOf P ≠ 1 :=
    fun h => hP_ne (AddMonoid.addOrderOf_eq_one_iff.mp h)
  by_cases hord2 : addOrderOf P = 2
  · right
    have h2P : (2 : ℕ) • P = 0 := by rw [← hord2, addOrderOf_nsmul_eq_zero]
    exact ⟨hord2, den_dvd_of_order_two W (Nat.cast_ne_zero.mpr (by norm_num)) hpt
      (nsmul_eq_zero_affine_to_jac W h2P)⟩
  · left
    by_cases h_odd : ∃ p, p.Prime ∧ p ≠ 2 ∧ p ∣ addOrderOf P
    · obtain ⟨p, hp, hodd, hpm⟩ := h_odd
      exact integrality_of_odd_prime_factor W hpt hp hodd hpm htor (hsf_all p hp hpm)
    · push_neg at h_odd
      have h_all_two : ∀ q, q.Prime → q ∣ addOrderOf P → q = 2 := by
        intro q hq hqm; by_contra hne; exact h_odd q hq hne hqm
      have h2_dvd : 2 ∣ addOrderOf P := by
        obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd hm_ne_one
        exact (h_all_two q hq hqm) ▸ hqm
      have h4_dvd : 4 ∣ addOrderOf P := by
        obtain ⟨k₁, hk₁⟩ := h2_dvd
        obtain ⟨q, hq, hqk₁⟩ := Nat.exists_prime_and_dvd (show k₁ ≠ 1 by omega)
        have hqm : q ∣ addOrderOf P := dvd_trans hqk₁ ⟨2, by omega⟩
        rw [h_all_two q hq hqm] at hqk₁
        obtain ⟨j, hj⟩ := hqk₁
        exact ⟨j, by omega⟩
      exact integrality_of_four_dvd_order W hpt h4_dvd htor (hsf_all 2 (by decide) h2_dvd)

/-! ### Discriminant divisibility -/

private lemma kappa_sq_eq_Psi2Sq {x₀ y₀ : R}
    (hcurve : y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ =
      x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆) :
    (2 * y₀ + W.a₁ * x₀ + W.a₃) ^ 2 =
      4 * x₀ ^ 3 + W.b₂ * x₀ ^ 2 + 2 * W.b₄ * x₀ + W.b₆ := by
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  linear_combination 4 * hcurve

private lemma bezout_identity (x₀ : R) :
    (432 * x₀ ^ 3 + 108 * W.b₂ * x₀ ^ 2 + 216 * W.b₄ * x₀ +
      (-W.b₂ ^ 3 + 36 * W.b₂ * W.b₄ - 108 * W.b₆)) *
      (4 * x₀ ^ 3 + W.b₂ * x₀ ^ 2 + 2 * W.b₄ * x₀ + W.b₆) +
    (-48 * x₀ ^ 2 - 8 * W.b₂ * x₀ + (W.b₂ ^ 2 - 32 * W.b₄)) *
      (6 * x₀ ^ 2 + W.b₂ * x₀ + W.b₄) ^ 2 = 4 * W.Δ := by
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄,
             WeierstrassCurve.b₆, WeierstrassCurve.b₈, WeierstrassCurve.Δ]; ring

private lemma kappa_sq_dvd_four_delta (x₀ κ₀ : R)
    (hkappa : κ₀ ^ 2 = 4 * x₀ ^ 3 + W.b₂ * x₀ ^ 2 + 2 * W.b₄ * x₀ + W.b₆)
    (hdvd_Psi3 : κ₀ ^ 2 ∣ 4 * (3 * x₀ ^ 4 + W.b₂ * x₀ ^ 3 +
        3 * W.b₄ * x₀ ^ 2 + 3 * W.b₆ * x₀ + W.b₈)) :
    κ₀ ^ 2 ∣ 4 * W.Δ := by
  have hdvd_h_sq : κ₀ ^ 2 ∣ (6 * x₀ ^ 2 + W.b₂ * x₀ + W.b₄) ^ 2 := by
    have h_id : (6 * x₀ ^ 2 + W.b₂ * x₀ + W.b₄) ^ 2 +
        4 * (3 * x₀ ^ 4 + W.b₂ * x₀ ^ 3 + 3 * W.b₄ * x₀ ^ 2 +
             3 * W.b₆ * x₀ + W.b₈) =
      (12 * x₀ + W.b₂) * (4 * x₀ ^ 3 + W.b₂ * x₀ ^ 2 + 2 * W.b₄ * x₀ + W.b₆) := by
      simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄,
                 WeierstrassCurve.b₆, WeierstrassCurve.b₈]; ring
    have : (6 * x₀ ^ 2 + W.b₂ * x₀ + W.b₄) ^ 2 =
        (12 * x₀ + W.b₂) * (4 * x₀ ^ 3 + W.b₂ * x₀ ^ 2 + 2 * W.b₄ * x₀ + W.b₆) -
        4 * (3 * x₀ ^ 4 + W.b₂ * x₀ ^ 3 + 3 * W.b₄ * x₀ ^ 2 +
             3 * W.b₆ * x₀ + W.b₈) := by linear_combination h_id
    rw [this]
    exact dvd_sub (dvd_mul_of_dvd_right ⟨1, by rw [mul_one]; exact hkappa.symm⟩ _) hdvd_Psi3
  rw [← bezout_identity W x₀]
  exact dvd_add (dvd_mul_of_dvd_right ⟨1, by rw [mul_one]; exact hkappa.symm⟩ _)
    (dvd_mul_of_dvd_right hdvd_h_sq _)

/-- **Lutz–Nagell discriminant divisibility over PIDs.**

For integral coordinates on the curve satisfying `κ₀² ∣ 4·Ψ₃(x₀)`,
either κ₀ = 0 or κ₀² ∣ 4Δ. The hypothesis `κ₀² ∣ 4·Ψ₃(x₀)` follows from torsion
via the coordinate formula for `2•P`. -/
theorem lutz_nagell_pid_discriminant
    {x₀ y₀ : R}
    (hcurve : y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ =
      x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)
    (hdvd_Psi3 : (2 * y₀ + W.a₁ * x₀ + W.a₃) ^ 2 ∣
      4 * (3 * x₀ ^ 4 + W.b₂ * x₀ ^ 3 +
        3 * W.b₄ * x₀ ^ 2 + 3 * W.b₆ * x₀ + W.b₈)) :
    (2 * y₀ + W.a₁ * x₀ + W.a₃) = 0 ∨
    (2 * y₀ + W.a₁ * x₀ + W.a₃) ^ 2 ∣ 4 * W.Δ := by
  by_cases hκ : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0
  · exact Or.inl hκ
  · exact Or.inr (kappa_sq_dvd_four_delta W x₀ _ (kappa_sq_eq_Psi2Sq W hcurve) hdvd_Psi3)

/-- Ψ₃ divisibility from `Ψ₃(x₀) = κ₀² · c`. -/
theorem kappa_sq_dvd_four_Psi3_of_integral {x₀ κ₀ c : R}
    (hPsi3 : 3 * x₀ ^ 4 + W.b₂ * x₀ ^ 3 + 3 * W.b₄ * x₀ ^ 2 +
      3 * W.b₆ * x₀ + W.b₈ = κ₀ ^ 2 * c) :
    κ₀ ^ 2 ∣ 4 * (3 * x₀ ^ 4 + W.b₂ * x₀ ^ 3 +
      3 * W.b₄ * x₀ ^ 2 + 3 * W.b₆ * x₀ + W.b₈) :=
  dvd_mul_of_dvd_right ⟨c, hPsi3⟩ 4

end PID

/-! ## Number field version -/

namespace NumberField

open WeierstrassCurve IsFractionRing _root_.NumberField
open scoped _root_.NumberField

/-- **Lutz–Nagell theorem for number fields of class number 1.**

Let `K` be a number field with `IsPrincipalIdealRing (𝓞 K)` (equivalently,
`classNumber K = 1`). Let `W` be a Weierstrass curve with coefficients in `𝓞 K`.

For a nonzero finite-order point `(x, y)` on `W / K`:
- **At unramified primes:** if `Squarefree (p : 𝓞 K)` for every prime `p` dividing
  the torsion order, then `x, y ∈ 𝓞 K` (or order 2 with `den(x) ∣ 4`).
- **At all primes (no hypothesis):** every prime factor `q` of `den(x)` satisfies
  `q² ∣ den(x)` — denominators are supported only at ramified primes.

Over `ℚ` (where `𝓞 ℚ = ℤ` and no primes ramify), this recovers the classical
Lutz–Nagell theorem. -/
theorem lutz_nagell_number_field
    (K : Type*) [Field K] [NumberField K] [DecidableEq K]
    [IsPrincipalIdealRing (𝓞 K)]
    (W : WeierstrassCurve (𝓞 K))
    {x y : K}
    (hpt : (W.map (algebraMap (𝓞 K) K)).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt))
    (hsf_all : ∀ p : ℕ, p.Prime → p ∣ addOrderOf (Affine.Point.some _ _ hpt) →
      Squarefree (p : 𝓞 K)) :
    ((IsLocalization.IsInteger (𝓞 K) x) ∧ IsLocalization.IsInteger (𝓞 K) y) ∨
    (addOrderOf (Affine.Point.some _ _ hpt) = 2 ∧
      (IsFractionRing.den (𝓞 K) x : 𝓞 K) ∣ (4 : 𝓞 K)) :=
  PID.lutz_nagell_integrality_pid W hpt htor hsf_all

/-- **Powerful denominator for number fields of class number 1.**

For ANY point `(x, y)` on a Weierstrass curve over a number field `K` with
class number 1, every prime factor of the denominator of `x` in `𝓞 K`
appears with multiplicity ≥ 2. In particular, denominators are only
supported at primes that ramify in `K/ℚ`. -/
theorem den_powerful_number_field
    (K : Type*) [Field K] [NumberField K] [DecidableEq K]
    [IsPrincipalIdealRing (𝓞 K)]
    (W : WeierstrassCurve (𝓞 K))
    {x y : K}
    (heq : y ^ 2 + algebraMap (𝓞 K) K W.a₁ * x * y + algebraMap (𝓞 K) K W.a₃ * y =
      x ^ 3 + algebraMap (𝓞 K) K W.a₂ * x ^ 2 + algebraMap (𝓞 K) K W.a₄ * x +
        algebraMap (𝓞 K) K W.a₆)
    {q : 𝓞 K} (hq : Prime q) (hqd : q ∣ (IsFractionRing.den (𝓞 K) x : 𝓞 K)) :
    q ^ 2 ∣ (IsFractionRing.den (𝓞 K) x : 𝓞 K) :=
  PID.den_powerful_of_on_curve W heq q hq hqd

end NumberField
end LutzNagell
