import Boundary.LFunctions.EndomorphismK0
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# K₀ trace logarithms

This file packages the logarithmic trace expansion as a formal power series
attached directly to a virtual finite-dimensional endomorphism class.

The coefficient of `X^n`, for `n > 0`, is the ordinary trace character applied
after the K₀ power operation `[V,F] ↦ [V,F^n]`, divided by `n`.  This keeps
Frobenius powers internal to the same virtual endomorphism class that controls
the determinant character.
-/

open scoped PowerSeries

universe u v

namespace Boundary
namespace K0TraceLog

noncomputable section

variable (K : Type u) [Field K]

/-- The formal logarithm determined by trace characters on a K₀ endomorphism
class.

For the current determinant convention `det(1 - T F)`, the sign is negative:
`log det(1 - T F) = -∑ Tr(F^n) T^n / n`. -/
def tracePowerLog (x : Boundary.EndomorphismK0.K0.{u, v} K) : K⟦X⟧ :=
  PowerSeries.mk fun n =>
    if n = 0 then 0
    else
      -Boundary.EndomorphismK0.traceCharacterK0 K 1
          (Boundary.EndomorphismK0.powerMapK0 K n x) / (n : K)

@[simp]
theorem coeff_tracePowerLog_zero (x : Boundary.EndomorphismK0.K0.{u, v} K) :
    PowerSeries.coeff K 0 (tracePowerLog K x) = 0 := by
  simp [tracePowerLog]

/-- Positive coefficients of the K₀ trace logarithm are trace characters of
the powered K₀ class. -/
theorem coeff_tracePowerLog
    (x : Boundary.EndomorphismK0.K0.{u, v} K) (n : ℕ) (hn : n ≠ 0) :
    PowerSeries.coeff K n (tracePowerLog K x) =
      -Boundary.EndomorphismK0.traceCharacterK0 K 1
          (Boundary.EndomorphismK0.powerMapK0 K n x) / (n : K) := by
  simp [tracePowerLog, hn]

/-- Equivalent positive-coefficient form using the `n`th trace character
directly. -/
theorem coeff_tracePowerLog_eq_traceCharacterK0
    (x : Boundary.EndomorphismK0.K0.{u, v} K) (n : ℕ) (hn : n ≠ 0) :
    PowerSeries.coeff K n (tracePowerLog K x) =
      -Boundary.EndomorphismK0.traceCharacterK0 K n x / (n : K) := by
  rw [coeff_tracePowerLog (K := K) x n hn]
  rw [Boundary.EndomorphismK0.traceCharacterK0_one_powerMapK0]

@[simp]
theorem tracePowerLog_zero :
    tracePowerLog K (0 : Boundary.EndomorphismK0.K0.{u, v} K) = 0 := by
  apply PowerSeries.ext
  intro n
  by_cases hn : n = 0
  · subst n
    simp
  · rw [coeff_tracePowerLog_eq_traceCharacterK0 (K := K) _ n hn]
    simp

/-- The K₀ trace logarithm is additive. -/
theorem tracePowerLog_add
    (x y : Boundary.EndomorphismK0.K0.{u, v} K) :
    tracePowerLog K (x + y) = tracePowerLog K x + tracePowerLog K y := by
  apply PowerSeries.ext
  intro n
  by_cases hn : n = 0
  · subst n
    simp [tracePowerLog]
  · simp [tracePowerLog, hn, map_add]
    rw [add_div]
    rw [add_comm]

@[simp]
theorem tracePowerLog_neg
    (x : Boundary.EndomorphismK0.K0.{u, v} K) :
    tracePowerLog K (-x) = -tracePowerLog K x := by
  apply PowerSeries.ext
  intro n
  by_cases hn : n = 0
  · subst n
    simp [tracePowerLog]
  · simp [tracePowerLog, hn]
    rw [neg_div]
    exact (neg_neg (Boundary.EndomorphismK0.traceCharacterK0 K 1
      (Boundary.EndomorphismK0.powerMapK0 K n x) / (n : K))).symm

theorem tracePowerLog_sub
    (x y : Boundary.EndomorphismK0.K0.{u, v} K) :
    tracePowerLog K (x - y) = tracePowerLog K x - tracePowerLog K y := by
  rw [sub_eq_add_neg, tracePowerLog_add, tracePowerLog_neg]
  simp [sub_eq_add_neg]

end

end K0TraceLog
end Boundary
