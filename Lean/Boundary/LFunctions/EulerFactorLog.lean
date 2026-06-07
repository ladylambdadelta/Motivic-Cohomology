import Boundary.LFunctions.K0TraceLog
import Boundary.LFunctions.TraceExpansion

/-!
# Euler and zeta logarithms on K₀ endomorphism classes

This file fixes the sign convention at the virtual-endomorphism level.

For a class `[V,F]`, `eulerLog` is the logarithm of the determinant Euler
factor `det(1 - T F)`, so it is `tracePowerLog`.

The reciprocal local zeta factor has the opposite logarithm, `zetaLog`.
-/

open scoped PowerSeries

universe u v

namespace Boundary
namespace EulerFactorLog

noncomputable section

variable (K : Type u) [Field K]

/-- Logarithm of the determinant Euler factor attached to a virtual
endomorphism class. -/
def eulerLog (x : Boundary.EndomorphismK0.K0.{u, v} K) : K⟦X⟧ :=
  Boundary.K0TraceLog.tracePowerLog K x

/-- Logarithm of the reciprocal local zeta factor attached to a virtual
endomorphism class. -/
def zetaLog (x : Boundary.EndomorphismK0.K0.{u, v} K) : K⟦X⟧ :=
  -eulerLog K x

@[simp]
theorem eulerLog_zero :
    eulerLog K (0 : Boundary.EndomorphismK0.K0.{u, v} K) = 0 := by
  simp [eulerLog]

theorem eulerLog_add
    (x y : Boundary.EndomorphismK0.K0.{u, v} K) :
    eulerLog K (x + y) = eulerLog K x + eulerLog K y := by
  exact Boundary.K0TraceLog.tracePowerLog_add K x y

@[simp]
theorem eulerLog_neg
    (x : Boundary.EndomorphismK0.K0.{u, v} K) :
    eulerLog K (-x) = -eulerLog K x := by
  exact Boundary.K0TraceLog.tracePowerLog_neg K x

theorem eulerLog_sub
    (x y : Boundary.EndomorphismK0.K0.{u, v} K) :
    eulerLog K (x - y) = eulerLog K x - eulerLog K y := by
  exact Boundary.K0TraceLog.tracePowerLog_sub K x y

@[simp]
theorem coeff_eulerLog_zero (x : Boundary.EndomorphismK0.K0.{u, v} K) :
    PowerSeries.coeff K 0 (eulerLog K x) = 0 := by
  simp [eulerLog]

theorem coeff_eulerLog
    (x : Boundary.EndomorphismK0.K0.{u, v} K) (n : ℕ) (hn : n ≠ 0) :
    PowerSeries.coeff K n (eulerLog K x) =
      -Boundary.EndomorphismK0.traceCharacterK0 K 1
          (Boundary.EndomorphismK0.powerMapK0 K n x) / (n : K) := by
  exact Boundary.K0TraceLog.coeff_tracePowerLog K x n hn

theorem coeff_eulerLog_eq_traceCharacterK0
    (x : Boundary.EndomorphismK0.K0.{u, v} K) (n : ℕ) (hn : n ≠ 0) :
    PowerSeries.coeff K n (eulerLog K x) =
      -Boundary.EndomorphismK0.traceCharacterK0 K n x / (n : K) := by
  exact Boundary.K0TraceLog.coeff_tracePowerLog_eq_traceCharacterK0 K x n hn

@[simp]
theorem zetaLog_zero :
    zetaLog K (0 : Boundary.EndomorphismK0.K0.{u, v} K) = 0 := by
  simp [zetaLog]

theorem zetaLog_add
    (x y : Boundary.EndomorphismK0.K0.{u, v} K) :
    zetaLog K (x + y) = zetaLog K x + zetaLog K y := by
  rw [zetaLog, eulerLog_add]
  rw [zetaLog, zetaLog]
  exact neg_add (eulerLog K x) (eulerLog K y)

@[simp]
theorem zetaLog_neg
    (x : Boundary.EndomorphismK0.K0.{u, v} K) :
    zetaLog K (-x) = -zetaLog K x := by
  simp [zetaLog]

theorem zetaLog_sub
    (x y : Boundary.EndomorphismK0.K0.{u, v} K) :
    zetaLog K (x - y) = zetaLog K x - zetaLog K y := by
  rw [sub_eq_add_neg, zetaLog_add, zetaLog_neg]
  simp [sub_eq_add_neg]

@[simp]
theorem coeff_zetaLog_zero (x : Boundary.EndomorphismK0.K0.{u, v} K) :
    PowerSeries.coeff K 0 (zetaLog K x) = 0 := by
  rw [zetaLog, map_neg]
  simp [eulerLog]

theorem coeff_zetaLog
    (x : Boundary.EndomorphismK0.K0.{u, v} K) (n : ℕ) (hn : n ≠ 0) :
    PowerSeries.coeff K n (zetaLog K x) =
      Boundary.EndomorphismK0.traceCharacterK0 K 1
          (Boundary.EndomorphismK0.powerMapK0 K n x) / (n : K) := by
  rw [zetaLog]
  rw [map_neg]
  rw [coeff_eulerLog (K := K) x n hn]
  rw [neg_div]
  rw [neg_neg]

theorem coeff_zetaLog_eq_traceCharacterK0
    (x : Boundary.EndomorphismK0.K0.{u, v} K) (n : ℕ) (hn : n ≠ 0) :
    PowerSeries.coeff K n (zetaLog K x) =
      Boundary.EndomorphismK0.traceCharacterK0 K n x / (n : K) := by
  rw [coeff_zetaLog (K := K) x n hn]
  rw [Boundary.EndomorphismK0.traceCharacterK0_one_powerMapK0]

/-- On a finite-dimensional endomorphism object, the abstract K₀ Euler log
agrees with the formal logarithm of the concrete Euler polynomial
`det(1 - T F)`. -/
theorem eulerLog_of_endomorphismObject
    [CharZero K] (A : Boundary.EndomorphismK0.EndomorphismObject.{u, v} K) :
    eulerLog K (Boundary.EndomorphismK0.mk K
      (Boundary.EndomorphismK0.of K A)) =
      Boundary.TraceExpansion.formalLog
        (Boundary.LinearEulerFactor.eulerPolynomial A.endomorphism : K⟦X⟧) := by
  apply PowerSeries.ext
  intro n
  by_cases hn : n = 0
  · subst n
    simp [eulerLog]
  · rw [coeff_eulerLog_eq_traceCharacterK0 (K := K)
      (Boundary.EndomorphismK0.mk K (Boundary.EndomorphismK0.of K A)) n hn]
    rw [Boundary.EndomorphismK0.traceCharacterK0_of]
    rw [Boundary.TraceExpansion.coeff_formalLog_eulerPolynomial_eq_neg_trace_pow
      (K := K) (F := A.endomorphism) (m := n) (hm := hn)]
    rfl

/-- The reciprocal zeta logarithm of a finite-dimensional endomorphism object is
the negative formal logarithm of the concrete Euler polynomial. -/
theorem zetaLog_of_endomorphismObject
    [CharZero K] (A : Boundary.EndomorphismK0.EndomorphismObject.{u, v} K) :
    zetaLog K (Boundary.EndomorphismK0.mk K
      (Boundary.EndomorphismK0.of K A)) =
      -Boundary.TraceExpansion.formalLog
        (Boundary.LinearEulerFactor.eulerPolynomial A.endomorphism : K⟦X⟧) := by
  rw [zetaLog]
  rw [eulerLog_of_endomorphismObject]

end

end EulerFactorLog
end Boundary
