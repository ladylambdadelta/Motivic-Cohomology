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

theorem eulerLog_zero :
    eulerLog K (0 : Boundary.EndomorphismK0.K0.{u, v} K) = 0 :=
  Boundary.K0TraceLog.tracePowerLog_zero K

theorem eulerLog_add
    (x y : Boundary.EndomorphismK0.K0.{u, v} K) :
    eulerLog K (x + y) = eulerLog K x + eulerLog K y :=
  Boundary.K0TraceLog.tracePowerLog_add K x y

theorem eulerLog_neg
    (x : Boundary.EndomorphismK0.K0.{u, v} K) :
    eulerLog K (-x) = -eulerLog K x :=
  Boundary.K0TraceLog.tracePowerLog_neg K x

theorem eulerLog_sub
    (x y : Boundary.EndomorphismK0.K0.{u, v} K) :
    eulerLog K (x - y) = eulerLog K x - eulerLog K y :=
  Boundary.K0TraceLog.tracePowerLog_sub K x y

theorem coeff_eulerLog_zero (x : Boundary.EndomorphismK0.K0.{u, v} K) :
    PowerSeries.coeff K 0 (eulerLog K x) = 0 :=
  Boundary.K0TraceLog.coeff_tracePowerLog_zero K x

theorem coeff_eulerLog
    (x : Boundary.EndomorphismK0.K0.{u, v} K) (n : ℕ) (hn : n ≠ 0) :
    PowerSeries.coeff K n (eulerLog K x) =
      -Boundary.EndomorphismK0.traceCharacterK0 K 1
          (Boundary.EndomorphismK0.powerMapK0 K n x) / (n : K) :=
  Boundary.K0TraceLog.coeff_tracePowerLog K x n hn

theorem coeff_eulerLog_eq_traceCharacterK0
    (x : Boundary.EndomorphismK0.K0.{u, v} K) (n : ℕ) (hn : n ≠ 0) :
    PowerSeries.coeff K n (eulerLog K x) =
      -Boundary.EndomorphismK0.traceCharacterK0 K n x / (n : K) :=
  Boundary.K0TraceLog.coeff_tracePowerLog_eq_traceCharacterK0 K x n hn

theorem zetaLog_zero :
    zetaLog K (0 : Boundary.EndomorphismK0.K0.{u, v} K) = 0 :=
  Eq.trans
    (congrArg Neg.neg (eulerLog_zero K))
    (neg_zero : -(0 : K⟦X⟧) = 0)

theorem zetaLog_add_neg_eulerLog
    (x y : Boundary.EndomorphismK0.K0.{u, v} K) :
    zetaLog K (x + y) = -(eulerLog K x + eulerLog K y) :=
  congrArg Neg.neg (eulerLog_add K x y)

theorem neg_eulerLog_add_eq_zetaLog_add
    (x y : Boundary.EndomorphismK0.K0.{u, v} K) :
    -(eulerLog K x + eulerLog K y) = zetaLog K x + zetaLog K y :=
  neg_add (eulerLog K x) (eulerLog K y)

theorem zetaLog_add
    (x y : Boundary.EndomorphismK0.K0.{u, v} K) :
    zetaLog K (x + y) = zetaLog K x + zetaLog K y :=
  Eq.trans
    (zetaLog_add_neg_eulerLog K x y)
    (neg_eulerLog_add_eq_zetaLog_add K x y)

theorem zetaLog_neg
    (x : Boundary.EndomorphismK0.K0.{u, v} K) :
    zetaLog K (-x) = -zetaLog K x :=
  congrArg Neg.neg (eulerLog_neg K x)

theorem zetaLog_sub_eq_add_neg
    (x y : Boundary.EndomorphismK0.K0.{u, v} K) :
    zetaLog K (x - y) = zetaLog K (x + -y) :=
  congrArg (zetaLog K) (sub_eq_add_neg x y)

theorem zetaLog_add_neg_eq_add_zetaLog_neg
    (x y : Boundary.EndomorphismK0.K0.{u, v} K) :
    zetaLog K (x + -y) = zetaLog K x + zetaLog K (-y) :=
  zetaLog_add K x (-y)

theorem zetaLog_add_zetaLog_neg_eq_sub
    (x y : Boundary.EndomorphismK0.K0.{u, v} K) :
    zetaLog K x + zetaLog K (-y) = zetaLog K x - zetaLog K y :=
  Eq.trans
    (congrArg (fun t : K⟦X⟧ => zetaLog K x + t) (zetaLog_neg K y))
    (sub_eq_add_neg (zetaLog K x) (zetaLog K y)).symm

theorem neg_neg_div_eq_div (a b : K) :
    -((-a) / b) = a / b :=
  Eq.trans
    (congrArg Neg.neg (neg_div b a))
    (neg_neg (a / b))

theorem zetaLog_sub
    (x y : Boundary.EndomorphismK0.K0.{u, v} K) :
    zetaLog K (x - y) = zetaLog K x - zetaLog K y :=
  Eq.trans
    (zetaLog_sub_eq_add_neg K x y)
    (Eq.trans
      (zetaLog_add_neg_eq_add_zetaLog_neg K x y)
      (zetaLog_add_zetaLog_neg_eq_sub K x y))

theorem coeff_zetaLog_zero (x : Boundary.EndomorphismK0.K0.{u, v} K) :
    PowerSeries.coeff K 0 (zetaLog K x) = 0 :=
  Eq.trans
    (map_neg (PowerSeries.coeff K 0) (eulerLog K x))
    (Eq.trans
      (congrArg Neg.neg (coeff_eulerLog_zero K x))
      (neg_zero : -(0 : K) = 0))

theorem coeff_zetaLog_eq_neg_coeff_eulerLog
    (x : Boundary.EndomorphismK0.K0.{u, v} K) (n : ℕ) :
    PowerSeries.coeff K n (zetaLog K x) =
      -PowerSeries.coeff K n (eulerLog K x) :=
  map_neg (PowerSeries.coeff K n) (eulerLog K x)

theorem neg_coeff_eulerLog_eq_traceCharacterK0_power
    (x : Boundary.EndomorphismK0.K0.{u, v} K) (n : ℕ) (hn : n ≠ 0) :
    -PowerSeries.coeff K n (eulerLog K x) =
      Boundary.EndomorphismK0.traceCharacterK0 K 1
          (Boundary.EndomorphismK0.powerMapK0 K n x) / (n : K) :=
  Eq.trans
    (congrArg Neg.neg (coeff_eulerLog K x n hn))
    (neg_neg_div_eq_div K
      (Boundary.EndomorphismK0.traceCharacterK0 K 1
        (Boundary.EndomorphismK0.powerMapK0 K n x))
      (n : K))

theorem coeff_zetaLog
    (x : Boundary.EndomorphismK0.K0.{u, v} K) (n : ℕ) (hn : n ≠ 0) :
    PowerSeries.coeff K n (zetaLog K x) =
      Boundary.EndomorphismK0.traceCharacterK0 K 1
          (Boundary.EndomorphismK0.powerMapK0 K n x) / (n : K) :=
  Eq.trans
    (coeff_zetaLog_eq_neg_coeff_eulerLog K x n)
    (neg_coeff_eulerLog_eq_traceCharacterK0_power K x n hn)

theorem coeff_zetaLog_power_trace_eq_traceCharacterK0
    (x : Boundary.EndomorphismK0.K0.{u, v} K) (n : ℕ) (_hn : n ≠ 0) :
    Boundary.EndomorphismK0.traceCharacterK0 K 1
          (Boundary.EndomorphismK0.powerMapK0 K n x) / (n : K) =
      Boundary.EndomorphismK0.traceCharacterK0 K n x / (n : K) :=
  congrArg
    (fun t : K => t / (n : K))
    (Boundary.EndomorphismK0.traceCharacterK0_one_powerMapK0
      (K := K) (n := n) (x := x))

theorem coeff_zetaLog_eq_traceCharacterK0
    (x : Boundary.EndomorphismK0.K0.{u, v} K) (n : ℕ) (hn : n ≠ 0) :
    PowerSeries.coeff K n (zetaLog K x) =
      Boundary.EndomorphismK0.traceCharacterK0 K n x / (n : K) :=
  Eq.trans
    (coeff_zetaLog K x n hn)
    (coeff_zetaLog_power_trace_eq_traceCharacterK0 K x n hn)

theorem eulerLog_of_endomorphismObject_coeff_zero
    [CharZero K] (A : Boundary.EndomorphismK0.EndomorphismObject.{u, v} K) :
    PowerSeries.coeff K 0
        (eulerLog K (Boundary.EndomorphismK0.mk K
          (Boundary.EndomorphismK0.of K A))) =
      PowerSeries.coeff K 0
        (Boundary.TraceExpansion.formalLog
          (Boundary.LinearEulerFactor.eulerPolynomial A.endomorphism : K⟦X⟧)) :=
  Eq.trans
    (coeff_eulerLog_zero K
      (Boundary.EndomorphismK0.mk K (Boundary.EndomorphismK0.of K A)))
    (Boundary.TraceExpansion.coeff_formalLog_zero
      (K := K)
      (f := (Boundary.LinearEulerFactor.eulerPolynomial A.endomorphism : K⟦X⟧))).symm

theorem eulerLog_of_endomorphismObject_coeff_nonzero
    [CharZero K] (A : Boundary.EndomorphismK0.EndomorphismObject.{u, v} K)
    (n : ℕ) (hn : n ≠ 0) :
    PowerSeries.coeff K n
        (eulerLog K (Boundary.EndomorphismK0.mk K
          (Boundary.EndomorphismK0.of K A))) =
      PowerSeries.coeff K n
        (Boundary.TraceExpansion.formalLog
          (Boundary.LinearEulerFactor.eulerPolynomial A.endomorphism : K⟦X⟧)) :=
  Eq.trans
    (coeff_eulerLog_eq_traceCharacterK0 K
      (Boundary.EndomorphismK0.mk K (Boundary.EndomorphismK0.of K A)) n hn)
    (Eq.trans
      (congrArg
        (fun t : K => -t / (n : K))
        (Boundary.EndomorphismK0.traceCharacterK0_of
          (K := K) (A := A) (n := n)))
      (Boundary.TraceExpansion.coeff_formalLog_eulerPolynomial_eq_neg_trace_pow
        (K := K) (F := A.endomorphism) (m := n) (hm := hn)).symm)

theorem eulerLog_of_endomorphismObject_coeff
    [CharZero K] (A : Boundary.EndomorphismK0.EndomorphismObject.{u, v} K)
    (n : ℕ) :
    PowerSeries.coeff K n
        (eulerLog K (Boundary.EndomorphismK0.mk K
          (Boundary.EndomorphismK0.of K A))) =
      PowerSeries.coeff K n
        (Boundary.TraceExpansion.formalLog
          (Boundary.LinearEulerFactor.eulerPolynomial A.endomorphism : K⟦X⟧)) :=
  match Decidable.em (n = 0) with
  | Or.inl hn =>
      Eq.subst
        (motive := fun m : ℕ =>
          PowerSeries.coeff K m
              (eulerLog K (Boundary.EndomorphismK0.mk K
                (Boundary.EndomorphismK0.of K A))) =
            PowerSeries.coeff K m
              (Boundary.TraceExpansion.formalLog
                (Boundary.LinearEulerFactor.eulerPolynomial A.endomorphism : K⟦X⟧)))
        hn.symm
        (eulerLog_of_endomorphismObject_coeff_zero K A)
  | Or.inr hn =>
      eulerLog_of_endomorphismObject_coeff_nonzero K A n hn

/-- On a finite-dimensional endomorphism object, the abstract K₀ Euler log
agrees with the formal logarithm of the concrete Euler polynomial
`det(1 - T F)`. -/
theorem eulerLog_of_endomorphismObject
    [CharZero K] (A : Boundary.EndomorphismK0.EndomorphismObject.{u, v} K) :
    eulerLog K (Boundary.EndomorphismK0.mk K
      (Boundary.EndomorphismK0.of K A)) =
      Boundary.TraceExpansion.formalLog
        (Boundary.LinearEulerFactor.eulerPolynomial A.endomorphism : K⟦X⟧) :=
  PowerSeries.ext (eulerLog_of_endomorphismObject_coeff K A)

/-- The reciprocal zeta logarithm of a finite-dimensional endomorphism object is
the negative formal logarithm of the concrete Euler polynomial. -/
theorem zetaLog_of_endomorphismObject
    [CharZero K] (A : Boundary.EndomorphismK0.EndomorphismObject.{u, v} K) :
    zetaLog K (Boundary.EndomorphismK0.mk K
      (Boundary.EndomorphismK0.of K A)) =
      -Boundary.TraceExpansion.formalLog
        (Boundary.LinearEulerFactor.eulerPolynomial A.endomorphism : K⟦X⟧) :=
  congrArg Neg.neg (eulerLog_of_endomorphismObject K A)

end

end EulerFactorLog
end Boundary
