import Boundary.LFunctionsRootedTreeCanonicalAll._outside_RH_rooted_import_cone.CohomologicalEulerFactor.EndomorphismK0.EndomorphismK0
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

abbrev K0Class :=
  Boundary.EndomorphismK0.K0.{u, v} K

def tracePowerLogCoeff (x : K0Class.{u, v} K) (n : ℕ) : K :=
  if n = 0 then 0
  else
    -Boundary.EndomorphismK0.traceCharacterK0 K 1
        (Boundary.EndomorphismK0.powerMapK0 K n x) / (n : K)

/-- The formal logarithm determined by trace characters on a K₀ endomorphism
class.

For the current determinant convention `det(1 - T F)`, the sign is negative:
`log det(1 - T F) = -∑ Tr(F^n) T^n / n`. -/
def tracePowerLog (x : K0Class.{u, v} K) : K⟦X⟧ :=
  PowerSeries.mk (tracePowerLogCoeff K x)

theorem coeff_tracePowerLog_eq_coeff (x : K0Class.{u, v} K) (n : ℕ) :
    PowerSeries.coeff K n (tracePowerLog K x) = tracePowerLogCoeff K x n := by
  exact PowerSeries.coeff_mk n (tracePowerLogCoeff K x)

theorem tracePowerLogCoeff_zero_index (x : K0Class.{u, v} K) :
    tracePowerLogCoeff K x 0 = 0 := by
  exact if_pos rfl

theorem tracePowerLogCoeff_pos
    (x : K0Class.{u, v} K) (n : ℕ) (hn : n ≠ 0) :
    tracePowerLogCoeff K x n =
      -Boundary.EndomorphismK0.traceCharacterK0 K 1
          (Boundary.EndomorphismK0.powerMapK0 K n x) / (n : K) := by
  exact if_neg hn

@[simp]
theorem coeff_tracePowerLog_zero (x : K0Class.{u, v} K) :
    PowerSeries.coeff K 0 (tracePowerLog K x) = 0 := by
  exact Eq.trans
    (coeff_tracePowerLog_eq_coeff (K := K) x 0)
    (tracePowerLogCoeff_zero_index (K := K) x)

/-- Positive coefficients of the K₀ trace logarithm are trace characters of
the powered K₀ class. -/
theorem coeff_tracePowerLog
    (x : K0Class.{u, v} K) (n : ℕ) (hn : n ≠ 0) :
    PowerSeries.coeff K n (tracePowerLog K x) =
      -Boundary.EndomorphismK0.traceCharacterK0 K 1
          (Boundary.EndomorphismK0.powerMapK0 K n x) / (n : K) := by
  exact Eq.trans
    (coeff_tracePowerLog_eq_coeff (K := K) x n)
    (tracePowerLogCoeff_pos (K := K) x n hn)

/-- Equivalent positive-coefficient form using the `n`th trace character
directly. -/
theorem coeff_tracePowerLog_eq_traceCharacterK0
    (x : K0Class.{u, v} K) (n : ℕ) (hn : n ≠ 0) :
    PowerSeries.coeff K n (tracePowerLog K x) =
      -Boundary.EndomorphismK0.traceCharacterK0 K n x / (n : K) := by
  exact Eq.trans
    (coeff_tracePowerLog (K := K) x n hn)
    (congrArg (fun t : K => -t / (n : K))
      (Boundary.EndomorphismK0.traceCharacterK0_one_powerMapK0 (K := K) n x))

theorem neg_add_div (a b c : K) :
    -(a + b) / c = -a / c + -b / c := by
  exact Eq.trans (congrArg (fun t : K => t / c) (neg_add a b))
    (add_div (-a) (-b) c)

theorem neg_neg_div_eq_neg_div_neg (a c : K) :
    - -a / c = -(-a / c) := by
  exact neg_div c (-a)

theorem coeff_zero_powerSeries (n : ℕ) :
    PowerSeries.coeff K n (0 : K⟦X⟧) = 0 := by
  rfl

theorem coeff_add_powerSeries (f g : K⟦X⟧) (n : ℕ) :
    PowerSeries.coeff K n (f + g) =
      PowerSeries.coeff K n f + PowerSeries.coeff K n g := by
  rfl

theorem coeff_neg_powerSeries (f : K⟦X⟧) (n : ℕ) :
    PowerSeries.coeff K n (-f) = -PowerSeries.coeff K n f := by
  rfl

theorem coeff_sub_powerSeries (f g : K⟦X⟧) (n : ℕ) :
    PowerSeries.coeff K n (f - g) =
      PowerSeries.coeff K n f - PowerSeries.coeff K n g := by
  rfl

theorem coeff_tracePowerLog_zero_at_index (n : ℕ) :
    PowerSeries.coeff K n (tracePowerLog K (0 : K0Class.{u, v} K)) = 0 := by
  if hn : n = 0 then
    exact Eq.trans (congrArg (fun m => PowerSeries.coeff K m
      (tracePowerLog K (0 : K0Class.{u, v} K))) hn)
      (coeff_tracePowerLog_zero (K := K) (0 : K0Class.{u, v} K))
  else
    exact Eq.trans
      (coeff_tracePowerLog_eq_traceCharacterK0 (K := K)
        (0 : K0Class.{u, v} K) n hn)
      (Eq.trans
        (congrArg (fun t : K => -t / (n : K))
          (map_zero (Boundary.EndomorphismK0.traceCharacterK0 K n)))
        (Eq.trans (congrArg (fun t : K => t / (n : K)) neg_zero) (zero_div (n : K))))

theorem coeff_tracePowerLog_add_at_zero
    (x y : K0Class.{u, v} K) :
    PowerSeries.coeff K 0 (tracePowerLog K (x + y)) =
      PowerSeries.coeff K 0 (tracePowerLog K x + tracePowerLog K y) := by
  exact Eq.trans (coeff_tracePowerLog_zero (K := K) (x + y))
    (Eq.symm
      (Eq.trans
        (coeff_add_powerSeries K (tracePowerLog K x) (tracePowerLog K y) 0)
        (Eq.trans
          (congrArg₂ HAdd.hAdd
            (coeff_tracePowerLog_zero (K := K) x)
            (coeff_tracePowerLog_zero (K := K) y))
          (zero_add 0))))

theorem coeff_tracePowerLog_add_at_pos
    (x y : K0Class.{u, v} K) (n : ℕ) (hn : n ≠ 0) :
    PowerSeries.coeff K n (tracePowerLog K (x + y)) =
      PowerSeries.coeff K n (tracePowerLog K x + tracePowerLog K y) := by
  exact Eq.trans
    (coeff_tracePowerLog (K := K) (x + y) n hn)
    (Eq.trans
      (congrArg (fun t : K => -t / (n : K))
        (Eq.trans
          (congrArg (Boundary.EndomorphismK0.traceCharacterK0 K 1)
            (map_add (Boundary.EndomorphismK0.powerMapK0 K n) x y))
          (map_add (Boundary.EndomorphismK0.traceCharacterK0 K 1)
            (Boundary.EndomorphismK0.powerMapK0 K n x)
            (Boundary.EndomorphismK0.powerMapK0 K n y))))
      (Eq.trans
        (neg_add_div (K := K)
          (Boundary.EndomorphismK0.traceCharacterK0 K 1
            (Boundary.EndomorphismK0.powerMapK0 K n x))
          (Boundary.EndomorphismK0.traceCharacterK0 K 1
            (Boundary.EndomorphismK0.powerMapK0 K n y))
          (n : K))
        (Eq.symm
          (Eq.trans
            (coeff_add_powerSeries K (tracePowerLog K x) (tracePowerLog K y) n)
            (congrArg₂ HAdd.hAdd
              (coeff_tracePowerLog (K := K) x n hn)
              (coeff_tracePowerLog (K := K) y n hn))))))

theorem coeff_tracePowerLog_add_at_index
    (x y : K0Class.{u, v} K) (n : ℕ) :
    PowerSeries.coeff K n (tracePowerLog K (x + y)) =
      PowerSeries.coeff K n (tracePowerLog K x + tracePowerLog K y) := by
  if hn : n = 0 then
    exact Eq.trans
      (congrArg (fun m => PowerSeries.coeff K m (tracePowerLog K (x + y))) hn)
      (Eq.trans
        (coeff_tracePowerLog_add_at_zero (K := K) x y)
        (congrArg (fun m => PowerSeries.coeff K m
          (tracePowerLog K x + tracePowerLog K y)) hn.symm))
  else
    exact coeff_tracePowerLog_add_at_pos (K := K) x y n hn

theorem coeff_tracePowerLog_neg_at_zero
    (x : K0Class.{u, v} K) :
    PowerSeries.coeff K 0 (tracePowerLog K (-x)) =
      PowerSeries.coeff K 0 (-tracePowerLog K x) := by
  exact Eq.trans (coeff_tracePowerLog_zero (K := K) (-x))
    (Eq.symm
      (Eq.trans
        (coeff_neg_powerSeries K (tracePowerLog K x) 0)
        (Eq.trans
          (congrArg Neg.neg (coeff_tracePowerLog_zero (K := K) x))
          neg_zero)))

theorem coeff_tracePowerLog_neg_at_pos
    (x : K0Class.{u, v} K) (n : ℕ) (hn : n ≠ 0) :
    PowerSeries.coeff K n (tracePowerLog K (-x)) =
      PowerSeries.coeff K n (-tracePowerLog K x) := by
  exact Eq.trans
    (coeff_tracePowerLog (K := K) (-x) n hn)
    (Eq.trans
      (congrArg (fun t : K => -t / (n : K))
        (Eq.trans
          (congrArg (Boundary.EndomorphismK0.traceCharacterK0 K 1)
            (map_neg (Boundary.EndomorphismK0.powerMapK0 K n) x))
          (map_neg (Boundary.EndomorphismK0.traceCharacterK0 K 1)
            (Boundary.EndomorphismK0.powerMapK0 K n x))))
      (Eq.trans
        (neg_neg_div_eq_neg_div_neg (K := K)
          (Boundary.EndomorphismK0.traceCharacterK0 K 1
            (Boundary.EndomorphismK0.powerMapK0 K n x))
          (n : K))
        (Eq.symm
          (Eq.trans
            (coeff_neg_powerSeries K (tracePowerLog K x) n)
            (congrArg Neg.neg (coeff_tracePowerLog (K := K) x n hn))))))

theorem coeff_tracePowerLog_neg_at_index
    (x : K0Class.{u, v} K) (n : ℕ) :
    PowerSeries.coeff K n (tracePowerLog K (-x)) =
      PowerSeries.coeff K n (-tracePowerLog K x) := by
  if hn : n = 0 then
    exact Eq.trans
      (congrArg (fun m => PowerSeries.coeff K m (tracePowerLog K (-x))) hn)
      (Eq.trans
        (coeff_tracePowerLog_neg_at_zero (K := K) x)
        (congrArg (fun m => PowerSeries.coeff K m (-tracePowerLog K x)) hn.symm))
  else
    exact coeff_tracePowerLog_neg_at_pos (K := K) x n hn

theorem coeff_tracePowerLog_sub_at_index
    (x y : K0Class.{u, v} K) (n : ℕ) :
    PowerSeries.coeff K n (tracePowerLog K (x - y)) =
      PowerSeries.coeff K n (tracePowerLog K x - tracePowerLog K y) := by
  exact Eq.trans
    (congrArg (fun z => PowerSeries.coeff K n (tracePowerLog K z))
      (sub_eq_add_neg x y))
    (Eq.trans
      (coeff_tracePowerLog_add_at_index (K := K) x (-y) n)
      (Eq.trans
        (congrArg (PowerSeries.coeff K n)
          (congrArg (fun f : K⟦X⟧ => tracePowerLog K x + f)
            (PowerSeries.ext (fun m => coeff_tracePowerLog_neg_at_index (K := K) y m))))
        (congrArg (PowerSeries.coeff K n)
          (Eq.symm (sub_eq_add_neg (tracePowerLog K x) (tracePowerLog K y))))))

@[simp]
theorem tracePowerLog_zero :
    tracePowerLog K (0 : K0Class.{u, v} K) = 0 := by
  exact PowerSeries.ext (fun n =>
    Eq.trans (coeff_tracePowerLog_zero_at_index (K := K) n)
      (Eq.symm (coeff_zero_powerSeries K n)))

/-- The K₀ trace logarithm is additive. -/
theorem tracePowerLog_add
    (x y : K0Class.{u, v} K) :
    tracePowerLog K (x + y) = tracePowerLog K x + tracePowerLog K y := by
  exact PowerSeries.ext (fun n => coeff_tracePowerLog_add_at_index (K := K) x y n)

@[simp]
theorem tracePowerLog_neg
    (x : K0Class.{u, v} K) :
    tracePowerLog K (-x) = -tracePowerLog K x := by
  exact PowerSeries.ext (fun n => coeff_tracePowerLog_neg_at_index (K := K) x n)

theorem tracePowerLog_sub
    (x y : K0Class.{u, v} K) :
    tracePowerLog K (x - y) = tracePowerLog K x - tracePowerLog K y := by
  exact PowerSeries.ext (fun n => coeff_tracePowerLog_sub_at_index (K := K) x y n)

end

end K0TraceLog
end Boundary
