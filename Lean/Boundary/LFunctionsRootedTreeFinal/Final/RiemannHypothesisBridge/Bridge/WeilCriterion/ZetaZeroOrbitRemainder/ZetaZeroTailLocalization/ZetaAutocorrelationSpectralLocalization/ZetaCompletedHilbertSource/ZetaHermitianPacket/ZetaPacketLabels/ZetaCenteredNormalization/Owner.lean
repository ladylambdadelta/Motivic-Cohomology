import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic

/-!
# Boundary zeta centered normalization

This file fixes the additive-line normalization used by the explicit-formula route:
critical-line centering, the `x = log t` coordinate, and the basic prime-power
centering identities.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Real Complex

/-- Center a complex parameter at the critical line. -/
def zetaCriticalCenter (s : ℂ) : ℂ := s - (1 / 2 : ℂ)

/-- The additive coordinate associated to a positive real variable. -/
def zetaAdditiveCoordinate (t : ℝ) : ℝ := Real.log t

/-- The multiplicative coordinate associated to an additive variable. -/
def zetaMultiplicativeCoordinate (x : ℝ) : ℝ := Real.exp x

/-- Prime-power packet centers on the additive line. -/
def zetaPrimePacketCenter (p n : ℝ) : ℝ := n * Real.log p

theorem zetaCriticalCenter_one_half : zetaCriticalCenter (1 / 2 : ℂ) = 0 := by
  change ((1 / 2 : ℂ) - (1 / 2 : ℂ)) = 0
  exact sub_self _

/-- The critical-line reflection sends the centered coordinate to its negative. -/
theorem complex_criticalCenter_reflection_sub_half
    (s : ℂ) :
    ((1 : ℂ) + -s) - (1 / 2 : ℂ) =
      - (s - (1 / 2 : ℂ)) := by
  have hone_sub_half :
      (1 : ℂ) - (1 / 2 : ℂ) = (1 / 2 : ℂ) :=
    eq_sub_iff_add_eq.mpr (add_halves (1 : ℂ)).symm
  have hone_add_neg_half :
      (1 : ℂ) + -(1 / 2 : ℂ) = (1 / 2 : ℂ) :=
    Eq.trans
      (sub_eq_add_neg (1 : ℂ) (1 / 2 : ℂ)).symm
      hone_sub_half
  have hneg_sub :
      - (s - (1 / 2 : ℂ)) = (1 / 2 : ℂ) + -s :=
    neg_sub s (1 / 2 : ℂ)
  calc
    ((1 : ℂ) + -s) - (1 / 2 : ℂ) =
        ((1 : ℂ) + -s) + -(1 / 2 : ℂ) :=
      sub_eq_add_neg ((1 : ℂ) + -s) (1 / 2 : ℂ)
    _ = (-s + (1 : ℂ)) + -(1 / 2 : ℂ) := by
      exact congrArg (fun x : ℂ => x + -(1 / 2 : ℂ))
        (add_comm (1 : ℂ) (-s))
    _ = -s + ((1 : ℂ) + -(1 / 2 : ℂ)) :=
      add_assoc (-s) (1 : ℂ) (-(1 / 2 : ℂ))
    _ = -s + (1 / 2 : ℂ) :=
      congrArg (fun x : ℂ => -s + x) hone_add_neg_half
    _ = (1 / 2 : ℂ) + -s :=
      add_comm (-s) (1 / 2 : ℂ)
    _ = - (s - (1 / 2 : ℂ)) :=
      hneg_sub.symm

theorem zetaCriticalCenter_one_sub (s : ℂ) :
    zetaCriticalCenter (1 - s) = - zetaCriticalCenter s := by
  change ((1 : ℂ) + -s) - (1 / 2 : ℂ) = - (s - (1 / 2 : ℂ))
  exact complex_criticalCenter_reflection_sub_half s

theorem zetaAdditiveCoordinate_exp (x : ℝ) :
    zetaAdditiveCoordinate (Real.exp x) = x := by
  change Real.log (Real.exp x) = x
  exact Real.log_exp x

theorem zetaMultiplicativeCoordinate_log {t : ℝ} (ht : 0 < t) :
    zetaMultiplicativeCoordinate (Real.log t) = t := by
  change Real.exp (Real.log t) = t
  exact Real.exp_log ht

theorem zetaAdditiveCoordinate_inv {t : ℝ} :
    zetaAdditiveCoordinate t⁻¹ = - zetaAdditiveCoordinate t := by
  change Real.log t⁻¹ = - Real.log t
  exact Real.log_inv t

theorem zetaAdditiveCoordinate_mul {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    zetaAdditiveCoordinate (x * y) =
      zetaAdditiveCoordinate x + zetaAdditiveCoordinate y := by
  change Real.log (x * y) = Real.log x + Real.log y
  exact Real.log_mul hx.ne' hy.ne'

theorem zetaPrimePacketCenter_pow {p : ℝ} (n : ℕ) :
    zetaPrimePacketCenter p n = Real.log (p ^ n) := by
  change (n : ℝ) * Real.log p = Real.log (p ^ n)
  exact (Real.log_pow p n).symm

/-- Successor packet centers add one logarithmic step. -/
theorem real_nat_succ_mul_log_eq_nat_mul_log_add_log
    (p : ℝ) (n : ℕ) :
    ((↑n + 1 : ℝ) * Real.log p) =
      ↑n * Real.log p + Real.log p := by
  calc
    ((↑n + 1 : ℝ) * Real.log p) =
        ↑n * Real.log p + 1 * Real.log p :=
      add_mul (↑n : ℝ) 1 (Real.log p)
    _ = ↑n * Real.log p + Real.log p :=
      congrArg (fun x : ℝ => ↑n * Real.log p + x)
        (one_mul (Real.log p))

theorem zetaPrimePacketCenter_succ {p : ℝ} (n : ℕ) :
    zetaPrimePacketCenter p (n + 1) =
      zetaPrimePacketCenter p n + Real.log p := by
  change ((↑n + 1) * Real.log p = ↑n * Real.log p + Real.log p)
  exact real_nat_succ_mul_log_eq_nat_mul_log_add_log p n

theorem zetaPrimePacketCenter_zero (p : ℝ) :
    zetaPrimePacketCenter p 0 = 0 := by
  change (0 : ℝ) * Real.log p = 0
  exact zero_mul _

end
end LFunctions
end Boundary
