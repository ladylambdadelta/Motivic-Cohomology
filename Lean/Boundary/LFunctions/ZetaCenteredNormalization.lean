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
  simp [zetaCriticalCenter]

theorem zetaCriticalCenter_one_sub (s : ℂ) :
    zetaCriticalCenter (1 - s) = - zetaCriticalCenter s := by
  change ((1 : ℂ) + -s) + -(1 / 2) = -(s + -(1 / 2))
  rw [neg_add, neg_neg]
  rw [add_comm (1 : ℂ) (-s)]
  rw [add_assoc]
  rw [show (1 : ℂ) + -(1 / 2) = (1 / 2 : ℂ) by
    rw [← sub_eq_add_neg, sub_half]]

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
  rw [zetaPrimePacketCenter, Real.log_pow]

theorem zetaPrimePacketCenter_succ {p : ℝ} (n : ℕ) :
    zetaPrimePacketCenter p (n + 1) =
      zetaPrimePacketCenter p n + Real.log p := by
  change ((↑n + 1) * Real.log p = ↑n * Real.log p + Real.log p)
  rw [add_mul, one_mul]

theorem zetaPrimePacketCenter_zero (p : ℝ) :
    zetaPrimePacketCenter p 0 = 0 := by
  simp [zetaPrimePacketCenter]

end
end LFunctions
end Boundary
