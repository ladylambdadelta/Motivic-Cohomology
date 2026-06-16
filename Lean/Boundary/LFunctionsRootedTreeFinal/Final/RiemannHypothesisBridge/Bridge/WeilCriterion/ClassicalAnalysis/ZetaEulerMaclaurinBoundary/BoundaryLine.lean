import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.Basic

/-!
# Boundary-line coordinate facts

This file owns coordinate-level facts for the line `s = 1 + it`, separated
from the analytic Euler-Maclaurin input.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Real coordinate of the canonical point `1 + it` on the boundary line. -/
theorem Complex.boundaryLineOnePointRealParam_re
    (t : ℝ) :
    (Complex.boundaryLineOnePointRealParam t).re = 1 := by
  unfold Complex.boundaryLineOnePointRealParam
  calc
    ((1 : ℂ) + (t : ℂ) * Complex.I).re =
        (1 : ℝ) + (t * 0 - 0 * 1) := rfl
    _ = 1 + (0 - 0 * 1) := by
      exact congrArg
        (fun x : ℝ => 1 + (x - 0 * 1))
        (mul_zero t)
    _ = 1 + (0 - 0) := by
      exact congrArg
        (fun x : ℝ => 1 + (0 - x))
        (zero_mul 1)
    _ = 1 + 0 := by
      exact congrArg (fun x : ℝ => 1 + x) (sub_self 0)
    _ = 1 := add_zero 1

/-- Imaginary coordinate of the canonical point `1 + it` on the boundary line. -/
theorem Complex.boundaryLineOnePointRealParam_im
    (t : ℝ) :
    (Complex.boundaryLineOnePointRealParam t).im = t := by
  unfold Complex.boundaryLineOnePointRealParam
  calc
    ((1 : ℂ) + (t : ℂ) * Complex.I).im =
        (0 : ℝ) + (t * 1 + 0 * 0) := rfl
    _ = 0 + (t + 0 * 0) := by
      exact congrArg
        (fun x : ℝ => 0 + (x + 0 * 0))
        (mul_one t)
    _ = 0 + (t + 0) := by
      exact congrArg
        (fun x : ℝ => 0 + (t + x))
        (zero_mul 0)
    _ = 0 + t := by
      exact congrArg (fun x : ℝ => 0 + x) (add_zero t)
    _ = t := zero_add t

/-- The vertical height of the canonical point `1 + it` is the absolute value of `t`. -/
theorem Complex.boundaryLineOnePointRealParam_vertical_height
    (t : ℝ) :
    ‖(Complex.boundaryLineOnePointRealParam t).im‖ = ‖t‖ := by
  exact congrArg norm (Complex.boundaryLineOnePointRealParam_im t)

end

end LFunctions
end Boundary
