import LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.Basic

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
  simp [Complex.boundaryLineOnePointRealParam]

/-- Imaginary coordinate of the canonical point `1 + it` on the boundary line. -/
theorem Complex.boundaryLineOnePointRealParam_im
    (t : ℝ) :
    (Complex.boundaryLineOnePointRealParam t).im = t := by
  simp [Complex.boundaryLineOnePointRealParam]

/-- The vertical height of the canonical point `1 + it` is the absolute value of `t`. -/
theorem Complex.boundaryLineOnePointRealParam_vertical_height
    (t : ℝ) :
    ‖(Complex.boundaryLineOnePointRealParam t).im‖ = ‖t‖ := by
  exact congrArg norm (Complex.boundaryLineOnePointRealParam_im t)

end

end LFunctions
end Boundary
