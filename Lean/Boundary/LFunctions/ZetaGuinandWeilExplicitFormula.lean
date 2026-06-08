import Boundary.LFunctions.ZetaCompletedExplicitFormulaAssembly

/-!
# Boundary Guinand-Weil explicit formula input

This file now exposes the completed explicit-formula theorem directly.
The canonical owner theorem is assembled in
`ZetaCompletedExplicitFormulaAssembly.lean`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The completed explicit-formula boundary sum in signed form. -/
noncomputable def zetaCompletedExplicitFormulaBoundarySum
    (f : ZetaAdmissibleFunction) : ℝ :=
  zetaCompletedBoundaryDefectGram f

/-- The completed explicit formula for autocorrelation probes. -/
theorem zeta_completed_explicit_formula_autocorrelation
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram f =
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaBoundarySum f := by
  exact Boundary.LFunctions.ZetaAdmissibleFunction.zeta_completed_explicit_formula_autocorrelation f

end
end LFunctions
end Boundary
