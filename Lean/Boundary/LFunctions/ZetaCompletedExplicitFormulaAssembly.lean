import Boundary.LFunctions.ZetaExplicitFormulaBoundaryTransport
import Boundary.LFunctions.ZetaExplicitFormulaComplexAnalysis

/-!
# Boundary completed explicit-formula assembly

This file owns the final class-free assembly theorem that combines the packet
comparison and explicit-formula boundary transport layers.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The completed explicit formula for autocorrelation probes, assembled from the
class-free owner theorems. -/
theorem zeta_completed_explicit_formula_autocorrelation
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram f =
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaBoundarySum f := by
  exact ZetaAdmissibleFunction.zetaCompletedZeroKreinGram_eq_explicitFormulaBoundarySum (f := f)

/-- The analytic package exposes the completed explicit-formula autocorrelation identity. -/
theorem ExplicitFormulaAnalyticPackage.zetaCompletedExplicitFormula_autocorrelation
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) :
    zetaCompletedZeroKreinGram f =
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaBoundarySum f := by
  exact ZetaAdmissibleFunction.zeta_completed_explicit_formula_autocorrelation f

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
