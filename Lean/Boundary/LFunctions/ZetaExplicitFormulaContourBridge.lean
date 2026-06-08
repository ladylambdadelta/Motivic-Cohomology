import Boundary.LFunctions.ZetaExplicitFormulaBoundaryTransport
import Boundary.LFunctions.ZetaExplicitFormulaAnalyticCore
import Boundary.LFunctions.ZetaExplicitFormulaNormalizationBridge

/-!
# Boundary explicit-formula contour bridge

This file is the owner-level wrapper for the completed contour-shift theorem
in the current repository normalization. The analytic content is carried by
the class-free transport theorem; this file keeps the exact final theorem
shape available in the contour namespace.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The completed explicit-formula contour bridge in the owner namespace. -/
theorem zetaCompletedExplicitFormulaContourBridge
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram f =
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaBoundarySum f := by
  exact zeta_completed_explicit_formula_autocorrelation_classFree f

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
