import Boundary.LFunctions.ZetaGuinandWeilExplicitFormula
import Boundary.LFunctions.ZetaCompletedPacketComparison
import Boundary.LFunctions.ZetaExplicitFormulaBoundaryTransport

/-!
# Boundary completed explicit-formula assembly

This file owns the final class-free assembly theorem that combines the
upstream Guinand-Weil input, packet comparison, and explicit-formula boundary
transport layers.
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
  rw [zetaCompletedZeroKreinGram_eq_boundaryDefectGram]
  simpa [ZetaAdmissibleFunction.zetaCompletedBoundaryDefectKreinGram] using
    (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaBoundarySum_eq_boundaryDefectKreinGram
      (f := f)).symm

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
