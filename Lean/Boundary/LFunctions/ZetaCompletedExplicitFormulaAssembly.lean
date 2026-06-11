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

/-- The completed explicit formula for convolution-autocorrelation probes, assembled from the
class-free owner theorems. This is the remaining analytic target, not a proved
boundary/packet normalization theorem. -/
def zeta_completed_explicit_formula_convolutionAutocorrelation
    (f : ZetaAdmissibleFunction) :
    Prop :=
  zetaCompletedZeroKreinGram (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
    ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f

/-- Historical public name for the convolution-autocorrelation explicit-formula target. -/
abbrev zeta_completed_explicit_formula_autocorrelation
    (f : ZetaAdmissibleFunction) : Prop :=
  zeta_completed_explicit_formula_convolutionAutocorrelation f

/-- The analytic package exposes the completed explicit-formula convolution-autocorrelation
target. -/
theorem ExplicitFormulaAnalyticPackage.zetaCompletedExplicitFormula_convolutionAutocorrelation_target
    {f : ZetaAdmissibleFunction} (_h : ExplicitFormulaAnalyticPackage f) :
    ZetaAdmissibleFunction.zeta_completed_explicit_formula_convolutionAutocorrelation f ↔
      zetaCompletedZeroKreinGram (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f := by
  rfl

/-- Historical package name for the convolution-autocorrelation explicit-formula target. -/
theorem ExplicitFormulaAnalyticPackage.zetaCompletedExplicitFormula_autocorrelation_target
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) :
    ZetaAdmissibleFunction.zeta_completed_explicit_formula_autocorrelation f ↔
      zetaCompletedZeroKreinGram (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f := by
  exact ExplicitFormulaAnalyticPackage
    .zetaCompletedExplicitFormula_convolutionAutocorrelation_target h

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
