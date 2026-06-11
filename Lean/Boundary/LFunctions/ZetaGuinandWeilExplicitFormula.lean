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

/-- The completed explicit formula for convolution-autocorrelation probes, as the remaining
analytic target. -/
def zeta_completed_explicit_formula_convolutionAutocorrelation
    (f : ZetaAdmissibleFunction) :
    Prop :=
  Boundary.LFunctions.ZetaAdmissibleFunction
    .zeta_completed_explicit_formula_convolutionAutocorrelation f

/-- Historical public name for the convolution-autocorrelation explicit-formula target. -/
abbrev zeta_completed_explicit_formula_autocorrelation
    (f : ZetaAdmissibleFunction) : Prop :=
  zeta_completed_explicit_formula_convolutionAutocorrelation f

/-- The Guinand-Weil target unfolds to the zero-side/Hermitian-boundary identity. -/
theorem zeta_completed_explicit_formula_convolutionAutocorrelation_iff
    (f : ZetaAdmissibleFunction) :
    zeta_completed_explicit_formula_convolutionAutocorrelation f ↔
      zetaCompletedZeroKreinGram (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f := by
  rfl

/-- Historical unfold theorem for the convolution-autocorrelation explicit-formula target. -/
theorem zeta_completed_explicit_formula_autocorrelation_iff
    (f : ZetaAdmissibleFunction) :
    zeta_completed_explicit_formula_autocorrelation f ↔
      zetaCompletedZeroKreinGram (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f := by
  exact zeta_completed_explicit_formula_convolutionAutocorrelation_iff f

end
end LFunctions
end Boundary
