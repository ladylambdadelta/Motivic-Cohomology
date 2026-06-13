import Boundary.LFunctions.ZetaExplicitFormulaComplexAnalysis

/-!
# Boundary explicit-formula vertical transport

This file owns the vertical-channel contour transport theorem used by the
final explicit-formula assembly.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The vertical side difference along a contour family. -/
noncomputable def explicitFormulaFamilyVerticalDifference
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
    zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T)

/-- Owner vertical-transport theorem: along an admissible contour family, the
vertical side difference converges to the analytic prime/archimedean/correction
boundary scalar. -/
theorem explicitFormulaFamilyVerticalDifference_tendsto_boundarySum_ownerVerticalTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) :
    Tendsto
      (fun T : ℝ => explicitFormulaFamilyVerticalDifference f F T)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)) := by
  sorry

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
