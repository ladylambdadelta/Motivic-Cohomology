import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.P_OrientedMinusMovingLogScalar

/-!
# Finite-height lower-vertical decay owner

This file owns the final BinetKernel-facing finite-height lower-vertical decay
theorem after the oriented minus moving-log scalar estimate has been proved.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open Filter
open MeasureTheory

/-- Final owner theorem for finite-height lower-vertical Binet branch-wall
decay. -/
theorem Complex.binetSecondFormula_finiteHeightLowerVerticalDifference_decay_owner :
    Complex.BinetSecondFormulaFiniteHeightLowerVerticalDifferenceDecay := by
  exact
    Complex.binetSecondFormula_finiteHeightLowerVerticalDifference_decay_of_oriented_minus
      Complex.binetSecondFormula_orientedMinusMovingLog_scaled_decay_owner

end

end LFunctions
end Boundary
