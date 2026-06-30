import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.L3_TailAccountingAndCancellation

/-!
# Binet branch-uniform tail assembly

This file owns only the final assembly of the Binet branch-uniform tail package.
The analytic branch-wall estimate is owned upstream as finite-height lower
vertical cancellation, where the endpoint-returned contour terms cancel before
taking norms.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Final owner theorem for branch-uniform Binet second-formula tail absorption.

The proof is intentionally a thin wrapper over the finite-height lower-vertical
cancellation owner theorem.  The branch-wall logarithmic terms are not bounded
separately in this file. -/
theorem Complex.binetSecondFormulaBranchUniformTailAbsorption_owner :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption := by
  exact
    Complex.binetSecondFormula_branchUniformTailAbsorption_of_finiteHeightLowerVerticalDifference_decay
      Complex.binetSecondFormula_finiteHeightLowerVerticalDifference_decay_owner

end

end LFunctions
end Boundary
