import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.Owner

/-!
# Archimedean Binet contour input surface

This file exposes the Binet/Abel-Plana contour inputs already constructed in
the `Final` analytic lane.  These inputs are one archimedean face of the trace
calculus; no new special-function proof is introduced here.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace AnalyticMotives

/-- The owner-proved Binet branch/tail absorption input. -/
theorem binetBranchUniformTailAbsorption :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption :=
  Complex.binetSecondFormulaBranchUniformTailAbsorption_owner

/-- The owner-proved endpoint-restored finite-height contour input. -/
theorem binetEndpointRestoredFiniteHeightContourInputs :
    Complex.BinetSecondFormulaEndpointRestoredFiniteHeightContourInputs :=
  Complex.binetSecondFormula_endpointRestoredFiniteHeightContourInputs_owner

end AnalyticMotives

end
end LFunctions
end Boundary
