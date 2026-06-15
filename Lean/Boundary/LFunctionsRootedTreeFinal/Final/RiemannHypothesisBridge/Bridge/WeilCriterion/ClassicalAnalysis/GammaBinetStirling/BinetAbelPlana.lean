import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaOwner

/-!
# Abel-Plana owner layer for Binet's second formula

This file owns the classical Abel-Plana input behind Binet's second
logarithmic formula for `Gamma`.  Abel-Plana constructs the analytic Binet
logarithm branch on the right half-plane.  Principal-log statements are
separate comparison theorems and must not be used as the owner output.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Abel-Plana constructs the analytic Euler/Binet logarithm branch of Gamma:
exponentiating the branch recovers `Gamma` on the open right half-plane.

Classically this is Binet's second logarithmic formula in its branch-correct
form, obtained from the Bohr-Mollerup/log-Gamma product by Abel-Plana
summation and the standard contour deformation of the logarithmic summand; see
Whittaker-Watson, *A Course of Modern Analysis*, Ch. XII, and DLMF §5.11.3. -/
theorem Complex.exp_binetLogGammaBranch_eq_Gamma_from_AbelPlana :
    ∀ w : ℂ,
      0 < w.re →
        Complex.exp (Complex.binetLogGammaBranch w) =
          Complex.Gamma w := by
  intro w hw
  exact
    Complex.exp_binetLogGammaBranch_eq_Gamma_from_AbelPlanaOwner
      w hw

/-- The contour-deformed tail comparison produced by the same Abel-Plana
deformation as Binet's second formula.

This theorem is deliberately integral-level: near the principal arctangent
branch point the pointwise principal-branch comparison is the wrong object,
while the deformed contour integral is bounded by the branch-safe majorant. -/
theorem Complex.binetSecondFormula_principalTailKernel_branchSingularity_absorbed_by_AbelPlanaContour :
    Complex.BinetSecondFormulaPrincipalTailKernelIntegralComparison
      Complex.binetSecondFormulaContourTailMajorantKernel 2 := by
  exact
    Complex.binetSecondFormula_principalTailKernel_branchSingularity_absorbed_by_AbelPlanaContourOwner

end

end LFunctions
end Boundary
