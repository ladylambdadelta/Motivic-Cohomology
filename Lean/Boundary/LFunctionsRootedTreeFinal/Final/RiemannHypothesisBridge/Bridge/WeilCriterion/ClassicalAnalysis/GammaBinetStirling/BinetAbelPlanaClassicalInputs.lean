import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaFiniteAsymptotics

/-!
# Classical analytic inputs for the Abel-Plana proof of Binet's formula

This file owns the two non-algebraic convergence inputs in the Abel-Plana
derivation of Binet's second logarithmic formula:

* logarithmic Stirling convergence of the finite endpoint/main term;
* convergence to zero of the finite Abel-Plana contour remainder.

The assembly file `BinetAbelPlanaOwner.lean` should consume these theorems as
leaf-level classical inputs, not carry their proof roots inline.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Complex logarithmic Stirling endpoint asymptotic for the finite
Abel-Plana main term.

This is the branch-compatible Stirling theorem for the exact finite main term
appearing in the Euler-product Abel-Plana summation.  The endpoint remainder is
then just the difference between this finite main term and the limiting Binet
main term. -/
theorem Complex.binetAbelPlanaFiniteMainTerm_tendsto_binetMainTerm_owner
    {w : ℂ}
    (hw : 0 < w.re) :
    Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteMainTerm N w)
      atTop
      (𝓝 (Complex.binetLogGammaMainTerm w)) := by
  exact
    Complex.binetAbelPlanaFiniteMainTerm_tendsto_binetMainTerm_from_endpointStirling_owner
      hw

/-- The finite Abel-Plana contour remainder for the logarithmic summand tends
to zero.

This is the genuine finite-remainder estimate.  It should be proved from the
Abel-Plana remainder formula and decay of the logarithmic summand along the
finite contour, not by asserting eventual exactness of a truncated formula. -/
theorem Complex.binetAbelPlanaFiniteRemainderError_tendsto_zero_owner
    {w : ℂ}
    (hw : 0 < w.re) :
    Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteRemainderError N w)
      atTop
      (𝓝 (0 : ℂ)) := by
  exact
    Complex.binetAbelPlanaFiniteRemainderError_tendsto_zero_from_contourNorm_owner
      hw

end

end LFunctions
end Boundary
