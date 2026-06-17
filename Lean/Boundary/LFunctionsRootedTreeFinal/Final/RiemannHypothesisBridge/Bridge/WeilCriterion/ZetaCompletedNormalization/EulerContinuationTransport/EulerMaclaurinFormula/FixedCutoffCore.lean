import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.BernoulliCore

/-!
# Fixed-cutoff Euler-Maclaurin core definitions

This file owns the fixed-cutoff functions used by the punctured-strip
holomorphic continuation argument.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- Defect of the raw zeta Euler-Maclaurin tail identity.  The boundary-line
continuation theorem is stated as vanishing of this holomorphic defect. -/
noncomputable def eulerMaclaurin_riemannZeta_tailIdentityDefect
    (z : ℂ) : ℂ :=
  (riemannZeta z - eulerMaclaurinZetaFinitePart z) -
    (eulerMaclaurinZetaMainTerm z +
      eulerMaclaurinZetaEndpointTerm z +
      eulerMaclaurinZetaBernoulliIntegralRemainder z)

/-- Fixed-cutoff finite Dirichlet window.  This is the holomorphic object used
in the identity theorem; unlike the height-dependent owner cutoff, `N` is a
parameter and therefore does not introduce floor-jump discontinuities. -/
noncomputable def eulerMaclaurinZetaFinitePartWithCutoff
    (N : ℕ)
    (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, 1 / (((n : ℕ) : ℂ) ^ z)

/-- Fixed-cutoff integral main term for the raw zeta Euler-Maclaurin formula. -/
noncomputable def eulerMaclaurinZetaMainTermWithCutoff
    (N : ℕ)
    (z : ℂ) : ℂ :=
  (((N : ℕ) : ℂ) ^ ((1 : ℂ) - z)) / (z - 1)

/-- Fixed-cutoff endpoint term for the raw zeta Euler-Maclaurin formula. -/
noncomputable def eulerMaclaurinZetaEndpointTermWithCutoff
    (N : ℕ)
    (z : ℂ) : ℂ :=
  (-(1 / 2 : ℂ)) * (1 / (((N : ℕ) : ℂ) ^ z))

/-- Fixed-cutoff Bernoulli integral core. -/
noncomputable def eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff
    (N : ℕ)
    (z : ℂ) : ℂ :=
  ∫ x in Set.Ioi (((N : ℕ) : ℝ)),
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
      (((x : ℝ) : ℂ) ^ (-(z + 1)))

/-- Fixed-cutoff Bernoulli remainder for the raw zeta Euler-Maclaurin formula. -/
noncomputable def eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff
    (N : ℕ)
    (z : ℂ) : ℂ :=
  -z * eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff N z

/-- Fixed-cutoff Euler-Maclaurin tail defect.  This is the correct object for
holomorphic identity-theorem arguments. -/
noncomputable def eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect
    (N : ℕ)
    (z : ℂ) : ℂ :=
  (riemannZeta z - eulerMaclaurinZetaFinitePartWithCutoff N z) -
    (eulerMaclaurinZetaMainTermWithCutoff N z +
      eulerMaclaurinZetaEndpointTermWithCutoff N z +
      eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff N z)

end

end LFunctions
end Boundary
