import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointFiniteBesselParts.FiniteGNSCapture

/-!
# Endpoint vector realization

This file owns the finite positive-trace realization of the completed endpoint
vector.  The statement is finite and trace-theoretic: after the cutoff has
captured the endpoint reconstruction vector, the finite positive trace matrix
contains the endpoint vector with a nonnegative orthogonal complement.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Source eventual nonnegativity of the finite hidden endpoint kernel window.

This is the finite Schur-complement form of endpoint-vector realization. -/
theorem completedEndpointPhysicalHiddenKernelWindow_eventually_nonnegative_source
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f) :
    ∀ᶠ N in atTop,
      0 ≤ completedEndpointPhysicalHiddenKernelWindow N f :=
  completedEndpointPhysicalHiddenKernelWindow_eventually_nonnegative_of_finiteGNSCapture_source
    f D hnonPrime

/-- Source finite-window domination of the completed endpoint trace Gram. -/
theorem completedEndpointTraceFiber_gram_le_finitePositiveRenormalizedBoundaryWindow_eventually_source
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f) :
    ∀ᶠ N in atTop,
      (completedWeilEndpointTraceFiber f).gram ≤
        finitePositiveRenormalizedBoundaryWindow N f :=
  (completedEndpointPhysicalHiddenKernelWindow_eventually_nonnegative_source
    f D hnonPrime).mono
    (fun N hN =>
      let hwindow :
            0 ≤
              finitePositiveRenormalizedBoundaryWindow N f -
                (completedWeilEndpointTraceFiber f).gram :=
          Eq.subst
            (motive := fun value : ℝ => 0 ≤ value)
            (completedEndpointPhysicalHiddenKernelWindow_eq_renormalizedBoundaryWindow_sub_endpointFiberGram
              N f)
            hN
      sub_nonneg.mp hwindow)

/-- A finite-window endpoint Gram domination gives endpoint-vector realization
in the finite positive trace matrix. -/
theorem completedEndpointFinitePositiveTraceMatrixEndpointVectorRealization_of_windowDomination
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (hdomination :
      (completedWeilEndpointTraceFiber f).gram ≤
        finitePositiveRenormalizedBoundaryWindow N f) :
    CompletedEndpointFinitePositiveTraceMatrixEndpointVectorRealization
      N f :=
  let hendpoint :
      (completedEndpointFinitePositiveTraceMatrix N f).endpointCompressionScalar =
        (completedWeilEndpointTraceFiber f).gram :=
    completedEndpointFinitePositiveTraceMatrix_endpointCompressionScalar_eq
      N f
  let htraceMatrix :
      (completedEndpointFinitePositiveTraceMatrix N f).traceScalar =
        finitePositiveRenormalizedBoundaryWindow N f :=
    completedEndpointFinitePositiveTraceMatrix_traceScalar_eq N f
  let hmatrix :
      CompletedEndpointFinitePositiveTraceMatrixEndpointBesselDomination
        N f :=
    Eq.subst
      (motive := fun endpointValue : ℝ =>
        endpointValue ≤
          (completedEndpointFinitePositiveTraceMatrix N f).traceScalar)
      hendpoint.symm
      (Eq.subst
        (motive := fun traceValue : ℝ =>
          (completedWeilEndpointTraceFiber f).gram ≤ traceValue)
        htraceMatrix.symm
        hdomination)
  let hhidden :
      0 ≤ (completedEndpointFinitePositiveTraceMatrix N f).hiddenKernelScalar :=
    completedEndpointFinitePositiveTraceMatrix_hiddenKernel_nonnegative_of_endpointBesselDomination
      N f hmatrix
  let hiddenKernel : ℝ :=
    (completedEndpointFinitePositiveTraceMatrix N f).hiddenKernelScalar
  let htrace :
      (completedEndpointFinitePositiveTraceMatrix N f).traceScalar =
        (completedEndpointFinitePositiveTraceMatrix N f).endpointCompressionScalar +
          hiddenKernel :=
    finitePositiveRenormalizedBoundaryWindow_eq_endpointTraceGram_add_finiteBesselSchurRemainder
      N f
  let hnonnegative : 0 ≤ hiddenKernel := hhidden
  Exists.intro hiddenKernel
    (And.intro htrace hnonnegative)

/-- Source finite endpoint-vector realization in the positive trace matrix.

This is the finite GNS/Riesz realization theorem for the endpoint vector. -/
theorem completedEndpointFinitePositiveTraceMatrixEndpointVectorRealization_eventually_source
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f) :
    ∀ᶠ N in atTop,
      CompletedEndpointFinitePositiveTraceMatrixEndpointVectorRealization
        N f :=
  (completedEndpointTraceFiber_gram_le_finitePositiveRenormalizedBoundaryWindow_eventually_source
    f D hnonPrime).mono
    (fun N hN =>
      completedEndpointFinitePositiveTraceMatrixEndpointVectorRealization_of_windowDomination
        N f hN)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
