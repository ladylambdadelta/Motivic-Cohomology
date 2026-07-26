import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointTraceCompression
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointTraceCompressionSource
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointFiniteBessel
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.TraceReconstruction

/-!
# Endpoint physical absorption primitive

This file owns the full trace-level endpoint absorption input before any
centered archimedean/correction specialization is applied.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The hidden endpoint kernel left after removing the visible endpoint trace
fiber from the completed physical boundary trace. -/
noncomputable def completedEndpointPhysicalHiddenKernel
    (f : ZetaAdmissibleFunction) : ℝ :=
  completedWeilEndpointAbsorbedPhysicalScalar f

/-- The hidden endpoint kernel is the endpoint-absorbed physical scalar. -/
theorem completedEndpointPhysicalHiddenKernel_eq_absorbedPhysical
    (f : ZetaAdmissibleFunction) :
    completedEndpointPhysicalHiddenKernel f =
      completedWeilEndpointAbsorbedPhysicalScalar f :=
  Eq.refl (completedEndpointPhysicalHiddenKernel f)

/-- The hidden endpoint kernel is the named endpoint trace remainder. -/
theorem completedEndpointPhysicalHiddenKernel_eq_traceRemainder
    (f : ZetaAdmissibleFunction) :
    completedEndpointPhysicalHiddenKernel f =
      completedWeilEndpointTraceRemainder f :=
  Eq.trans
    (completedEndpointPhysicalHiddenKernel_eq_absorbedPhysical f)
    (completedWeilEndpointTraceRemainder_eq_absorbedPhysicalScalar f).symm

/-- The completed physical boundary trace splits into the visible endpoint
trace Gram plus the hidden endpoint kernel. -/
theorem completedBoundaryChannel_convolutionAutocorrelation_re_eq_endpointFiberGram_add_physicalHiddenKernel
    (f : ZetaAdmissibleFunction) :
    Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
      (completedWeilEndpointTraceFiber f).gram +
        completedEndpointPhysicalHiddenKernel f :=
  Eq.trans
    (completedBoundaryChannel_convolutionAutocorrelation_re_eq_endpointFiberGram_add_traceRemainder
      f)
    (congrArg
      (fun value : ℝ => (completedWeilEndpointTraceFiber f).gram + value)
      (completedEndpointPhysicalHiddenKernel_eq_traceRemainder f).symm)

/-- The hidden endpoint kernel is the physical boundary scalar minus the
visible endpoint trace Gram. -/
theorem completedEndpointPhysicalHiddenKernel_eq_boundaryChannel_sub_endpointFiberGram
    (f : ZetaAdmissibleFunction) :
    completedEndpointPhysicalHiddenKernel f =
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) -
        (completedWeilEndpointTraceFiber f).gram :=
  Eq.trans
    (completedEndpointPhysicalHiddenKernel_eq_traceRemainder f)
    (Eq.trans
      (completedWeilEndpointTraceRemainder_eq_absorbedPhysicalScalar f)
      (Eq.trans
        (completedWeilEndpointAbsorbedPhysicalScalar_eq_boundaryChannel_re_sub_diagonalDebt
          f)
        (congrArg
          (fun value : ℝ =>
            Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) -
              value)
          (completedWeilEndpointTraceFiber_gram_eq_diagonalDebt f).symm)))

/-- The finite hidden endpoint kernel windows converge to the completed hidden
endpoint kernel. -/
theorem completedEndpointPhysicalHiddenKernelWindow_tendsto_hiddenKernel_source
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => completedEndpointPhysicalHiddenKernelWindow N f)
      atTop
      (𝓝 (completedEndpointPhysicalHiddenKernel f)) :=
  let hboundary :
      Tendsto
        (fun N : ℕ => finitePositiveRenormalizedBoundaryWindow N f)
        atTop
        (𝓝 (Complex.re
          (completedBoundaryChannel (convolutionAutocorrelation f)))) :=
    finitePositiveRenormalizedBoundaryWindow_tendsto_boundaryChannel f
  let hendpoint :
      Tendsto
        (fun N : ℕ => (completedWeilEndpointTraceFiber f).gram)
        atTop
        (𝓝 ((completedWeilEndpointTraceFiber f).gram)) :=
    tendsto_const_nhds
  let hsub :
      Tendsto
        (fun N : ℕ =>
          finitePositiveRenormalizedBoundaryWindow N f -
            (completedWeilEndpointTraceFiber f).gram)
        atTop
        (𝓝
          (Complex.re
              (completedBoundaryChannel (convolutionAutocorrelation f)) -
            (completedWeilEndpointTraceFiber f).gram)) :=
    hboundary.sub hendpoint
  let hwindow :
      (fun N : ℕ => completedEndpointPhysicalHiddenKernelWindow N f) =
        (fun N : ℕ =>
          finitePositiveRenormalizedBoundaryWindow N f -
            (completedWeilEndpointTraceFiber f).gram) :=
    funext
      (fun N : ℕ =>
      completedEndpointPhysicalHiddenKernelWindow_eq_renormalizedBoundaryWindow_sub_endpointFiberGram
        N f)
  Eq.subst
    (motive := fun value : ℝ =>
      Tendsto
        (fun N : ℕ => completedEndpointPhysicalHiddenKernelWindow N f)
        atTop
        (𝓝 value))
    (completedEndpointPhysicalHiddenKernel_eq_boundaryChannel_sub_endpointFiberGram
      f).symm
    (Eq.subst
      (motive := fun u : ℕ → ℝ =>
        Tendsto u atTop
          (𝓝
            (Complex.re
                (completedBoundaryChannel (convolutionAutocorrelation f)) -
              (completedWeilEndpointTraceFiber f).gram)))
      hwindow.symm
      hsub)

/-- Source positivity of the hidden endpoint kernel in the full physical
boundary trace. -/
theorem completedEndpointPhysicalHiddenKernel_nonnegative_source
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f) :
    0 ≤ completedEndpointPhysicalHiddenKernel f :=
  let hendpointBoundary :
      (completedWeilEndpointTraceFiber f).gram ≤
        Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) :=
    completedEndpointTraceFiber_gram_le_boundaryChannel_finiteBessel_source
      f D hnonPrime
  let hsub :
      0 ≤
        Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) -
          (completedWeilEndpointTraceFiber f).gram :=
    sub_nonneg.mpr hendpointBoundary
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (completedEndpointPhysicalHiddenKernel_eq_boundaryChannel_sub_endpointFiberGram
      f).symm
    hsub

/-- Source prime-boundary comparison for the completed physical endpoint
absorption lane. -/
theorem primeBoundaryChannel_convolutionAutocorrelation_re_eq_positiveChannel_sourcePhysicalPrimitive
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hcoordinateZero :
      Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) =
      completedPrimeDefectKernelPositiveChannel f :=
  let hboundary :
      Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) =
        completedPrimeOffDiagonalChannel f :=
    (completedPrimeOffDiagonalChannel_eq_primeBoundaryChannel f).symm
  let hoffZero :
      completedPrimeOffDiagonalChannel f = 0 :=
    completedPrimeOffDiagonalChannel_eq_zero_ownerTraceReconstruction
      f D
  let hpositiveZero :
      0 = completedPrimeDefectKernelPositiveChannel f :=
    (completedPrimeDefectKernelPositiveChannel_eq_zero_of_completedLowerWeightNormalization
      f).symm
  hboundary.trans (hoffZero.trans hpositiveZero)

/-- Source nonnegativity of the endpoint-absorbed physical trace scalar.

This is the full trace Schur-complement positivity statement: after the two
endpoint diagonal fibers are removed from the completed physical boundary
trace, the remaining hidden kernel is nonnegative. -/
theorem completedWeilEndpointAbsorbedPhysicalScalar_nonnegative_sourcePhysicalPrimitive
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f) :
    0 ≤ completedWeilEndpointAbsorbedPhysicalScalar f :=
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (completedEndpointPhysicalHiddenKernel_eq_absorbedPhysical f)
    (completedEndpointPhysicalHiddenKernel_nonnegative_source f D hnonPrime)

/-- Finite-Bessel physical absorption gives endpoint domination by the positive
GNS presentation after the physical boundary scalar has been identified with
that presentation. -/
theorem completedEndpointTraceFiber_gram_le_positivePresentation_sourcePhysicalPrimitive_of_finiteBessel
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f)
    (boundary_eq_positive :
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
        zetaCompletedGNSPositiveBoundaryPresentationScalar f) :
    (completedWeilEndpointTraceFiber f).gram ≤
      zetaCompletedGNSPositiveBoundaryPresentationScalar f :=
  completedEndpointTraceFiber_gram_le_positivePresentation_traceCompression_of_finiteBessel
    f D hnonPrime boundary_eq_positive

/-- Finite-Bessel physical absorption gives nonnegativity of the
positive-presentation endpoint compression remainder after scalar transport. -/
theorem completedEndpointFiberPositivePresentationRemainder_nonnegative_sourcePhysicalPrimitive_of_finiteBessel
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f)
    (boundary_eq_positive :
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
        zetaCompletedGNSPositiveBoundaryPresentationScalar f) :
    0 ≤ completedEndpointFiberPositivePresentationRemainder f :=
  (completedEndpointFiberPositivePresentationRemainder_nonnegative_iff_endpointFiberGram_le_positivePresentation
    f).mpr
    (completedEndpointTraceFiber_gram_le_positivePresentation_sourcePhysicalPrimitive_of_finiteBessel
      f D hnonPrime boundary_eq_positive)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
