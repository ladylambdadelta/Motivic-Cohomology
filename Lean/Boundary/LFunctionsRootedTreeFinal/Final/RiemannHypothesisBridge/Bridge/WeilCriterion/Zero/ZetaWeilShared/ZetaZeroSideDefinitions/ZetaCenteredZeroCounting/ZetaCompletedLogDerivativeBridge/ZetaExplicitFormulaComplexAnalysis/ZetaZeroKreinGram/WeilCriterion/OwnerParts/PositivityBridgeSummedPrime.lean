import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PositivityTraceReductions
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.SummedPrimeTransport
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.OwnerParts.BoundaryCancellationInputs

/-!
# Summed-prime positivity bridge wrappers

This file owns the final summed-prime and ledger-cancellation wrappers that feed
the completed Weil positivity bridge.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Summed prime transport plus matrix comparison identifies the raw prime
boundary channel with the positive GNS channel on each autocorrelation seed. -/
theorem primeBoundaryChannel_re_eq_positiveChannel_of_summedTransport_matrixComparison_owner
    (summedTransport :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedSummedPrimeContourTimeTransport f)
    (matrixComparison :
      ∀ f : ZetaAdmissibleFunction,
        Complex.re
            (ZetaAdmissibleFunction.zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
          Complex.re
            (ZetaAdmissibleFunction.zetaPrimeTwoFaceGNSMatrixCoefficient f)) :
    ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.zetaCompletedPhysicalPrimeBoundaryScalar f =
        ZetaAdmissibleFunction.zetaCompletedGNSPositiveBoundaryPresentationScalar f :=
  fun f =>
    ZetaAdmissibleFunction.primeBoundaryChannel_convolutionAutocorrelation_re_eq_positiveChannel_of_summedTransport
      f (summedTransport f) (matrixComparison f)

/-- Completed Weil positivity follows from the summed prime transport,
matrix comparison, and nonnegativity of the concrete canonical endpoint
kernel remainder. -/
theorem zetaWeilQuadraticPositivity_of_summedPrimeTransport_sourceEndpointKernelRemainder_owner
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (boundaryIdentification : ZetaWeilAutocorrelationBoundaryIdentification)
    (summedTransport :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedSummedPrimeContourTimeTransport f)
    (matrixComparison :
      ∀ f : ZetaAdmissibleFunction,
        Complex.re
            (ZetaAdmissibleFunction.zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
          Complex.re
            (ZetaAdmissibleFunction.zetaPrimeTwoFaceGNSMatrixCoefficient f))
    (sourceEndpointKernelRemainderNonnegative :
      ∀ f : ZetaAdmissibleFunction,
        0 ≤
          ZetaAdmissibleFunction.completedBoundaryHilbertSourceEndpointKernelRemainder
            (ZetaAdmissibleFunction.completedBoundaryHilbertSource f)) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_primeComparison_sourceEndpointKernelRemainder_owner
    hbranch
    hpartialOneTwo
    hcompactOneTwo
    hfinite
    hpartialLeft
    hcompactBoundary
    boundaryIdentification
    (primeBoundaryChannel_re_eq_positiveChannel_of_summedTransport_matrixComparison_owner
      summedTransport
      matrixComparison)
    sourceEndpointKernelRemainderNonnegative

/-- Boundary-cancellation ledger data gives the completed/raw two-face
matrix comparison required by summed prime transport. -/
theorem completedPrimeTwoFace_matrixComparison_of_ledgerCancellation_owner
    (f : ZetaAdmissibleFunction)
    (hledger :
      ZetaAdmissibleFunction.ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f)
    (horiented :
      Summable
        (fun ι : ZetaAdmissibleFunction.ZetaPrimePowerIndex =>
          ZetaAdmissibleFunction.zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
            ι f)) :
    Complex.re
        (ZetaAdmissibleFunction.zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
      Complex.re
        (ZetaAdmissibleFunction.zetaPrimeTwoFaceGNSMatrixCoefficient f) :=
  ZetaAdmissibleFunction.completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_finite_boundaryCancellation
    f hledger horiented

/-- Ledger cancellation supplies the pointwise completed/raw two-face matrix
comparison. -/
theorem completedPrimeTwoFace_matrixComparison_of_ledgerCancellation_family_owner
    (ledgerCancellation :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f)
    (orientedSummable :
      ∀ f : ZetaAdmissibleFunction,
        Summable
          (fun ι : ZetaAdmissibleFunction.ZetaPrimePowerIndex =>
            ZetaAdmissibleFunction.zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
              ι f)) :
    ∀ f : ZetaAdmissibleFunction,
      Complex.re
          (ZetaAdmissibleFunction.zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re
          (ZetaAdmissibleFunction.zetaPrimeTwoFaceGNSMatrixCoefficient f) :=
  fun f =>
    completedPrimeTwoFace_matrixComparison_of_ledgerCancellation_owner
      f (ledgerCancellation f) (orientedSummable f)

/-- Completed Weil positivity follows from summed prime transport, the
completed prime-power ledger cancellation, and nonnegativity of the concrete
canonical endpoint kernel remainder. -/
theorem zetaWeilQuadraticPositivity_of_summedPrimeTransport_ledgerCancellation_sourceEndpointKernelRemainder_owner
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (boundaryIdentification : ZetaWeilAutocorrelationBoundaryIdentification)
    (summedTransport :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedSummedPrimeContourTimeTransport f)
    (ledgerCancellation :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f)
    (orientedSummable :
      ∀ f : ZetaAdmissibleFunction,
        Summable
          (fun ι : ZetaAdmissibleFunction.ZetaPrimePowerIndex =>
            ZetaAdmissibleFunction.zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
              ι f))
    (sourceEndpointKernelRemainderNonnegative :
      ∀ f : ZetaAdmissibleFunction,
        0 ≤
          ZetaAdmissibleFunction.completedBoundaryHilbertSourceEndpointKernelRemainder
            (ZetaAdmissibleFunction.completedBoundaryHilbertSource f)) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_summedPrimeTransport_sourceEndpointKernelRemainder_owner
    hbranch
    hpartialOneTwo
    hcompactOneTwo
    hfinite
    hpartialLeft
    hcompactBoundary
    boundaryIdentification
    summedTransport
    (completedPrimeTwoFace_matrixComparison_of_ledgerCancellation_family_owner
      ledgerCancellation
      orientedSummable)
    sourceEndpointKernelRemainderNonnegative

/-- Endpoint-fiber domination gives nonnegativity of the concrete source
endpoint-kernel remainder. -/
theorem sourceEndpointKernelRemainder_nonnegative_of_endpointFiberDomination_owner
    (endpointFiberDomination :
      ∀ f : ZetaAdmissibleFunction,
        (ZetaAdmissibleFunction.completedWeilEndpointTraceFiber f).gram ≤
          ZetaAdmissibleFunction.zetaCompletedGNSPositiveBoundaryPresentationScalar f) :
    ∀ f : ZetaAdmissibleFunction,
      0 ≤
        ZetaAdmissibleFunction.completedBoundaryHilbertSourceEndpointKernelRemainder
          (ZetaAdmissibleFunction.completedBoundaryHilbertSource f) :=
  fun f =>
    ZetaAdmissibleFunction.completedBoundaryHilbertSourceEndpointKernelRemainder_source_nonnegative_of_endpointFiberGram_le_positivePresentation
      f (endpointFiberDomination f)

/-- Completed Weil positivity follows from summed prime transport, completed
prime-power ledger cancellation, and the endpoint-trace domination theorem
against the positive GNS presentation. -/
theorem zetaWeilQuadraticPositivity_of_summedPrimeTransport_ledgerCancellation_endpointFiberDomination_owner
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (boundaryIdentification : ZetaWeilAutocorrelationBoundaryIdentification)
    (summedTransport :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedSummedPrimeContourTimeTransport f)
    (ledgerCancellation :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f)
    (orientedSummable :
      ∀ f : ZetaAdmissibleFunction,
        Summable
          (fun ι : ZetaAdmissibleFunction.ZetaPrimePowerIndex =>
            ZetaAdmissibleFunction.zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
              ι f))
    (endpointFiberDomination :
      ∀ f : ZetaAdmissibleFunction,
        (ZetaAdmissibleFunction.completedWeilEndpointTraceFiber f).gram ≤
          ZetaAdmissibleFunction.zetaCompletedGNSPositiveBoundaryPresentationScalar f) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_summedPrimeTransport_ledgerCancellation_sourceEndpointKernelRemainder_owner
    hbranch
    hpartialOneTwo
    hcompactOneTwo
    hfinite
    hpartialLeft
    hcompactBoundary
    boundaryIdentification
    summedTransport
    ledgerCancellation
    orientedSummable
    (sourceEndpointKernelRemainder_nonnegative_of_endpointFiberDomination_owner
      endpointFiberDomination)

/-- Endpoint trace domination is the pointwise endpoint-fiber domination
used by the positive GNS presentation comparison. -/
theorem endpointFiberDomination_of_endpointTraceDomination_owner
    (endpointTraceDomination :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedEndpointTraceDomination f) :
    ∀ f : ZetaAdmissibleFunction,
      (ZetaAdmissibleFunction.completedWeilEndpointTraceFiber f).gram ≤
        ZetaAdmissibleFunction.zetaCompletedGNSPositiveBoundaryPresentationScalar f :=
  fun f =>
    (ZetaAdmissibleFunction.completedEndpointTraceDomination_iff_endpointFiberGram_le_positivePresentation
      f).mp
      (endpointTraceDomination f)

/-- Completed Weil positivity follows from summed prime transport, completed
prime-power ledger cancellation, and the named endpoint trace domination
theorem. -/
theorem zetaWeilQuadraticPositivity_of_summedPrimeTransport_ledgerCancellation_endpointTraceDomination_owner
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (boundaryIdentification : ZetaWeilAutocorrelationBoundaryIdentification)
    (summedTransport :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedSummedPrimeContourTimeTransport f)
    (ledgerCancellation :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f)
    (orientedSummable :
      ∀ f : ZetaAdmissibleFunction,
        Summable
          (fun ι : ZetaAdmissibleFunction.ZetaPrimePowerIndex =>
            ZetaAdmissibleFunction.zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
              ι f))
    (endpointTraceDomination :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedEndpointTraceDomination f) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_summedPrimeTransport_ledgerCancellation_endpointFiberDomination_owner
    hbranch
    hpartialOneTwo
    hcompactOneTwo
    hfinite
    hpartialLeft
    hcompactBoundary
    boundaryIdentification
    summedTransport
    ledgerCancellation
    orientedSummable
    (endpointFiberDomination_of_endpointTraceDomination_owner
      endpointTraceDomination)

/-- Completed Weil positivity from explicit diagonal-debt real-coordinate
`HasSum` inputs for every autocorrelation seed, ledger cancellation, and
endpoint trace domination. -/
theorem zetaWeilQuadraticPositivity_of_autocorrelation_diagonalDebtCoordinate_re_hasSum_ledgerCancellation_endpointTraceDomination_owner
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (boundaryIdentification : ZetaWeilAutocorrelationBoundaryIdentification)
    (C Creflect : ZetaAdmissibleFunction → ℝ)
    (hhasSum :
      ∀ f : ZetaAdmissibleFunction,
        HasSum
          (fun index : ZetaAdmissibleFunction.ZetaPrimePowerIndex =>
            Complex.re
              (ZetaAdmissibleFunction.zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate
                index (ZetaAdmissibleFunction.convolutionAutocorrelation f)))
          (C f))
    (hhasSumReflect :
      ∀ f : ZetaAdmissibleFunction,
        HasSum
          (fun index : ZetaAdmissibleFunction.ZetaPrimePowerIndex =>
            Complex.re
              (ZetaAdmissibleFunction.zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate
                index
                (ZetaAdmissibleFunction.reflect
                  (ZetaAdmissibleFunction.convolutionAutocorrelation f))))
          (Creflect f))
    (ledgerCancellation :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f)
    (orientedSummable :
      ∀ f : ZetaAdmissibleFunction,
        Summable
          (fun ι : ZetaAdmissibleFunction.ZetaPrimePowerIndex =>
            ZetaAdmissibleFunction.zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
              ι f))
    (endpointTraceDomination :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedEndpointTraceDomination f) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_summedPrimeTransport_ledgerCancellation_endpointTraceDomination_owner
    hbranch
    hpartialOneTwo
    hcompactOneTwo
    hfinite
    hpartialLeft
    hcompactBoundary
    boundaryIdentification
    (ZetaAdmissibleFunction.completedSummedPrimeContourTimeTransport_family_owner_of_autocorrelation_diagonalDebtCoordinate_re_hasSum
      C Creflect hhasSum hhasSumReflect)
    ledgerCancellation
    orientedSummable
    endpointTraceDomination

/-- Completed Weil positivity from summability of the diagonal-debt
real-coordinate streams for every autocorrelation seed, ledger cancellation,
and endpoint trace domination. -/
theorem zetaWeilQuadraticPositivity_of_autocorrelation_diagonalDebtCoordinate_re_summable_ledgerCancellation_endpointTraceDomination_owner
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (boundaryIdentification : ZetaWeilAutocorrelationBoundaryIdentification)
    (hsummable :
      ∀ f : ZetaAdmissibleFunction,
        Summable
          (fun index : ZetaAdmissibleFunction.ZetaPrimePowerIndex =>
            Complex.re
              (ZetaAdmissibleFunction.zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate
                index (ZetaAdmissibleFunction.convolutionAutocorrelation f))))
    (hsummableReflect :
      ∀ f : ZetaAdmissibleFunction,
        Summable
          (fun index : ZetaAdmissibleFunction.ZetaPrimePowerIndex =>
            Complex.re
              (ZetaAdmissibleFunction.zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate
                index
                (ZetaAdmissibleFunction.reflect
                  (ZetaAdmissibleFunction.convolutionAutocorrelation f)))))
    (ledgerCancellation :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f)
    (orientedSummable :
      ∀ f : ZetaAdmissibleFunction,
        Summable
          (fun ι : ZetaAdmissibleFunction.ZetaPrimePowerIndex =>
            ZetaAdmissibleFunction.zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
              ι f))
    (endpointTraceDomination :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedEndpointTraceDomination f) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_summedPrimeTransport_ledgerCancellation_endpointTraceDomination_owner
    hbranch
    hpartialOneTwo
    hcompactOneTwo
    hfinite
    hpartialLeft
    hcompactBoundary
    boundaryIdentification
    (ZetaAdmissibleFunction.completedSummedPrimeContourTimeTransport_family_owner_of_autocorrelation_diagonalDebtCoordinate_re_summable
      hsummable hsummableReflect)
    ledgerCancellation
    orientedSummable
    endpointTraceDomination

/-- Completed Weil positivity from trace-Bessel summed-prime transport,
completed prime-power ledger cancellation, and endpoint trace domination.
The analytic bundle remains explicit here because the summed-prime transport
owner consumes it downstream: the branch and boundary estimates enter the
summed-prime transport, while the boundary identification feeds the final
Weil-form transport. -/
theorem zetaWeilQuadraticPositivity_of_traceBesselSummedPrimeTransport_ledgerCancellation_endpointTraceDomination_owner
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (boundaryIdentification : ZetaWeilAutocorrelationBoundaryIdentification)
    (ledgerCancellation :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f)
    (orientedSummable :
      ∀ f : ZetaAdmissibleFunction,
        Summable
          (fun ι : ZetaAdmissibleFunction.ZetaPrimePowerIndex =>
            ZetaAdmissibleFunction.zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
              ι f))
    (endpointTraceDomination :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedEndpointTraceDomination f) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_summedPrimeTransport_ledgerCancellation_endpointTraceDomination_owner
    hbranch
    hpartialOneTwo
    hcompactOneTwo
    hfinite
    hpartialLeft
    hcompactBoundary
    boundaryIdentification
    ZetaAdmissibleFunction.completedSummedPrimeContourTimeTransport_family_owner_traceBessel
    ledgerCancellation
    orientedSummable
    endpointTraceDomination

/-- Completed Weil positivity from trace-Bessel summed-prime transport,
the owner ledger-cancellation package, and endpoint trace domination. -/
theorem zetaWeilQuadraticPositivity_of_traceBesselSummedPrimeTransport_endpointTraceDomination_owner
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (boundaryIdentification : ZetaWeilAutocorrelationBoundaryIdentification)
    (endpointTraceDomination :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedEndpointTraceDomination f) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_traceBesselSummedPrimeTransport_ledgerCancellation_endpointTraceDomination_owner
    hbranch
    hpartialOneTwo
    hcompactOneTwo
    hfinite
    hpartialLeft
    hcompactBoundary
    boundaryIdentification
    ZetaAdmissibleFunction.zetaCompletedPrimePowerAutocorrelationLedgerCancellation_owner
    ZetaAdmissibleFunction.zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_summable_owner
    endpointTraceDomination

/-- The endpoint Schur-projection owner theorem gives endpoint trace
domination for every autocorrelation seed. -/
theorem endpointTraceDomination_family_ownerSchurProjection
    (f : ZetaAdmissibleFunction) :
    ZetaAdmissibleFunction.CompletedEndpointTraceDomination f :=
  (ZetaAdmissibleFunction.completedEndpointTraceDomination_iff_endpointFiberGram_le_positivePresentation
    f).mpr
    (ZetaAdmissibleFunction.completedEndpointTraceFiber_gram_le_positivePresentation_ownerSchurProjection
      f)

/-- Completed Weil positivity from trace-Bessel summed-prime transport, owner
ledger cancellation, and owner endpoint Schur-projection domination. -/
theorem zetaWeilQuadraticPositivity_of_traceBesselSummedPrimeTransport_owner
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (boundaryIdentification : ZetaWeilAutocorrelationBoundaryIdentification) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_traceBesselSummedPrimeTransport_endpointTraceDomination_owner
    hbranch
    hpartialOneTwo
    hcompactOneTwo
    hfinite
    hpartialLeft
    hcompactBoundary
    boundaryIdentification
    endpointTraceDomination_family_ownerSchurProjection

/-- Boundary-to-positive scalar identification and endpoint absorption give
the endpoint trace domination family consumed by the summed-prime positivity
bridge. -/
theorem endpointTraceDomination_family_of_boundaryToPositive_endpointAbsorption_owner
    (boundaryToPositive :
      ∀ f : ZetaAdmissibleFunction,
        Complex.re
            (ZetaAdmissibleFunction.completedBoundaryChannel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)) =
          ZetaAdmissibleFunction.zetaCompletedGNSPositiveBoundaryPresentationScalar
            f)
    (endpointAbsorption :
      ∀ f : ZetaAdmissibleFunction,
        0 ≤
          ZetaAdmissibleFunction.completedWeilEndpointAbsorbedPhysicalScalar
            f) :
    ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedEndpointTraceDomination f :=
  fun f =>
    ZetaAdmissibleFunction.completedEndpointTraceDomination_of_boundary_eq_positivePresentation_absorbedPhysical
      f
      (boundaryToPositive f)
      (endpointAbsorption f)

/-- Completed Weil positivity from trace-Bessel summed-prime transport,
owner ledger cancellation, boundary-to-positive scalar identification, and
endpoint absorption. -/
theorem zetaWeilQuadraticPositivity_of_traceBesselSummedPrimeTransport_boundaryToPositive_endpointAbsorption_owner
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (boundaryIdentification : ZetaWeilAutocorrelationBoundaryIdentification)
    (boundaryToPositive :
      ∀ f : ZetaAdmissibleFunction,
        Complex.re
            (ZetaAdmissibleFunction.completedBoundaryChannel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)) =
          ZetaAdmissibleFunction.zetaCompletedGNSPositiveBoundaryPresentationScalar
            f)
    (endpointAbsorption :
      ∀ f : ZetaAdmissibleFunction,
        0 ≤
          ZetaAdmissibleFunction.completedWeilEndpointAbsorbedPhysicalScalar
            f) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_traceBesselSummedPrimeTransport_endpointTraceDomination_owner
    hbranch
    hpartialOneTwo
    hcompactOneTwo
    hfinite
    hpartialLeft
    hcompactBoundary
    boundaryIdentification
    (endpointTraceDomination_family_of_boundaryToPositive_endpointAbsorption_owner
      boundaryToPositive
      endpointAbsorption)

end

end LFunctions
end Boundary
