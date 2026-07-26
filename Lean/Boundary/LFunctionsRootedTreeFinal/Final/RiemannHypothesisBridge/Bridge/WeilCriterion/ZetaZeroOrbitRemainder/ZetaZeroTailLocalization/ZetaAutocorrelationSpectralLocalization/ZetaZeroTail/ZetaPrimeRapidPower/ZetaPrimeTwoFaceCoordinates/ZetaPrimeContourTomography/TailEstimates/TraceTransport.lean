import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.CoordinateTail
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.HolographicTraceSeparationParts.DiagonalResidualFunctionalParts.DiagonalDebtAnnihilatorGapAssembly
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.TraceTransportParts.DiagonalOwnerLimit
namespace Boundary
namespace LFunctions
noncomputable section
open Filter
open scoped BigOperators Topology
namespace ZetaAdmissibleFunction

theorem finiteSpectralPrimeOffDiagonalWindow_eq_contourRealizedTimeDistributionWindow_traceTransport_source
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finiteSpectralPrimeOffDiagonalWindow N f =
      finitePrimeContourRealizedTimeDistributionWindow N
        (convolutionAutocorrelation f) :=
  Eq.refl (finiteSpectralPrimeOffDiagonalWindow N f)
theorem zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_sum_eq_matrixWindow_traceTransport_source
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (∑ index in ZetaPrimePowerIndex.window N,
        zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f) =
      zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f :=
  zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_sum_eq_matrixWindow_traceTransport_source_limit_core
    N f
theorem finiteSpectralPrimeOffDiagonalWindow_eq_neg_twoFaceWindow_re_traceTransport_source
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finiteSpectralPrimeOffDiagonalWindow N f =
      -Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) :=
  let s : Finset ZetaPrimePowerIndex := ZetaPrimePowerIndex.window N
  let A : ZetaPrimePowerIndex → ℂ :=
    fun index : ZetaPrimePowerIndex =>
      -((index.weight : ℂ) *
        (zetaCompletedExplicitFormulaPhi
            (convolutionAutocorrelation f) index.center +
          star
            (zetaCompletedExplicitFormulaPhi
              (convolutionAutocorrelation f) index.center)))
  let T : ZetaPrimePowerIndex → ℂ :=
    fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f
  let hpoint :
      ∀ index : ZetaPrimePowerIndex, A index = -T index :=
    fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralSampleCoordinate_eq_neg_twoFaceBoundaryCoordinate
        index f
  let hsum :
      (∑ index in s, A index) = ∑ index in s, -T index :=
    Finset.sum_congr
      (Eq.refl s)
      (fun index membership => hpoint index)
  let hneg :
      (∑ index in s, -T index) = -(∑ index in s, T index) :=
    Finset.sum_neg_distrib
  let hmatrix :
      (∑ index in s, T index) =
        zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f :=
    zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_sum_eq_matrixWindow_traceTransport_source
      N f
  let hstart :
      finiteSpectralPrimeOffDiagonalWindow N f =
        Complex.re (∑ index in s, A index) :=
    Eq.refl (finiteSpectralPrimeOffDiagonalWindow N f)
  let hsumRe :
      Complex.re (∑ index in s, A index) =
        Complex.re (∑ index in s, -T index) :=
    congrArg Complex.re hsum
  let hnegRe :
      Complex.re (∑ index in s, -T index) =
        Complex.re (-(∑ index in s, T index)) :=
    congrArg Complex.re hneg
  let hmatrixRe :
      Complex.re (-(∑ index in s, T index)) =
        Complex.re (-zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) :=
    congrArg
      (fun z : ℂ => Complex.re (-z))
      hmatrix
  let hfinal :
      Complex.re (-zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) =
        -Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) :=
    Complex.neg_re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f)
  hstart.trans (hsumRe.trans (hnegRe.trans (hmatrixRe.trans hfinal)))

theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_neg_completedSpectralPrimeOffDiagonalChannel_source_core
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
      -completedSpectralPrimeOffDiagonalChannel f :=
  let T : ℂ := zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f
  let B : ℂ := zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f
  let hboundary :
      B = -T :=
    zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient_eq_neg_matrixCoefficient
      f
  let hboundaryReStep :
      Complex.re B = Complex.re (-T) :=
    congrArg Complex.re hboundary
  let hboundaryRe :
      Complex.re B = -Complex.re T :=
    hboundaryReStep.trans (Complex.neg_re T)
  let hspectral :
      completedSpectralPrimeOffDiagonalChannel f = Complex.re B :=
    completedSpectralPrimeOffDiagonalChannel_eq_completedTwoFaceBoundaryCoefficient_re
      f
  let hstart :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re T :=
    Eq.refl (Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f))
  let hdouble :
      Complex.re T = -(-Complex.re T) :=
    (neg_neg (Complex.re T)).symm
  let hboundaryNeg :
      -(-Complex.re T) = -Complex.re B :=
    congrArg Neg.neg hboundaryRe.symm
  let hspectralNeg :
      -Complex.re B = -completedSpectralPrimeOffDiagonalChannel f :=
    congrArg Neg.neg hspectral.symm
  hstart.trans (hdouble.trans (hboundaryNeg.trans hspectralNeg))

theorem zetaPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_traceTransport_source_core
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) = 0 :=
  zetaPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_of_completedLowerWeightNormalization
    f

def CompletedPrimeDefectCoordinateTraceAnnihilation
    (f : ZetaAdmissibleFunction) : Prop :=
  zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f = 0 ∧
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      0

def CompletedPrimeDefectCoordinateOwnerTransport
    (f : ZetaAdmissibleFunction) : Prop :=
  completedPrimeOffDiagonalChannel f =
      completedPrimeDefectKernelPositiveChannel f ∧
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f)

theorem completedPrimeOffDiagonalChannel_eq_positiveChannel_traceTransport_source_core
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    completedPrimeOffDiagonalChannel f =
      completedPrimeDefectKernelPositiveChannel f :=
  completedPrimeOffDiagonalChannel_eq_ownerPositiveChannel_twoFaceZero_source
    f D

theorem completedPrimeOffDiagonalChannel_eq_zero_traceTransport_source_core
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    completedPrimeOffDiagonalChannel f = 0 :=
  (completedPrimeOffDiagonalChannel_eq_positiveChannel_traceTransport_source_core
    f D).trans
    (completedPrimeDefectKernelPositiveChannel_eq_zero_of_completedLowerWeightNormalization
      f)

theorem completedPrimeTraceTimeScalar_eq_spectralScalar_traceTransport_source_core
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    completedPrimeTraceTimeScalar f =
      completedPrimeTraceSpectralScalar f :=
  let htime :
      completedPrimeTraceTimeScalar f =
        completedPrimeOffDiagonalChannel f :=
    completedPrimeTraceTimeScalar_eq_offDiagonalChannel_source f
  let htimeZero :
      completedPrimeTraceTimeScalar f = 0 :=
    htime.trans
      (completedPrimeOffDiagonalChannel_eq_zero_traceTransport_source_core f D)
  let hspectral :
      completedPrimeTraceSpectralScalar f =
        -Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
    completedPrimeTraceSpectralScalar_eq_neg_twoFace_source f
  let htwoFaceZero :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0 :=
    zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_source f
  let hnegZero :
      -Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = -0 :=
    congrArg Neg.neg htwoFaceZero
  let hspectralZero :
      completedPrimeTraceSpectralScalar f = 0 :=
    hspectral.trans (hnegZero.trans neg_zero)
  htimeZero.trans hspectralZero.symm

theorem completedPrimeTraceFunctionalGap_eq_zero_traceTransport_source_core
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    completedPrimeTraceFunctionalGap f = 0 :=
  let hscalar :
      completedPrimeTraceTimeScalar f =
        completedPrimeTraceSpectralScalar f :=
    completedPrimeTraceTimeScalar_eq_spectralScalar_traceTransport_source_core f
      D
  let htime :
      Complex.re
          (zetaCompletedExplicitFormulaPrimePowerContribution
            (convolutionAutocorrelation f)) =
        completedPrimeTraceTimeScalar f :=
    (completedPrimeTraceTimeScalar_eq f).symm
  let hspectral :
      completedPrimeTraceSpectralScalar f =
        Complex.re
          (zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
            (convolutionAutocorrelation f)) :=
    completedPrimeTraceSpectralScalar_eq f
  let htrace : Complex.re
        (zetaCompletedExplicitFormulaPrimePowerContribution
          (convolutionAutocorrelation f)) =
      Complex.re
        (zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
          (convolutionAutocorrelation f)) :=
    htime.trans (hscalar.trans hspectral)
  completedPrimeTraceFunctionalGap_eq_zero_of_traceEquality f htrace

theorem completedPrimeOffDiagonalChannel_eq_neg_twoFace_re_traceTransport_source_core
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    completedPrimeOffDiagonalChannel f =
      -Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
  let hscalar :
      completedPrimeTraceTimeScalar f =
        completedPrimeTraceSpectralScalar f :=
    completedPrimeTraceTimeScalar_eq_spectralScalar_traceTransport_source_core
      f D
  let htime :
      completedPrimeTraceTimeScalar f =
        completedPrimeOffDiagonalChannel f :=
    completedPrimeTraceTimeScalar_eq_offDiagonalChannel_source f
  let hspectral :
      completedPrimeTraceSpectralScalar f =
        -Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
    completedPrimeTraceSpectralScalar_eq_neg_twoFace_source f
  htime.symm.trans (hscalar.trans hspectral)

theorem neg_completedPrimeOffDiagonalChannel_eq_twoFace_re_traceTransport_source_core
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    -completedPrimeOffDiagonalChannel f =
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
  let hO_negT :
      completedPrimeOffDiagonalChannel f =
        -Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
    completedPrimeOffDiagonalChannel_eq_neg_twoFace_re_traceTransport_source_core
      f D
  let hneg :
      -completedPrimeOffDiagonalChannel f =
        -(-Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)) :=
    congrArg Neg.neg hO_negT
  hneg.trans
    (neg_neg
      (Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)))

theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_neg_completedPrimeOffDiagonalChannel_traceTransport_source_core
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
      -completedPrimeOffDiagonalChannel f :=
  (neg_completedPrimeOffDiagonalChannel_eq_twoFace_re_traceTransport_source_core
    f D).symm

theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_traceTransport_source_core
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0 :=
  zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_source f

theorem completedSpectralPrimeOffDiagonalChannel_eq_zero_traceTransport_source_core
    (f : ZetaAdmissibleFunction) :
    completedSpectralPrimeOffDiagonalChannel f = 0 :=
  let htwoFace :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        -completedSpectralPrimeOffDiagonalChannel f :=
    zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_neg_completedSpectralPrimeOffDiagonalChannel_source_core
      f
  let hzero :
      -completedSpectralPrimeOffDiagonalChannel f = 0 :=
    htwoFace.symm.trans
      (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_traceTransport_source_core
        f)
  (neg_neg (completedSpectralPrimeOffDiagonalChannel f)).symm.trans
    ((congrArg Neg.neg hzero).trans neg_zero)

theorem finitePrimeContourRealizedTimeDistributionWindow_tendsto_completedPairing_traceTransport_source_core
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    Tendsto
      (fun N : ℕ =>
        finitePrimeContourRealizedTimeDistributionWindow N
          (convolutionAutocorrelation f))
      atTop
      (𝓝 (completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f))) :=
  finitePrimeContourRealizedTimeDistributionWindow_tendsto_completedPairing_ownerTailEstimate
    f
    hmajorant

theorem completedPrimeContourRealizedTimeDistributionPairing_eq_spectralDistributionPairing_traceTransport_source_core
    (f : ZetaAdmissibleFunction) :
    completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f) =
      completedPrimeSpectralDistributionPairing
        (zetaCompletedSpectralLaplaceTransform
          (convolutionAutocorrelation f)) :=
  Eq.refl
    (completedPrimeContourRealizedTimeDistributionPairing
      (convolutionAutocorrelation f))

theorem completedPrimeContourRealizedTimeDistributionPairing_eq_completedSpectralPrimeOffDiagonalChannel_traceTransport_source_core
    (f : ZetaAdmissibleFunction) :
    completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f) =
      completedSpectralPrimeOffDiagonalChannel f :=
  let hrealized :
      completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f) =
        completedPrimeSpectralDistributionPairing
          (zetaCompletedSpectralLaplaceTransform
            (convolutionAutocorrelation f)) :=
    completedPrimeContourRealizedTimeDistributionPairing_eq_spectralDistributionPairing_traceTransport_source_core
      f
  let hspectral :
      completedSpectralPrimeOffDiagonalChannel f =
        completedPrimeSpectralDistributionPairing
          (zetaCompletedSpectralLaplaceTransform
            (convolutionAutocorrelation f)) :=
    completedSpectralPrimeOffDiagonalChannel_eq_spectralDistributionPairing
      f
  hrealized.trans hspectral.symm

theorem completedPrimeContourRealizedTimeDistributionPairing_eq_zero_traceTransport_source_core
    (f : ZetaAdmissibleFunction) :
    completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f) = 0 :=
  let hchannel :
      completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f) =
        completedSpectralPrimeOffDiagonalChannel f :=
    completedPrimeContourRealizedTimeDistributionPairing_eq_completedSpectralPrimeOffDiagonalChannel_traceTransport_source_core
      f
  hchannel.trans
    (completedSpectralPrimeOffDiagonalChannel_eq_zero_traceTransport_source_core
      f)

theorem finitePrimeContourRealizedTimeDistributionWindow_tendsto_zero_traceTransport_source_core
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    Tendsto
      (fun N : ℕ =>
        finitePrimeContourRealizedTimeDistributionWindow N
          (convolutionAutocorrelation f))
      atTop
      (𝓝 0) :=
  let hlimit :
      Tendsto
        (fun N : ℕ =>
          finitePrimeContourRealizedTimeDistributionWindow N
            (convolutionAutocorrelation f))
        atTop
        (𝓝 (completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f))) :=
    finitePrimeContourRealizedTimeDistributionWindow_tendsto_completedPairing_traceTransport_source_core
      f hmajorant
  let hzero :
      completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f) = 0 :=
    completedPrimeContourRealizedTimeDistributionPairing_eq_zero_traceTransport_source_core
      f
  Eq.subst
    (motive := fun value : ℝ =>
      Tendsto
        (fun N : ℕ =>
          finitePrimeContourRealizedTimeDistributionWindow N
            (convolutionAutocorrelation f))
        atTop
        (𝓝 value))
    hzero
    hlimit

theorem finiteSpectralPrimeOffDiagonalWindow_tendsto_zero_traceTransport_source_core
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    Tendsto
      (fun N : ℕ => finiteSpectralPrimeOffDiagonalWindow N f)
      atTop
      (𝓝 0) :=
  let hcontour :
      Tendsto
        (fun N : ℕ =>
          finitePrimeContourRealizedTimeDistributionWindow N
            (convolutionAutocorrelation f))
        atTop
        (𝓝 0) :=
    finitePrimeContourRealizedTimeDistributionWindow_tendsto_zero_traceTransport_source_core
      f hmajorant
  let hfun :
      (fun N : ℕ => finiteSpectralPrimeOffDiagonalWindow N f) =
        fun N : ℕ =>
          finitePrimeContourRealizedTimeDistributionWindow N
            (convolutionAutocorrelation f) :=
    funext
      (fun N : ℕ =>
      finiteSpectralPrimeOffDiagonalWindow_eq_contourRealizedTimeDistributionWindow_traceTransport_source
        N f)
  Eq.subst
    (motive := fun stream : ℕ → ℝ =>
      Tendsto stream atTop (𝓝 0))
    hfun.symm
    hcontour

theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_rawTwoFace_re_source_core
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
      Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) :=
  let hcompleted : Complex.re
      (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0 :=
    zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_source f
  let hraw : Complex.re
      (zetaPrimeTwoFaceGNSMatrixCoefficient f) = 0 :=
    zetaPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_of_completedLowerWeightNormalization
      f
  hcompleted.trans hraw.symm
theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_rawTwoFace_re_of_positiveOffDiagonalGap_eq_zero_source_core
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hgapZero : completedPrimePositiveOffDiagonalGap f = 0) :
    Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
      Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) :=
  let hcompleted : Complex.re
      (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0 :=
    zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_source f
  let hraw : Complex.re
      (zetaPrimeTwoFaceGNSMatrixCoefficient f) = 0 :=
    zetaPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_of_completedLowerWeightNormalization
      f
  hcompleted.trans hraw.symm

theorem zetaCompletedPrimeDefectKernelDiagonalDebt_re_eq_zero_source_core
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) = 0 :=
  zetaCompletedPrimeDefectKernelDiagonalDebt_re_eq_zero_of_twoFace_re_eq
    f
    (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_rawTwoFace_re_source_core
      f hmajorant hcoordinateZero)

theorem zetaCompletedPrimeDefectKernelDiagonalDebt_re_eq_zero_of_positiveOffDiagonalGap_eq_zero_source_core
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hgapZero : completedPrimePositiveOffDiagonalGap f = 0) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) = 0 :=
  zetaCompletedPrimeDefectKernelDiagonalDebt_re_eq_zero_of_twoFace_re_eq
    f
    (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_rawTwoFace_re_of_positiveOffDiagonalGap_eq_zero_source_core
      f hmajorant hgapZero)

theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_ownerDiagonalDebt_re_source_core
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) :=
  let hcoordinate :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
        atTop
        (𝓝
          (Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f))) :=
    zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_coordinateTsum_re_of_spectralMajorant
      f
      hmajorant
  let howner :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
        atTop
        (𝓝 (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))) :=
    zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_ownerDiagonalDebt_re_source_limit_core
      f hmajorant hcoordinateZero
  tendsto_nhds_unique hcoordinate howner

theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_ownerDiagonalDebt_re_of_positiveOffDiagonalGap_eq_zero_source_core
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hgapZero : completedPrimePositiveOffDiagonalGap f = 0) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) :=
  (diagonalDebtCoordinateResidual_re_eq_zero_of_traceGap_zero_and_positiveOffDiagonalGap_zero_source
    f hmajorant
    (completedPrimeTraceFunctionalGap_eq_zero_traceTransport_source_core f D)
    hgapZero).trans
    (zetaCompletedPrimeDefectKernelDiagonalDebt_re_eq_zero_of_positiveOffDiagonalGap_eq_zero_source_core
      f hmajorant hgapZero).symm

theorem completedPrimeDefectCoordinateOwnerTransport_traceTransport_source_core
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    CompletedPrimeDefectCoordinateOwnerTransport f :=
  And.intro
    (completedPrimeOffDiagonalChannel_eq_positiveChannel_traceTransport_source_core
      f D)
    (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_ownerDiagonalDebt_re_source_core
      f hmajorant hcoordinateZero)

theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_ownerDiagonalDebt_re_source_core
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
      atTop
      (𝓝 (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))) :=
    zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_ownerDiagonalDebt_re_source_limit_core
    f hmajorant hcoordinateZero

theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_ownerPositiveChannel_source_core
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
      completedPrimeDefectKernelPositiveChannel f :=
  zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_completedPrimeDefectKernelPositiveChannel_of_diagonalDebtCoordinateTsum_re
    f
    hmajorant
    (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_ownerDiagonalDebt_re_source_core
      f hmajorant hcoordinateZero)

theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_ownerPositiveChannel_of_positiveOffDiagonalGap_eq_zero_source_core
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hgapZero : completedPrimePositiveOffDiagonalGap f = 0) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
      completedPrimeDefectKernelPositiveChannel f :=
  zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_completedPrimeDefectKernelPositiveChannel_of_diagonalDebtCoordinateTsum_re
    f
    hmajorant
    (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_ownerDiagonalDebt_re_of_positiveOffDiagonalGap_eq_zero_source_core
      f D hmajorant hgapZero)

theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_zero_traceTransport_source_core
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f = 0 :=
  let htransport :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
        completedPrimeDefectKernelPositiveChannel f :=
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_ownerPositiveChannel_source_core
      f hmajorant hcoordinateZero
  let howner :
      completedPrimeDefectKernelPositiveChannel f = 0 :=
    completedPrimeDefectKernelPositiveChannel_eq_zero_of_completedLowerWeightNormalization
      f
  htransport.trans howner

theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_zero_traceTransport_source_core
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      0 :=
  hcoordinateZero

theorem completedPrimeDefectCoordinateTraceAnnihilation_traceTransport_source_core
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    CompletedPrimeDefectCoordinateTraceAnnihilation f :=
  ⟨zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_zero_traceTransport_source_core
      f hmajorant hcoordinateZero,
    zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_zero_traceTransport_source_core
      f hmajorant hcoordinateZero⟩

theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_zero_traceTransport_source_core
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
      atTop
      (𝓝 0) :=
  let hownerLimit :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
        atTop
        (𝓝 (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))) :=
    zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_ownerDiagonalDebt_re_source_core
      f hmajorant hcoordinateZero
  let hownerZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
        0 :=
    zetaCompletedPrimeDefectKernelDiagonalDebt_re_eq_zero_source_core
      f hmajorant hcoordinateZero
  Eq.subst
    (motive := fun value : ℝ =>
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
        atTop
        (𝓝 value))
    hownerZero
    hownerLimit

theorem zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_zero_traceTransport_source_core
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
      atTop
      (𝓝 0) :=
  let hcoordinate :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝 (zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f)) :=
    zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_coordinateTsum_re_of_spectralMajorant
      f
      hmajorant
  let hzero :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f = 0 :=
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_zero_traceTransport_source_core
      f hmajorant hcoordinateZero
  Eq.subst
    (motive := fun value : ℝ =>
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝 value))
    hzero
    hcoordinate

theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_re_tendsto_zero_traceTransport_source_core
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Tendsto
      (fun N : ℕ =>
        Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f))
      atTop
      (𝓝 0) :=
  let hdiagonal :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
        atTop
        (𝓝 0) :=
    zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_zero_traceTransport_source_core
      f
      hmajorant
      hcoordinateZero
  let hpositive :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝 0) :=
    zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_zero_traceTransport_source_core
      f
      hmajorant
      hcoordinateZero
  let hsub :
      Tendsto
        (fun N : ℕ =>
          zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f -
            zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝 (0 - 0)) :=
    hdiagonal.sub hpositive
  let hzero : 0 - 0 = (0 : ℝ) :=
    sub_self 0
  let htarget :
      Tendsto
        (fun N : ℕ =>
          zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f -
            zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun value : ℝ =>
        Tendsto
          (fun N : ℕ =>
            zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f -
              zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
          atTop
          (𝓝 value))
      hzero
      hsub
  let hfun :
      (fun N : ℕ =>
        Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f)) =
        fun N : ℕ =>
          zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f -
            zetaCompletedPrimeDefectKernelPositiveRealWindow N f :=
    funext
      (fun N : ℕ =>
      zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_re_eq_diagonalDebt_sub_positiveWindow_re_traceTransport_source
        N f)
  Eq.subst
    (motive := fun stream : ℕ → ℝ =>
      Tendsto stream atTop (𝓝 0))
    hfun.symm
    htarget

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
