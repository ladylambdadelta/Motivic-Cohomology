import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Annihilator.Density.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingDecayParts.TraceBesselParts.PrimeWeightedSamplingBesselSource
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeSpectralMajorantSummability
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.SpectralMajorant
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.OwnerParts.Part07
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.HolographicTraceSeparationParts.DiagonalResidualFunctionalParts.TraceScalarPrimitives

/-!
# Diagonal-debt annihilator source

This file owns the direct completed-zero annihilator representation of the
completed diagonal-debt coordinate residual.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The diagonal-debt source only needs unconditional trace-Bessel summability;
the historical window-limit hypotheses are compatibility inputs and do not
belong in this upstream owner. -/
theorem zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_positiveRealWindowLimit
    (f : ZetaAdmissibleFunction) (C Creflect : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        C)
    (hhasSumReflect :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate
              index (ZetaAdmissibleFunction.reflect f)))
        Creflect) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
  zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_diagonalDebt_owner
    f C Creflect hhasSum hhasSumReflect

/-- A completed-zero coordinate functional carries the diagonal-debt residual
at the selected probe. -/
def DiagonalDebtCoordinateFunctionalRepresents
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (f : ZetaAdmissibleFunction)
    (L : ZetaCompletedZeroCoordinateL1 →L[ℂ] ℂ) : Prop :=
  ((Complex.re
      (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) : ℝ) :
    ℂ) =
    L
      (zetaCompletedZeroSideCoordinateL1LinearMap
        hbranch hpartialOneTwo hcompactOneTwo hfinite
        hpartialLeft hcompactBoundary f)

/-- A completed-zero coordinate functional vanishes on all admissible probe
coordinates. -/
def DiagonalDebtCoordinateFunctionalVanishes
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (L : ZetaCompletedZeroCoordinateL1 →L[ℂ] ℂ) : Prop :=
  ∀ g : ZetaAdmissibleFunction,
    L
      (zetaCompletedZeroSideCoordinateL1LinearMap
      hbranch hpartialOneTwo hcompactOneTwo hfinite
      hpartialLeft hcompactBoundary g) = 0

/-- The completed diagonal coordinate residual expands as one combined
positive-coordinate plus two-face trace scalar. -/
theorem diagonalDebtCoordinateResidual_re_eq_positiveCoordinate_add_twoFace_source
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f +
        Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
  let hexpansion :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f +
          zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f =
        zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f :=
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_add_twoFace_eq_diagonalDebtCoordinateTsum
      f
      hmajorant
  let hdiagonal :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        Complex.re
          (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f +
            zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
    congrArg Complex.re hexpansion.symm
  let hadd :
      Complex.re
          (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f +
            zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f) +
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
    Complex.add_re
      (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f)
      (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)
  let hpositive :
      Complex.re (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f) +
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f +
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
    Eq.refl
      (Complex.re (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f) +
        Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f))
  Eq.trans hdiagonal (Eq.trans hadd hpositive)

/-- Explicit diagonal-debt real-coordinate `HasSum` inputs expand the
completed diagonal coordinate residual as one combined positive-coordinate
plus two-face trace scalar. -/
theorem diagonalDebtCoordinateResidual_re_eq_positiveCoordinate_add_twoFace_of_diagonalDebtCoordinate_re_hasSum_source
    (f : ZetaAdmissibleFunction) (C Creflect : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        C)
    (hhasSumReflect :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate
              index (ZetaAdmissibleFunction.reflect f)))
        Creflect) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f +
        Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
  let hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
    zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_positiveRealWindowLimit
      f C Creflect hhasSum hhasSumReflect
  let hexpansion :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f +
          zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f =
        zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f :=
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_add_twoFace_eq_diagonalDebtCoordinateTsum
      f hmajorant
  let hdiagonal :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        Complex.re
          (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f +
            zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
    congrArg Complex.re hexpansion.symm
  let hadd :
      Complex.re
          (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f +
            zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f) +
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
    Complex.add_re
      (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f)
      (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)
  let hpositive :
      Complex.re (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f) +
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f +
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
    Eq.refl
      (Complex.re (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f) +
        Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f))
  Eq.trans hdiagonal (Eq.trans hadd hpositive)

/-- The time-side trace scalar is the completed off-diagonal channel. -/
theorem completedPrimeTraceTimeScalar_eq_offDiagonalChannel_source
    (f : ZetaAdmissibleFunction) :
    completedPrimeTraceTimeScalar f =
      completedPrimeOffDiagonalChannel f :=
  (completedPrimeTraceTimeScalar_eq f).trans
    (completedPrimeOffDiagonalChannel_eq_primePowerContribution_re f).symm

/-- The spectral-side trace scalar is the negative completed two-face real
coefficient. -/
theorem completedPrimeTraceSpectralScalar_eq_neg_twoFace_source
    (f : ZetaAdmissibleFunction) :
    completedPrimeTraceSpectralScalar f =
      -Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
  let B : ℂ := zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f
  let T : ℂ := zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f
  let hboundary : B = -T :=
    zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient_eq_neg_matrixCoefficient
      f
  let hboundaryRe_start :
      Complex.re B = Complex.re (-T) :=
    congrArg Complex.re hboundary
  let hboundaryRe_neg :
      Complex.re (-T) = -Complex.re T :=
    Complex.neg_re T
  let hboundaryRe :
      Complex.re B = -Complex.re T :=
    hboundaryRe_start.trans hboundaryRe_neg
  let hspectral :
      completedSpectralPrimeOffDiagonalChannel f =
        Complex.re B :=
    completedSpectralPrimeOffDiagonalChannel_eq_completedTwoFaceBoundaryCoefficient_re
      f
  let htrace :
      completedPrimeTraceSpectralScalar f =
        completedSpectralPrimeOffDiagonalChannel f :=
    (completedSpectralPrimeOffDiagonalChannel_eq_spectralSampleContribution_re
      f).trans
      (completedPrimeTraceSpectralScalar_eq f).symm
  let htarget :
      -Complex.re T =
        -Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
    Eq.refl (-Complex.re T)
  htrace.trans (hspectral.trans (hboundaryRe.trans htarget))

/-- The completed prime trace functional gap is the off-diagonal channel plus
the completed two-face real coefficient. -/
theorem completedPrimeTraceFunctionalGap_eq_offDiagonal_add_twoFace_source
    (f : ZetaAdmissibleFunction) :
    completedPrimeTraceFunctionalGap f =
      completedPrimeOffDiagonalChannel f +
        Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
  let timeScalar : ℝ := completedPrimeTraceTimeScalar f
  let spectralScalar : ℝ := completedPrimeTraceSpectralScalar f
  let offDiagonal : ℝ := completedPrimeOffDiagonalChannel f
  let twoFace : ℝ :=
    Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)
  let hgap :
      completedPrimeTraceFunctionalGap f =
        timeScalar - spectralScalar :=
    completedPrimeTraceFunctionalGap_eq f
  let htime :
      timeScalar = offDiagonal :=
    completedPrimeTraceTimeScalar_eq_offDiagonalChannel_source f
  let hspectral :
      spectralScalar = -twoFace :=
    completedPrimeTraceSpectralScalar_eq_neg_twoFace_source f
  let hsub :
      timeScalar - spectralScalar = timeScalar + -spectralScalar :=
    sub_eq_add_neg timeScalar spectralScalar
  let htimeTransport :
      timeScalar + -spectralScalar = offDiagonal + -spectralScalar :=
    congrArg (fun value : ℝ => value + -spectralScalar) htime
  let hspectralTransport :
      offDiagonal + -spectralScalar = offDiagonal + -(-twoFace) :=
    congrArg (fun value : ℝ => offDiagonal + -value) hspectral
  let hdoubleNeg :
      offDiagonal + -(-twoFace) = offDiagonal + twoFace :=
    congrArg (fun value : ℝ => offDiagonal + value) (neg_neg twoFace)
  let htarget :
      offDiagonal + twoFace =
        completedPrimeOffDiagonalChannel f +
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
    Eq.refl (offDiagonal + twoFace)
  hgap.trans
    (hsub.trans
      (htimeTransport.trans
        (hspectralTransport.trans
          (hdoubleNeg.trans htarget))))

/-- The completed diagonal-debt coordinate residual is the trace functional
gap plus the raw positive/off-diagonal mismatch. -/
theorem diagonalDebtCoordinateResidual_re_eq_traceFunctionalGap_add_positiveOffDiagonalGap_source
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      completedPrimeTraceFunctionalGap f +
        completedPrimePositiveOffDiagonalGap f :=
  let positive : ℝ :=
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f
  let offDiagonal : ℝ :=
    completedPrimeOffDiagonalChannel f
  let twoFace : ℝ :=
    Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)
  let traceGap : ℝ :=
    completedPrimeTraceFunctionalGap f
  let positiveGap : ℝ :=
    completedPrimePositiveOffDiagonalGap f
  let hdiagonal :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        positive + twoFace :=
    diagonalDebtCoordinateResidual_re_eq_positiveCoordinate_add_twoFace_source
      f hmajorant
  let htrace :
      traceGap = offDiagonal + twoFace :=
    completedPrimeTraceFunctionalGap_eq_offDiagonal_add_twoFace_source
      f
  let hgap :
      positiveGap = positive - offDiagonal :=
    completedPrimePositiveOffDiagonalGap_eq f
  let hsub :
      (positive + twoFace) - (offDiagonal + twoFace) =
        positive - offDiagonal :=
    add_sub_add_right_eq_sub positive offDiagonal twoFace
  let hsum :
      positive + twoFace =
        (positive - offDiagonal) + (offDiagonal + twoFace) :=
    sub_eq_iff_eq_add.mp hsub
  let hgapTransport :
      (positive - offDiagonal) + (offDiagonal + twoFace) =
        positiveGap + (offDiagonal + twoFace) :=
    congrArg
      (fun value : ℝ => value + (offDiagonal + twoFace))
      hgap.symm
  let htraceTransport :
      positiveGap + (offDiagonal + twoFace) =
        positiveGap + traceGap :=
    congrArg
      (fun value : ℝ => positiveGap + value)
      htrace.symm
  let hcomm :
      positiveGap + traceGap = traceGap + positiveGap :=
    add_comm positiveGap traceGap
  let htargetDef :
      traceGap + positiveGap =
        completedPrimeTraceFunctionalGap f +
          completedPrimePositiveOffDiagonalGap f :=
    Eq.refl (traceGap + positiveGap)
  hdiagonal.trans
    (hsum.trans
      (hgapTransport.trans
        (htraceTransport.trans
          (hcomm.trans htargetDef))))

/-- Independent vanishing of the trace gap and the positive/off-diagonal gap
annihilates the diagonal-debt coordinate residual. -/
theorem diagonalDebtCoordinateResidual_re_eq_zero_of_traceGap_zero_and_positiveOffDiagonalGap_zero_source
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (htraceZero : completedPrimeTraceFunctionalGap f = 0)
    (hpositiveGapZero : completedPrimePositiveOffDiagonalGap f = 0) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      0 :=
  let hdecomposition :
      Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        completedPrimeTraceFunctionalGap f +
          completedPrimePositiveOffDiagonalGap f :=
    diagonalDebtCoordinateResidual_re_eq_traceFunctionalGap_add_positiveOffDiagonalGap_source
      f hmajorant
  let htraceTransport :
      completedPrimeTraceFunctionalGap f +
          completedPrimePositiveOffDiagonalGap f =
        0 + completedPrimePositiveOffDiagonalGap f :=
    congrArg
      (fun value : ℝ =>
        value + completedPrimePositiveOffDiagonalGap f)
      htraceZero
  let hpositiveTransport :
      0 + completedPrimePositiveOffDiagonalGap f = 0 + 0 :=
    congrArg
      (fun value : ℝ => 0 + value)
      hpositiveGapZero
  let haddZero :
      (0 : ℝ) + 0 = 0 :=
    zero_add (0 : ℝ)
  hdecomposition.trans
    (htraceTransport.trans
      (hpositiveTransport.trans haddZero))

/-- Once the raw positive/off-diagonal mismatch vanishes, the diagonal-debt
coordinate residual is the trace functional gap. -/
theorem diagonalDebtCoordinateResidual_re_eq_completedPrimeTraceFunctionalGap_of_positiveOffDiagonalGap_eq_zero_source
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hgapZero : completedPrimePositiveOffDiagonalGap f = 0) :
    Complex.re
        (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      completedPrimeTraceFunctionalGap f :=
  let hdecomposition :
      Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        completedPrimeTraceFunctionalGap f +
          completedPrimePositiveOffDiagonalGap f :=
    diagonalDebtCoordinateResidual_re_eq_traceFunctionalGap_add_positiveOffDiagonalGap_source
      f hmajorant
  let hgapTransport :
      completedPrimeTraceFunctionalGap f +
          completedPrimePositiveOffDiagonalGap f =
        completedPrimeTraceFunctionalGap f + 0 :=
    congrArg
      (fun value : ℝ => completedPrimeTraceFunctionalGap f + value)
      hgapZero
  let haddZero :
      completedPrimeTraceFunctionalGap f + 0 =
        completedPrimeTraceFunctionalGap f :=
    add_zero (completedPrimeTraceFunctionalGap f)
  hdecomposition.trans (hgapTransport.trans haddZero)

/-- The off-diagonal/positive-coordinate comparison kills the named raw
positive/off-diagonal mismatch. -/
theorem completedPrimePositiveOffDiagonalGap_eq_zero_of_offDiagonal_eq_positiveCoordinate_source
    (f : ZetaAdmissibleFunction)
    (hoffPositive :
      completedPrimeOffDiagonalChannel f =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f) :
    completedPrimePositiveOffDiagonalGap f = 0 :=
  let hpositiveOffDiagonal :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
        completedPrimeOffDiagonalChannel f :=
    hoffPositive.symm
  let hsub :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f -
          completedPrimeOffDiagonalChannel f =
        0 :=
    sub_eq_zero.mpr hpositiveOffDiagonal
  (completedPrimePositiveOffDiagonalGap_eq f).trans hsub

/-- If the diagonal coordinate scalar and completed two-face real scalar both
vanish, then the raw positive coordinate scalar vanishes. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_zero_of_diagonalCoordinate_zero_and_twoFace_zero_source
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hdiagonal :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0)
    (htwoFace :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f = 0 :=
  let hsum :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f +
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
    diagonalDebtCoordinateResidual_re_eq_positiveCoordinate_add_twoFace_source
      f hmajorant
  let htwoFaceTransport :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f + 0 =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f +
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
    congrArg
      (fun value : ℝ =>
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f + value)
      htwoFace.symm
  let hsumReverse :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f +
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) :=
    hsum.symm
  let hpositiveAddZero :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f + 0 = 0 :=
    htwoFaceTransport.trans (hsumReverse.trans hdiagonal)
  let haddZero :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f + 0 :=
    (add_zero
      (zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f)).symm
  haddZero.trans hpositiveAddZero

/-- If the raw positive coordinate scalar and completed two-face real scalar
both vanish, then the diagonal coordinate scalar vanishes. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_zero_of_positiveCoordinate_zero_and_twoFace_zero_source
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hpositive :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f = 0)
    (htwoFace :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      0 :=
  let hsum :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f +
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
    diagonalDebtCoordinateResidual_re_eq_positiveCoordinate_add_twoFace_source
      f hmajorant
  let hpositiveTransport :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f +
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        0 + Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
    congrArg
      (fun value : ℝ =>
        value + Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f))
      hpositive
  let htwoFaceTransport :
      0 + Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        0 + 0 :=
    congrArg
      (fun value : ℝ => 0 + value)
      htwoFace
  let hzero :
      0 + 0 = (0 : ℝ) :=
    zero_add 0
  hsum.trans
    (hpositiveTransport.trans
      (htwoFaceTransport.trans hzero))

/-- With completed two-face real cancellation, diagonal-coordinate
annihilation and positive-coordinate annihilation are equivalent. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_zero_iff_positiveCoordinate_zero_of_twoFace_zero_source
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (htwoFace :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0 ↔
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f = 0 :=
  Iff.intro
    (fun hdiagonal =>
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_zero_of_diagonalCoordinate_zero_and_twoFace_zero_source
        f hmajorant hdiagonal htwoFace)
    (fun hpositive =>
      zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_zero_of_positiveCoordinate_zero_and_twoFace_zero_source
        f hmajorant hpositive htwoFace)

/-- If the completed off-diagonal channel and raw positive coordinate scalar
both vanish, then the named positive/off-diagonal gap vanishes. -/
theorem completedPrimePositiveOffDiagonalGap_eq_zero_of_positive_zero_and_offDiagonal_zero_source
    (f : ZetaAdmissibleFunction)
    (hpositive :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f = 0)
    (hoffDiagonal :
      completedPrimeOffDiagonalChannel f = 0) :
    completedPrimePositiveOffDiagonalGap f = 0 :=
  let hpositiveTransport :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f -
          completedPrimeOffDiagonalChannel f =
        0 - completedPrimeOffDiagonalChannel f :=
    congrArg
      (fun value : ℝ => value - completedPrimeOffDiagonalChannel f)
      hpositive
  let hoffDiagonalTransport :
      0 - completedPrimeOffDiagonalChannel f =
        0 - 0 :=
    congrArg
      (fun value : ℝ => 0 - value)
      hoffDiagonal
  let hsubZero :
      (0 : ℝ) - 0 = 0 :=
    sub_self (0 : ℝ)
  let hraw :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f -
          completedPrimeOffDiagonalChannel f =
        0 :=
    hpositiveTransport.trans (hoffDiagonalTransport.trans hsubZero)
  (completedPrimePositiveOffDiagonalGap_eq f).trans hraw

/-- The raw completed positive coordinate total reconstructs the owner
completed positive prime-defect channel when the diagonal coordinate has been
transported to the owner diagonal debt. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_ownerPositiveChannel_of_coordinateOwner_source
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) →
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
      completedPrimeDefectKernelPositiveChannel f :=
  fun hcoordinateOwner =>
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_completedPrimeDefectKernelPositiveChannel_of_diagonalDebtCoordinateTsum_re
      f
      hmajorant
      hcoordinateOwner

/-- Explicit diagonal-debt real-coordinate `HasSum` inputs reconstruct the raw
completed positive coordinate total as the owner completed positive
prime-defect channel when the diagonal coordinate has been transported to the
owner diagonal debt. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_ownerPositiveChannel_of_coordinateOwner_of_diagonalDebtCoordinate_re_hasSum_source
    (f : ZetaAdmissibleFunction) (C Creflect : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        C)
    (hhasSumReflect :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate
              index (ZetaAdmissibleFunction.reflect f)))
        Creflect) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) →
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
      completedPrimeDefectKernelPositiveChannel f :=
  fun hcoordinateOwner =>
  let hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
    zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_positiveRealWindowLimit
      f C Creflect hhasSum hhasSumReflect
  zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_completedPrimeDefectKernelPositiveChannel_of_diagonalDebtCoordinateTsum_re
    f
    hmajorant
    hcoordinateOwner

/-- If both the completed off-diagonal channel and the raw positive coordinate
total reconstruct the owner positive channel, then they agree. -/
theorem completedPrimeOffDiagonalChannel_eq_positiveCoordinateTsumRe_of_ownerPositiveChannel_source
    (f : ZetaAdmissibleFunction)
    (hoffOwner :
      completedPrimeOffDiagonalChannel f =
        completedPrimeDefectKernelPositiveChannel f)
    (hcoordinateOwner :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
        completedPrimeDefectKernelPositiveChannel f) :
    completedPrimeOffDiagonalChannel f =
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f :=
  hoffOwner.trans hcoordinateOwner.symm

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
