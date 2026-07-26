import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.OwnerParts.ContourTomography
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.SpectralMajorant
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeSpectralMajorantSummability
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.OwnerParts.PrimePowerCoordinates
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.DiagonalTransportParts.PositiveRealWindowLimit
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimePowerPacketsParts.Part04

/-!
# Boundary two-face paired trace-kernel source

This file owns the paired rectangular trace-kernel cancellation input before
the real-shadow and ledger projections consume it.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped BigOperators Topology

namespace ZetaAdmissibleFunction

/-- A completed two-face trace-kernel zero-sum statement for the paired
autocorrelation coordinate stream.  This is the narrow analytic input; the
rectangular ledger is only its boxed exhaustion. -/
def ZetaCompletedPrimePowerAutocorrelationPairedTraceKernelHasSumZero
    (f : ZetaAdmissibleFunction) : Prop :=
  HasSum
    (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
          index f +
        zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
          index f)
    0

/-- The paired trace-kernel coordinate is the completed two-face/GNS
symmetrized coordinate. -/
theorem zetaCompletedPrimePowerAutocorrelationPairedTraceKernelCoordinate_eq_twoFaceGNS
    (index : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
        index f +
      zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
        index f =
      zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f := by
  have horiented :
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate index f =
        zetaCompletedPrimeTwoFaceGNSOrientedCoordinate index f := by
    exact
      (zetaCompletedPrimeTwoFaceGNSOrientedCoordinate_eq_weightedSeedPair
        index f).symm
  have hopposite :
      zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
          index f =
        star (zetaCompletedPrimeTwoFaceGNSOrientedCoordinate index f) := by
    have hstar :
        star
          (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
            index f) =
          zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
            index f :=
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_star_eq_opposite
        index f
    calc
      zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
          index f =
          star
            (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
              index f) := by
        exact hstar.symm
      _ =
          star (zetaCompletedPrimeTwoFaceGNSOrientedCoordinate index f) := by
        exact congrArg star horiented
  calc
    zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
        index f +
      zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
        index f =
        zetaCompletedPrimeTwoFaceGNSOrientedCoordinate index f +
          zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
            index f := by
      exact congrArg
        (fun value : ℂ =>
          value +
            zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
              index f)
        horiented
    _ =
        zetaCompletedPrimeTwoFaceGNSOrientedCoordinate index f +
          star (zetaCompletedPrimeTwoFaceGNSOrientedCoordinate index f) := by
      exact congrArg
        (fun value : ℂ =>
          zetaCompletedPrimeTwoFaceGNSOrientedCoordinate index f + value)
        hopposite
    _ =
        zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f := by
      exact Eq.refl _

/-- Summability of the paired trace-kernel coordinate stream follows from the
completed prime spectral majorant. -/
theorem zetaCompletedPrimePowerAutocorrelationPairedTraceKernel_summable
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
            index f +
          zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
            index f) := by
  exact
    (summable_zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_of_spectralMajorant
      f
      hmajorant).congr
      (fun index : ZetaPrimePowerIndex =>
        (zetaCompletedPrimePowerAutocorrelationPairedTraceKernelCoordinate_eq_twoFaceGNS
          index f).symm)

/-- Explicit diagonal-debt real-coordinate `HasSum` inputs give summability of
the paired trace-kernel coordinate stream. -/
theorem zetaCompletedPrimePowerAutocorrelationPairedTraceKernel_summable_of_diagonalDebtCoordinate_re_hasSum
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
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
            index f +
          zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
            index f) := by
  have hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
    zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_diagonalDebt_owner
      f C Creflect hhasSum hhasSumReflect
  exact
    (summable_zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_of_spectralMajorant
      f hmajorant).congr
      (fun index : ZetaPrimePowerIndex =>
        (zetaCompletedPrimePowerAutocorrelationPairedTraceKernelCoordinate_eq_twoFaceGNS
          index f).symm)

/-- The paired trace-kernel coordinate stream sums to the completed two-face
matrix coefficient. -/
theorem zetaCompletedPrimePowerAutocorrelationPairedTraceKernel_hasSum_matrixCoefficient
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
            index f +
          zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
            index f)
      (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) := by
  let paired : ZetaPrimePowerIndex → ℂ :=
    fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
          index f +
        zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
          index f
  let twoFace : ZetaPrimePowerIndex → ℂ :=
    fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f
  have hpaired : Summable paired := by
    exact zetaCompletedPrimePowerAutocorrelationPairedTraceKernel_summable f hmajorant
  have htsum :
      (∑' index : ZetaPrimePowerIndex, paired index) =
        zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f := by
    have hpoint : paired = twoFace := by
      funext index
      unfold paired
      unfold twoFace
      exact
        zetaCompletedPrimePowerAutocorrelationPairedTraceKernelCoordinate_eq_twoFaceGNS
          index f
    calc
      (∑' index : ZetaPrimePowerIndex, paired index) =
          ∑' index : ZetaPrimePowerIndex, twoFace index := by
        exact congrArg
          (fun stream : ZetaPrimePowerIndex → ℂ =>
            ∑' index : ZetaPrimePowerIndex, stream index)
          hpoint
      _ =
          zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f := by
        unfold twoFace
        exact zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_tsum_eq_matrixCoefficient
          f
  exact Eq.subst
    (motive := fun value : ℂ => HasSum paired value)
    htsum
    hpaired.hasSum

/-- Explicit diagonal-debt real-coordinate `HasSum` inputs make the paired
trace-kernel coordinate stream sum to the completed two-face matrix
coefficient. -/
theorem zetaCompletedPrimePowerAutocorrelationPairedTraceKernel_hasSum_matrixCoefficient_of_diagonalDebtCoordinate_re_hasSum
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
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
            index f +
          zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
            index f)
      (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) := by
  let paired : ZetaPrimePowerIndex → ℂ :=
    fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
          index f +
        zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
          index f
  let twoFace : ZetaPrimePowerIndex → ℂ :=
    fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f
  have hpaired : Summable paired := by
    exact
      zetaCompletedPrimePowerAutocorrelationPairedTraceKernel_summable_of_diagonalDebtCoordinate_re_hasSum
        f C Creflect hhasSum hhasSumReflect
  have htsum :
      (∑' index : ZetaPrimePowerIndex, paired index) =
        zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f := by
    have hpoint : paired = twoFace := by
      funext index
      unfold paired
      unfold twoFace
      exact
        zetaCompletedPrimePowerAutocorrelationPairedTraceKernelCoordinate_eq_twoFaceGNS
          index f
    calc
      (∑' index : ZetaPrimePowerIndex, paired index) =
          ∑' index : ZetaPrimePowerIndex, twoFace index := by
        exact congrArg
          (fun stream : ZetaPrimePowerIndex → ℂ =>
            ∑' index : ZetaPrimePowerIndex, stream index)
          hpoint
      _ =
          zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f := by
        unfold twoFace
        exact zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_tsum_eq_matrixCoefficient
          f
  exact Eq.subst
    (motive := fun value : ℂ => HasSum paired value)
    htsum
    hpaired.hasSum

/-- Vanishing of the completed two-face matrix coefficient is exactly the
remaining analytic input needed for paired trace-kernel zero-summation. -/
theorem zetaCompletedPrimePowerAutocorrelationPairedTraceKernel_hasSum_zero_of_matrixCoefficient_eq_zero
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hmatrix : zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f = 0) :
    ZetaCompletedPrimePowerAutocorrelationPairedTraceKernelHasSumZero f := by
  exact Eq.subst
    (motive := fun value : ℂ =>
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
              index f +
            zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
              index f)
        value)
    hmatrix
    (zetaCompletedPrimePowerAutocorrelationPairedTraceKernel_hasSum_matrixCoefficient
      f hmajorant)

/-- Source real-scalar vanishing of the completed two-face matrix
coefficient. -/
theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_pairedTraceKernel_source
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0 :=
  let hmajorantTransport :
      (Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0) =
        (Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0) :=
    congrArg
      (fun value : Summable (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeSpectralCoordinateMajorant index f) =>
        Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0)
      (Eq.refl hmajorant)
  Eq.mp hmajorantTransport
    (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_source f)

/-- Source vanishing of the completed two-face matrix coefficient, assembled
from its real and imaginary scalar parts. -/
theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_eq_zero_pairedTraceKernel_source
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f = 0 := by
  exact Complex.ext
    (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_pairedTraceKernel_source
      f hmajorant)
    (Eq.trans
      (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_im_eq_zero f)
      (Complex.zero_im).symm)

/-- A paired trace-kernel zero-sum gives rectangular box convergence. -/
theorem zetaCompletedPrimePowerAutocorrelationTwoFaceCoordinate_boxSum_tendsto_zero_of_pairedTraceKernel_hasSum_zero
    (f : ZetaAdmissibleFunction)
    (htrace :
      ZetaCompletedPrimePowerAutocorrelationPairedTraceKernelHasSumZero f) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ index in ZetaPrimePowerIndex.box N,
          (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
              index f +
            zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
              index f))
      Filter.atTop
      (nhds 0) := by
  exact
    ZetaPrimePowerIndex.tendsto_sum_box_zero_of_hasSum_complex
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
            index f +
          zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
            index f)
      htrace

/-- A paired trace-kernel zero-sum gives the residue-ledger cancellation
proposition. -/
theorem zetaCompletedPrimePowerAutocorrelationLedgerCancellation_of_pairedTraceKernel_hasSum_zero
    (f : ZetaAdmissibleFunction)
    (htrace :
      ZetaCompletedPrimePowerAutocorrelationPairedTraceKernelHasSumZero f) :
    ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f := by
  exact
    zetaCompletedPrimePowerAutocorrelationTwoFaceCoordinate_boxSum_tendsto_zero_of_pairedTraceKernel_hasSum_zero
      f
      htrace

/-- Source completed two-face trace-kernel zero-sum for the paired
autocorrelation coordinate stream. -/
theorem zetaCompletedPrimePowerAutocorrelationPairedTraceKernel_hasSum_zero_source
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    ZetaCompletedPrimePowerAutocorrelationPairedTraceKernelHasSumZero f := by
  exact
    zetaCompletedPrimePowerAutocorrelationPairedTraceKernel_hasSum_zero_of_matrixCoefficient_eq_zero
      f
      hmajorant
      (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_eq_zero_pairedTraceKernel_source
        f hmajorant)

/-- Source rectangular cancellation for the paired completed two-face
autocorrelation coordinate stream. -/
theorem zetaCompletedPrimePowerAutocorrelationTwoFaceCoordinate_boxSum_tendsto_zero_pairedTraceKernel_source
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ index in ZetaPrimePowerIndex.box N,
          (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
              index f +
            zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
              index f))
      Filter.atTop
      (nhds 0) := by
  exact
    zetaCompletedPrimePowerAutocorrelationTwoFaceCoordinate_boxSum_tendsto_zero_of_pairedTraceKernel_hasSum_zero
        f
      (zetaCompletedPrimePowerAutocorrelationPairedTraceKernel_hasSum_zero_source
        f hmajorant)

/-- Source residue-ledger cancellation for the paired completed two-face
autocorrelation coordinate stream. -/
theorem zetaCompletedPrimePowerAutocorrelationLedgerCancellation_pairedTraceKernel_source
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f := by
  exact
    zetaCompletedPrimePowerAutocorrelationLedgerCancellation_of_pairedTraceKernel_hasSum_zero
      f
      (zetaCompletedPrimePowerAutocorrelationPairedTraceKernel_hasSum_zero_source
        f hmajorant)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
