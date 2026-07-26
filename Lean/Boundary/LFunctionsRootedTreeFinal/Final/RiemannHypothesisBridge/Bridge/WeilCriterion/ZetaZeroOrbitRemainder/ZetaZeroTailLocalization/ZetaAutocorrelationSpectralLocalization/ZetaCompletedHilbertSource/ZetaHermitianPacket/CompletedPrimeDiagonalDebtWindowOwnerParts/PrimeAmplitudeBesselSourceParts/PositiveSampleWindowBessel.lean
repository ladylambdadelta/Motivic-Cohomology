import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimePowerSampling
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.HermitianBoundaryDefect
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingDecayParts.TraceBesselParts.PrimeWeightedSamplingTraceEnergy
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeSpectralMajorantSummability
import Mathlib.Topology.Algebra.InfiniteSum.Order

namespace Boundary
namespace LFunctions

noncomputable section

open scoped BigOperators

namespace ZetaAdmissibleFunction

/-- The boundary scalar used to dominate completed diagonal-debt real
windows. -/
noncomputable def zetaCompletedPrimeDefectKernelDiagonalDebtBoundaryScalar_hilbertFrame_source
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaCompletedGNSDiagonalDebtBoundaryForm f)

/-- The prime owner scalar inside the completed diagonal-debt boundary scalar. -/
noncomputable def zetaCompletedPrimeDefectKernelDiagonalDebtPrimeOwnerScalar_hilbertFrame_source
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f)

/-- A real three-channel scalar rearranged after subtracting a finite window. -/
theorem real_three_channel_sub_window_eq_prime_sub_window_add_arch_add_correction_hilbertFrame
    (D A R W : ℝ) :
    (D + A + R) - W = (D - W) + A + R :=
  let hstep1 :
      (D + A + R) - W =
        (D + A + R) + -W :=
    sub_eq_add_neg (D + A + R) W
  let hstep2 :
      (D + A + R) + -W =
        ((D + A) + R) + -W :=
    Eq.refl ((D + A + R) + -W)
  let hstep3 :
      ((D + A) + R) + -W =
        (D + A) + (R + -W) :=
    add_assoc (D + A) R (-W)
  let hstep4 :
      (D + A) + (R + -W) =
        (D + A) + (-W + R) :=
    congrArg (fun value : ℝ => (D + A) + value)
      (add_comm R (-W))
  let hstep5 :
      (D + A) + (-W + R) =
        ((D + A) + -W) + R :=
    (add_assoc (D + A) (-W) R).symm
  let hstep6 :
      ((D + A) + -W) + R =
        (D + (A + -W)) + R :=
    congrArg (fun value : ℝ => value + R)
      (add_assoc D A (-W))
  let hstep7 :
      (D + (A + -W)) + R =
        (D + (-W + A)) + R :=
    congrArg (fun value : ℝ => (D + value) + R)
      (add_comm A (-W))
  let hstep8 :
      (D + (-W + A)) + R =
        ((D + -W) + A) + R :=
    congrArg (fun value : ℝ => value + R)
      ((add_assoc D (-W) A).symm)
  let hstep9 :
      ((D + -W) + A) + R =
        (D - W + A) + R :=
    congrArg (fun value : ℝ => (value + A) + R)
      (sub_eq_add_neg D W).symm
  let hstep10 :
      (D - W + A) + R =
      (D - W) + A + R :=
    Eq.refl ((D - W + A) + R)
  hstep1.trans
    (hstep2.trans
      (hstep3.trans
        (hstep4.trans
          (hstep5.trans
            (hstep6.trans
              (hstep7.trans
                (hstep8.trans
                  (hstep9.trans hstep10))))))))

/-- The completed diagonal-debt boundary scalar is the prime owner scalar plus
the archimedean and correction Gram channels. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtBoundaryScalar_eq_prime_add_arch_add_correction_hilbertFrame_source
    (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeDefectKernelDiagonalDebtBoundaryScalar_hilbertFrame_source f =
      zetaCompletedPrimeDefectKernelDiagonalDebtPrimeOwnerScalar_hilbertFrame_source f +
        ZetaHermitianPacketEnsemble.archimedeanPacketGram
          (zetaCompletedHermitianBoundaryDefect f) +
        ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f) :=
  let D : ℂ := zetaCompletedPrimeDefectKernelDiagonalDebt f
  let A : ℝ :=
    ZetaHermitianPacketEnsemble.archimedeanPacketGram
      (zetaCompletedHermitianBoundaryDefect f)
  let R : ℝ :=
    ZetaHermitianPacketEnsemble.correctionPacketGram
      (zetaCompletedHermitianBoundaryDefect f)
  let hform :
      zetaCompletedGNSDiagonalDebtBoundaryForm f =
        D + (A : ℂ) + (R : ℂ) :=
    Eq.refl (zetaCompletedGNSDiagonalDebtBoundaryForm f)
  let hstep1 :
      Complex.re (D + (A : ℂ) + (R : ℂ)) =
        Complex.re (D + (A : ℂ)) + Complex.re (R : ℂ) :=
    Complex.add_re (D + (A : ℂ)) (R : ℂ)
  let hstep2 :
      Complex.re (D + (A : ℂ)) + Complex.re (R : ℂ) =
        (Complex.re D + Complex.re (A : ℂ)) + Complex.re (R : ℂ) :=
    congrArg
      (fun value : ℝ => value + Complex.re (R : ℂ))
      (Complex.add_re D (A : ℂ))
  let hstep3 :
      (Complex.re D + Complex.re (A : ℂ)) + Complex.re (R : ℂ) =
        (Complex.re D + A) + Complex.re (R : ℂ) :=
    congrArg
      (fun value : ℝ => (Complex.re D + value) + Complex.re (R : ℂ))
      (Complex.ofReal_re A)
  let hstep4 :
      (Complex.re D + A) + Complex.re (R : ℂ) =
        (Complex.re D + A) + R :=
    congrArg
      (fun value : ℝ => (Complex.re D + A) + value)
      (Complex.ofReal_re R)
  let hstep5 :
      (Complex.re D + A) + R =
        Complex.re D + A + R :=
    Eq.refl ((Complex.re D + A) + R)
  let hre :
      Complex.re (D + (A : ℂ) + (R : ℂ)) =
        Complex.re D + A + R :=
    hstep1.trans (hstep2.trans (hstep3.trans (hstep4.trans hstep5)))
  let htarget :
      Complex.re D + A + R =
        zetaCompletedPrimeDefectKernelDiagonalDebtPrimeOwnerScalar_hilbertFrame_source f +
          ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) +
          ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) :=
    Eq.refl (Complex.re D + A + R)
  Eq.trans
    (congrArg Complex.re hform)
    (Eq.subst
      (motive := fun value : ℝ =>
        value =
          zetaCompletedPrimeDefectKernelDiagonalDebtPrimeOwnerScalar_hilbertFrame_source f +
            ZetaHermitianPacketEnsemble.archimedeanPacketGram
              (zetaCompletedHermitianBoundaryDefect f) +
            ZetaHermitianPacketEnsemble.correctionPacketGram
              (zetaCompletedHermitianBoundaryDefect f))
      htarget.symm
      hre)

/-- A finite completed prime diagonal-debt real window is the finite sum of
real diagonal-debt coordinates over that window. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_eq_sum_re_hilbertFrame_source
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f =
      ∑ index in ZetaPrimePowerIndex.window N,
        Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f) :=
  Complex.re_sum
    (ZetaPrimePowerIndex.window N)
    (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f)

/-- The completed prime diagonal-debt coordinate stream is summable at the
Hilbert-frame source level. -/
theorem zetaCompletedPrimeSpectralCoordinateMajorant_summable_hilbertFrame_source
    (f : ZetaAdmissibleFunction) (Cpos : ℝ) (kpos : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (Cneg : ℝ) (kneg : ℕ)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
  let hpositiveWeighted :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) :=
    zetaCompletedPrimeSpectralAmplitudeIndex_normSq_summable_traceEnergy_source
      f Cpos kpos hpos
  let hoppositeWeighted :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f‖ ^ 2) :=
    (zetaCompletedPrimeSpectralAmplitudeIndex_normSq_summable_traceEnergy_source
      (ZetaAdmissibleFunction.reflect f) Cneg kneg hneg).congr
      (fun index : ZetaPrimePowerIndex =>
        let hpositiveReflect :
            ‖zetaCompletedPrimeSpectralAmplitudeIndex index
                (ZetaAdmissibleFunction.reflect f)‖ ^ 2 =
              zetaCompletedPrimePositiveWeightedSampleNormSq index
                (ZetaAdmissibleFunction.reflect f) :=
          zetaCompletedPrimeSpectralAmplitudeIndex_norm_sq_eq_weightedSampleNormSq
            index (ZetaAdmissibleFunction.reflect f)
        let hoppositeWeighted :
            zetaCompletedPrimeOppositeWeightedSampleNormSq index f =
              zetaCompletedPrimePositiveWeightedSampleNormSq index
                (ZetaAdmissibleFunction.reflect f) :=
          zetaCompletedPrimeOppositeWeightedSampleNormSq_eq_positive_reflect
            index f
        let hoppositeNorm :
            ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f‖ ^ 2 =
              zetaCompletedPrimeOppositeWeightedSampleNormSq index f :=
          zetaCompletedPrimeOppositeSpectralAmplitudeIndex_norm_sq_eq_weightedSampleNormSq
            index f
        hpositiveReflect.trans
          (hoppositeWeighted.symm.trans hoppositeNorm.symm))
  (hpositiveWeighted.add hoppositeWeighted).congr
    (fun index : ZetaPrimePowerIndex =>
      Eq.refl
        (‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 +
          ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f‖ ^ 2))

theorem zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_spectralPolynomialBounds_hilbertFrame_source
    (f : ZetaAdmissibleFunction) (Cpos Cneg : ℝ) (kpos kneg : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
  zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_spectralPolynomialBounds
    f Cpos kpos Cneg kneg hpos hneg

/-- The completed prime diagonal-debt coordinate stream is summable from the
Hilbert-frame spectral-coordinate majorant. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_summable_hilbertFrame_source
    (f : ZetaAdmissibleFunction) (Cpos : ℝ) (kpos : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (Cneg : ℝ) (kneg : ℕ)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f) :=
  summable_zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_of_spectralMajorant
    f
    (zetaCompletedPrimeSpectralCoordinateMajorant_summable_hilbertFrame_source
      f Cpos kpos hpos Cneg kneg hneg)

theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_summable_of_spectralPolynomialBounds_hilbertFrame_source
    (f : ZetaAdmissibleFunction) (Cpos Cneg : ℝ) (kpos kneg : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f) :=
  summable_zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_of_spectralMajorant
    f
    (zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_spectralPolynomialBounds_hilbertFrame_source
      f Cpos Cneg kpos kneg hpos hneg)

/-- The real completed prime diagonal-debt coordinate stream has the real part
of its raw coordinate presentation as its sum. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_hasSum_coordinateTsum_hilbertFrame_source
    (f : ZetaAdmissibleFunction) (Cpos Cneg : ℝ) (kpos kneg : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
      (Complex.re
        (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f)) :=
  let hcomplex :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f)
        (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) :=
    (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_summable_hilbertFrame_source
      f Cpos kpos hpos Cneg kneg hneg).hasSum
  (RCLike.reCLM : ℂ →L[ℝ] ℝ).hasSum hcomplex

theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_hasSum_coordinateTsum_of_spectralPolynomialBounds_hilbertFrame_source
    (f : ZetaAdmissibleFunction) (Cpos Cneg : ℝ) (kpos kneg : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
      (Complex.re
        (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f)) :=
  let hcomplex :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f)
        (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) :=
    (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_summable_of_spectralPolynomialBounds_hilbertFrame_source
      f Cpos Cneg kpos kneg hpos hneg).hasSum
  (RCLike.reCLM : ℂ →L[ℝ] ℝ).hasSum hcomplex

/-- Diagonal-debt real-coordinate `HasSum` inputs for a probe and its
reflection give Hilbert-frame spectral-coordinate majorant summability. -/
theorem zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_hilbertFrame_source
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
  zetaCompletedPrimeSpectralCoordinateMajorant_summable_owner f

/-- Diagonal-debt real-coordinate `HasSum` inputs give Hilbert-frame complex
summability of the completed diagonal-debt coordinate stream. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_summable_of_diagonalDebtCoordinate_re_hasSum_hilbertFrame_source
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
        zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f) :=
  summable_zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_of_spectralMajorant
    f
    (zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_hilbertFrame_source
      f C Creflect hhasSum hhasSumReflect)

/-- Diagonal-debt real-coordinate `HasSum` inputs reconstruct the real part of
the raw completed diagonal-debt coordinate presentation. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_hasSum_coordinateTsum_of_diagonalDebtCoordinate_re_hasSum_hilbertFrame_source
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
        Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
      (Complex.re
        (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f)) :=
  let hcomplex :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f)
        (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) :=
    (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_summable_of_diagonalDebtCoordinate_re_hasSum_hilbertFrame_source
      f C Creflect hhasSum hhasSumReflect).hasSum
  (RCLike.reCLM : ℂ →L[ℝ] ℝ).hasSum hcomplex

/-- A positive completed prime face coordinate is bounded by its completed
diagonal-debt coordinate real scalar. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_le_diagonalDebtCoordinate_re_hilbertFrame_source
    (index : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 ≤
      Complex.re
        (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f) :=
  let hcoordinate :
      Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f) =
        Complex.normSq
            (zetaCompletedPrimeSpectralAmplitudeIndex index f) +
          Complex.normSq
            (zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f) :=
    zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_eq_normSq_add_normSq
      index f
  let hpositiveNorm :
      ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 =
        Complex.normSq
          (zetaCompletedPrimeSpectralAmplitudeIndex index f) :=
    (Complex.normSq_eq_norm_sq
      (zetaCompletedPrimeSpectralAmplitudeIndex index f)).symm
  let hoppositeNonnegative :
      0 ≤
        Complex.normSq
          (zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f) :=
    Complex.normSq_nonneg
      (zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f)
  let hleftLe :
      Complex.normSq
          (zetaCompletedPrimeSpectralAmplitudeIndex index f) ≤
        Complex.normSq
            (zetaCompletedPrimeSpectralAmplitudeIndex index f) +
          Complex.normSq
            (zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f) :=
    le_add_of_nonneg_right hoppositeNonnegative
  Eq.subst
    (motive := fun value : ℝ =>
      ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 ≤ value)
    hcoordinate.symm
    (Eq.subst
      (motive := fun value : ℝ =>
        value ≤
          Complex.normSq
              (zetaCompletedPrimeSpectralAmplitudeIndex index f) +
            Complex.normSq
              (zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f))
      hpositiveNorm.symm
      hleftLe)

/-- A positive completed prime face window is bounded by the completed
diagonal-debt real window. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_windowSubtrace_le_diagonalDebtRealWindow_hilbertFrame_source
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (∑ index in ZetaPrimePowerIndex.window N,
      ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) ≤
      zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f :=
  let hsum :
      (∑ index in ZetaPrimePowerIndex.window N,
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) ≤
        ∑ index in ZetaPrimePowerIndex.window N,
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f) :=
    Finset.sum_le_sum
      (fun index membership =>
        zetaCompletedPrimeSpectralAmplitudeIndex_normSq_le_diagonalDebtCoordinate_re_hilbertFrame_source
          index f)
  let hrealWindow :
      zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f =
        ∑ index in ZetaPrimePowerIndex.window N,
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f) :=
    zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_eq_sum_re_hilbertFrame_source
      N f
  Eq.subst
    (motive := fun value : ℝ =>
      (∑ index in ZetaPrimePowerIndex.window N,
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) ≤ value)
    hrealWindow.symm
    hsum

/-- Every finite completed diagonal-debt real window is bounded by the real part
of the raw completed diagonal-debt coordinate presentation. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_le_coordinateTsumRe_hilbertFrame_source
    (N : ℕ) (f : ZetaAdmissibleFunction) (Cpos Cneg : ℝ) (kpos kneg : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f ≤
      Complex.re
        (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) :=
  let hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        (Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f)) :=
    zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_hasSum_coordinateTsum_hilbertFrame_source
      f Cpos Cneg kpos kneg hpos hneg
  let hnonnegative :
      ∀ index : ZetaPrimePowerIndex,
        0 ≤
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f) :=
    fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_nonnegative
        index f
  let hsum :
      (∑ index in ZetaPrimePowerIndex.window N,
        Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f)) ≤
        Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) :=
    sum_le_hasSum
      (ZetaPrimePowerIndex.window N)
      (fun index membership => hnonnegative index)
      hhasSum
  Eq.subst
    (motive := fun value : ℝ =>
      value ≤
        Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f))
    (zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_eq_sum_re_hilbertFrame_source
      N f).symm
    hsum

/-- Completed diagonal-debt real windows are uniformly bounded at the
Hilbert-frame source level. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_upperBound_hilbertFrame_source
    (f : ZetaAdmissibleFunction) (Cpos Cneg : ℝ) (kpos kneg : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    ∃ C : ℝ,
      ∀ N : ℕ,
        zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f ≤ C :=
  ⟨Complex.re
      (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f),
    fun N : ℕ =>
      zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_le_coordinateTsumRe_hilbertFrame_source
        N f Cpos Cneg kpos kneg hpos hneg⟩

/-- A diagonal-debt real-coordinate `HasSum` directly bounds all completed
diagonal-debt real windows. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_upperBound_of_diagonalDebtCoordinate_re_hasSum_hilbertFrame_source
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        C) :
    ∃ B : ℝ,
      ∀ N : ℕ,
        zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f ≤ B :=
  let hnonnegative :
      ∀ index : ZetaPrimePowerIndex,
        0 ≤
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f) :=
    fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_nonnegative
        index f
  let hbound :
      ∀ N : ℕ,
        zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f ≤ C :=
    fun N : ℕ =>
    let hsum :
        (∑ index in ZetaPrimePowerIndex.window N,
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f)) ≤
          C :=
      sum_le_hasSum
        (ZetaPrimePowerIndex.window N)
        (fun index membership => hnonnegative index)
        hhasSum
    Eq.subst
      (motive := fun value : ℝ => value ≤ C)
      (zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_eq_sum_re_hilbertFrame_source
        N f).symm
      hsum
  ⟨C, hbound⟩

/-- A diagonal-debt real-window upper bound gives a Hilbert-amplitude
norm-square window upper bound. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_window_upperBound_of_diagonalDebtRealWindow_upperBound_hilbertFrame
    (f : ZetaAdmissibleFunction)
    (hdiagonal :
      ∃ C : ℝ,
        ∀ N : ℕ,
          zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f ≤ C) :
    ∃ C : ℝ,
      ∀ N : ℕ,
        (∑ index in ZetaPrimePowerIndex.window N,
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) ≤ C :=
  match hdiagonal with
  | ⟨C, hC⟩ =>
      ⟨C,
        fun N : ℕ =>
          le_trans
            (zetaCompletedPrimeSpectralAmplitudeIndex_normSq_windowSubtrace_le_diagonalDebtRealWindow_hilbertFrame_source
              N f)
            (hC N)⟩

/-- Genuine-window Hilbert-amplitude norm-square sums are uniformly bounded. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_window_upperBound_hilbertFrame_source
    (f : ZetaAdmissibleFunction) (Cpos Cneg : ℝ) (kpos kneg : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    ∃ C : ℝ,
      ∀ N : ℕ,
        (∑ index in ZetaPrimePowerIndex.window N,
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) ≤ C :=
  zetaCompletedPrimeSpectralAmplitudeIndex_normSq_window_upperBound_of_diagonalDebtRealWindow_upperBound_hilbertFrame
    f
    (zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_upperBound_hilbertFrame_source
      f Cpos Cneg kpos kneg hpos hneg)

theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_window_upperBound_of_spectralPolynomialBounds_hilbertFrame_source
    (f : ZetaAdmissibleFunction) (Cpos Cneg : ℝ) (kpos kneg : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    ∃ B : ℝ,
      ∀ N : ℕ,
        (∑ index in ZetaPrimePowerIndex.window N,
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) ≤ B :=
  zetaCompletedPrimeSpectralAmplitudeIndex_normSq_window_upperBound_of_diagonalDebtRealWindow_upperBound_hilbertFrame
    f
    (zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_upperBound_of_diagonalDebtCoordinate_re_hasSum_hilbertFrame_source
      f (Complex.re
        (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f))
      (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_hasSum_coordinateTsum_of_spectralPolynomialBounds_hilbertFrame_source
        f Cpos Cneg kpos kneg hpos hneg))

theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_window_upperBound_of_diagonalDebtCoordinate_re_hasSum_hilbertFrame_source
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        C) :
    ∃ B : ℝ,
      ∀ N : ℕ,
        (∑ index in ZetaPrimePowerIndex.window N,
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) ≤ B :=
  zetaCompletedPrimeSpectralAmplitudeIndex_normSq_window_upperBound_of_diagonalDebtRealWindow_upperBound_hilbertFrame
    f
    (zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_upperBound_of_diagonalDebtCoordinate_re_hasSum_hilbertFrame_source
      f C hhasSum)

theorem zetaCompletedPrimePositiveWeightedSampleNormSq_window_eq_amplitudeNormSqWindow_hilbertFrame
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (∑ index in ZetaPrimePowerIndex.window N,
      zetaCompletedPrimePositiveWeightedSampleNormSq index f) =
      ∑ index in ZetaPrimePowerIndex.window N,
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 :=
  Finset.sum_congr (Eq.refl (ZetaPrimePowerIndex.window N))
    (fun index membership =>
      (zetaCompletedPrimeSpectralAmplitudeIndex_norm_sq_eq_weightedSampleNormSq
        index f).symm)

theorem zetaCompletedPrimePositiveWeightedSampleNormSq_window_upperBound_of_amplitudeNormSqWindow_upperBound_hilbertFrame
    (f : ZetaAdmissibleFunction)
    (hamplitude :
      ∃ C : ℝ,
        ∀ N : ℕ,
          (∑ index in ZetaPrimePowerIndex.window N,
            ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) ≤ C) :
    ∃ C : ℝ,
      ∀ N : ℕ,
        (∑ index in ZetaPrimePowerIndex.window N,
          zetaCompletedPrimePositiveWeightedSampleNormSq index f) ≤ C :=
  match hamplitude with
  | ⟨C, hC⟩ =>
      ⟨C,
        fun N : ℕ =>
          Eq.subst
            (motive := fun value : ℝ => value ≤ C)
            (zetaCompletedPrimePositiveWeightedSampleNormSq_window_eq_amplitudeNormSqWindow_hilbertFrame
              N f).symm
            (hC N)⟩

theorem zetaCompletedPrimePositiveWeightedSampleNormSq_window_upperBound_hilbertFrame_source
    (f : ZetaAdmissibleFunction) (Cpos Cneg : ℝ) (kpos kneg : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    ∃ C : ℝ,
      ∀ N : ℕ,
        (∑ index in ZetaPrimePowerIndex.window N,
          zetaCompletedPrimePositiveWeightedSampleNormSq index f) ≤ C :=
  zetaCompletedPrimePositiveWeightedSampleNormSq_window_upperBound_of_amplitudeNormSqWindow_upperBound_hilbertFrame
    f
    (zetaCompletedPrimeSpectralAmplitudeIndex_normSq_window_upperBound_hilbertFrame_source
      f Cpos Cneg kpos kneg hpos hneg)

theorem zetaCompletedPrimePositiveWeightedSampleNormSq_window_upperBound_of_spectralPolynomialBounds_hilbertFrame_source
    (f : ZetaAdmissibleFunction) (Cpos Cneg : ℝ) (kpos kneg : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    ∃ C : ℝ,
      ∀ N : ℕ,
        (∑ index in ZetaPrimePowerIndex.window N,
          zetaCompletedPrimePositiveWeightedSampleNormSq index f) ≤ C :=
  zetaCompletedPrimePositiveWeightedSampleNormSq_window_upperBound_of_amplitudeNormSqWindow_upperBound_hilbertFrame
    f
    (zetaCompletedPrimeSpectralAmplitudeIndex_normSq_window_upperBound_of_spectralPolynomialBounds_hilbertFrame_source
      f Cpos Cneg kpos kneg hpos hneg)

theorem zetaCompletedPrimePositiveWeightedSampleNormSq_window_upperBound_of_diagonalDebtCoordinate_re_hasSum_hilbertFrame_source
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        C) :
    ∃ B : ℝ,
      ∀ N : ℕ,
        (∑ index in ZetaPrimePowerIndex.window N,
          zetaCompletedPrimePositiveWeightedSampleNormSq index f) ≤ B :=
  zetaCompletedPrimePositiveWeightedSampleNormSq_window_upperBound_of_amplitudeNormSqWindow_upperBound_hilbertFrame
    f
    (zetaCompletedPrimeSpectralAmplitudeIndex_normSq_window_upperBound_of_diagonalDebtCoordinate_re_hasSum_hilbertFrame_source
      f C hhasSum)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
