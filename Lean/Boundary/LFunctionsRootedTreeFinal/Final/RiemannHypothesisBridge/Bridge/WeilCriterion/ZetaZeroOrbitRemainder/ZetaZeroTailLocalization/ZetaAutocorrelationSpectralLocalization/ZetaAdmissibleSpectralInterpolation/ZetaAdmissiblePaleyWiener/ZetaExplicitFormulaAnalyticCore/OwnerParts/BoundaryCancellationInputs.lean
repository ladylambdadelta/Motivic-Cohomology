import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.OwnerParts.ContourTomography
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingDecay
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.OwnerParts.BoundaryCancellationRealShadowParts.TwoFaceWindowParts.LedgerCancellation

/-!
# Boundary cancellation owner inputs

This file owns the analytic inputs consumed by the completed prime-power
autocorrelation cancellation algebra.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped BigOperators Topology

namespace ZetaAdmissibleFunction

/-- The completed positive prime trace-energy scalar attached to an
autocorrelation probe. -/
noncomputable def zetaCompletedPrimePositiveTraceEnergy
    (f : ZetaAdmissibleFunction) : ℝ :=
  ∑' index : ZetaPrimePowerIndex,
    zetaCompletedPrimePositiveWeightedSampleNormSq index f

/-- Trace-energy reconstruction identifies the positive completed prime
weighted sample norm-square family as an absolutely convergent trace-energy
series. -/
theorem zetaCompletedPrimePositiveWeightedSampleNormSq_hasSum_traceEnergyReconstruction
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C k) :
  HasSum
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimePositiveWeightedSampleNormSq index f)
      (zetaCompletedPrimePositiveTraceEnergy f) := by
  exact
    ((completedAutocorrelationSpectralTransform_weightedPrimeSampling_summable_ownerSamplingDecay
        f C k hbound).congr
      (fun index : ZetaPrimePowerIndex =>
        (zetaCompletedPrimePositiveWeightedSampleNormSq_eq_weightedPrimeSampling
          index f).symm)).hasSum

/-- Trace-energy reconstruction gives summability of the positive completed
prime weighted sample norm-square family. -/
theorem zetaCompletedPrimePositiveWeightedSampleNormSq_summable_of_traceEnergyReconstruction
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimePositiveWeightedSampleNormSq index f) := by
  exact
    (zetaCompletedPrimePositiveWeightedSampleNormSq_hasSum_traceEnergyReconstruction
      f C k hbound).summable

/-- Boundary-cancellation input: the positive completed prime weighted sample
norm-square family is summable on autocorrelation probes. -/
theorem zetaCompletedPrimePositiveWeightedSampleNormSq_summable_boundaryCancellationInput
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimePositiveWeightedSampleNormSq index f) := by
  exact
    zetaCompletedPrimePositiveWeightedSampleNormSq_summable_of_traceEnergyReconstruction
      f C k hbound

/-! The historical real-axis route remains available as a compatibility
wrapper.  Its real-axis polynomial-bound hypothesis remains part of this
legacy interface; the repaired vertical owner chain is exposed separately at
the Hermitian-packet trace-Bessel boundary. -/

theorem zetaCompletedPrimePositiveWeightedSampleNormSq_summable_of_spectralPolynomialBound
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (_hbound : PrimeCenterSpectralPolynomialBound f C k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimePositiveWeightedSampleNormSq index f) := by
  exact
    (zetaCompletedPrimePositiveWeightedSampleNormSq_summable_boundaryCancellationInput
      f C k _hbound).congr
      (fun index : ZetaPrimePowerIndex =>
        (zetaCompletedPrimePositiveWeightedSampleNormSq_eq_weightedPrimeSampling
          index f).symm)

/-- The opposite weighted prime-center sample-square is the positive
sample-square of the reflected seed, at the boundary-cancellation owner level. -/
theorem zetaCompletedPrimeOppositeWeightedSampleNormSq_eq_positive_reflect_boundaryCancellationInput
    (index : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeOppositeWeightedSampleNormSq index f =
      zetaCompletedPrimePositiveWeightedSampleNormSq index
        (ZetaAdmissibleFunction.reflect f) := by
  exact zetaCompletedPrimeOppositeWeightedSampleNormSq_eq_positive_reflect
    index f

/-- Boundary-cancellation input: the opposite completed prime weighted sample
norm-square family is summable on autocorrelation probes. -/
theorem zetaCompletedPrimeOppositeWeightedSampleNormSq_summable_boundaryCancellationInput
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) C k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeOppositeWeightedSampleNormSq index f) := by
  exact
    (zetaCompletedPrimePositiveWeightedSampleNormSq_summable_boundaryCancellationInput
      (ZetaAdmissibleFunction.reflect f) C k hbound).congr
      (fun index : ZetaPrimePowerIndex =>
        (zetaCompletedPrimeOppositeWeightedSampleNormSq_eq_positive_reflect_boundaryCancellationInput
          index f).symm)

theorem zetaCompletedPrimeOppositeWeightedSampleNormSq_summable_of_spectralPolynomialBound
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (_hbound : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) C k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeOppositeWeightedSampleNormSq index f) := by
  exact
    (zetaCompletedPrimePositiveWeightedSampleNormSq_summable_boundaryCancellationInput
      (ZetaAdmissibleFunction.reflect f) C k _hbound).congr
      (fun index : ZetaPrimePowerIndex =>
        (zetaCompletedPrimeOppositeWeightedSampleNormSq_eq_positive_reflect_boundaryCancellationInput
          index f).symm)

/-- Boundary-cancellation input: the completed prime spectral coordinate
majorant is summable on autocorrelation probes. -/
theorem zetaCompletedPrimeSpectralCoordinateMajorant_summable_boundaryCancellationInput
    (f : ZetaAdmissibleFunction) (Cpos Cneg : ℝ) (kpos kneg : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeSpectralCoordinateMajorant index f) := by
  have hpositive :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) :=
    (zetaCompletedPrimePositiveWeightedSampleNormSq_summable_boundaryCancellationInput
      f Cpos kpos hpos).congr
      (fun index : ZetaPrimePowerIndex =>
        (zetaCompletedPrimeSpectralAmplitudeIndex_norm_sq_eq_weightedSampleNormSq
          index f).symm)
  have hopposite :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f‖ ^ 2) :=
    (zetaCompletedPrimeOppositeWeightedSampleNormSq_summable_boundaryCancellationInput
      f Cneg kneg hneg).congr
      (fun index : ZetaPrimePowerIndex =>
        (zetaCompletedPrimeOppositeSpectralAmplitudeIndex_norm_sq_eq_weightedSampleNormSq
          index f).symm)
  exact
    (hpositive.add hopposite).congr
      (fun index : ZetaPrimePowerIndex => Eq.refl
        (zetaCompletedPrimeSpectralCoordinateMajorant index f))

theorem zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_spectralPolynomialBounds
    (f : ZetaAdmissibleFunction) (Cpos Cneg : ℝ) (kpos kneg : ℕ)
    (_hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (_hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeSpectralCoordinateMajorant index f) := by
  have hpositive :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) :=
    (zetaCompletedPrimePositiveWeightedSampleNormSq_summable_of_spectralPolynomialBound
      f Cpos kpos _hpos).congr
      (fun index : ZetaPrimePowerIndex =>
        (zetaCompletedPrimeSpectralAmplitudeIndex_norm_sq_eq_weightedSampleNormSq
          index f).symm)
  have hopposite :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f‖ ^ 2) :=
    (zetaCompletedPrimeOppositeWeightedSampleNormSq_summable_of_spectralPolynomialBound
      f Cneg kneg _hneg).congr
      (fun index : ZetaPrimePowerIndex =>
        (zetaCompletedPrimeOppositeSpectralAmplitudeIndex_norm_sq_eq_weightedSampleNormSq
          index f).symm)
  exact
    (hpositive.add hopposite).congr
      (fun index : ZetaPrimePowerIndex => Eq.refl
        (zetaCompletedPrimeSpectralCoordinateMajorant index f))

/-- The finite completed two-face prime autocorrelation ledger window. -/
noncomputable def zetaCompletedPrimePowerAutocorrelationTwoFaceLedgerWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  ∑ index in ZetaPrimePowerIndex.box N,
    (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate index f +
      zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
        index f)

/-- The explicit finite two-face ledger window unfolds to the residue-ledger
window shape. -/
theorem zetaCompletedPrimePowerAutocorrelationTwoFaceLedgerWindow_eq
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimePowerAutocorrelationTwoFaceLedgerWindow N f =
      ∑ index in ZetaPrimePowerIndex.box N,
        (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate index f +
          zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
            index f) := by
  rfl

/-- The completed two-face autocorrelation coordinate family is summable. -/
theorem zetaCompletedPrimePowerAutocorrelationTwoFaceCoordinate_summable_traceReconstruction
    (f : ZetaAdmissibleFunction) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate index f +
          zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
            index f) := by
  have hsource :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate index f +
            zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
              index f)
        0 :=
    zetaCompletedPrimePowerAutocorrelationTwoFaceCoordinate_hasSum_zero_contourLedger_source
      f
  exact hsource.summable

theorem zetaCompletedPrimePowerAutocorrelationTwoFaceCoordinate_summable_of_spectralPolynomialBounds
    (f : ZetaAdmissibleFunction) (Cpos Cneg : ℝ) (kpos kneg : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate index f +
          zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
            index f) := by
  have hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
    zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_spectralPolynomialBounds
      f Cpos Cneg kpos kneg hpos hneg
  have horiented :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
            index f) :=
    (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_summable_of_spectralMajorant
      f (hsource.summable)).congr
      (fun index => Eq.refl _)
  have hopposite :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
            index f) :=
    (zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate_summable_of_spectralMajorant
      f (hsource.summable)).congr
      (fun index => Eq.refl _)
  exact horiented.add hopposite

theorem zetaCompletedPrimePowerAutocorrelationTwoFaceCoordinate_hasSum_zero_of_spectralPolynomialBounds
    (f : ZetaAdmissibleFunction) (Cpos Cneg : ℝ) (kpos kneg : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate index f +
          zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
            index f)
      0 := by
  let paired : ZetaPrimePowerIndex → ℂ :=
    fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate index f +
        zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
          index f
  have hpairedSummable : Summable paired := by
    exact zetaCompletedPrimePowerAutocorrelationTwoFaceCoordinate_summable_of_spectralPolynomialBounds
      f
  have hboxTsum :
      Filter.Tendsto
        (fun N : ℕ => ∑ index in ZetaPrimePowerIndex.box N, paired index)
        Filter.atTop
        (nhds (∑' index : ZetaPrimePowerIndex, paired index)) :=
    ZetaPrimePowerIndex.tendsto_sum_box_of_hasSum_complex
      paired (∑' index : ZetaPrimePowerIndex, paired index)
      hpairedSummable.hasSum
  have hboxZero :
      Filter.Tendsto
        (fun N : ℕ => ∑ index in ZetaPrimePowerIndex.box N, paired index)
        Filter.atTop (nhds 0) :=
    zetaCompletedPrimePowerAutocorrelationTwoFaceCoordinate_boxSum_tendsto_zero_traceKernel_source_primitive
      f
  have htotal : (∑' index : ZetaPrimePowerIndex, paired index) = 0 :=
    tendsto_nhds_unique hboxTsum hboxZero
  exact Eq.subst (motive := fun value : ℂ => HasSum paired value)
    htotal hpairedSummable.hasSum

/-- Source contour-ledger `HasSum` cancellation for the paired completed
two-face prime-power autocorrelation coordinate stream. -/
theorem zetaCompletedPrimePowerAutocorrelationTwoFaceCoordinate_hasSum_zero_contourLedger_source_core
    (f : ZetaAdmissibleFunction) :
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate index f +
          zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
            index f)
      0 := by
  let paired : ZetaPrimePowerIndex → ℂ :=
    fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate index f +
        zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
          index f
  have hpairedSummable : Summable paired := by
    exact zetaCompletedPrimePowerAutocorrelationTwoFaceCoordinate_summable_traceReconstruction
      f
  have hboxTsum :
      Filter.Tendsto
        (fun N : ℕ =>
          ∑ index in ZetaPrimePowerIndex.box N, paired index)
        Filter.atTop
        (nhds (∑' index : ZetaPrimePowerIndex, paired index)) :=
    ZetaPrimePowerIndex.tendsto_sum_box_of_hasSum_complex
      paired
      (∑' index : ZetaPrimePowerIndex, paired index)
      hpairedSummable.hasSum
  have hboxZero :
      Filter.Tendsto
        (fun N : ℕ =>
          ∑ index in ZetaPrimePowerIndex.box N, paired index)
        Filter.atTop
        (nhds 0) :=
    zetaCompletedPrimePowerAutocorrelationTwoFaceCoordinate_boxSum_tendsto_zero_traceKernel_source_primitive
      f
  have htotal :
      (∑' index : ZetaPrimePowerIndex, paired index) = 0 :=
    tendsto_nhds_unique hboxTsum hboxZero
  exact Eq.subst
    (motive := fun value : ℂ => HasSum paired value)
    htotal
    hpairedSummable.hasSum

/-- Source contour-ledger cancellation for paired two-face coordinate windows. -/
theorem zetaCompletedPrimePowerAutocorrelationTwoFaceCoordinate_boxSum_tendsto_zero_contourLedger_source
    (f : ZetaAdmissibleFunction) :
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
    zetaCompletedPrimePowerAutocorrelationTwoFaceCoordinate_boxSum_tendsto_zero_traceKernel_source_primitive
      f

/-- Source contour-ledger `HasSum` cancellation for the paired completed
two-face prime-power autocorrelation coordinate stream. -/
theorem zetaCompletedPrimePowerAutocorrelationTwoFaceCoordinate_hasSum_zero_contourLedger_source
    (f : ZetaAdmissibleFunction) :
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate index f +
          zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
            index f)
      0 := by
  exact
    zetaCompletedPrimePowerAutocorrelationTwoFaceCoordinate_hasSum_zero_contourLedger_source_core
      f

/-- Source contour-ledger cancellation for the completed two-face prime-power
autocorrelation rectangles.

This is the boxed finite-window form of the non-circular contour input.  The
source theorem above owns the stronger paired-coordinate `HasSum 0` statement;
real-shadow and ledger-window forms are algebraic consequences of this boxed
exhaustion. -/
theorem zetaCompletedPrimePowerAutocorrelationLedgerCancellation_contourLedger_source
    (f : ZetaAdmissibleFunction) :
    ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f := by
  exact
    zetaCompletedPrimePowerAutocorrelationTwoFaceCoordinate_boxSum_tendsto_zero_traceKernel_source_primitive
      f

/-- Source rectangular-window cancellation for the oriented real shadow of the
completed autocorrelation prime-power face. -/
theorem zetaCompletedPrimePowerAutocorrelationOrientedRealShadowBoxSum_tendsto_zero_traceReconstruction_source
    (f : ZetaAdmissibleFunction) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ index in ZetaPrimePowerIndex.box N,
          ((2 : ℝ) *
            Complex.re
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
                index f) : ℂ))
      Filter.atTop
      (nhds 0) := by
  exact
    zetaCompletedPrimePowerAutocorrelation_oriented_boxRealShadow_tendsto_zero_contourTomography
      f
      (zetaCompletedPrimePowerAutocorrelationLedgerCancellation_contourLedger_source
        f)

/-- Source rectangular-window cancellation for the completed paired two-face
autocorrelation coordinate stream. -/
theorem zetaCompletedPrimePowerAutocorrelationTwoFaceCoordinate_boxSum_tendsto_zero_traceReconstruction_source
    (f : ZetaAdmissibleFunction) :
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
    zetaCompletedPrimePowerAutocorrelationTwoFaceCoordinate_boxSum_tendsto_zero_contourLedger_source
      f

/-- Trace reconstruction identifies the completed paired two-face
autocorrelation coordinate stream as a zero-sum trace. -/
theorem zetaCompletedPrimePowerAutocorrelationTwoFaceCoordinate_hasSum_zero_traceReconstruction
    (f : ZetaAdmissibleFunction) :
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
            index f +
          zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
            index f)
      0 := by
  exact
    zetaCompletedPrimePowerAutocorrelationTwoFaceCoordinate_hasSum_zero_contourLedger_source
      f

/-- Trace reconstruction identifies the completed two-face autocorrelation
coordinate total with zero. -/
theorem zetaCompletedPrimePowerAutocorrelationTwoFaceCoordinate_tsum_eq_zero_traceReconstruction
    (f : ZetaAdmissibleFunction) :
    (∑' index : ZetaPrimePowerIndex,
      (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate index f +
        zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
          index f)) = 0 := by
  exact
    (zetaCompletedPrimePowerAutocorrelationTwoFaceCoordinate_hasSum_zero_traceReconstruction
      f).tsum_eq

/-- Trace reconstruction supplies convergence of the finite completed two-face
prime autocorrelation ledger windows. -/
theorem zetaCompletedPrimePowerAutocorrelationTwoFaceLedgerWindow_tendsto_zero_traceReconstruction_core
    (f : ZetaAdmissibleFunction) :
    Filter.Tendsto
      (fun N : ℕ =>
        zetaCompletedPrimePowerAutocorrelationTwoFaceLedgerWindow N f)
      Filter.atTop
      (nhds 0) := by
  have hsource :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate index f +
            zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
              index f)
        0 :=
    zetaCompletedPrimePowerAutocorrelationTwoFaceCoordinate_hasSum_zero_contourLedger_source
      f
  have hsummable :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate index f +
            zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
              index f) :=
    hsource.summable
  have hbox :
      Filter.Tendsto
        (fun N : ℕ =>
          ∑ index in ZetaPrimePowerIndex.box N,
            (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate index f +
              zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
                index f))
        Filter.atTop
        (nhds
          (∑' index : ZetaPrimePowerIndex,
            (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate index f +
              zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
                index f))) :=
    ZetaPrimePowerIndex.tendsto_sum_box_of_hasSum_complex
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate index f +
          zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
            index f)
      (∑' index : ZetaPrimePowerIndex,
        (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate index f +
          zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
            index f))
      hsummable.hasSum
  have htotal :
      (∑' index : ZetaPrimePowerIndex,
        (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate index f +
          zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
            index f)) = 0 :=
    hsource.tsum_eq
  have hwindow :
      (fun N : ℕ =>
        zetaCompletedPrimePowerAutocorrelationTwoFaceLedgerWindow N f) =
        (fun N : ℕ =>
          ∑ index in ZetaPrimePowerIndex.box N,
            (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate index f +
              zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
                index f)) := by
    funext N
    exact zetaCompletedPrimePowerAutocorrelationTwoFaceLedgerWindow_eq N f
  exact Eq.subst
    (motive := fun window : ℕ → ℂ =>
      Filter.Tendsto window Filter.atTop (nhds 0))
    hwindow.symm
    (Eq.subst
      (motive := fun value : ℂ =>
        Filter.Tendsto
          (fun N : ℕ =>
            ∑ index in ZetaPrimePowerIndex.box N,
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate index f +
                zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
                  index f))
          Filter.atTop
          (nhds value))
      htotal
      hbox)

/-- Trace reconstruction supplies convergence of twice the real part of the
rectangular oriented autocorrelation prime-power box sum. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_boxSum_twoRealPart_tendsto_zero_traceReconstruction_source
    (f : ZetaAdmissibleFunction) :
    Filter.Tendsto
      (fun N : ℕ =>
        (2 : ℝ) *
          (Complex.re
            (zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum
              N f) : ℂ))
      Filter.atTop
      (nhds 0) := by
  have hledger :
      Filter.Tendsto
        (fun N : ℕ =>
          zetaCompletedPrimePowerAutocorrelationTwoFaceLedgerWindow N f)
        Filter.atTop
        (nhds 0) :=
    zetaCompletedPrimePowerAutocorrelationTwoFaceLedgerWindow_tendsto_zero_traceReconstruction_core
      f
  have hfun :
      (fun N : ℕ =>
        (2 : ℝ) *
          (Complex.re
            (zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum
              N f) : ℂ)) =
        (fun N : ℕ =>
          zetaCompletedPrimePowerAutocorrelationTwoFaceLedgerWindow N f) := by
    funext N
    calc
      (2 : ℝ) *
          (Complex.re
            (zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum
              N f) : ℂ) =
          ∑ index in ZetaPrimePowerIndex.box N,
            ((2 : ℝ) *
              Complex.re
                (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
                  index f) : ℂ) := by
        exact
          (zetaCompletedPrimePowerAutocorrelation_oriented_boxRealShadow_eq_two_re_boxSum_source
            N
            f).symm
      _ =
          ∑ index in ZetaPrimePowerIndex.box N,
            (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate index f +
              zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
                index f) := by
        exact
          (zetaCompletedPrimePowerAutocorrelation_oriented_add_opposite_boxSum_eq_realShadow
            N
            f).symm
      _ =
          zetaCompletedPrimePowerAutocorrelationTwoFaceLedgerWindow N f := by
        exact
          (zetaCompletedPrimePowerAutocorrelationTwoFaceLedgerWindow_eq
            N
            f).symm
  exact Eq.subst
    (motive := fun window : ℕ → ℂ =>
      Filter.Tendsto window Filter.atTop (nhds 0))
    hfun.symm
    hledger

/-- Trace reconstruction supplies convergence of the finite oriented
real-shadow prime autocorrelation windows. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_boxRealShadow_tendsto_zero_traceReconstruction_source
    (f : ZetaAdmissibleFunction) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ index in ZetaPrimePowerIndex.box N,
          ((2 : ℝ) *
            Complex.re
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
                index f) : ℂ))
      Filter.atTop
      (nhds 0) := by
  have hbox :
      Filter.Tendsto
        (fun N : ℕ =>
          (2 : ℝ) *
            (Complex.re
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum
                N f) : ℂ))
        Filter.atTop
        (nhds 0) :=
    zetaCompletedPrimePowerAutocorrelation_oriented_boxSum_twoRealPart_tendsto_zero_traceReconstruction_source
      f
  have hfun :
      (fun N : ℕ =>
        ∑ index in ZetaPrimePowerIndex.box N,
          ((2 : ℝ) *
            Complex.re
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
                index f) : ℂ)) =
        (fun N : ℕ =>
          (2 : ℝ) *
            (Complex.re
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum
                N f) : ℂ)) := by
    funext N
    exact
      zetaCompletedPrimePowerAutocorrelation_oriented_boxRealShadow_eq_two_re_boxSum_source
        N
        f
  exact Eq.subst
    (motive := fun window : ℕ → ℂ =>
      Filter.Tendsto window Filter.atTop (nhds 0))
    hfun.symm
    hbox

/-- The two-face ledger window is the oriented real-shadow window. -/
theorem zetaCompletedPrimePowerAutocorrelationTwoFaceLedgerWindow_eq_orientedRealShadow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimePowerAutocorrelationTwoFaceLedgerWindow N f =
      ∑ index in ZetaPrimePowerIndex.box N,
        ((2 : ℝ) *
          Complex.re
            (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
              index f) : ℂ) := by
  exact Eq.trans
    (zetaCompletedPrimePowerAutocorrelationTwoFaceLedgerWindow_eq N f)
    (zetaCompletedPrimePowerAutocorrelation_oriented_add_opposite_boxSum_eq_realShadow
      N f)

/-- Trace reconstruction supplies convergence of the finite completed two-face
prime autocorrelation ledger windows by real-shadow transport. -/
theorem zetaCompletedPrimePowerAutocorrelationTwoFaceLedgerWindow_tendsto_zero_traceReconstruction_source
    (f : ZetaAdmissibleFunction) :
    Filter.Tendsto
      (fun N : ℕ =>
        zetaCompletedPrimePowerAutocorrelationTwoFaceLedgerWindow N f)
      Filter.atTop
      (nhds 0) := by
  exact
    zetaCompletedPrimePowerAutocorrelationTwoFaceLedgerWindow_tendsto_zero_traceReconstruction_core
      f

/-- Trace reconstruction gives convergence of finite completed two-face prime
autocorrelation ledger windows. -/
theorem zetaCompletedPrimePowerAutocorrelationTwoFaceLedgerWindow_tendsto_zero_of_traceReconstruction
    (f : ZetaAdmissibleFunction) :
    Filter.Tendsto
      (fun N : ℕ =>
        zetaCompletedPrimePowerAutocorrelationTwoFaceLedgerWindow N f)
      Filter.atTop
      (nhds 0) := by
  exact
    zetaCompletedPrimePowerAutocorrelationTwoFaceLedgerWindow_tendsto_zero_traceReconstruction_source
      f

/-- Trace reconstruction supplies the finite-window completed two-face prime
autocorrelation ledger cancellation. -/
theorem zetaCompletedPrimePowerAutocorrelationLedgerCancellation_traceReconstruction_source
    (f : ZetaAdmissibleFunction) :
    ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f := by
  exact
    zetaCompletedPrimePowerAutocorrelationLedgerCancellation_contourLedger_source
      f

/-- Trace reconstruction gives the completed prime-power autocorrelation
ledger cancellation used by the residue-ledger source layer. -/
theorem zetaCompletedPrimePowerAutocorrelationLedgerCancellation_of_traceReconstruction
    (f : ZetaAdmissibleFunction) :
    ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f := by
  exact
    zetaCompletedPrimePowerAutocorrelationLedgerCancellation_traceReconstruction_source
      f

/-- Owner source theorem for finite rectangular cancellation of the two
oriented autocorrelation prime-power faces. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_add_opposite_boxSum_tendsto_zero_owner
    (f : ZetaAdmissibleFunction) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ index in ZetaPrimePowerIndex.box N,
          (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate index f +
            zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
              index f))
      Filter.atTop
      (nhds 0) := by
  exact
    zetaCompletedPrimePowerAutocorrelation_oriented_add_opposite_boxSum_tendsto_zero_residueLedger_source
      f
      (zetaCompletedPrimePowerAutocorrelationLedgerCancellation_of_traceReconstruction
        f)

/-- Owner convergence for the rectangular real shadow of the oriented
autocorrelation prime-power face. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_boxRealShadow_tendsto_zero_owner
    (f : ZetaAdmissibleFunction) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ index in ZetaPrimePowerIndex.box N,
          ((2 : ℝ) *
            Complex.re
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
                index f) : ℂ))
      Filter.atTop
      (nhds 0) := by
  have hledger :
      Filter.Tendsto
        (fun N : ℕ =>
          ∑ index in ZetaPrimePowerIndex.box N,
            (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate index f +
              zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
                index f))
        Filter.atTop
        (nhds 0) :=
    zetaCompletedPrimePowerAutocorrelation_oriented_add_opposite_boxSum_tendsto_zero_owner
      f
  have hfun :
      (fun N : ℕ =>
        ∑ index in ZetaPrimePowerIndex.box N,
          ((2 : ℝ) *
            Complex.re
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
                index f) : ℂ)) =
        (fun N : ℕ =>
          ∑ index in ZetaPrimePowerIndex.box N,
            (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate index f +
              zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
                index f)) := by
    funext N
    exact
      (zetaCompletedPrimePowerAutocorrelation_oriented_add_opposite_boxSum_eq_realShadow
        N f).symm
  exact Eq.subst
    (motive := fun u : ℕ → ℂ =>
      Filter.Tendsto u Filter.atTop (nhds 0))
    hfun.symm
    hledger

/-- Owner convergence for twice the real part of the rectangular oriented
autocorrelation prime-power box sum. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_boxSum_twoRealPart_tendsto_zero_owner
    (f : ZetaAdmissibleFunction) :
    Filter.Tendsto
      (fun N : ℕ =>
        (2 : ℝ) *
          (Complex.re
            (zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum
              N f) : ℂ))
      Filter.atTop
      (nhds 0) := by
  have hshadow :
      Filter.Tendsto
        (fun N : ℕ =>
          ∑ index in ZetaPrimePowerIndex.box N,
            ((2 : ℝ) *
              Complex.re
                (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
                  index f) : ℂ))
        Filter.atTop
        (nhds 0) :=
    zetaCompletedPrimePowerAutocorrelation_oriented_boxRealShadow_tendsto_zero_owner
      f
  have hfun :
      (fun N : ℕ =>
        (2 : ℝ) *
          (Complex.re
            (zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum
              N f) : ℂ)) =
        (fun N : ℕ =>
          ∑ index in ZetaPrimePowerIndex.box N,
            ((2 : ℝ) *
              Complex.re
                (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
                  index f) : ℂ)) := by
    funext N
    exact
      (zetaCompletedPrimePowerAutocorrelation_oriented_boxRealShadow_eq_two_re_boxSum_source
        N f
      ).symm
  exact Eq.subst
    (motive := fun u : ℕ → ℂ =>
      Filter.Tendsto u Filter.atTop (nhds 0))
    hfun.symm
    hshadow

/-- Owner theorem for completed prime-power autocorrelation ledger
cancellation. -/
theorem zetaCompletedPrimePowerAutocorrelationLedgerCancellation_owner
    (f : ZetaAdmissibleFunction) :
    ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f := by
  exact
    zetaCompletedPrimePowerAutocorrelationLedgerCancellation_of_traceReconstruction
      f

/-- Owner theorem for summability of oriented completed prime-power
autocorrelation coordinates. -/
theorem zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_summable_owner
    (f : ZetaAdmissibleFunction) (Cpos Cneg : ℝ) (kpos kneg : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
          index f) := by
  exact
    zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_summable_of_spectralMajorant
      f
      (zetaCompletedPrimeSpectralCoordinateMajorant_summable_boundaryCancellationInput
        f Cpos Cneg kpos kneg hpos hneg)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
