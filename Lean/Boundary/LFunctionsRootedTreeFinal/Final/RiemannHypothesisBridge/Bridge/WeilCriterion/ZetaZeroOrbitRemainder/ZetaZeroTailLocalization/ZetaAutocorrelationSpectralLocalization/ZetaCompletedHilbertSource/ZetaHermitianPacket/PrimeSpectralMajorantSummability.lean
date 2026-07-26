import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingDensityDecay
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingSpectralOwner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingDecayParts.TraceBesselParts.PrimeWeightedSamplingBesselSource
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingDecayParts.TraceBesselParts.PrimeAmplitudeFrameSummability

/-!
# Prime spectral majorant summability

This file owns summability of the completed prime spectral coordinate majorant
on autocorrelation probes.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-! ### Corrected vertical Fourier consumer

This is the downstream spectral-majorant entry point for the vertical lane.
The weighted vertical predicate is consumed directly, so no real-Laplace
envelope is introduced into the Fourier sampling proof. -/

theorem zetaCompletedPrimeVerticalWeightedSample_summable_owner
    (f : ZetaAdmissibleFunction) (D : ℝ) (k : ℕ)
    (hbound : VerticalPrimeCenterWeightedSpectralPolynomialBound f D k) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling
          ι f) := by
  exact
    completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling_summable_of_weightedVerticalBound
      f D k hbound

theorem zetaCompletedPrimeVerticalWeightedSample_window_upperBound_owner
    (f : ZetaAdmissibleFunction) (D : ℝ) (k : ℕ)
    (hbound : VerticalPrimeCenterWeightedSpectralPolynomialBound f D k) :
    ∀ N : ℕ,
      completedAutocorrelationSpectralTransform_verticalWeightedPrimeSamplingWindow
          N f ≤
        ∑ ι in ZetaPrimePowerIndex.window N,
          D * ZetaPrimePowerIndex.polynomialHeightDecay k ι := by
  exact fun N =>
    completedAutocorrelationSpectralTransform_verticalWeightedPrimeSamplingWindow_le_weightedVerticalMajorantWindow
      f D k N hbound

theorem zetaCompletedPrimeVerticalWeightedSample_summable_of_verticalDensityBound_owner
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hC : 0 ≤ C)
    (hdensity : ∀ index : ZetaPrimePowerIndex,
      completedAutocorrelationSpectralTransform_verticalPrimeCenterPlancherelDensity
          index f ≤
        C * ZetaPrimePowerIndex.polynomialHeightDecay k index) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling
          index f) := by
  match verticalPrimeCenterWeightedSpectralPolynomialBound_of_verticalDensityBound_owner
      f C k hC hdensity with
  | ⟨D, l, hD, hbound⟩ =>
      exact zetaCompletedPrimeVerticalWeightedSample_summable_owner f D l hbound

theorem zetaCompletedPrimeVerticalOppositeWeightedSample_summable_of_reflect_verticalDensityBound_owner
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hC : 0 ≤ C)
    (hdensity : ∀ index : ZetaPrimePowerIndex,
      completedAutocorrelationSpectralTransform_verticalPrimeCenterPlancherelDensity
          index (ZetaAdmissibleFunction.reflect f) ≤
        C * ZetaPrimePowerIndex.polynomialHeightDecay k index) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling
          index (ZetaAdmissibleFunction.reflect f)) := by
  exact zetaCompletedPrimeVerticalWeightedSample_summable_of_verticalDensityBound_owner
    (ZetaAdmissibleFunction.reflect f) C k hC hdensity

theorem zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSq_summable_of_reflect_verticalDensityBound_owner
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hC : 0 ≤ C)
    (hdensity : ∀ index : ZetaPrimePowerIndex,
      completedAutocorrelationSpectralTransform_verticalPrimeCenterPlancherelDensity
          index (ZetaAdmissibleFunction.reflect f) ≤
        C * ZetaPrimePowerIndex.polynomialHeightDecay k index) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex index f‖ ^ 2) := by
  match verticalPrimeCenterWeightedSpectralPolynomialBound_of_verticalDensityBound_owner
      (ZetaAdmissibleFunction.reflect f) C k hC hdensity with
  | ⟨D, l, hD, hbound⟩ =>
      exact zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSq_summable_majorant_owner
        f D l hbound

theorem zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSq_summable_of_verticalDensityBound_owner
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hC : 0 ≤ C)
    (hdensity : ∀ index : ZetaPrimePowerIndex,
      completedAutocorrelationSpectralTransform_verticalPrimeCenterPlancherelDensity
          index f ≤
        C * ZetaPrimePowerIndex.polynomialHeightDecay k index) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeVerticalSpectralAmplitudeIndex index f‖ ^ 2) := by
  match verticalPrimeCenterWeightedSpectralPolynomialBound_of_verticalDensityBound_owner
      f C k hC hdensity with
  | ⟨D, l, hD, hbound⟩ =>
      exact zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSq_summable_majorant_owner
        f D l hbound

theorem zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSq_summable_majorant_owner
    (f : ZetaAdmissibleFunction) (D : ℝ) (k : ℕ)
    (hbound : VerticalPrimeCenterWeightedSpectralPolynomialBound f D k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeVerticalSpectralAmplitudeIndex index f‖ ^ 2) :=
  zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSq_summable_frame_source
    f D k hbound

theorem zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSq_summable_majorant_owner
    (f : ZetaAdmissibleFunction) (D : ℝ) (k : ℕ)
    (hbound : VerticalPrimeCenterWeightedSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) D k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex index f‖ ^ 2) :=
  zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSq_summable_frame_source
    f D k hbound

theorem zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSq_window_upperBound_majorant_owner
    (f : ZetaAdmissibleFunction) (D : ℝ) (k : ℕ)
    (hbound : VerticalPrimeCenterWeightedSpectralPolynomialBound f D k) :
    ∀ N : ℕ,
      ∑ index in ZetaPrimePowerIndex.window N,
        ‖zetaCompletedPrimeVerticalSpectralAmplitudeIndex index f‖ ^ 2 ≤
      zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSqTraceEnergy f :=
  fun N =>
    zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSq_windowSubtrace_le_traceEnergy_owner
      f D k N hbound

theorem zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSq_window_upperBound_majorant_owner
    (f : ZetaAdmissibleFunction) (D : ℝ) (k : ℕ)
    (hbound : VerticalPrimeCenterWeightedSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) D k) :
    ∀ N : ℕ,
      ∑ index in ZetaPrimePowerIndex.window N,
        ‖zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex index f‖ ^ 2 ≤
      zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSqTraceEnergy f :=
  fun N =>
    zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSq_windowSubtrace_le_traceEnergy_owner
      f D k N hbound

/-- Nonnegative real values are equal to their real norm. -/
theorem real_norm_eq_self_of_nonnegative
    (x : ℝ) (hx : 0 ≤ x) :
    ‖x‖ = x :=
  Real.norm_of_nonneg hx

/-- The completed prime-power weight has complex norm equal to the underlying
real weight. -/
theorem zetaPrimePowerIndex_complex_norm_weight_eq_weight
    (index : ZetaPrimePowerIndex) :
    ‖(ZetaPrimePowerIndex.weight index : ℂ)‖ =
      ZetaPrimePowerIndex.weight index :=
  Eq.trans
    (Complex.norm_real (ZetaPrimePowerIndex.weight index))
    (Real.norm_of_nonneg
      (ZetaPrimePowerIndex.weight_nonnegative index))

/-- Pure rectangular-height algebra: squaring one polynomial-decay bound is
absorbed by another polynomial-height decay bound. -/
theorem polynomialHeightDecay_square_absorbs_bound_owner
    (C : ℝ) (k : ℕ) (hC : 0 ≤ C) :
    ∃ D : ℝ, ∃ l : ℕ,
      0 ≤ D ∧
        ∀ index : ZetaPrimePowerIndex,
          (C * ZetaPrimePowerIndex.polynomialHeightDecay k index) *
              (C * ZetaPrimePowerIndex.polynomialHeightDecay k index) ≤
            D * ZetaPrimePowerIndex.polynomialHeightDecay l index :=
  let D : ℝ := C * C
  let hD : 0 ≤ D :=
    mul_nonneg hC hC
  let hbound :
      ∀ index : ZetaPrimePowerIndex,
        (C * ZetaPrimePowerIndex.polynomialHeightDecay k index) *
            (C * ZetaPrimePowerIndex.polynomialHeightDecay k index) ≤
          D * ZetaPrimePowerIndex.polynomialHeightDecay k index :=
    fun index =>
    let d : ℝ := ZetaPrimePowerIndex.polynomialHeightDecay k index
    let hd_nonnegative : 0 ≤ d :=
      ZetaPrimePowerIndex.polynomialHeightDecay_nonnegative k index
    let hd_le_one : d ≤ 1 :=
      ZetaPrimePowerIndex.polynomialHeightDecay_le_one k index
    let hmul : d * d ≤ d * 1 :=
        mul_le_mul_of_nonneg_left hd_le_one hd_nonnegative
    let hd_square_le_d : d * d ≤ d :=
      Eq.subst
        (motive := fun value : ℝ => d * d ≤ value)
        (mul_one d)
        hmul
    let hscaled : D * (d * d) ≤ D * d :=
      mul_le_mul_of_nonneg_left hd_square_le_d hD
    let hstepOne :
        (C * d) * (C * d) = C * (d * (C * d)) :=
      mul_assoc C d (C * d)
    let hstepTwo :
        C * (d * (C * d)) = C * ((d * C) * d) :=
      congrArg (fun value : ℝ => C * value)
        (mul_assoc d C d).symm
    let hstepThree :
        C * ((d * C) * d) = C * ((C * d) * d) :=
      congrArg
        (fun value : ℝ => C * (value * d))
        (mul_comm d C)
    let hstepFour :
        C * ((C * d) * d) = C * (C * (d * d)) :=
      congrArg (fun value : ℝ => C * value)
        (mul_assoc C d d)
    let hstepFive :
        C * (C * (d * d)) = (C * C) * (d * d) :=
      (mul_assoc C C (d * d)).symm
    let hstepSix :
        (C * C) * (d * d) = D * (d * d) :=
      Eq.refl ((C * C) * (d * d))
    let hleft :
        (C * d) * (C * d) = D * (d * d) :=
      hstepOne.trans
        (hstepTwo.trans
          (hstepThree.trans
            (hstepFour.trans
              (hstepFive.trans hstepSix))))
    Eq.subst
      (motive := fun value : ℝ => value ≤ D * d)
      hleft.symm
      hscaled
  Exists.intro D
    (Exists.intro k
      (And.intro hD hbound))

/-- Multiplying a density polynomial bound by the completed prime-power weight
is absorbed by shifting the polynomial height exponent. -/
theorem completedAutocorrelationSpectralTransform_weight_mul_density_bound_of_density_bound
    (f : ZetaAdmissibleFunction)
    (C : ℝ) (k : ℕ)
    (hC : 0 ≤ C)
    (hdensity :
      ∀ index : ZetaPrimePowerIndex,
        ‖completedAutocorrelationSpectralTransform_primeCenterPlancherelDensity
            index f‖ ≤
          C * ZetaPrimePowerIndex.polynomialHeightDecay k index) :
    ∃ D : ℝ, ∃ l : ℕ,
      0 ≤ D ∧
        ∀ index : ZetaPrimePowerIndex,
          ‖completedAutocorrelationSpectralTransform_weightedPrimeSampling
              index f‖ ≤
            D * ZetaPrimePowerIndex.polynomialHeightDecay l index :=
  completedAutocorrelationSpectralTransform_weightedPrimeSampling_bound_of_density_bound_ownerTraceReconstruction
    f C k hC hdensity

/-- Owner theorem for summability of the positive completed prime weighted
sample norm squares. -/
theorem zetaCompletedPrimePositiveWeightedSampleNormSq_summable_owner
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimePositiveWeightedSampleNormSq index f) :=
  (zetaCompletedPrimeSpectralAmplitudeIndex_normSq_summable_traceBessel_source
    f C k hbound).congr
    (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralAmplitudeIndex_norm_sq_eq_weightedSampleNormSq
        index f)

/-- Owner theorem for summability of the opposite completed prime weighted
sample norm squares. -/
theorem zetaCompletedPrimeOppositeWeightedSampleNormSq_summable_owner
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) C k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeOppositeWeightedSampleNormSq index f) :=
  (zetaCompletedPrimePositiveWeightedSampleNormSq_summable_owner
    (ZetaAdmissibleFunction.reflect f) C k hbound).congr
    (fun index : ZetaPrimePowerIndex =>
      (zetaCompletedPrimeOppositeWeightedSampleNormSq_eq_positive_reflect
        index f).symm)

/-- A real-axis prime-center spectral bound gives summability of the positive
completed prime weighted sample norm-square stream. -/
theorem zetaCompletedPrimePositiveWeightedSampleNormSq_summable_of_spectralPolynomialBound
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimePositiveWeightedSampleNormSq index f) :=
  (weightedPrimeSampling_summable_of_spectralPolynomialBound
    f C k hbound).congr
    (fun index : ZetaPrimePowerIndex =>
      (zetaCompletedPrimePositiveWeightedSampleNormSq_eq_weightedPrimeSampling
        index f).symm)

/-- A real-axis prime-center spectral bound for the reflected probe gives
summability of the opposite completed prime weighted sample norm-square
stream. -/
theorem zetaCompletedPrimeOppositeWeightedSampleNormSq_summable_of_reflect_spectralPolynomialBound
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) C k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeOppositeWeightedSampleNormSq index f) :=
  (zetaCompletedPrimePositiveWeightedSampleNormSq_summable_of_spectralPolynomialBound
    (ZetaAdmissibleFunction.reflect f) C k hbound).congr
    (fun index : ZetaPrimePowerIndex =>
      (zetaCompletedPrimeOppositeWeightedSampleNormSq_eq_positive_reflect
        index f).symm)

/-- Owner theorem for summability of the positive completed prime spectral
amplitude squares. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_summable_owner
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) :=
  zetaCompletedPrimeSpectralAmplitudeIndex_normSq_summable_traceBessel_source
    f C k hbound

/-- Owner theorem for summability of the opposite completed prime spectral
amplitude squares. -/
theorem zetaCompletedPrimeOppositeSpectralAmplitudeIndex_normSq_summable_owner
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) C k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f‖ ^ 2) :=
  (zetaCompletedPrimeOppositeWeightedSampleNormSq_summable_owner
    f C k hbound).congr
    (fun index : ZetaPrimePowerIndex =>
      (zetaCompletedPrimeOppositeSpectralAmplitudeIndex_norm_sq_eq_weightedSampleNormSq
        index f).symm)

/-- A real-axis prime-center spectral bound gives summability of the positive
completed prime spectral-amplitude square stream. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_summable_of_spectralPolynomialBound
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) :=
  (zetaCompletedPrimePositiveWeightedSampleNormSq_summable_of_spectralPolynomialBound
    f C k hbound).congr
    (fun index : ZetaPrimePowerIndex =>
      (zetaCompletedPrimeSpectralAmplitudeIndex_norm_sq_eq_weightedSampleNormSq
        index f).symm)

/-- A real-axis prime-center spectral bound for the reflected probe gives
summability of the opposite completed prime spectral-amplitude square stream. -/
theorem zetaCompletedPrimeOppositeSpectralAmplitudeIndex_normSq_summable_of_reflect_spectralPolynomialBound
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) C k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f‖ ^ 2) :=
  (zetaCompletedPrimeOppositeWeightedSampleNormSq_summable_of_reflect_spectralPolynomialBound
    f C k hbound).congr
    (fun index : ZetaPrimePowerIndex =>
      (zetaCompletedPrimeOppositeSpectralAmplitudeIndex_norm_sq_eq_weightedSampleNormSq
        index f).symm)

/-- The completed prime spectral coordinate majorant is the sum of the two
face square families. -/
theorem zetaCompletedPrimeSpectralCoordinateMajorant_eq_normSq_add_normSq
    (f : ZetaAdmissibleFunction) :
    (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f) =
      fun index : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 +
          ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f‖ ^ 2 :=
  funext
    (fun index : ZetaPrimePowerIndex =>
      Eq.refl (zetaCompletedPrimeSpectralCoordinateMajorant index f))

/-- Pointwise form of the completed prime spectral coordinate majorant
presentation. -/
theorem zetaCompletedPrimeSpectralCoordinateMajorant_apply_eq_normSq_add_normSq
    (f : ZetaAdmissibleFunction) (index : ZetaPrimePowerIndex) :
    zetaCompletedPrimeSpectralCoordinateMajorant index f =
      ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 +
        ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f‖ ^ 2 :=
  Eq.refl (zetaCompletedPrimeSpectralCoordinateMajorant index f)

/-- The two-face spectral majorant is pointwise nonnegative. -/
theorem zetaCompletedPrimeSpectralCoordinateMajorant_nonnegative
    (f : ZetaAdmissibleFunction) (index : ZetaPrimePowerIndex) :
    0 ≤ zetaCompletedPrimeSpectralCoordinateMajorant index f := by
  exact Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (zetaCompletedPrimeSpectralCoordinateMajorant_apply_eq_normSq_add_normSq f index)
    (add_nonneg
      (sq_nonneg ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖)
      (sq_nonneg ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f‖))

/-! The two envelope inequalities are the canonical arithmetic input for the
completed prime spectral coordinate majorant. -/
theorem zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_envelopePolynomialBounds_owner
    (f : ZetaAdmissibleFunction) (Cpos Cneg : ℝ) (kpos kneg : ℕ)
    (hCpos : 0 ≤ Cpos) (hCneg : 0 ≤ Cneg)
    (henvpos : ∀ index : ZetaPrimePowerIndex,
      zetaPaleyWienerZeroOrderEnvelope
          f (canonicalZetaPaleyWienerSupportInterval f)
          index.center index.center ≤
        Cpos * ZetaPrimePowerIndex.polynomialHeightDecay kpos index)
    (henvneg : ∀ index : ZetaPrimePowerIndex,
      zetaPaleyWienerZeroOrderEnvelope
          (ZetaAdmissibleFunction.reflect f)
          (canonicalZetaPaleyWienerSupportInterval
            (ZetaAdmissibleFunction.reflect f))
          index.center index.center ≤
        Cneg * ZetaPrimePowerIndex.polynomialHeightDecay kneg index) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeSpectralCoordinateMajorant index f) := by
  exact zetaCompletedPrimeSpectralCoordinateMajorant_summable_owner
    f Cpos kpos
    (primeCenterSpectralPolynomialBound_of_canonicalEnvelope_polynomialBound
      f Cpos kpos hCpos henvpos)
    Cneg kneg
    (primeCenterSpectralPolynomialBound_of_canonicalEnvelope_polynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg hCneg henvneg)

/-! A family-level cut for the scheduled contour transport.  The proof is
pointwise in the admissible seed, so no downstream package may silently turn
the envelope estimates into an unconditional majorant. -/
theorem zetaCompletedPrimeSpectralCoordinateMajorant_summable_family_of_envelopePolynomialBounds_owner
    (Cpos Cneg : ℝ) (kpos kneg : ℕ)
    (hCpos : 0 ≤ Cpos) (hCneg : 0 ≤ Cneg)
    (henvpos : ∀ f : ZetaAdmissibleFunction, ∀ index : ZetaPrimePowerIndex,
      zetaPaleyWienerZeroOrderEnvelope
          f (canonicalZetaPaleyWienerSupportInterval f)
          index.center index.center ≤
        Cpos * ZetaPrimePowerIndex.polynomialHeightDecay kpos index)
    (henvneg : ∀ f : ZetaAdmissibleFunction, ∀ index : ZetaPrimePowerIndex,
      zetaPaleyWienerZeroOrderEnvelope
          (ZetaAdmissibleFunction.reflect f)
          (canonicalZetaPaleyWienerSupportInterval
            (ZetaAdmissibleFunction.reflect f))
          index.center index.center ≤
        Cneg * ZetaPrimePowerIndex.polynomialHeightDecay kneg index) :
    ∀ f : ZetaAdmissibleFunction,
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
  fun f =>
    zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_envelopePolynomialBounds_owner
      f Cpos Cneg kpos kneg hCpos hCneg
      (henvpos f) (henvneg f)

/-- Owner theorem for summability of the completed prime spectral coordinate
majorant on autocorrelation probes. -/
theorem zetaCompletedPrimeSpectralCoordinateMajorant_summable_owner
    (f : ZetaAdmissibleFunction) (Cpos : ℝ) (kpos : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (Cneg : ℝ) (kneg : ℕ)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
  let hpositive :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) :=
    zetaCompletedPrimeSpectralAmplitudeIndex_normSq_summable_owner
      f Cpos kpos hpos
  let hopposite :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f‖ ^ 2) :=
    zetaCompletedPrimeOppositeSpectralAmplitudeIndex_normSq_summable_owner
      f Cneg kneg hneg
  (hpositive.add hopposite).congr
    (fun index : ZetaPrimePowerIndex =>
      (zetaCompletedPrimeSpectralCoordinateMajorant_apply_eq_normSq_add_normSq
        f index).symm)

/-! Acyclic owner entry point: an arithmetic proof of majorant summability is
transported directly to the positive sampling stream and its square family. -/

theorem zetaCompletedPrimePositiveWeightedSampleNormSq_summable_of_majorant_summable_owner
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimePositiveWeightedSampleNormSq index f) := by
  exact
    (completedAutocorrelationSpectralTransform_weightedPrimeSampling_summable_of_majorant_summable_traceEnergy_owner
      f hmajorant).congr
      (fun index : ZetaPrimePowerIndex =>
        (zetaCompletedPrimePositiveWeightedSampleNormSq_eq_weightedPrimeSampling
          index f).symm)

theorem zetaCompletedPrimeOppositeWeightedSampleNormSq_summable_of_reflect_majorant_summable_owner
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index
            (ZetaAdmissibleFunction.reflect f))) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeOppositeWeightedSampleNormSq index f) := by
  exact
    (zetaCompletedPrimePositiveWeightedSampleNormSq_summable_of_majorant_summable_owner
      (ZetaAdmissibleFunction.reflect f) hmajorant).congr
      (fun index : ZetaPrimePowerIndex =>
        (zetaCompletedPrimeOppositeWeightedSampleNormSq_eq_positive_reflect
          index f).symm)

theorem zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_two_face_summable_owner
    (f : ZetaAdmissibleFunction)
    (hpos :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2))
    (hneg :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f‖ ^ 2)) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeSpectralCoordinateMajorant index f) := by
  exact (hpos.add hneg).congr
    (fun index : ZetaPrimePowerIndex =>
      (zetaCompletedPrimeSpectralCoordinateMajorant_apply_eq_normSq_add_normSq
        f index).symm)

theorem zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_two_face_weightedDensityBounds_owner
    (f : ZetaAdmissibleFunction)
    (Cpos Cneg : ℝ) (kpos kneg : ℕ)
    (hpos : PrimeCenterWeightedSpectralDensityPolynomialBound f Cpos kpos)
    (hneg : PrimeCenterWeightedSpectralDensityPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
  zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_two_face_weightedSpectralDensityPolynomialBounds
    f Cpos Cneg kpos kneg hpos hneg

/-- Real-axis prime-center spectral bounds for a probe and its reflection give
summability of the completed prime spectral coordinate majorant. -/
theorem zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_spectralPolynomialBounds
    (f : ZetaAdmissibleFunction)
    (Cpos : ℝ) (kpos : ℕ)
    (Cneg : ℝ) (kneg : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
  let hpositive :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) :=
    zetaCompletedPrimeSpectralAmplitudeIndex_normSq_summable_of_spectralPolynomialBound
      f Cpos kpos hpos
  let hopposite :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f‖ ^ 2) :=
    zetaCompletedPrimeOppositeSpectralAmplitudeIndex_normSq_summable_of_reflect_spectralPolynomialBound
      f Cneg kneg hneg
  (hpositive.add hopposite).congr
    (fun index : ZetaPrimePowerIndex =>
      (zetaCompletedPrimeSpectralCoordinateMajorant_apply_eq_normSq_add_normSq
        f index).symm)

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary
