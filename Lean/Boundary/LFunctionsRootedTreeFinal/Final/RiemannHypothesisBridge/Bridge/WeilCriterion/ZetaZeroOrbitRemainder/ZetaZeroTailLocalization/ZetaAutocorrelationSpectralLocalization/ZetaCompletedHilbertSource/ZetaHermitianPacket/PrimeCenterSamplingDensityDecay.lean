import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingWeightBound
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingEnvelope

/-!
# Prime-center sampling density decay

This file owns the non-circular transport from a real-axis prime-center
spectral bound to density decay, weighted sampling decay, and summability.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- A real-axis prime-center spectral bound for one admissible probe. -/
def PrimeCenterSpectralPolynomialBound
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ) : Prop :=
  0 ≤ C ∧
    ∀ index : ZetaPrimePowerIndex,
      ‖zetaCompletedSpectralLaplaceTransform f index.center‖ ≤
      C * ZetaPrimePowerIndex.polynomialHeightDecay k index

def PrimeCenterWeightedSpectralPolynomialBound
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ) : Prop :=
  0 ≤ C ∧
    ∀ index : ZetaPrimePowerIndex,
      ZetaPrimePowerIndex.weight index *
          ‖zetaCompletedSpectralLaplaceTransform f index.center‖ ≤
        C * ZetaPrimePowerIndex.polynomialHeightDecay k index

def PrimeCenterWeightedSpectralDensityPolynomialBound
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ) : Prop :=
  0 ≤ C ∧
    ∀ index : ZetaPrimePowerIndex,
      ZetaPrimePowerIndex.weight index *
          ‖zetaCompletedSpectralLaplaceTransform f index.center‖ ^ 2 ≤
        C * ZetaPrimePowerIndex.polynomialHeightDecay k index

theorem primeCenterWeightedSpectralDensityPolynomialBound_of_weightedEnvelopeSquareBound
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hC : 0 ≤ C)
    (henvelope : ∀ index : ZetaPrimePowerIndex,
      ZetaPrimePowerIndex.weight index *
          (zetaPaleyWienerZeroOrderEnvelope
            f (canonicalZetaPaleyWienerSupportInterval f)
            index.center index.center) ^ 2 ≤
        C * ZetaPrimePowerIndex.polynomialHeightDecay k index) :
    PrimeCenterWeightedSpectralDensityPolynomialBound f C k := by
  exact ⟨hC, fun index =>
    have hweight : 0 ≤ ZetaPrimePowerIndex.weight index :=
      ZetaPrimePowerIndex.weight_nonnegative index
    have htransform :=
      zetaLaplaceTransform_realCenter_le_canonicalSupportEnvelope
        f index.center
    have htransform' :
        ‖zetaCompletedSpectralLaplaceTransform f index.center‖ ≤
          zetaPaleyWienerZeroOrderEnvelope
            f (canonicalZetaPaleyWienerSupportInterval f)
            index.center index.center := by
      exact htransform
    have hsquare :
        ‖zetaCompletedSpectralLaplaceTransform f index.center‖ ^ 2 ≤
          (zetaPaleyWienerZeroOrderEnvelope
            f (canonicalZetaPaleyWienerSupportInterval f)
            index.center index.center) ^ 2 := by
      apply sq_le_sq.mpr
      calc
        |‖zetaCompletedSpectralLaplaceTransform f index.center‖| =
            ‖zetaCompletedSpectralLaplaceTransform f index.center‖ :=
          abs_of_nonneg (norm_nonneg _)
        _ ≤ zetaPaleyWienerZeroOrderEnvelope
            f (canonicalZetaPaleyWienerSupportInterval f)
            index.center index.center := htransform'
        _ = |zetaPaleyWienerZeroOrderEnvelope
            f (canonicalZetaPaleyWienerSupportInterval f)
            index.center index.center| :=
          (abs_of_nonneg
            (zetaPaleyWienerZeroOrderEnvelope_pos
              f (canonicalZetaPaleyWienerSupportInterval f)
              index.center index.center).le).symm
    have hweighted :
        ZetaPrimePowerIndex.weight index *
            ‖zetaCompletedSpectralLaplaceTransform f index.center‖ ^ 2 ≤
          ZetaPrimePowerIndex.weight index *
            (zetaPaleyWienerZeroOrderEnvelope
              f (canonicalZetaPaleyWienerSupportInterval f)
              index.center index.center) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hsquare hweight
    le_trans hweighted (henvelope index)⟩

theorem weightedPrimeSampling_bound_of_weightedSpectralDensityPolynomialBound
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterWeightedSpectralDensityPolynomialBound f C k) :
    ∃ D : ℝ, ∃ l : ℕ,
      0 ≤ D ∧
        ∀ index : ZetaPrimePowerIndex,
          ‖completedAutocorrelationSpectralTransform_weightedPrimeSampling
              index f‖ ≤
            D * ZetaPrimePowerIndex.polynomialHeightDecay l index := by
  exact ⟨C, k, hbound.left, fun index =>
    have hnonnegative :
        0 ≤ completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f :=
      completedAutocorrelationSpectralTransform_weightedPrimeSampling_nonnegative
        index f
    have hnorm :
        ‖completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f‖ =
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f :=
      Real.norm_of_nonneg hnonnegative
    have hsampling :=
      completedAutocorrelationSpectralTransform_weightedPrimeSampling_eq_weight_mul_density
        index f
    Eq.subst
      (motive := fun value : ℝ =>
        value ≤ C * ZetaPrimePowerIndex.polynomialHeightDecay k index)
      hnorm.symm
      (Eq.subst
        (motive := fun value : ℝ =>
          value ≤ C * ZetaPrimePowerIndex.polynomialHeightDecay k index)
        hsampling.symm
        (hbound.right index))⟩

theorem weightedPrimeSampling_summable_of_weightedSpectralDensityPolynomialBound
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterWeightedSpectralDensityPolynomialBound f C k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f) := by
  match weightedPrimeSampling_bound_of_weightedSpectralDensityPolynomialBound
    f C k hbound with
  | ⟨D, l, hD, hnorm⟩ =>
      exact Summable.of_norm_bounded
        (fun index : ZetaPrimePowerIndex =>
          D * ZetaPrimePowerIndex.polynomialHeightDecay l index)
        (ZetaPrimePowerIndex.summable_const_mul_polynomialHeightDecay D l)
        hnorm

theorem weightedPrimeSampling_finiteSubtrace_upperBound_of_weightedSpectralDensityPolynomialBound
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterWeightedSpectralDensityPolynomialBound f C k) :
    ∃ B : ℝ, ∀ s : Finset ZetaPrimePowerIndex,
      ∑ index in s,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f ≤ B := by
  have hsum :=
    weightedPrimeSampling_summable_of_weightedSpectralDensityPolynomialBound
      f C k hbound
  have hhasSum := hsum.hasSum
  have hnonnegative :
      ∀ index : ZetaPrimePowerIndex,
        0 ≤ completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f := by
    intro index
    exact completedAutocorrelationSpectralTransform_weightedPrimeSampling_nonnegative
      index f
  exact ⟨∑' index : ZetaPrimePowerIndex,
      completedAutocorrelationSpectralTransform_weightedPrimeSampling index f,
    fun s => sum_le_hasSum s
      (fun index membership => hnonnegative index) hhasSum⟩

theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteSubtrace_upperBound_of_weightedSpectralDensityPolynomialBound
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterWeightedSpectralDensityPolynomialBound f C k) :
    ∃ B : ℝ, ∀ s : Finset ZetaPrimePowerIndex,
      ∑ index in s,
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 ≤ B := by
  match weightedPrimeSampling_finiteSubtrace_upperBound_of_weightedSpectralDensityPolynomialBound
      f C k hbound with
  | ⟨B, hB⟩ =>
      exact ⟨B, fun s =>
        Eq.subst
          (motive := fun value : ℝ => value ≤ B)
          (Finset.sum_congr (Eq.refl s)
            (fun index membership =>
              (zetaCompletedPrimeSpectralAmplitudeIndex_norm_sq_eq_weightedSampleNormSq
                index f).trans
                (zetaCompletedPrimePositiveWeightedSampleNormSq_eq_weightedPrimeSampling
                  index f))).symm
          (hB s)⟩

theorem zetaCompletedPrimeOppositeSpectralAmplitudeIndex_normSq_finiteSubtrace_upperBound_of_reflect_weightedSpectralDensityPolynomialBound
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterWeightedSpectralDensityPolynomialBound
      (ZetaAdmissibleFunction.reflect f) C k) :
    ∃ B : ℝ, ∀ s : Finset ZetaPrimePowerIndex,
      ∑ index in s,
        ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f‖ ^ 2 ≤ B := by
  match
      zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteSubtrace_upperBound_of_weightedSpectralDensityPolynomialBound
        (ZetaAdmissibleFunction.reflect f) C k hbound with
  | ⟨B, hB⟩ =>
      exact ⟨B, fun s =>
        have hterm : ∀ index : ZetaPrimePowerIndex,
            ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f‖ ^ 2 =
              ‖zetaCompletedPrimeSpectralAmplitudeIndex index
                (ZetaAdmissibleFunction.reflect f)‖ ^ 2 := by
          intro index
          exact
            (zetaCompletedPrimeOppositeSpectralAmplitudeIndex_norm_sq_eq_weightedSampleNormSq
              index f).trans
              ((zetaCompletedPrimeOppositeWeightedSampleNormSq_eq_positive_reflect
                index f).trans
                (zetaCompletedPrimeSpectralAmplitudeIndex_norm_sq_eq_weightedSampleNormSq
                  index (ZetaAdmissibleFunction.reflect f)).symm)
        calc
          ∑ index in s,
              ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f‖ ^ 2 =
            ∑ index in s,
              ‖zetaCompletedPrimeSpectralAmplitudeIndex index
                (ZetaAdmissibleFunction.reflect f)‖ ^ 2 :=
            Finset.sum_congr (Eq.refl s) (fun index membership => hterm index)
          _ ≤ B := hB s⟩

theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_summable_of_weightedSpectralDensityPolynomialBound
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterWeightedSpectralDensityPolynomialBound f C k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) := by
  have hfinite :=
    zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteSubtrace_upperBound_of_weightedSpectralDensityPolynomialBound
      f C k hbound
  match hfinite with
  | ⟨B, hB⟩ =>
      exact summable_of_sum_le
        (fun index => sq_nonneg
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖)
        hB

theorem zetaCompletedPrimeOppositeSpectralAmplitudeIndex_normSq_summable_of_reflect_weightedSpectralDensityPolynomialBound
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterWeightedSpectralDensityPolynomialBound
      (ZetaAdmissibleFunction.reflect f) C k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f‖ ^ 2) := by
  have hfinite :=
    zetaCompletedPrimeOppositeSpectralAmplitudeIndex_normSq_finiteSubtrace_upperBound_of_reflect_weightedSpectralDensityPolynomialBound
      f C k hbound
  match hfinite with
  | ⟨B, hB⟩ =>
      exact summable_of_sum_le
        (fun index => sq_nonneg
          ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f‖)
        hB

theorem zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_two_face_weightedSpectralDensityPolynomialBounds
    (f : ZetaAdmissibleFunction) (Cpos Cneg : ℝ) (kpos kneg : ℕ)
    (hpos : PrimeCenterWeightedSpectralDensityPolynomialBound f Cpos kpos)
    (hneg : PrimeCenterWeightedSpectralDensityPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeSpectralCoordinateMajorant index f) := by
  exact
    ((zetaCompletedPrimeSpectralAmplitudeIndex_normSq_summable_of_weightedSpectralDensityPolynomialBound
      f Cpos kpos hpos).add
      (zetaCompletedPrimeOppositeSpectralAmplitudeIndex_normSq_summable_of_reflect_weightedSpectralDensityPolynomialBound
        f Cneg kneg hneg)).congr
      (fun index : ZetaPrimePowerIndex => Eq.refl
        (zetaCompletedPrimeSpectralCoordinateMajorant index f))

theorem primeCenterWeightedSpectralPolynomialBound_of_weightedEnvelopeBound
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hC : 0 ≤ C)
    (henvelope : ∀ index : ZetaPrimePowerIndex,
      ZetaPrimePowerIndex.weight index *
          zetaPaleyWienerZeroOrderEnvelope
            f (canonicalZetaPaleyWienerSupportInterval f)
            index.center index.center ≤
        C * ZetaPrimePowerIndex.polynomialHeightDecay k index) :
    PrimeCenterWeightedSpectralPolynomialBound f C k := by
  exact ⟨hC, fun index =>
    have hweight : 0 ≤ ZetaPrimePowerIndex.weight index :=
      ZetaPrimePowerIndex.weight_nonnegative index
    have htransform :=
      zetaLaplaceTransform_realCenter_le_canonicalSupportEnvelope
        f index.center
    have hweighted :
        ZetaPrimePowerIndex.weight index *
            ‖zetaCompletedSpectralLaplaceTransform f index.center‖ ≤
          ZetaPrimePowerIndex.weight index *
            zetaPaleyWienerZeroOrderEnvelope
              f (canonicalZetaPaleyWienerSupportInterval f)
              index.center index.center := by
      exact mul_le_mul_of_nonneg_left htransform hweight
    le_trans hweighted (henvelope index)⟩

/-- The analytic-to-arithmetic owner cut.  The only input needed here is the
pointwise polynomial majorant for the canonical real-center Paley--Wiener
envelope; all transform transport is discharged at this owner level. -/
theorem primeCenterSpectralPolynomialBound_of_canonicalEnvelope_polynomialBound
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hC : 0 ≤ C)
    (henvelope : ∀ index : ZetaPrimePowerIndex,
      zetaPaleyWienerZeroOrderEnvelope
          f (canonicalZetaPaleyWienerSupportInterval f)
          index.center index.center ≤
        C * ZetaPrimePowerIndex.polynomialHeightDecay k index) :
    PrimeCenterSpectralPolynomialBound f C k := by
  exact ⟨hC, fun index =>
    (show ‖zetaCompletedSpectralLaplaceTransform f index.center‖ ≤
        C * ZetaPrimePowerIndex.polynomialHeightDecay k index by
      have htransform :
          ‖zetaCompletedSpectralLaplaceTransform f index.center‖ ≤
            zetaPaleyWienerZeroOrderEnvelope
              f (canonicalZetaPaleyWienerSupportInterval f)
              index.center index.center := by
        exact zetaLaplaceTransform_realCenter_le_canonicalSupportEnvelope
          f index.center
      exact htransform.trans (henvelope index))⟩

theorem normalizedScale_primeCenterSpectralPolynomialBound_of_canonicalEnvelope_polynomialBound
    (a : ℝ) (ha : 0 < a) (f : ZetaAdmissibleFunction)
    (C : ℝ) (k : ℕ)
    (hC : 0 ≤ C)
    (henvelope : ∀ index : ZetaPrimePowerIndex,
      zetaPaleyWienerZeroOrderEnvelope
          f (canonicalZetaPaleyWienerSupportInterval f)
          (a * index.center) (a * index.center) ≤
        C * ZetaPrimePowerIndex.polynomialHeightDecay k index) :
    PrimeCenterSpectralPolynomialBound (normalizedScale a f) C k := by
  exact ⟨hC, fun index =>
    (show ‖zetaCompletedSpectralLaplaceTransform (normalizedScale a f)
          index.center‖ ≤
        C * ZetaPrimePowerIndex.polynomialHeightDecay k index by
      have htransform :
          ‖zetaCompletedSpectralLaplaceTransform (normalizedScale a f)
              index.center‖ ≤
            zetaPaleyWienerZeroOrderEnvelope
              f (canonicalZetaPaleyWienerSupportInterval f)
              (a * index.center) (a * index.center) := by
        exact normalizedScale_realCenter_le_originalSupportEnvelope
          a ha f index.center
      exact htransform.trans (henvelope index))⟩

/-- Pure height algebra: the square of a polynomial-height decay bound is
absorbed by another polynomial-height decay bound. -/
theorem primeCenterSampling_polynomialHeightDecay_square_bound
    (C : ℝ) (k : ℕ) (hC : 0 ≤ C) :
    ∃ D : ℝ, ∃ l : ℕ,
      0 ≤ D ∧
        ∀ index : ZetaPrimePowerIndex,
          (C * ZetaPrimePowerIndex.polynomialHeightDecay k index) *
              (C * ZetaPrimePowerIndex.polynomialHeightDecay k index) ≤
            D * ZetaPrimePowerIndex.polynomialHeightDecay l index := by
  let D : ℝ := C * C
  have hD : 0 ≤ D :=
    mul_nonneg hC hC
  have hbound :
      ∀ index : ZetaPrimePowerIndex,
        (C * ZetaPrimePowerIndex.polynomialHeightDecay k index) *
            (C * ZetaPrimePowerIndex.polynomialHeightDecay k index) ≤
          D * ZetaPrimePowerIndex.polynomialHeightDecay k index := by
    intro index
    let d : ℝ := ZetaPrimePowerIndex.polynomialHeightDecay k index
    have hd_nonnegative : 0 ≤ d :=
      ZetaPrimePowerIndex.polynomialHeightDecay_nonnegative k index
    have hd_le_one : d ≤ 1 :=
      ZetaPrimePowerIndex.polynomialHeightDecay_le_one k index
    have hd_square_le_d : d * d ≤ d := by
      have hmul : d * d ≤ d * 1 :=
        mul_le_mul_of_nonneg_left hd_le_one hd_nonnegative
      exact Eq.subst
        (motive := fun value : ℝ => d * d ≤ value)
        (mul_one d)
        hmul
    have hscaled : D * (d * d) ≤ D * d :=
      mul_le_mul_of_nonneg_left hd_square_le_d hD
    have hleft :
        (C * d) * (C * d) = D * (d * d) := by
      have hstep1 :
          (C * d) * (C * d) = C * (d * (C * d)) :=
        mul_assoc C d (C * d)
      have hstep2 :
          C * (d * (C * d)) = C * ((d * C) * d) :=
        congrArg (fun value : ℝ => C * value)
          (mul_assoc d C d).symm
      have hstep3 :
          C * ((d * C) * d) = C * ((C * d) * d) :=
        congrArg
          (fun value : ℝ => C * (value * d))
          (mul_comm d C)
      have hstep4 :
          C * ((C * d) * d) = C * (C * (d * d)) :=
        congrArg (fun value : ℝ => C * value)
          (mul_assoc C d d)
      have hstep5 :
          C * (C * (d * d)) = (C * C) * (d * d) :=
        (mul_assoc C C (d * d)).symm
      have hstep6 :
          (C * C) * (d * d) = D * (d * d) := by
        rfl
      exact
        hstep1.trans
          (hstep2.trans
            (hstep3.trans
              (hstep4.trans
                (hstep5.trans hstep6))))
    exact Eq.subst
      (motive := fun value : ℝ => value ≤ D * d)
      hleft.symm
      hscaled
  exact ⟨D, k, hD, hbound⟩

/-- A real-axis prime-center spectral bound gives polynomial decay of the
prime-center Plancherel density. -/
theorem primeCenterPlancherelDensity_bound_of_spectralPolynomialBound
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C k) :
    ∃ D : ℝ, ∃ l : ℕ,
      0 ≤ D ∧
        ∀ index : ZetaPrimePowerIndex,
          ‖completedAutocorrelationSpectralTransform_primeCenterPlancherelDensity
              index f‖ ≤
            D * ZetaPrimePowerIndex.polynomialHeightDecay l index := by
  match
    primeCenterSampling_polynomialHeightDecay_square_bound
      C k hbound.left with
  | ⟨D, l, hD, hsquare⟩ =>
      have hdensity :
          ∀ index : ZetaPrimePowerIndex,
            ‖completedAutocorrelationSpectralTransform_primeCenterPlancherelDensity
                index f‖ ≤
              D * ZetaPrimePowerIndex.polynomialHeightDecay l index := by
        intro index
        let A : ℝ := ‖zetaCompletedSpectralLaplaceTransform f index.center‖
        let B : ℝ := C * ZetaPrimePowerIndex.polynomialHeightDecay k index
        have hA_nonnegative :
            0 ≤ A :=
          norm_nonneg
            (zetaCompletedSpectralLaplaceTransform f index.center)
        have hA_le_B : A ≤ B := hbound.right index
        have hB_nonnegative : 0 ≤ B :=
          le_trans hA_nonnegative hA_le_B
        have hsq : A * A ≤ B * B :=
          mul_le_mul hA_le_B hA_le_B hA_nonnegative hB_nonnegative
        have hdensity_norm :
            ‖completedAutocorrelationSpectralTransform_primeCenterPlancherelDensity
                index f‖ =
              A * A := by
          unfold completedAutocorrelationSpectralTransform_primeCenterPlancherelDensity
          unfold A
          have hnormSq_nonnegative :
              0 ≤ ‖zetaCompletedSpectralLaplaceTransform f index.center‖ ^ 2 :=
            sq_nonneg ‖zetaCompletedSpectralLaplaceTransform f index.center‖
          have hrealNorm :
              ‖‖zetaCompletedSpectralLaplaceTransform f index.center‖ ^ 2‖ =
                ‖zetaCompletedSpectralLaplaceTransform f index.center‖ ^ 2 :=
            Real.norm_of_nonneg hnormSq_nonnegative
          exact hrealNorm.trans
            (pow_two ‖zetaCompletedSpectralLaplaceTransform f index.center‖)
        have hB_expand :
            B * B =
              (C * ZetaPrimePowerIndex.polynomialHeightDecay k index) *
                (C * ZetaPrimePowerIndex.polynomialHeightDecay k index) := by
          unfold B
          rfl
        have htarget :
            B * B ≤ D * ZetaPrimePowerIndex.polynomialHeightDecay l index :=
          Eq.subst
            (motive := fun value : ℝ =>
              value ≤ D * ZetaPrimePowerIndex.polynomialHeightDecay l index)
            hB_expand.symm
            (hsquare index)
        exact Eq.subst
          (motive := fun value : ℝ =>
            value ≤ D * ZetaPrimePowerIndex.polynomialHeightDecay l index)
          hdensity_norm.symm
          (le_trans hsq htarget)
      exact ⟨D, l, hD, hdensity⟩

/-- A real-axis prime-center spectral bound gives polynomial decay of the
weighted prime-center sampling stream. -/
theorem weightedPrimeSampling_bound_of_spectralPolynomialBound
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C k) :
    ∃ D : ℝ, ∃ l : ℕ,
      0 ≤ D ∧
        ∀ index : ZetaPrimePowerIndex,
          ‖completedAutocorrelationSpectralTransform_weightedPrimeSampling
              index f‖ ≤
            D * ZetaPrimePowerIndex.polynomialHeightDecay l index := by
  match primeCenterPlancherelDensity_bound_of_spectralPolynomialBound
      f C k hbound with
  | ⟨D, l, hD, hdensity⟩ =>
      exact
        completedAutocorrelationSpectralTransform_weightedPrimeSampling_bound_of_density_bound_ownerTraceReconstruction
          f D l hD hdensity

/-- Polynomial decay of the weighted prime-center sampling stream gives
summability of that stream. -/
theorem weightedPrimeSampling_summable_of_weightedPolynomialBound
    (f : ZetaAdmissibleFunction) (D : ℝ) (l : ℕ)
    (hbound :
      ∀ index : ZetaPrimePowerIndex,
        ‖completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f‖ ≤
          D * ZetaPrimePowerIndex.polynomialHeightDecay l index) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f) := by
  exact
    Summable.of_norm_bounded
      (fun index : ZetaPrimePowerIndex =>
        D * ZetaPrimePowerIndex.polynomialHeightDecay l index)
      (ZetaPrimePowerIndex.summable_const_mul_polynomialHeightDecay D l)
      hbound

/-- A real-axis prime-center spectral bound gives summability of the completed
weighted prime-center sampling stream. -/
theorem weightedPrimeSampling_summable_of_spectralPolynomialBound
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f) := by
  match weightedPrimeSampling_bound_of_spectralPolynomialBound f C k hbound with
  | ⟨D, l, hdata⟩ =>
      exact weightedPrimeSampling_summable_of_weightedPolynomialBound
        f D l hdata.right

/-- Summability of the nonnegative completed weighted prime-center sampling
stream gives a finite-subtrace Bessel bound with the `tsum` as bound. -/
theorem weightedPrimeSampling_finiteSubtrace_upperBound_of_summable
    (f : ZetaAdmissibleFunction)
    (hsum :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f)) :
    ∃ C : ℝ,
      ∀ s : Finset ZetaPrimePowerIndex,
        ∑ index in s,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f ≤ C := by
  let C : ℝ :=
    ∑' index : ZetaPrimePowerIndex,
      completedAutocorrelationSpectralTransform_weightedPrimeSampling
        index f
  have hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f)
        C := by
    unfold C
    exact hsum.hasSum
  have hnonnegative :
      ∀ index : ZetaPrimePowerIndex,
        0 ≤
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f := by
    intro index
    exact
      completedAutocorrelationSpectralTransform_weightedPrimeSampling_nonnegative
        index f
  have hbound :
      ∀ s : Finset ZetaPrimePowerIndex,
        ∑ index in s,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f ≤ C := by
    intro s
    exact sum_le_hasSum
      s
      (fun index membership => hnonnegative index)
      hhasSum
  exact ⟨C, hbound⟩

/-- A real-axis prime-center spectral bound gives finite-subtrace Bessel
domination for the completed weighted prime-center sampling stream. -/
theorem weightedPrimeSampling_finiteSubtrace_upperBound_of_spectralPolynomialBound
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C k) :
    ∃ B : ℝ,
      ∀ s : Finset ZetaPrimePowerIndex,
        ∑ index in s,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f ≤ B := by
  exact
    weightedPrimeSampling_finiteSubtrace_upperBound_of_summable
      f
      (weightedPrimeSampling_summable_of_spectralPolynomialBound
        f C k hbound)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
