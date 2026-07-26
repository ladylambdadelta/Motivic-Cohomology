import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimePowerPackets
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.OwnerParts.Base
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.AtomicDistributionGaussianProbe
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.AtomicDistributionGaussianCutoffUniformPaleyWiener

/-!
# Completed prime-power sampling

This file owns the weighted prime-center sampling primitives attached to the
completed prime-power packet layer.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped BigOperators

namespace ZetaAdmissibleFunction

/-! ### Corrected vertical prime-center owner

Prime-power centers are real heights, while Paley--Wiener decay is a vertical
(Fourier) estimate.  The corrected sampling point therefore lies on the
imaginary axis; it is kept as a separate owner primitive so that the old
real-Laplace compatibility definitions cannot be mistaken for the analytic
sampling route.
-/

/-- The vertical Fourier point attached to a prime-power center. -/
noncomputable def completedPrimeCenterVerticalPoint
    (ι : ZetaPrimePowerIndex) : ℂ :=
  (ι.center : ℂ) * Complex.I

/-- The corrected prime-center point lies on the critical vertical line. -/
theorem completedPrimeCenterVerticalPoint_re
    (ι : ZetaPrimePowerIndex) :
    (completedPrimeCenterVerticalPoint ι).re = 0 := by
  unfold completedPrimeCenterVerticalPoint
  change (ι.center * 0 - 0 * 1) = 0
  exact sub_eq_zero.mpr
    (Eq.trans (mul_zero ι.center) (zero_mul (1 : ℝ)).symm)

/-- Its imaginary coordinate is the prime-power center. -/
theorem completedPrimeCenterVerticalPoint_im
    (ι : ZetaPrimePowerIndex) :
    (completedPrimeCenterVerticalPoint ι).im = ι.center := by
  unfold completedPrimeCenterVerticalPoint
  change (ι.center * 1 + 0 * 0) = ι.center
  exact Eq.trans
    (congrArg (fun value : ℝ => value + 0)
      (mul_one ι.center))
    (add_zero ι.center)

/-- Vertical Paley--Wiener decay is available at every corrected prime-center
sample, with the height variable exposed explicitly. -/
theorem completedPrimeCenterVerticalSample_decay_owner
    (f : ZetaAdmissibleFunction) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ι : ZetaPrimePowerIndex,
        ‖zetaCompletedExplicitFormulaPhi f
            (completedPrimeCenterVerticalPoint ι)‖ ≤
          C * (1 + ‖ι.center‖) ^ (-(N : ℤ)) := by
  match zetaPhi_verticalStripRapidDecay_of_admissible_owner f 0 0 N with
  | ⟨C, hC, hbound⟩ =>
      exact ⟨C, hC, fun ι =>
        let z := completedPrimeCenterVerticalPoint ι
        have hzre_lower : (0 : ℝ) ≤ z.re := by
          exact Eq.subst completedPrimeCenterVerticalPoint_re.symm
            (le_refl (0 : ℝ))
        have hzre_upper : z.re ≤ (0 : ℝ) := by
          exact Eq.subst completedPrimeCenterVerticalPoint_re.symm
            (le_refl (0 : ℝ))
        have hraw := hbound z hzre_lower hzre_upper
        have him : ‖z.im‖ = ‖ι.center‖ := by
          exact congrArg norm (completedPrimeCenterVerticalPoint_im ι)
        Eq.subst
          (motive := fun value : ℝ =>
            ‖zetaCompletedExplicitFormulaPhi f z‖ ≤
              C * (1 + value) ^ (-(N : ℤ)))
          him.symm
          hraw⟩

/-- The corrected prime-center Plancherel density, sampled on the vertical
Fourier axis. -/
noncomputable def completedAutocorrelationSpectralTransform_verticalPrimeCenterPlancherelDensity
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  ‖zetaCompletedExplicitFormulaPhi f (completedPrimeCenterVerticalPoint ι)‖ ^ 2

/-- The corrected vertical prime-center density is nonnegative. -/
theorem completedAutocorrelationSpectralTransform_verticalPrimeCenterPlancherelDensity_nonnegative
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    0 ≤
      completedAutocorrelationSpectralTransform_verticalPrimeCenterPlancherelDensity
        ι f :=
  sq_nonneg
    ‖zetaCompletedExplicitFormulaPhi f (completedPrimeCenterVerticalPoint ι)‖

/-! The density decay is the squared form of the vertical Paley--Wiener
estimate.  This is kept at the sampling owner so later Bessel and trace files
consume a proved analytic statement rather than reconstructing the square
estimate locally. -/

theorem completedAutocorrelationSpectralTransform_verticalPrimeCenterPlancherelDensity_decay_owner
    (f : ZetaAdmissibleFunction) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ι : ZetaPrimePowerIndex,
        completedAutocorrelationSpectralTransform_verticalPrimeCenterPlancherelDensity
            ι f ≤
          (C * (1 + ‖ι.center‖) ^ (-(N : ℤ))) ^ 2 := by
  match completedPrimeCenterVerticalSample_decay_owner f N with
  | ⟨C, hC, hsample⟩ =>
      exact ⟨C, hC, fun ι =>
        let A : ℝ :=
          ‖zetaCompletedExplicitFormulaPhi f
            (completedPrimeCenterVerticalPoint ι)‖
        let B : ℝ := C * (1 + ‖ι.center‖) ^ (-(N : ℤ))
        have hAB : A ≤ B := by
          unfold A B
          exact hsample ι
        have hA : 0 ≤ A := norm_nonneg _
        have hB : 0 ≤ B := le_trans hA hAB
        have hsq : A * A ≤ B * B :=
          mul_le_mul hAB hAB hA hB
        have hleft :
            completedAutocorrelationSpectralTransform_verticalPrimeCenterPlancherelDensity
                ι f = A * A := by
          unfold completedAutocorrelationSpectralTransform_verticalPrimeCenterPlancherelDensity
          unfold A
          exact (pow_two _).symm
        have hright :
            B * B = (C * (1 + ‖ι.center‖) ^ (-(N : ℤ))) ^ 2 := by
          unfold B
          exact (pow_two _).symm
        calc
          completedAutocorrelationSpectralTransform_verticalPrimeCenterPlancherelDensity
              ι f = A * A := hleft
          _ ≤ B * B := hsq
          _ = (C * (1 + ‖ι.center‖) ^ (-(N : ℤ))) ^ 2 := hright⟩

/-- The corrected weighted prime-center sampling family. -/
noncomputable def completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  ZetaPrimePowerIndex.weight ι *
    completedAutocorrelationSpectralTransform_verticalPrimeCenterPlancherelDensity
      ι f

/-- Square-root-weighted vertical Fourier amplitude at a prime-power center. -/
noncomputable def zetaCompletedPrimeVerticalSpectralAmplitudeIndex
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℂ :=
  (ZetaPrimePowerIndex.sqrtWeight ι : ℂ) *
    zetaCompletedExplicitFormulaPhi f (completedPrimeCenterVerticalPoint ι)

theorem zetaCompletedPrimeVerticalSpectralAmplitudeIndex_norm_sq_eq_weightedVerticalSample
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    ‖zetaCompletedPrimeVerticalSpectralAmplitudeIndex ι f‖ ^ 2 =
      completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling
        ι f := by
  let r : ℝ := ZetaPrimePowerIndex.sqrtWeight ι
  let A : ℂ :=
    zetaCompletedExplicitFormulaPhi f (completedPrimeCenterVerticalPoint ι)
  have hr_nonneg : 0 ≤ r := by
    exact Real.sqrt_nonneg _
  have hnorm_r : ‖(r : ℂ)‖ = r := by
    calc
      ‖(r : ℂ)‖ = |r| := by
        exact RCLike.norm_ofReal r
      _ = r := by
        exact abs_of_nonneg hr_nonneg
  have hnorm : ‖(r : ℂ) * A‖ = r * ‖A‖ := by
    calc
      ‖(r : ℂ) * A‖ = ‖(r : ℂ)‖ * ‖A‖ := by
        exact norm_mul (r : ℂ) A
      _ = r * ‖A‖ := by
        exact congrArg (fun x : ℝ => x * ‖A‖) hnorm_r
  have hweight : r * r = ZetaPrimePowerIndex.weight ι := by
    exact ZetaPrimePowerIndex.sqrtWeight_mul_self ι
  have hleft :
      ‖zetaCompletedPrimeVerticalSpectralAmplitudeIndex ι f‖ ^ 2 =
        (r * ‖A‖) ^ 2 := by
    unfold zetaCompletedPrimeVerticalSpectralAmplitudeIndex
    unfold r A
    exact congrArg (fun x : ℝ => x ^ 2) hnorm
  have hmiddle :
      (r * ‖A‖) ^ 2 =
        ZetaPrimePowerIndex.weight ι * ‖A‖ ^ 2 := by
    exact real_mul_norm_square_from_weight r ‖A‖
      (ZetaPrimePowerIndex.weight ι) hweight
  have hright :
      ZetaPrimePowerIndex.weight ι * ‖A‖ ^ 2 =
        completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling
          ι f := by
    unfold completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling
    unfold completedAutocorrelationSpectralTransform_verticalPrimeCenterPlancherelDensity
    unfold A
    exact Eq.refl
  exact hleft.trans (hmiddle.trans hright)

/-- The opposite vertical Fourier amplitude is owned by reflection of the
positive vertical packet. -/
noncomputable def zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedPrimeVerticalSpectralAmplitudeIndex
    ι (ZetaAdmissibleFunction.reflect f)

theorem zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_norm_sq_eq_reflectedWeightedVerticalSample
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    ‖zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex ι f‖ ^ 2 =
      completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling
        ι (ZetaAdmissibleFunction.reflect f) := by
  unfold zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex
  exact zetaCompletedPrimeVerticalSpectralAmplitudeIndex_norm_sq_eq_weightedVerticalSample
    ι (ZetaAdmissibleFunction.reflect f)

/-- The corrected weighted sample is weight times vertical density. -/
theorem completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling_eq_weight_mul_density
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling
        ι f =
      ZetaPrimePowerIndex.weight ι *
        completedAutocorrelationSpectralTransform_verticalPrimeCenterPlancherelDensity
          ι f :=
  Eq.refl
    (completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling
      ι f)

/-- The corrected weighted vertical sample is nonnegative. -/
theorem completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling_nonnegative
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    0 ≤ completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling
      ι f :=
  mul_nonneg
    (ZetaPrimePowerIndex.weight_nonnegative ι)
    (completedAutocorrelationSpectralTransform_verticalPrimeCenterPlancherelDensity_nonnegative
      ι f)

/-- Summability owner for the corrected vertical sampling lane.  The analytic
majorant is supplied at this boundary; all positivity and series transport
are discharged here before Bessel or trace consumers are entered. -/
theorem completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling_summable_of_majorant
    (f : ZetaAdmissibleFunction) (D : ℝ) (k : ℕ)
    (hbound : ∀ ι : ZetaPrimePowerIndex,
      completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling
          ι f ≤
        D * ZetaPrimePowerIndex.polynomialHeightDecay k ι) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling
          ι f) :=
  Summable.of_nonneg_of_le
    (fun ι =>
      completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling_nonnegative
        ι f)
    hbound
    (ZetaPrimePowerIndex.summable_const_mul_polynomialHeightDecay D k)

/-- Finite vertical weighted sampling mass in the genuine prime-power window. -/
noncomputable def completedAutocorrelationSpectralTransform_verticalWeightedPrimeSamplingWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  ∑ ι in ZetaPrimePowerIndex.window N,
    completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling
      ι f

/-! ### Gaussian localization bridge

The canonical Gaussian cutoff sequence is already an admissible probe.  These
owners connect that sequence to the corrected vertical prime sampler without
reintroducing the invalid real-axis polynomial envelope. -/

noncomputable def completedGaussianCutoffVerticalWeightedPrimeSampling
    (n : ℕ) (ι : ZetaPrimePowerIndex) : ℝ :=
  completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling
    ι (ZetaAdmissibleFunction.admissibleGaussianCutoffNat n)

theorem completedGaussianCutoffVerticalWeightedPrimeSampling_nonnegative
    (n : ℕ) (ι : ZetaPrimePowerIndex) :
    0 ≤ completedGaussianCutoffVerticalWeightedPrimeSampling n ι := by
  unfold completedGaussianCutoffVerticalWeightedPrimeSampling
  exact completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling_nonnegative
    ι (ZetaAdmissibleFunction.admissibleGaussianCutoffNat n)

noncomputable def completedGaussianCutoffVerticalWeightedPrimeSamplingWindow
    (n N : ℕ) : ℝ :=
  ∑ ι in ZetaPrimePowerIndex.window N,
    completedGaussianCutoffVerticalWeightedPrimeSampling n ι

theorem completedGaussianCutoffVerticalWeightedPrimeSamplingWindow_eq_source
    (n N : ℕ) :
    completedGaussianCutoffVerticalWeightedPrimeSamplingWindow n N =
      completedAutocorrelationSpectralTransform_verticalWeightedPrimeSamplingWindow
        N (ZetaAdmissibleFunction.admissibleGaussianCutoffNat n) := by
  unfold completedGaussianCutoffVerticalWeightedPrimeSamplingWindow
  unfold completedGaussianCutoffVerticalWeightedPrimeSampling
  exact Eq.refl _

theorem completedGaussianCutoffVerticalWeightedPrimeSamplingWindow_nonnegative
    (n N : ℕ) :
    0 ≤ completedGaussianCutoffVerticalWeightedPrimeSamplingWindow n N := by
  unfold completedGaussianCutoffVerticalWeightedPrimeSamplingWindow
  exact Finset.sum_nonneg
    (fun ι hι => completedGaussianCutoffVerticalWeightedPrimeSampling_nonnegative n ι)

theorem completedGaussianCutoffVerticalWeightedPrimeSamplingWindow_le_majorantWindow
    (n N : ℕ) (D : ℝ) (k : ℕ)
    (hbound : ∀ ι : ZetaPrimePowerIndex,
      completedGaussianCutoffVerticalWeightedPrimeSampling n ι ≤
        D * ZetaPrimePowerIndex.polynomialHeightDecay k ι) :
    completedGaussianCutoffVerticalWeightedPrimeSamplingWindow n N ≤
      ∑ ι in ZetaPrimePowerIndex.window N,
        D * ZetaPrimePowerIndex.polynomialHeightDecay k ι := by
  unfold completedGaussianCutoffVerticalWeightedPrimeSamplingWindow
  exact Finset.sum_le_sum (fun ι hι => hbound ι)

theorem completedGaussianCutoffVerticalSpectralEval_highFrequencyDecay_owner
    (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, ∀ ι : ZetaPrimePowerIndex,
        1 ≤ ‖ι.center‖ →
        ‖zetaSpectralEval
            (ZetaAdmissibleFunction.admissibleGaussianCutoffNat n)
            ((0 : ℝ) +
              (((1 : ℝ) * (ι.center - 0) : ℝ) : ℂ) * Complex.I)‖ ≤
          C * (1 + ‖ι.center‖) ^ (-(N : ℤ)) := by
  match admissibleGaussianCutoffNat_uniformPaleyWiener_highAffineFrequency
      0 1 (by exact zero_lt_one) N with
  | ⟨C, hC, hbound⟩ =>
      exact ⟨C, hC, fun n ι hι =>
        hbound n 0 ι.center
          (by
            have hzero : |(0 : ℝ)| = 0 := abs_zero
            exact Eq.subst
              (motive := fun value : ℝ => value ≤ 1)
              hzero.symm
              zero_le_one)
          (by exact hι)⟩

theorem completedGaussianCutoffVerticalSpectralEval_decay_owner
    (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, ∀ ι : ZetaPrimePowerIndex,
        ‖zetaSpectralEval
            (ZetaAdmissibleFunction.admissibleGaussianCutoffNat n)
            ((0 : ℝ) +
              (((1 : ℝ) * (ι.center - 0) : ℝ) : ℂ) * Complex.I)‖ ≤
          C * (1 + ‖ι.center‖) ^ (-(N : ℤ)) := by
  match admissibleGaussianCutoffNat_uniformPaleyWiener_shiftedScale
      0 1 (by exact zero_lt_one) N with
  | ⟨C, hC, hbound⟩ =>
      exact ⟨C, hC, fun n ι =>
        hbound n 0 ι.center
          (by
            have hzero : |(0 : ℝ)| = 0 := abs_zero
            exact Eq.subst
              (motive := fun value : ℝ => value ≤ 1)
              hzero.symm
              zero_le_one)⟩

/-! The Gaussian spectral-evaluation stream is kept distinct from the
completed autocorrelation stream: the former is the quantity controlled by the
uniform Gaussian Paley--Wiener theorem above. -/

noncomputable def completedGaussianCutoffVerticalSpectralEvalWeightedPrimeSampling
    (n : ℕ) (ι : ZetaPrimePowerIndex) : ℝ :=
  ZetaPrimePowerIndex.weight ι *
    ‖zetaSpectralEval
      (ZetaAdmissibleFunction.admissibleGaussianCutoffNat n)
      ((0 : ℝ) + (((1 : ℝ) * (ι.center - 0) : ℝ) : ℂ) * Complex.I)‖ ^ 2

noncomputable def completedGaussianCutoffVerticalSpectralEvalAmplitude
    (n : ℕ) (ι : ZetaPrimePowerIndex) : ℂ :=
  (ZetaPrimePowerIndex.sqrtWeight ι : ℂ) *
    zetaSpectralEval
      (ZetaAdmissibleFunction.admissibleGaussianCutoffNat n)
      ((0 : ℝ) + (((1 : ℝ) * (ι.center - 0) : ℝ) : ℂ) * Complex.I)

theorem completedGaussianCutoffVerticalSpectralEvalAmplitude_norm_sq_eq_weightedSample
    (n : ℕ) (ι : ZetaPrimePowerIndex) :
    ‖completedGaussianCutoffVerticalSpectralEvalAmplitude n ι‖ ^ 2 =
      completedGaussianCutoffVerticalSpectralEvalWeightedPrimeSampling n ι := by
  let r : ℝ := ZetaPrimePowerIndex.sqrtWeight ι
  let A : ℂ :=
    zetaSpectralEval
      (ZetaAdmissibleFunction.admissibleGaussianCutoffNat n)
      ((0 : ℝ) + (((1 : ℝ) * (ι.center - 0) : ℝ) : ℂ) * Complex.I)
  have hr_nonneg : 0 ≤ r := by
    exact Real.sqrt_nonneg _
  have hnorm_r : ‖(r : ℂ)‖ = r := by
    calc
      ‖(r : ℂ)‖ = |r| := by exact RCLike.norm_ofReal r
      _ = r := by exact abs_of_nonneg hr_nonneg
  have hnorm : ‖(r : ℂ) * A‖ = r * ‖A‖ := by
    calc
      ‖(r : ℂ) * A‖ = ‖(r : ℂ)‖ * ‖A‖ := by exact norm_mul (r : ℂ) A
      _ = r * ‖A‖ := by exact congrArg (fun x : ℝ => x * ‖A‖) hnorm_r
  have hweight : r * r = ZetaPrimePowerIndex.weight ι := by
    exact ZetaPrimePowerIndex.sqrtWeight_mul_self ι
  have hleft :
      ‖completedGaussianCutoffVerticalSpectralEvalAmplitude n ι‖ ^ 2 =
        (r * ‖A‖) ^ 2 := by
    unfold completedGaussianCutoffVerticalSpectralEvalAmplitude
    unfold r A
    exact congrArg (fun x : ℝ => x ^ 2) hnorm
  have hmiddle :
      (r * ‖A‖) ^ 2 = ZetaPrimePowerIndex.weight ι * ‖A‖ ^ 2 := by
    exact real_mul_norm_square_from_weight r ‖A‖
      (ZetaPrimePowerIndex.weight ι) hweight
  have hright :
      ZetaPrimePowerIndex.weight ι * ‖A‖ ^ 2 =
        completedGaussianCutoffVerticalSpectralEvalWeightedPrimeSampling n ι := by
    unfold completedGaussianCutoffVerticalSpectralEvalWeightedPrimeSampling
    unfold A
    exact Eq.refl _
  exact hleft.trans (hmiddle.trans hright)

theorem completedGaussianCutoffVerticalSpectralEvalWeightedPrimeSampling_nonnegative
    (n : ℕ) (ι : ZetaPrimePowerIndex) :
    0 ≤ completedGaussianCutoffVerticalSpectralEvalWeightedPrimeSampling n ι := by
  unfold completedGaussianCutoffVerticalSpectralEvalWeightedPrimeSampling
  exact mul_nonneg
    (ZetaPrimePowerIndex.weight_nonnegative ι)
    (sq_nonneg _)

theorem completedGaussianCutoffVerticalSpectralEvalWeightedPrimeSampling_decay_owner
    (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, ∀ ι : ZetaPrimePowerIndex,
        completedGaussianCutoffVerticalSpectralEvalWeightedPrimeSampling n ι ≤
          ZetaPrimePowerIndex.weight ι *
            (C * (1 + ‖ι.center‖) ^ (-(N : ℤ))) ^ 2 := by
  match completedGaussianCutoffVerticalSpectralEval_decay_owner N with
  | ⟨C, hC, hdecay⟩ =>
      exact ⟨C, hC, fun n ι =>
        let A : ℝ :=
          ‖zetaSpectralEval
            (ZetaAdmissibleFunction.admissibleGaussianCutoffNat n)
            ((0 : ℝ) +
              (((1 : ℝ) * (ι.center - 0) : ℝ) : ℂ) * Complex.I)‖
        let B : ℝ := C * (1 + ‖ι.center‖) ^ (-(N : ℤ))
        have hAB : A ≤ B := by
          unfold A B
          exact hdecay n ι
        have hA : 0 ≤ A := norm_nonneg _
        have hB : 0 ≤ B := le_trans hA hAB
        have hsq : A * A ≤ B * B := mul_le_mul hAB hAB hA hB
        have hweighted :
            ZetaPrimePowerIndex.weight ι * (A * A) ≤
              ZetaPrimePowerIndex.weight ι * (B * B) :=
          mul_le_mul_of_nonneg_left hsq
            (ZetaPrimePowerIndex.weight_nonnegative ι)
        have hleft :
            completedGaussianCutoffVerticalSpectralEvalWeightedPrimeSampling n ι =
              ZetaPrimePowerIndex.weight ι * (A * A) := by
          unfold completedGaussianCutoffVerticalSpectralEvalWeightedPrimeSampling
          unfold A
          exact congrArg (fun value : ℝ =>
            ZetaPrimePowerIndex.weight ι * value) (pow_two _).symm
        have hright :
            ZetaPrimePowerIndex.weight ι * (B * B) =
              ZetaPrimePowerIndex.weight ι *
                (C * (1 + ‖ι.center‖) ^ (-(N : ℤ))) ^ 2 := by
          unfold B
          exact congrArg (fun value : ℝ =>
            ZetaPrimePowerIndex.weight ι * value) (pow_two _).symm
        calc
          completedGaussianCutoffVerticalSpectralEvalWeightedPrimeSampling n ι =
              ZetaPrimePowerIndex.weight ι * (A * A) := hleft
          _ ≤ ZetaPrimePowerIndex.weight ι * (B * B) := hweighted
          _ = ZetaPrimePowerIndex.weight ι *
                (C * (1 + ‖ι.center‖) ^ (-(N : ℤ))) ^ 2 := hright⟩

theorem completedGaussianCutoffVerticalSpectralEvalAmplitude_norm_sq_decay_owner
    (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, ∀ ι : ZetaPrimePowerIndex,
        ‖completedGaussianCutoffVerticalSpectralEvalAmplitude n ι‖ ^ 2 ≤
          ZetaPrimePowerIndex.weight ι *
            (C * (1 + ‖ι.center‖) ^ (-(N : ℤ))) ^ 2 := by
  match completedGaussianCutoffVerticalSpectralEvalWeightedPrimeSampling_decay_owner N with
  | ⟨C, hC, hbound⟩ =>
      exact ⟨C, hC, fun n ι =>
        Eq.subst
          (motive := fun value : ℝ =>
            value ≤ ZetaPrimePowerIndex.weight ι *
              (C * (1 + ‖ι.center‖) ^ (-(N : ℤ))) ^ 2)
          (completedGaussianCutoffVerticalSpectralEvalAmplitude_norm_sq_eq_weightedSample
            n ι).symm
          (hbound n ι)⟩

noncomputable def completedGaussianCutoffVerticalSpectralEvalWeightedPrimeSamplingWindow
    (n N : ℕ) : ℝ :=
  ∑ ι in ZetaPrimePowerIndex.window N,
    completedGaussianCutoffVerticalSpectralEvalWeightedPrimeSampling n ι

theorem completedGaussianCutoffVerticalSpectralEvalWeightedPrimeSamplingWindow_nonnegative
    (n N : ℕ) :
    0 ≤ completedGaussianCutoffVerticalSpectralEvalWeightedPrimeSamplingWindow n N := by
  unfold completedGaussianCutoffVerticalSpectralEvalWeightedPrimeSamplingWindow
  exact Finset.sum_nonneg
    (fun ι hι =>
      completedGaussianCutoffVerticalSpectralEvalWeightedPrimeSampling_nonnegative n ι)

theorem completedGaussianCutoffVerticalSpectralEvalWeightedPrimeSamplingWindow_le_decayWindow
    (n N degree : ℕ) (C : ℝ)
    (hbound : ∀ ι : ZetaPrimePowerIndex,
      completedGaussianCutoffVerticalSpectralEvalWeightedPrimeSampling n ι ≤
        ZetaPrimePowerIndex.weight ι *
          (C * (1 + ‖ι.center‖) ^ (-(degree : ℤ))) ^ 2) :
    completedGaussianCutoffVerticalSpectralEvalWeightedPrimeSamplingWindow n N ≤
      ∑ ι in ZetaPrimePowerIndex.window N,
        ZetaPrimePowerIndex.weight ι *
          (C * (1 + ‖ι.center‖) ^ (-(degree : ℤ))) ^ 2 := by
  unfold completedGaussianCutoffVerticalSpectralEvalWeightedPrimeSamplingWindow
  exact Finset.sum_le_sum (fun ι hι => hbound ι)

theorem completedGaussianCutoffVerticalSpectralEvalWeightedPrimeSamplingWindow_le_decayWindow_owner
    (n N degree : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      completedGaussianCutoffVerticalSpectralEvalWeightedPrimeSamplingWindow n N ≤
        ∑ ι in ZetaPrimePowerIndex.window N,
          ZetaPrimePowerIndex.weight ι *
            (C * (1 + ‖ι.center‖) ^ (-(degree : ℤ))) ^ 2 := by
  match completedGaussianCutoffVerticalSpectralEvalWeightedPrimeSampling_decay_owner degree with
  | ⟨C, hC, hbound⟩ =>
      exact ⟨C, hC,
        completedGaussianCutoffVerticalSpectralEvalWeightedPrimeSamplingWindow_le_decayWindow
          n N degree C hbound⟩

noncomputable def completedGaussianCutoffVerticalSpectralEvalAmplitudeWindowEnergy
    (n N : ℕ) : ℝ :=
  ∑ ι in ZetaPrimePowerIndex.window N,
    ‖completedGaussianCutoffVerticalSpectralEvalAmplitude n ι‖ ^ 2

theorem completedGaussianCutoffVerticalSpectralEvalAmplitudeWindowEnergy_eq_weightedWindow
    (n N : ℕ) :
    completedGaussianCutoffVerticalSpectralEvalAmplitudeWindowEnergy n N =
      completedGaussianCutoffVerticalSpectralEvalWeightedPrimeSamplingWindow n N := by
  unfold completedGaussianCutoffVerticalSpectralEvalAmplitudeWindowEnergy
  unfold completedGaussianCutoffVerticalSpectralEvalWeightedPrimeSamplingWindow
  exact Finset.sum_congr rfl
    (fun ι hι =>
      completedGaussianCutoffVerticalSpectralEvalAmplitude_norm_sq_eq_weightedSample
        n ι)

theorem completedGaussianCutoffVerticalSpectralEvalAmplitudeWindowEnergy_nonnegative
    (n N : ℕ) :
    0 ≤ completedGaussianCutoffVerticalSpectralEvalAmplitudeWindowEnergy n N := by
  unfold completedGaussianCutoffVerticalSpectralEvalAmplitudeWindowEnergy
  exact Finset.sum_nonneg
    (fun ι hι => sq_nonneg
      ‖completedGaussianCutoffVerticalSpectralEvalAmplitude n ι‖)

/-! The Gaussian window energy is the amplitude-side form of the decay
window.  Keeping this transport at the Gaussian owner prevents downstream
Bessel files from reopening the pointwise norm-square calculation. -/

theorem completedGaussianCutoffVerticalSpectralEvalAmplitudeWindowEnergy_le_decayWindow_owner
    (n N degree : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      completedGaussianCutoffVerticalSpectralEvalAmplitudeWindowEnergy n N ≤
        ∑ ι in ZetaPrimePowerIndex.window N,
          ZetaPrimePowerIndex.weight ι *
            (C * (1 + ‖ι.center‖) ^ (-(degree : ℤ))) ^ 2 := by
  match
    completedGaussianCutoffVerticalSpectralEvalWeightedPrimeSamplingWindow_le_decayWindow_owner
      n N degree with
  | ⟨C, hC, hwindow⟩ =>
      exact ⟨C, hC,
        Eq.subst
          (motive := fun value : ℝ => value ≤
            ∑ ι in ZetaPrimePowerIndex.window N,
              ZetaPrimePowerIndex.weight ι *
                (C * (1 + ‖ι.center‖) ^ (-(degree : ℤ))) ^ 2)
          (completedGaussianCutoffVerticalSpectralEvalAmplitudeWindowEnergy_eq_weightedWindow
            n N).symm
          hwindow⟩

/-- The corrected finite vertical window is nonnegative. -/
theorem completedAutocorrelationSpectralTransform_verticalWeightedPrimeSamplingWindow_nonnegative
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    0 ≤
      completedAutocorrelationSpectralTransform_verticalWeightedPrimeSamplingWindow
        N f := by
  unfold completedAutocorrelationSpectralTransform_verticalWeightedPrimeSamplingWindow
  exact Finset.sum_nonneg
    (fun ι hι =>
      completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling_nonnegative
        ι f)

/-- A pointwise vertical polynomial majorant transports to every finite window. -/
theorem completedAutocorrelationSpectralTransform_verticalWeightedPrimeSamplingWindow_le_majorantWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) (D : ℝ) (k : ℕ)
    (hbound : ∀ ι : ZetaPrimePowerIndex,
      completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling
          ι f ≤
        D * ZetaPrimePowerIndex.polynomialHeightDecay k ι) :
    completedAutocorrelationSpectralTransform_verticalWeightedPrimeSamplingWindow
        N f ≤
      ∑ ι in ZetaPrimePowerIndex.window N,
        D * ZetaPrimePowerIndex.polynomialHeightDecay k ι := by
  unfold completedAutocorrelationSpectralTransform_verticalWeightedPrimeSamplingWindow
  exact Finset.sum_le_sum
    (fun ι hι => hbound ι)

/-- The weighted prime-center sampling family for the completed autocorrelation
spectral transform. -/
noncomputable def completedAutocorrelationSpectralTransform_weightedPrimeSampling
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  ZetaPrimePowerIndex.weight ι *
    ‖zetaCompletedSpectralLaplaceTransform f ι.center‖ ^ 2

/-- The prime-center Plancherel/localization density of the completed
autocorrelation spectral transform before inserting the explicit prime-power
weight. -/
noncomputable def completedAutocorrelationSpectralTransform_primeCenterPlancherelDensity
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  ‖zetaCompletedSpectralLaplaceTransform f ι.center‖ ^ 2

/-- The prime-center Plancherel/localization density is nonnegative. -/
theorem completedAutocorrelationSpectralTransform_primeCenterPlancherelDensity_nonnegative
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    0 ≤
      completedAutocorrelationSpectralTransform_primeCenterPlancherelDensity
        ι f :=
  sq_nonneg ‖zetaCompletedSpectralLaplaceTransform f ι.center‖

/-- Weighted prime sampling is the explicit prime-power weight times the
completed autocorrelation prime-center Plancherel/localization density. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_eq_weight_mul_density
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    completedAutocorrelationSpectralTransform_weightedPrimeSampling ι f =
      ZetaPrimePowerIndex.weight ι *
        completedAutocorrelationSpectralTransform_primeCenterPlancherelDensity
          ι f :=
  Eq.refl (completedAutocorrelationSpectralTransform_weightedPrimeSampling ι f)

/-- Weighted prime sampling is nonnegative. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_nonnegative
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    0 ≤ completedAutocorrelationSpectralTransform_weightedPrimeSampling ι f :=
  let hweight : 0 ≤ ZetaPrimePowerIndex.weight ι :=
    ZetaPrimePowerIndex.weight_nonnegative ι
  let hdensity :
      0 ≤
        completedAutocorrelationSpectralTransform_primeCenterPlancherelDensity
          ι f :=
    completedAutocorrelationSpectralTransform_primeCenterPlancherelDensity_nonnegative
      ι f
  Eq.subst
    (motive := fun x : ℝ =>
      0 ≤ x)
    (completedAutocorrelationSpectralTransform_weightedPrimeSampling_eq_weight_mul_density
      ι f).symm
    (mul_nonneg hweight hdensity)

/-- Nongenuine prime-power indices have zero weighted prime sampling. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_eq_zero_of_not_isGenuine
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (hι : ¬ ZetaPrimePowerIndex.IsGenuine ι) :
    completedAutocorrelationSpectralTransform_weightedPrimeSampling ι f = 0 :=
  let hweight : ZetaPrimePowerIndex.weight ι = 0 :=
    ZetaPrimePowerIndex.weight_eq_zero_of_not_isGenuine ι hι
  Eq.trans
    (congrArg
      (fun x : ℝ =>
        x * ‖zetaCompletedSpectralLaplaceTransform f ι.center‖ ^ 2)
      hweight)
    (zero_mul (‖zetaCompletedSpectralLaplaceTransform f ι.center‖ ^ 2))

/-- Rectangular boxes and genuine prime-power windows give the same weighted
prime-sampling sum, because nongenuine indices have zero completed prime
weight. -/
theorem sum_box_completedAutocorrelationSpectralTransform_weightedPrimeSampling_eq_sum_window
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (∑ ι in ZetaPrimePowerIndex.box N,
      completedAutocorrelationSpectralTransform_weightedPrimeSampling ι f) =
      ∑ ι in ZetaPrimePowerIndex.window N,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling ι f :=
  ZetaPrimePowerIndex.sum_box_eq_sum_window_of_zero_not_isGenuine
    (fun ι : ZetaPrimePowerIndex =>
      completedAutocorrelationSpectralTransform_weightedPrimeSampling ι f)
    (fun ι hι =>
      completedAutocorrelationSpectralTransform_weightedPrimeSampling_eq_zero_of_not_isGenuine
        ι f hι)
    N

/-- The finite weighted prime-power sampling mass of the completed
autocorrelation spectral transform over the genuine prime-power window. -/
noncomputable def completedAutocorrelationSpectralTransform_weightedPrimeSamplingWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  ∑ ι in ZetaPrimePowerIndex.window N,
    completedAutocorrelationSpectralTransform_weightedPrimeSampling ι f

/-- The weighted prime-power sampling window unfolds to the finite
genuine-window sum. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSamplingWindow_eq_sum
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedAutocorrelationSpectralTransform_weightedPrimeSamplingWindow N f =
      ∑ ι in ZetaPrimePowerIndex.window N,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling ι f :=
  Eq.refl (completedAutocorrelationSpectralTransform_weightedPrimeSamplingWindow N f)

/-- The rectangular box sampling sum equals the genuine weighted prime-power
sampling window. -/
theorem sum_box_completedAutocorrelationSpectralTransform_weightedPrimeSampling_eq_window
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (∑ ι in ZetaPrimePowerIndex.box N,
      completedAutocorrelationSpectralTransform_weightedPrimeSampling ι f) =
      completedAutocorrelationSpectralTransform_weightedPrimeSamplingWindow N f :=
  Eq.trans
    (sum_box_completedAutocorrelationSpectralTransform_weightedPrimeSampling_eq_sum_window
      N f)
    (completedAutocorrelationSpectralTransform_weightedPrimeSamplingWindow_eq_sum
      N f).symm

/-- The finite weighted prime-power sampling mass is nonnegative. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSamplingWindow_nonnegative
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    0 ≤
      completedAutocorrelationSpectralTransform_weightedPrimeSamplingWindow
        N f :=
  Finset.sum_nonneg
    (fun ι hι =>
      completedAutocorrelationSpectralTransform_weightedPrimeSampling_nonnegative
        ι f)

/-- The finite weighted prime-power sampling mass is the finite sum of the
explicit prime-power weights times the prime-center Plancherel/localization
density. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSamplingWindow_eq_weight_mul_density_sum
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedAutocorrelationSpectralTransform_weightedPrimeSamplingWindow N f =
      ∑ ι in ZetaPrimePowerIndex.window N,
        ZetaPrimePowerIndex.weight ι *
          completedAutocorrelationSpectralTransform_primeCenterPlancherelDensity
            ι f :=
  Finset.sum_congr
    (Eq.refl (ZetaPrimePowerIndex.window N))
    (fun ι hι =>
      completedAutocorrelationSpectralTransform_weightedPrimeSampling_eq_weight_mul_density
        ι f)

/-- The positive seed-face weighted sample-square is the completed
spectral-transform weighted prime sampling family. -/
theorem zetaCompletedPrimePositiveWeightedSampleNormSq_eq_weightedPrimeSampling
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimePositiveWeightedSampleNormSq ι f =
      completedAutocorrelationSpectralTransform_weightedPrimeSampling ι f :=
  Eq.refl (zetaCompletedPrimePositiveWeightedSampleNormSq ι f)

/-- The opposite weighted prime-center sample-square is the positive
sample-square of the reflected seed. -/
theorem zetaCompletedPrimeOppositeWeightedSampleNormSq_eq_positive_reflect
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeOppositeWeightedSampleNormSq ι f =
      zetaCompletedPrimePositiveWeightedSampleNormSq ι
        (ZetaAdmissibleFunction.reflect f) :=
  let hsample :
      zetaCompletedPrimeHermitianNegativeSeedAmplitude ι.p ι.n f =
        zetaCompletedPrimeHermitianSeedAmplitude ι.p ι.n
          (ZetaAdmissibleFunction.reflect f) :=
    (zetaCompletedExplicitFormulaPhi_reflect f
      (zetaPrimePacketCenter ι.p ι.n)).symm
  congrArg
    (fun A : ℂ => ZetaPrimePowerIndex.weight ι * ‖A‖ ^ 2)
    hsample

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
