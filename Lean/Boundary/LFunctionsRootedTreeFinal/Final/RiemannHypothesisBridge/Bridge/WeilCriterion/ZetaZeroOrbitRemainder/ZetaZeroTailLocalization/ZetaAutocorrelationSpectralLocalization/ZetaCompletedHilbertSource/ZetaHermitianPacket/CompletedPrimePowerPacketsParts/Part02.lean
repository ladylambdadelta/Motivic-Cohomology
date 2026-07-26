import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimePowerPacketsParts.Part01

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The prime spectral majorant for the two real-axis amplitude families.

This is a comparison majorant for estimates after a contour realization supplies
summability; the code does not treat independent real-axis Laplace seed samples
as intrinsically square-summable. -/
noncomputable def zetaCompletedPrimeSpectralCoordinateMajorant
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  ‖zetaCompletedPrimeSpectralAmplitudeIndex ι f‖ ^ 2 +
    ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f‖ ^ 2

/-- The positive weighted prime sample norm square before the square-root-weight
amplitude packaging. -/
noncomputable def zetaCompletedPrimePositiveWeightedSampleNormSq
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  ZetaPrimePowerIndex.weight ι *
    ‖zetaCompletedPrimeHermitianSeedAmplitude ι.p ι.n f‖ ^ 2

/-- The opposite weighted prime sample norm square before the square-root-weight
amplitude packaging. -/
noncomputable def zetaCompletedPrimeOppositeWeightedSampleNormSq
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  ZetaPrimePowerIndex.weight ι *
    ‖zetaCompletedPrimeHermitianNegativeSeedAmplitude ι.p ι.n f‖ ^ 2

/-- Expanding a square-root-weighted real square only uses associativity,
commutativity, and the recorded square-root weight identity. -/
private theorem real_mul_norm_square_from_weight
    (r x w : ℝ) (hweight : r * r = w) :
    (r * x) ^ 2 = w * x ^ 2 :=
  calc
    (r * x) ^ 2 = (r * x) * (r * x) := by
      exact pow_two (r * x)
    _ = r * (x * (r * x)) := by
      exact mul_assoc r x (r * x)
    _ = r * ((x * r) * x) := by
      exact congrArg (fun z : ℝ => r * z) ((mul_assoc x r x).symm)
    _ = r * ((r * x) * x) := by
      exact congrArg (fun z : ℝ => r * (z * x)) (mul_comm x r)
    _ = r * (r * (x * x)) := by
      exact congrArg (fun z : ℝ => r * z) (mul_assoc r x x)
    _ = (r * r) * (x * x) := by
      exact (mul_assoc r r (x * x)).symm
    _ = w * (x * x) := by
      exact congrArg (fun z : ℝ => z * (x * x)) hweight
    _ = w * x ^ 2 := by
      exact congrArg (fun z : ℝ => w * z) (pow_two x).symm

/-- A nonnegative product of two real sizes is bounded by the sum of their squares. -/
private theorem nonnegative_mul_le_sq_add_sq
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x * y ≤ x ^ 2 + y ^ 2 := by
  have hxy_nonnegative : 0 ≤ x * y := by
    exact mul_nonneg hx hy
  have hproduct_le_twice : x * y ≤ 2 * x * y := by
    calc
      x * y = 1 * (x * y) := by
        exact (one_mul (x * y)).symm
      _ ≤ 2 * (x * y) := by
        exact mul_le_mul_of_nonneg_right one_le_two hxy_nonnegative
      _ = 2 * x * y := by
        exact (mul_assoc (2 : ℝ) x y).symm
  exact hproduct_le_twice.trans (two_mul_le_add_sq x y)

/-- The positive square-root-weight amplitude has norm square equal to the positive
weighted prime sample norm square. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_norm_sq_eq_weightedSampleNormSq
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    ‖zetaCompletedPrimeSpectralAmplitudeIndex ι f‖ ^ 2 =
      zetaCompletedPrimePositiveWeightedSampleNormSq ι f := by
  let r : ℝ := ZetaPrimePowerIndex.sqrtWeight ι
  let A : ℂ := zetaCompletedPrimeHermitianSeedAmplitude ι.p ι.n f
  have hr_nonneg : 0 ≤ r := by
    exact Real.sqrt_nonneg _
  have hnorm_r : ‖(r : ℂ)‖ = r := by
    calc
      ‖(r : ℂ)‖ = |r| := by
        exact RCLike.norm_ofReal r
      _ = r := by
        exact abs_of_nonneg hr_nonneg
  have hnorm :
      ‖(r : ℂ) * A‖ = r * ‖A‖ := by
    calc
      ‖(r : ℂ) * A‖ = ‖(r : ℂ)‖ * ‖A‖ := by
        exact norm_mul (r : ℂ) A
      _ = r * ‖A‖ := by
        exact congrArg (fun x : ℝ => x * ‖A‖) hnorm_r
  have hweight : r * r = ZetaPrimePowerIndex.weight ι := by
    exact ZetaPrimePowerIndex.sqrtWeight_mul_self ι
  calc
    ‖(r : ℂ) * A‖ ^ 2 = (r * ‖A‖) ^ 2 := by
      exact congrArg (fun x : ℝ => x ^ 2) hnorm
    _ = ZetaPrimePowerIndex.weight ι * ‖A‖ ^ 2 := by
      exact real_mul_norm_square_from_weight r ‖A‖ (ZetaPrimePowerIndex.weight ι) hweight

/-- The opposite square-root-weight amplitude has norm square equal to the opposite
weighted prime sample norm square. -/
theorem zetaCompletedPrimeOppositeSpectralAmplitudeIndex_norm_sq_eq_weightedSampleNormSq
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f‖ ^ 2 =
      zetaCompletedPrimeOppositeWeightedSampleNormSq ι f := by
  let r : ℝ := ZetaPrimePowerIndex.sqrtWeight ι
  let A : ℂ := zetaCompletedPrimeHermitianNegativeSeedAmplitude ι.p ι.n f
  have hr_nonneg : 0 ≤ r := by
    exact Real.sqrt_nonneg _
  have hnorm_r : ‖(r : ℂ)‖ = r := by
    calc
      ‖(r : ℂ)‖ = |r| := by
        exact RCLike.norm_ofReal r
      _ = r := by
        exact abs_of_nonneg hr_nonneg
  have hnorm :
      ‖(r : ℂ) * A‖ = r * ‖A‖ := by
    calc
      ‖(r : ℂ) * A‖ = ‖(r : ℂ)‖ * ‖A‖ := by
        exact norm_mul (r : ℂ) A
      _ = r * ‖A‖ := by
        exact congrArg (fun x : ℝ => x * ‖A‖) hnorm_r
  have hweight : r * r = ZetaPrimePowerIndex.weight ι := by
    exact ZetaPrimePowerIndex.sqrtWeight_mul_self ι
  calc
    ‖(r : ℂ) * A‖ ^ 2 = (r * ‖A‖) ^ 2 := by
      exact congrArg (fun x : ℝ => x ^ 2) hnorm
    _ = ZetaPrimePowerIndex.weight ι * ‖A‖ ^ 2 := by
      exact real_mul_norm_square_from_weight r ‖A‖ (ZetaPrimePowerIndex.weight ι) hweight

/-- The norm of a two-face product is bounded by the sum of the two squared face norms. -/
theorem complex_norm_mul_star_le_sq_add_sq (a b : ℂ) :
    ‖a * star b‖ ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  have hmul : ‖a * star b‖ ≤ ‖a‖ * ‖star b‖ :=
    norm_mul_le a (star b)
  have hstar : ‖star b‖ = ‖b‖ :=
    norm_star b
  have hmul_faces : ‖a * star b‖ ≤ ‖a‖ * ‖b‖ :=
    Eq.subst
      (motive := fun x : ℝ => ‖a * star b‖ ≤ ‖a‖ * x)
      hstar
      hmul
  have hface_arith : ‖a‖ * ‖b‖ ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    exact nonnegative_mul_le_sq_add_sq ‖a‖ ‖b‖ (norm_nonneg a) (norm_nonneg b)
  exact hmul_faces.trans hface_arith

/-- The norm of one defect-square coordinate is bounded by twice the sum of the squared
face norms. -/
theorem complex_norm_defect_square_le_two_sq_add_sq (a b : ℂ) :
    ‖(a - b) * star (a - b)‖ ≤
      2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have hmul : ‖(a - b) * star (a - b)‖ ≤
      ‖a - b‖ * ‖star (a - b)‖ :=
    norm_mul_le (a - b) (star (a - b))
  have hstar : ‖star (a - b)‖ = ‖a - b‖ :=
    norm_star (a - b)
  have hmul_self : ‖(a - b) * star (a - b)‖ ≤
      ‖a - b‖ * ‖a - b‖ :=
    Eq.subst
      (motive := fun x : ℝ =>
        ‖(a - b) * star (a - b)‖ ≤ ‖a - b‖ * x)
      hstar
      hmul
  have hsub : ‖a - b‖ ≤ ‖a‖ + ‖b‖ :=
    norm_sub_le a b
  have hsub_nonneg : 0 ≤ ‖a - b‖ :=
    norm_nonneg (a - b)
  have hsum_nonneg : 0 ≤ ‖a‖ + ‖b‖ :=
    add_nonneg (norm_nonneg a) (norm_nonneg b)
  have hsquare :
      ‖a - b‖ * ‖a - b‖ ≤
        (‖a‖ + ‖b‖) * (‖a‖ + ‖b‖) :=
    mul_le_mul hsub hsub hsub_nonneg hsum_nonneg
  have harith :
      (‖a‖ + ‖b‖) * (‖a‖ + ‖b‖) ≤
        2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
    exact Eq.subst
      (motive := fun x : ℝ => x ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2))
      (pow_two (‖a‖ + ‖b‖))
      (add_sq_le (a := ‖a‖) (b := ‖b‖))
  exact hmul_self.trans (hsquare.trans harith)

/-- The positive defect-square coordinate is bounded by twice the spectral majorant. -/
theorem norm_zetaCompletedPrimeDefectKernelPositiveCoordinate_le_spectralMajorant
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    ‖zetaCompletedPrimeDefectKernelPositiveCoordinate ι f‖ ≤
      2 * zetaCompletedPrimeSpectralCoordinateMajorant ι f := by
  exact
    complex_norm_defect_square_le_two_sq_add_sq
      (zetaCompletedPrimeSpectralAmplitudeIndex ι f)
      (zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f)

/-- The oriented two-face coordinate is bounded by the spectral majorant. -/
theorem norm_zetaCompletedPrimeTwoFaceGNSOrientedCoordinate_le_spectralMajorant
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    ‖zetaCompletedPrimeTwoFaceGNSOrientedCoordinate ι f‖ ≤
      zetaCompletedPrimeSpectralCoordinateMajorant ι f := by
  exact
    complex_norm_mul_star_le_sq_add_sq
      (zetaCompletedPrimeSpectralAmplitudeIndex ι f)
      (zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f)

/-- The completed diagonal-debt coordinate is bounded by the spectral majorant. -/
theorem norm_zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_le_spectralMajorant
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    ‖zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate ι f‖ ≤
      zetaCompletedPrimeSpectralCoordinateMajorant ι f := by
  let a : ℂ := zetaCompletedPrimeSpectralAmplitudeIndex ι f
  let b : ℂ := zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f
  have ha :
      ‖a * star a‖ = ‖a‖ ^ 2 := by
    calc
      ‖a * star a‖ = ‖a‖ * ‖star a‖ := by
        exact norm_mul a (star a)
      _ = ‖a‖ * ‖a‖ := by
        exact congrArg (fun x : ℝ => ‖a‖ * x) (norm_star a)
      _ = ‖a‖ ^ 2 := by
        exact (pow_two ‖a‖).symm
  have hb :
      ‖b * star b‖ = ‖b‖ ^ 2 := by
    calc
      ‖b * star b‖ = ‖b‖ * ‖star b‖ := by
        exact norm_mul b (star b)
      _ = ‖b‖ * ‖b‖ := by
        exact congrArg (fun x : ℝ => ‖b‖ * x) (norm_star b)
      _ = ‖b‖ ^ 2 := by
        exact (pow_two ‖b‖).symm
  calc
    ‖a * star a + b * star b‖ ≤
        ‖a * star a‖ + ‖b * star b‖ := by
      exact norm_add_le (a * star a) (b * star b)
    _ = ‖a‖ ^ 2 + ‖b * star b‖ := by
      exact congrArg (fun x : ℝ => x + ‖b * star b‖) ha
    _ = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
      exact congrArg (fun x : ℝ => ‖a‖ ^ 2 + x) hb

/-- A complex family bounded by twice the completed spectral majorant is summable. -/
theorem summable_complex_family_of_norm_le_two_spectralMajorant
    (f : ZetaAdmissibleFunction)
    (u : ZetaPrimePowerIndex → ℂ)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f))
    (hbound :
      ∀ ι : ZetaPrimePowerIndex,
        ‖u ι‖ ≤ 2 * zetaCompletedPrimeSpectralCoordinateMajorant ι f) :
    Summable u := by
  have htwo_majorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          2 * zetaCompletedPrimeSpectralCoordinateMajorant ι f) :=
    Summable.mul_left 2 hmajorant
  exact
    Summable.of_norm_bounded
      (fun ι : ZetaPrimePowerIndex =>
        2 * zetaCompletedPrimeSpectralCoordinateMajorant ι f)
      htwo_majorant
      hbound

/-- A complex family bounded by the completed spectral majorant is summable. -/
theorem summable_complex_family_of_norm_le_spectralMajorant
    (f : ZetaAdmissibleFunction)
    (u : ZetaPrimePowerIndex → ℂ)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f))
    (hbound :
      ∀ ι : ZetaPrimePowerIndex,
        ‖u ι‖ ≤ zetaCompletedPrimeSpectralCoordinateMajorant ι f) :
    Summable u := by
  exact
    Summable.of_norm_bounded
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimeSpectralCoordinateMajorant ι f)
      hmajorant
      hbound

/-- Summability of the spectral majorant implies summability of the positive defect-square
coordinates. -/
theorem summable_zetaCompletedPrimeDefectKernelPositiveCoordinate_of_spectralMajorant
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f)) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimeDefectKernelPositiveCoordinate ι f) := by
  exact
    summable_complex_family_of_norm_le_two_spectralMajorant
      f
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimeDefectKernelPositiveCoordinate ι f)
      hmajorant
      (fun ι : ZetaPrimePowerIndex =>
        norm_zetaCompletedPrimeDefectKernelPositiveCoordinate_le_spectralMajorant
          ι f)

/-- Summability of the spectral majorant implies summability of the oriented two-face
coordinates. -/
theorem summable_zetaCompletedPrimeTwoFaceGNSOrientedCoordinate_of_spectralMajorant
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f)) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimeTwoFaceGNSOrientedCoordinate ι f) := by
  exact
    summable_complex_family_of_norm_le_spectralMajorant
      f
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimeTwoFaceGNSOrientedCoordinate ι f)
      hmajorant
      (fun ι : ZetaPrimePowerIndex =>
        norm_zetaCompletedPrimeTwoFaceGNSOrientedCoordinate_le_spectralMajorant
          ι f)

/-- Spectral-majorant summability transports to the analytic oriented cross coordinate. -/
theorem zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_summable_of_spectralMajorant
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f)) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) := by
  have hgns :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeTwoFaceGNSOrientedCoordinate ι f) :=
    summable_zetaCompletedPrimeTwoFaceGNSOrientedCoordinate_of_spectralMajorant
      f hmajorant
  exact hgns.congr
    (fun ι : ZetaPrimePowerIndex =>
      zetaCompletedPrimeTwoFaceGNSOrientedCoordinate_eq_weightedSeedPair ι f)

/-- Spectral-majorant summability transports to the opposite analytic cross coordinate. -/
theorem zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate_summable_of_spectralMajorant
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f)) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate ι f) := by
  have horiented :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) :=
    zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_summable_of_spectralMajorant
      f hmajorant
  have hstar :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          star
            (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) :=
    horiented.star
  exact hstar.congr
    (fun ι : ZetaPrimePowerIndex =>
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_star_eq_opposite ι f)

/-- Summability of the spectral majorant implies summability of the completed diagonal-debt
coordinates. -/
theorem summable_zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_of_spectralMajorant
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f)) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate ι f) := by
  exact
    summable_complex_family_of_norm_le_spectralMajorant
      f
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate ι f)
      hmajorant
      (fun ι : ZetaPrimePowerIndex =>
        norm_zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_le_spectralMajorant
          ι f)

/-- Summability of the spectral majorant implies summability of the symmetrized two-face
coordinates. -/
theorem summable_zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_of_spectralMajorant
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f)) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) := by
  let C : ZetaPrimePowerIndex → ℂ :=
    fun ι : ZetaPrimePowerIndex =>
      zetaCompletedPrimeTwoFaceGNSOrientedCoordinate ι f
  have hC : Summable C :=
    summable_zetaCompletedPrimeTwoFaceGNSOrientedCoordinate_of_spectralMajorant
      f hmajorant
  have hstar : Summable (fun ι : ZetaPrimePowerIndex => star (C ι)) :=
    hC.star
  have hsum : Summable (fun ι : ZetaPrimePowerIndex => C ι + star (C ι)) :=
    hC.add hstar
  exact hsum

/-- Taking real parts commutes with the completed prime-power sum of positive defect
coordinates. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinate_re_tsum_eq_coordinateTsum_re
    (f : ZetaAdmissibleFunction)
    (hsum :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeDefectKernelPositiveCoordinate ι f)) :
    (∑' ι : ZetaPrimePowerIndex,
        Complex.re (zetaCompletedPrimeDefectKernelPositiveCoordinate ι f)) =
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f := by
  exact
    (Complex.re_tsum hsum).symm

/-- Taking real parts commutes with the completed prime-power sum of diagonal-debt
coordinates. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_tsum_eq_coordinateTsum_re
    (f : ZetaAdmissibleFunction)
    (hsum :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate ι f)) :
    (∑' ι : ZetaPrimePowerIndex,
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate ι f)) =
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) := by
  exact
    (Complex.re_tsum hsum).symm

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
