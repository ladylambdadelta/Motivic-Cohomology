import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.ArchimedeanCriticalLineIntegrability

/-!
# Normalized signed completed boundary

The archimedean channel is a signed continuum form. Boundary positivity is
therefore exactly the assertion that the prime-positive channel and the
positive archimedean variation absorb the negative variation.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The real positive variation of the centered archimedean quadratic form. -/
noncomputable def zetaCompletedArchimedeanPositiveVariationScalar
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaCompletedArchimedeanPositiveQuadraticForm f)

/-- The real negative variation of the centered archimedean quadratic form. -/
noncomputable def zetaCompletedArchimedeanNegativeVariationScalar
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaCompletedArchimedeanNegativeQuadraticForm f)

/-- The real part of a positive Gram coordinate is its nonnegative weight
times the seed norm-square. -/
theorem zetaCompletedArchimedeanPositiveGramCoordinate_re_eq
    (f : ZetaAdmissibleFunction) (t : ℝ) :
    Complex.re (zetaCompletedArchimedeanPositiveGramCoordinate f t) =
      zetaCompletedArchimedeanPositiveWeight t *
        Complex.normSq
          (zetaCompletedExplicitFormulaPhi f ((t : ℂ) * Complex.I)) :=
  calc
    Complex.re (zetaCompletedArchimedeanPositiveGramCoordinate f t) =
        Complex.re
          ((zetaCompletedArchimedeanPositiveWeight t : ℂ) *
            (Complex.normSq
              (zetaCompletedExplicitFormulaPhi f
                ((t : ℂ) * Complex.I)) : ℂ)) :=
      congrArg Complex.re
        (congrArg
          (fun right : ℂ =>
            (zetaCompletedArchimedeanPositiveWeight t : ℂ) * right)
          (zetaCompletedArchimedeanProbeGram_eq_normSq f t))
    _ = Complex.re
          ((zetaCompletedArchimedeanPositiveWeight t *
            Complex.normSq
              (zetaCompletedExplicitFormulaPhi f
                ((t : ℂ) * Complex.I)) : ℝ) : ℂ) :=
      congrArg Complex.re
        (Complex.ofReal_mul
          (zetaCompletedArchimedeanPositiveWeight t)
          (Complex.normSq
            (zetaCompletedExplicitFormulaPhi f
              ((t : ℂ) * Complex.I)))).symm
    _ = zetaCompletedArchimedeanPositiveWeight t *
          Complex.normSq
            (zetaCompletedExplicitFormulaPhi f
              ((t : ℂ) * Complex.I)) :=
      Complex.ofReal_re _

/-- The real part of a negative Gram coordinate is its nonnegative weight
times the seed norm-square. -/
theorem zetaCompletedArchimedeanNegativeGramCoordinate_re_eq
    (f : ZetaAdmissibleFunction) (t : ℝ) :
    Complex.re (zetaCompletedArchimedeanNegativeGramCoordinate f t) =
      zetaCompletedArchimedeanNegativeWeight t *
        Complex.normSq
          (zetaCompletedExplicitFormulaPhi f ((t : ℂ) * Complex.I)) :=
  calc
    Complex.re (zetaCompletedArchimedeanNegativeGramCoordinate f t) =
        Complex.re
          ((zetaCompletedArchimedeanNegativeWeight t : ℂ) *
            (Complex.normSq
              (zetaCompletedExplicitFormulaPhi f
                ((t : ℂ) * Complex.I)) : ℂ)) :=
      congrArg Complex.re
        (congrArg
          (fun right : ℂ =>
            (zetaCompletedArchimedeanNegativeWeight t : ℂ) * right)
          (zetaCompletedArchimedeanProbeGram_eq_normSq f t))
    _ = Complex.re
          ((zetaCompletedArchimedeanNegativeWeight t *
            Complex.normSq
              (zetaCompletedExplicitFormulaPhi f
                ((t : ℂ) * Complex.I)) : ℝ) : ℂ) :=
      congrArg Complex.re
        (Complex.ofReal_mul
          (zetaCompletedArchimedeanNegativeWeight t)
          (Complex.normSq
            (zetaCompletedExplicitFormulaPhi f
              ((t : ℂ) * Complex.I)))).symm
    _ = zetaCompletedArchimedeanNegativeWeight t *
          Complex.normSq
            (zetaCompletedExplicitFormulaPhi f
              ((t : ℂ) * Complex.I)) :=
      Complex.ofReal_re _

/-- The positive archimedean weight is nonnegative. -/
theorem zetaCompletedArchimedeanPositiveWeight_nonnegative
    (t : ℝ) :
    0 ≤ zetaCompletedArchimedeanPositiveWeight t :=
  le_max_right (zetaCompletedArchimedeanSignedWeight t) 0

/-- The negative archimedean weight is nonnegative. -/
theorem zetaCompletedArchimedeanNegativeWeight_nonnegative
    (t : ℝ) :
    0 ≤ zetaCompletedArchimedeanNegativeWeight t :=
  le_max_right (-zetaCompletedArchimedeanSignedWeight t) 0

/-- The positive archimedean coordinate product is nonnegative. -/
theorem zetaCompletedArchimedeanPositiveGramCoordinate_product_nonnegative
    (f : ZetaAdmissibleFunction) (t : ℝ) :
    0 ≤ zetaCompletedArchimedeanPositiveWeight t *
      Complex.normSq
        (zetaCompletedExplicitFormulaPhi f ((t : ℂ) * Complex.I)) :=
  mul_nonneg
    (zetaCompletedArchimedeanPositiveWeight_nonnegative t)
    (Complex.normSq_nonneg
      (zetaCompletedExplicitFormulaPhi f ((t : ℂ) * Complex.I)))

/-- The negative archimedean coordinate product is nonnegative. -/
theorem zetaCompletedArchimedeanNegativeGramCoordinate_product_nonnegative
    (f : ZetaAdmissibleFunction) (t : ℝ) :
    0 ≤ zetaCompletedArchimedeanNegativeWeight t *
      Complex.normSq
        (zetaCompletedExplicitFormulaPhi f ((t : ℂ) * Complex.I)) :=
  mul_nonneg
    (zetaCompletedArchimedeanNegativeWeight_nonnegative t)
    (Complex.normSq_nonneg
      (zetaCompletedExplicitFormulaPhi f ((t : ℂ) * Complex.I)))

/-- Every positive archimedean Gram coordinate has nonnegative real part. -/
theorem zetaCompletedArchimedeanPositiveGramCoordinate_re_nonnegative
    (f : ZetaAdmissibleFunction) (t : ℝ) :
    0 ≤ Complex.re (zetaCompletedArchimedeanPositiveGramCoordinate f t) :=
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (zetaCompletedArchimedeanPositiveGramCoordinate_re_eq f t).symm
    (zetaCompletedArchimedeanPositiveGramCoordinate_product_nonnegative f t)

/-- Every negative archimedean Gram coordinate has nonnegative real part. -/
theorem zetaCompletedArchimedeanNegativeGramCoordinate_re_nonnegative
    (f : ZetaAdmissibleFunction) (t : ℝ) :
    0 ≤ Complex.re (zetaCompletedArchimedeanNegativeGramCoordinate f t) :=
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (zetaCompletedArchimedeanNegativeGramCoordinate_re_eq f t).symm
    (zetaCompletedArchimedeanNegativeGramCoordinate_product_nonnegative f t)

/-- The integral of the positive coordinate real parts is nonnegative. -/
theorem zetaCompletedArchimedeanPositiveGramCoordinate_re_integral_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ ∫ t : ℝ,
      Complex.re (zetaCompletedArchimedeanPositiveGramCoordinate f t) :=
  MeasureTheory.integral_nonneg
    (zetaCompletedArchimedeanPositiveGramCoordinate_re_nonnegative f)

/-- The integral of the negative coordinate real parts is nonnegative. -/
theorem zetaCompletedArchimedeanNegativeGramCoordinate_re_integral_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ ∫ t : ℝ,
      Complex.re (zetaCompletedArchimedeanNegativeGramCoordinate f t) :=
  MeasureTheory.integral_nonneg
    (zetaCompletedArchimedeanNegativeGramCoordinate_re_nonnegative f)

/-- Positive coordinate integration commutes with real part. -/
theorem zetaCompletedArchimedeanPositiveGramCoordinate_re_integral_eq
    (f : ZetaAdmissibleFunction) :
    (∫ t : ℝ,
      Complex.re (zetaCompletedArchimedeanPositiveGramCoordinate f t)) =
      Complex.re
        (∫ t : ℝ,
          zetaCompletedArchimedeanPositiveGramCoordinate f t) :=
  integral_re
    (zetaCompletedArchimedeanPositiveGramCoordinate_integrable f)

/-- Negative coordinate integration commutes with real part. -/
theorem zetaCompletedArchimedeanNegativeGramCoordinate_re_integral_eq
    (f : ZetaAdmissibleFunction) :
    (∫ t : ℝ,
      Complex.re (zetaCompletedArchimedeanNegativeGramCoordinate f t)) =
      Complex.re
        (∫ t : ℝ,
          zetaCompletedArchimedeanNegativeGramCoordinate f t) :=
  integral_re
    (zetaCompletedArchimedeanNegativeGramCoordinate_integrable f)

/-- The positive archimedean variation scalar is nonnegative. -/
theorem zetaCompletedArchimedeanPositiveVariationScalar_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedArchimedeanPositiveVariationScalar f :=
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (zetaCompletedArchimedeanPositiveGramCoordinate_re_integral_eq f)
    (zetaCompletedArchimedeanPositiveGramCoordinate_re_integral_nonnegative
      f)

/-- The negative archimedean variation scalar is nonnegative. -/
theorem zetaCompletedArchimedeanNegativeVariationScalar_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedArchimedeanNegativeVariationScalar f :=
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (zetaCompletedArchimedeanNegativeGramCoordinate_re_integral_eq f)
    (zetaCompletedArchimedeanNegativeGramCoordinate_re_integral_nonnegative
      f)

/-- The real signed archimedean form is positive variation minus negative
variation. -/
theorem zetaCompletedArchimedeanSignedQuadraticForm_re_eq_variation_sub
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedArchimedeanSignedQuadraticForm f) =
      zetaCompletedArchimedeanPositiveVariationScalar f -
        zetaCompletedArchimedeanNegativeVariationScalar f :=
  Eq.trans
    (congrArg Complex.re
      (zetaCompletedArchimedeanSignedQuadraticForm_eq_positive_sub_negative_owner
        f))
    (Complex.sub_re
      (zetaCompletedArchimedeanPositiveQuadraticForm f)
      (zetaCompletedArchimedeanNegativeQuadraticForm f))

/-- The physical prime scalar on an autocorrelation probe. -/
noncomputable def zetaCompletedPhysicalPrimeBoundaryScalar
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (primeBoundaryChannel (convolutionAutocorrelation f))

/-- The real completed-pole correction scalar on an autocorrelation probe. -/
noncomputable def zetaCompletedPhysicalCorrectionBoundaryScalar
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (poleBoundaryChannel (convolutionAutocorrelation f))

/-- The normalized signed completed boundary scalar. -/
noncomputable def zetaCompletedNormalizedSignedBoundaryScalar
    (f : ZetaAdmissibleFunction) : ℝ :=
  zetaCompletedPhysicalPrimeBoundaryScalar f +
    zetaCompletedPhysicalCorrectionBoundaryScalar f +
      Complex.re (zetaCompletedArchimedeanSignedQuadraticForm f)

/-- The real archimedean boundary channel is the normalized signed continuum
form. -/
theorem archimedeanBoundaryChannel_convolutionAutocorrelation_re_eq_normalizedSignedForm
    (f : ZetaAdmissibleFunction) :
    Complex.re
        (archimedeanBoundaryChannel (convolutionAutocorrelation f)) =
      Complex.re (zetaCompletedArchimedeanSignedQuadraticForm f) :=
  Eq.trans
    (congrArg Complex.re
      (archimedeanBoundaryChannel_unfold (convolutionAutocorrelation f)))
    (Eq.trans
      (Complex.ofReal_re
        (Complex.re
          (zetaCompletedExplicitFormulaArchimedeanContribution
            (convolutionAutocorrelation f)))).symm
      (congrArg Complex.re
        (zetaCompletedArchimedeanSignedQuadraticForm_eq_archimedeanContribution_re_owner
          f)).symm)

/-- The completed boundary has no separate completion channel. -/
theorem completedBoundaryChannel_convolutionAutocorrelation_eq_prime_add_archimedean_add_pole
    (f : ZetaAdmissibleFunction) :
    completedBoundaryChannel (convolutionAutocorrelation f) =
      primeBoundaryChannel (convolutionAutocorrelation f) +
        archimedeanBoundaryChannel (convolutionAutocorrelation f) +
        poleBoundaryChannel (convolutionAutocorrelation f) :=
  calc
    completedBoundaryChannel (convolutionAutocorrelation f) =
        primeBoundaryChannel (convolutionAutocorrelation f) +
          archimedeanBoundaryChannel (convolutionAutocorrelation f) +
          poleBoundaryChannel (convolutionAutocorrelation f) +
          completionBoundaryChannel (convolutionAutocorrelation f) :=
      completedBoundaryChannel_eq_prime_add_archimedean_add_pole_add_completion
        (convolutionAutocorrelation f)
    _ =
        (primeBoundaryChannel (convolutionAutocorrelation f) +
          archimedeanBoundaryChannel (convolutionAutocorrelation f) +
          poleBoundaryChannel (convolutionAutocorrelation f)) + 0 :=
      congrArg₂ HAdd.hAdd
        (Eq.refl
          (primeBoundaryChannel (convolutionAutocorrelation f) +
            archimedeanBoundaryChannel (convolutionAutocorrelation f) +
            poleBoundaryChannel (convolutionAutocorrelation f)))
        (completionBoundaryChannel_unfold (convolutionAutocorrelation f))
    _ =
        primeBoundaryChannel (convolutionAutocorrelation f) +
          archimedeanBoundaryChannel (convolutionAutocorrelation f) +
          poleBoundaryChannel (convolutionAutocorrelation f) :=
      add_zero
        (primeBoundaryChannel (convolutionAutocorrelation f) +
          archimedeanBoundaryChannel (convolutionAutocorrelation f) +
          poleBoundaryChannel (convolutionAutocorrelation f))

/-- Definition unfolding for the physical prime scalar. -/
theorem zetaCompletedPhysicalPrimeBoundaryScalar_eq_re
    (f : ZetaAdmissibleFunction) :
    zetaCompletedPhysicalPrimeBoundaryScalar f =
      Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) :=
  rfl

/-- Definition unfolding for the physical correction scalar. -/
theorem zetaCompletedPhysicalCorrectionBoundaryScalar_eq_re
    (f : ZetaAdmissibleFunction) :
    zetaCompletedPhysicalCorrectionBoundaryScalar f =
      Complex.re (poleBoundaryChannel (convolutionAutocorrelation f)) :=
  rfl

/-- Replace raw real parts by the named physical scalars. -/
theorem completedBoundaryChannel_three_part_re_eq_prime_archimedean_correction
    (f : ZetaAdmissibleFunction) :
    Complex.re
        ((primeBoundaryChannel (convolutionAutocorrelation f) +
          archimedeanBoundaryChannel (convolutionAutocorrelation f)) +
          poleBoundaryChannel (convolutionAutocorrelation f)) =
      (zetaCompletedPhysicalPrimeBoundaryScalar f +
        Complex.re
          (archimedeanBoundaryChannel (convolutionAutocorrelation f))) +
        zetaCompletedPhysicalCorrectionBoundaryScalar f :=
  calc
    Complex.re
        ((primeBoundaryChannel (convolutionAutocorrelation f) +
          archimedeanBoundaryChannel (convolutionAutocorrelation f)) +
          poleBoundaryChannel (convolutionAutocorrelation f)) =
        Complex.re
          (primeBoundaryChannel (convolutionAutocorrelation f) +
            archimedeanBoundaryChannel (convolutionAutocorrelation f)) +
          Complex.re (poleBoundaryChannel (convolutionAutocorrelation f)) :=
      Complex.add_re
        (primeBoundaryChannel (convolutionAutocorrelation f) +
          archimedeanBoundaryChannel (convolutionAutocorrelation f))
        (poleBoundaryChannel (convolutionAutocorrelation f))
    _ =
        (Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) +
          Complex.re
            (archimedeanBoundaryChannel (convolutionAutocorrelation f))) +
          Complex.re (poleBoundaryChannel (convolutionAutocorrelation f)) :=
      congrArg
        (fun value : ℝ =>
          value + Complex.re (poleBoundaryChannel (convolutionAutocorrelation f)))
        (Complex.add_re
          (primeBoundaryChannel (convolutionAutocorrelation f))
          (archimedeanBoundaryChannel (convolutionAutocorrelation f)))
    _ =
        (zetaCompletedPhysicalPrimeBoundaryScalar f +
          Complex.re
            (archimedeanBoundaryChannel (convolutionAutocorrelation f))) +
          zetaCompletedPhysicalCorrectionBoundaryScalar f :=
      congrArg₂ HAdd.hAdd
        (congrArg₂ HAdd.hAdd
          (zetaCompletedPhysicalPrimeBoundaryScalar_eq_re f).symm
          (Eq.refl
            (Complex.re
              (archimedeanBoundaryChannel (convolutionAutocorrelation f))))
        )
        (zetaCompletedPhysicalCorrectionBoundaryScalar_eq_re f).symm

/-- Three-term scalar regrouping for the normalized signed boundary. -/
theorem completedBoundaryChannel_prime_archimedean_correction_scalar_regroup
    (primeScalar correctionScalar archimedeanScalar : ℝ) :
    (primeScalar + archimedeanScalar) + correctionScalar =
      primeScalar + correctionScalar + archimedeanScalar :=
  calc
    (primeScalar + archimedeanScalar) + correctionScalar =
        primeScalar + (archimedeanScalar + correctionScalar) :=
      add_assoc primeScalar archimedeanScalar correctionScalar
    _ = primeScalar + (correctionScalar + archimedeanScalar) :=
      congrArg
        (fun value : ℝ => primeScalar + value)
        (add_comm archimedeanScalar correctionScalar)
    _ = primeScalar + correctionScalar + archimedeanScalar :=
      (add_assoc primeScalar correctionScalar archimedeanScalar).symm

/-- The completed boundary real part equals the named physical scalars plus
the signed archimedean scalar. -/
theorem completedBoundaryChannel_convolutionAutocorrelation_re_eq_physical_plus_signed
    (f : ZetaAdmissibleFunction) :
    Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
      zetaCompletedPhysicalPrimeBoundaryScalar f +
        zetaCompletedPhysicalCorrectionBoundaryScalar f +
        Complex.re (zetaCompletedArchimedeanSignedQuadraticForm f) :=
  Eq.trans
    (congrArg Complex.re
      (completedBoundaryChannel_convolutionAutocorrelation_eq_prime_add_archimedean_add_pole
        f))
    (Eq.trans
      (completedBoundaryChannel_three_part_re_eq_prime_archimedean_correction
        f)
      (Eq.trans
        (congrArg
          (fun value : ℝ =>
            (zetaCompletedPhysicalPrimeBoundaryScalar f + value) +
              zetaCompletedPhysicalCorrectionBoundaryScalar f)
          (archimedeanBoundaryChannel_convolutionAutocorrelation_re_eq_normalizedSignedForm
            f))
        (completedBoundaryChannel_prime_archimedean_correction_scalar_regroup
          (zetaCompletedPhysicalPrimeBoundaryScalar f)
          (zetaCompletedPhysicalCorrectionBoundaryScalar f)
          (Complex.re (zetaCompletedArchimedeanSignedQuadraticForm f)))))

/-- The completed boundary is the physical prime scalar plus the normalized
signed archimedean form. -/
theorem completedBoundaryChannel_convolutionAutocorrelation_re_eq_normalizedSignedScalar
    (f : ZetaAdmissibleFunction) :
    Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
      zetaCompletedNormalizedSignedBoundaryScalar f :=
  completedBoundaryChannel_convolutionAutocorrelation_re_eq_physical_plus_signed
    f

/-- The normalized signed scalar is the physical prime scalar plus the
positive archimedean variation, minus the negative archimedean variation. -/
theorem zetaCompletedNormalizedSignedBoundaryScalar_eq_reserve_sub_negative
    (f : ZetaAdmissibleFunction) :
    zetaCompletedNormalizedSignedBoundaryScalar f =
      (zetaCompletedPhysicalPrimeBoundaryScalar f +
        zetaCompletedPhysicalCorrectionBoundaryScalar f +
        zetaCompletedArchimedeanPositiveVariationScalar f) -
        zetaCompletedArchimedeanNegativeVariationScalar f :=
  calc
    zetaCompletedNormalizedSignedBoundaryScalar f =
        zetaCompletedPhysicalPrimeBoundaryScalar f +
          zetaCompletedPhysicalCorrectionBoundaryScalar f +
          (zetaCompletedArchimedeanPositiveVariationScalar f -
            zetaCompletedArchimedeanNegativeVariationScalar f) :=
      congrArg
        (fun value : ℝ =>
          zetaCompletedPhysicalPrimeBoundaryScalar f +
            zetaCompletedPhysicalCorrectionBoundaryScalar f + value)
        (zetaCompletedArchimedeanSignedQuadraticForm_re_eq_variation_sub f)
    _ =
        (zetaCompletedPhysicalPrimeBoundaryScalar f +
          zetaCompletedPhysicalCorrectionBoundaryScalar f +
          zetaCompletedArchimedeanPositiveVariationScalar f) -
          zetaCompletedArchimedeanNegativeVariationScalar f :=
      (add_sub_assoc
        (zetaCompletedPhysicalPrimeBoundaryScalar f +
          zetaCompletedPhysicalCorrectionBoundaryScalar f)
        (zetaCompletedArchimedeanPositiveVariationScalar f)
        (zetaCompletedArchimedeanNegativeVariationScalar f)).symm

/-- Signed boundary nonnegativity implies normalized absorption. -/
theorem zetaCompletedNormalizedAbsorption_of_signedBoundaryScalar_nonnegative
    (f : ZetaAdmissibleFunction)
    (scalarNonnegative :
      0 ≤ zetaCompletedNormalizedSignedBoundaryScalar f) :
    zetaCompletedArchimedeanNegativeVariationScalar f ≤
      zetaCompletedPhysicalPrimeBoundaryScalar f +
        zetaCompletedPhysicalCorrectionBoundaryScalar f +
        zetaCompletedArchimedeanPositiveVariationScalar f :=
  sub_nonneg.mp
    (Eq.subst
      (motive := fun value : ℝ => 0 ≤ value)
      (zetaCompletedNormalizedSignedBoundaryScalar_eq_reserve_sub_negative
        f)
      scalarNonnegative)

/-- Normalized absorption implies signed boundary nonnegativity. -/
theorem zetaCompletedNormalizedSignedBoundaryScalar_nonnegative_of_absorption
    (f : ZetaAdmissibleFunction)
    (absorption :
      zetaCompletedArchimedeanNegativeVariationScalar f ≤
        zetaCompletedPhysicalPrimeBoundaryScalar f +
          zetaCompletedPhysicalCorrectionBoundaryScalar f +
          zetaCompletedArchimedeanPositiveVariationScalar f) :
    0 ≤ zetaCompletedNormalizedSignedBoundaryScalar f :=
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (zetaCompletedNormalizedSignedBoundaryScalar_eq_reserve_sub_negative f).symm
    (sub_nonneg.mpr absorption)

/-- Boundary nonnegativity is exactly normalized absorption of the negative
archimedean variation. -/
theorem zetaCompletedNormalizedSignedBoundaryScalar_nonnegative_iff_absorption
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedNormalizedSignedBoundaryScalar f ↔
      zetaCompletedArchimedeanNegativeVariationScalar f ≤
        zetaCompletedPhysicalPrimeBoundaryScalar f +
          zetaCompletedPhysicalCorrectionBoundaryScalar f +
          zetaCompletedArchimedeanPositiveVariationScalar f :=
  Iff.intro
    (zetaCompletedNormalizedAbsorption_of_signedBoundaryScalar_nonnegative f)
    (zetaCompletedNormalizedSignedBoundaryScalar_nonnegative_of_absorption f)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
