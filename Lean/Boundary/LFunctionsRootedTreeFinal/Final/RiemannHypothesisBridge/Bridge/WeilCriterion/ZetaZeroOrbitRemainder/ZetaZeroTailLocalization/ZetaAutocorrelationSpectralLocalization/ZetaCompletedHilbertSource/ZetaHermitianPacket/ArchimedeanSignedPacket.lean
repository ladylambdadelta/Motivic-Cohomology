import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.OwnerParts.BoundaryChannels
import Mathlib.Algebra.Order.Group.MinMax

/-!
# Signed archimedean packet

The critical-line Gamma kernel is represented as a signed continuum weight.
Its positive and negative variations are kept separate; no rank-one point
evaluation is used.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open MeasureTheory

namespace ZetaAdmissibleFunction

/-- The real critical-line weight of the completed archimedean kernel. -/
noncomputable def zetaCompletedArchimedeanSignedWeight (t : ℝ) : ℝ :=
  Complex.re
    (zetaCompletedArchimedeanHermitianKernel t)

/-- The positive variation of the archimedean signed weight. -/
noncomputable def zetaCompletedArchimedeanPositiveWeight (t : ℝ) : ℝ :=
  max (zetaCompletedArchimedeanSignedWeight t) 0

/-- The negative variation of the archimedean signed weight. -/
noncomputable def zetaCompletedArchimedeanNegativeWeight (t : ℝ) : ℝ :=
  max (-zetaCompletedArchimedeanSignedWeight t) 0

/-- The signed weight is its positive variation minus its negative variation. -/
theorem zetaCompletedArchimedeanSignedWeight_eq_positive_sub_negative
    (t : ℝ) :
    zetaCompletedArchimedeanSignedWeight t =
      zetaCompletedArchimedeanPositiveWeight t -
        zetaCompletedArchimedeanNegativeWeight t := by
  exact
    (max_zero_sub_eq_self
      (zetaCompletedArchimedeanSignedWeight t)).symm

/-- The positive continuum amplitude of a probe. -/
noncomputable def zetaCompletedArchimedeanPositiveAmplitude
    (f : ZetaAdmissibleFunction) (t : ℝ) : ℂ :=
  (Real.sqrt (zetaCompletedArchimedeanPositiveWeight t) : ℂ) *
    zetaCompletedExplicitFormulaPhi f (t * Complex.I)

/-- The negative continuum amplitude of a probe. -/
noncomputable def zetaCompletedArchimedeanNegativeAmplitude
    (f : ZetaAdmissibleFunction) (t : ℝ) : ℂ :=
  (Real.sqrt (zetaCompletedArchimedeanNegativeWeight t) : ℂ) *
    zetaCompletedExplicitFormulaPhi f (t * Complex.I)

/-- The signed pointwise archimedean Gram coordinate. -/
noncomputable def zetaCompletedArchimedeanSignedGramCoordinate
    (f : ZetaAdmissibleFunction) (t : ℝ) : ℂ :=
  (zetaCompletedArchimedeanSignedWeight t : ℂ) *
    (zetaCompletedExplicitFormulaPhi f (t * Complex.I) *
      star (zetaCompletedExplicitFormulaPhi f (t * Complex.I)))

/-- The positive pointwise archimedean Gram coordinate. -/
noncomputable def zetaCompletedArchimedeanPositiveGramCoordinate
    (f : ZetaAdmissibleFunction) (t : ℝ) : ℂ :=
  (zetaCompletedArchimedeanPositiveWeight t : ℂ) *
    (zetaCompletedExplicitFormulaPhi f (t * Complex.I) *
      star (zetaCompletedExplicitFormulaPhi f (t * Complex.I)))

/-- The negative pointwise archimedean Gram coordinate. -/
noncomputable def zetaCompletedArchimedeanNegativeGramCoordinate
    (f : ZetaAdmissibleFunction) (t : ℝ) : ℂ :=
  (zetaCompletedArchimedeanNegativeWeight t : ℂ) *
    (zetaCompletedExplicitFormulaPhi f (t * Complex.I) *
      star (zetaCompletedExplicitFormulaPhi f (t * Complex.I)))

/-- Pointwise Jordan decomposition of the signed archimedean Gram packet. -/
theorem zetaCompletedArchimedeanSignedGramCoordinate_eq_positive_sub_negative
    (f : ZetaAdmissibleFunction) (t : ℝ) :
    zetaCompletedArchimedeanSignedGramCoordinate f t =
      zetaCompletedArchimedeanPositiveGramCoordinate f t -
        zetaCompletedArchimedeanNegativeGramCoordinate f t := by
  let probeGram : ℂ :=
    zetaCompletedExplicitFormulaPhi f (t * Complex.I) *
      star (zetaCompletedExplicitFormulaPhi f (t * Complex.I))
  have realWeightEquality :
      zetaCompletedArchimedeanSignedWeight t =
        zetaCompletedArchimedeanPositiveWeight t -
          zetaCompletedArchimedeanNegativeWeight t :=
    zetaCompletedArchimedeanSignedWeight_eq_positive_sub_negative t
  have complexWeightEquality :
      (zetaCompletedArchimedeanSignedWeight t : ℂ) =
        (zetaCompletedArchimedeanPositiveWeight t : ℂ) -
          (zetaCompletedArchimedeanNegativeWeight t : ℂ) := by
    exact Eq.trans
      (congrArg (fun value : ℝ => (value : ℂ)) realWeightEquality)
      (ofReal_sub
        (zetaCompletedArchimedeanPositiveWeight t)
        (zetaCompletedArchimedeanNegativeWeight t))
  calc
    zetaCompletedArchimedeanSignedGramCoordinate f t =
        (zetaCompletedArchimedeanSignedWeight t : ℂ) * probeGram := by
      exact Eq.refl _
    _ =
        ((zetaCompletedArchimedeanPositiveWeight t : ℂ) -
          (zetaCompletedArchimedeanNegativeWeight t : ℂ)) * probeGram := by
      exact congrArg (fun value : ℂ => value * probeGram)
        complexWeightEquality
    _ =
        (zetaCompletedArchimedeanPositiveWeight t : ℂ) * probeGram -
          (zetaCompletedArchimedeanNegativeWeight t : ℂ) * probeGram := by
      exact sub_mul
        (zetaCompletedArchimedeanPositiveWeight t : ℂ)
        (zetaCompletedArchimedeanNegativeWeight t : ℂ)
        probeGram
    _ =
        zetaCompletedArchimedeanPositiveGramCoordinate f t -
          zetaCompletedArchimedeanNegativeGramCoordinate f t := by
      exact Eq.refl _

/-- Continuum packet carrying both variations of the signed archimedean
kernel. -/
structure ZetaCompletedArchimedeanSignedPacket where
  positiveAmplitude : ℝ → ℂ
  negativeAmplitude : ℝ → ℂ

/-- The canonical signed archimedean packet attached to a probe. -/
noncomputable def zetaCompletedArchimedeanSignedPacket
    (f : ZetaAdmissibleFunction) : ZetaCompletedArchimedeanSignedPacket where
  positiveAmplitude := zetaCompletedArchimedeanPositiveAmplitude f
  negativeAmplitude := zetaCompletedArchimedeanNegativeAmplitude f

/-- The positive amplitude projection of the canonical packet. -/
theorem zetaCompletedArchimedeanSignedPacket_positiveAmplitude
    (f : ZetaAdmissibleFunction) :
    (zetaCompletedArchimedeanSignedPacket f).positiveAmplitude =
      zetaCompletedArchimedeanPositiveAmplitude f := by
  exact Eq.refl _

/-- The negative amplitude projection of the canonical packet. -/
theorem zetaCompletedArchimedeanSignedPacket_negativeAmplitude
    (f : ZetaAdmissibleFunction) :
    (zetaCompletedArchimedeanSignedPacket f).negativeAmplitude =
      zetaCompletedArchimedeanNegativeAmplitude f := by
  exact Eq.refl _

/-- Every imaginary-axis coordinate is fixed by the spectral dagger. -/
theorem zetaCompletedImaginaryCoordinate_dagger_fixed (t : ℝ) :
    -star ((t : ℂ) * Complex.I) = (t : ℂ) * Complex.I := by
  have realStar : star (t : ℂ) = (t : ℂ) :=
    Complex.conj_ofReal t
  have imaginaryStar : star Complex.I = -Complex.I :=
    Complex.conj_I
  calc
    -star ((t : ℂ) * Complex.I) =
        -(star Complex.I * star (t : ℂ)) := by
      exact congrArg Neg.neg (star_mul (t : ℂ) Complex.I)
    _ = -((-Complex.I) * (t : ℂ)) := by
      exact congrArg₂ (fun left right : ℂ => -(left * right))
        imaginaryStar realStar
    _ = -(-(Complex.I * (t : ℂ))) := by
      exact congrArg Neg.neg (neg_mul Complex.I (t : ℂ))
    _ = Complex.I * (t : ℂ) :=
      neg_neg (Complex.I * (t : ℂ))
    _ = (t : ℂ) * Complex.I :=
      mul_comm Complex.I (t : ℂ)

/-- On the imaginary axis, the autocorrelation transform is the seed Gram
coordinate at the same spectral point. -/
theorem zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation_imaginary
    (f : ZetaAdmissibleFunction) (t : ℝ) :
    zetaCompletedExplicitFormulaPhi
        (convolutionAutocorrelation f) ((t : ℂ) * Complex.I) =
      zetaCompletedExplicitFormulaPhi f ((t : ℂ) * Complex.I) *
        star (zetaCompletedExplicitFormulaPhi f ((t : ℂ) * Complex.I)) := by
  have generalFactorization :=
    zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation
      f ((t : ℂ) * Complex.I)
  exact Eq.trans generalFactorization
    (congrArg
      (fun value : ℂ =>
        zetaCompletedExplicitFormulaPhi f ((t : ℂ) * Complex.I) *
          star (zetaCompletedExplicitFormulaPhi f value))
      (zetaCompletedImaginaryCoordinate_dagger_fixed t))

/-- A spectral seed coordinate times its dagger is the real norm-square
coordinate. -/
theorem zetaCompletedArchimedeanProbeGram_eq_normSq
    (f : ZetaAdmissibleFunction) (t : ℝ) :
    zetaCompletedExplicitFormulaPhi f ((t : ℂ) * Complex.I) *
        star (zetaCompletedExplicitFormulaPhi f ((t : ℂ) * Complex.I)) =
      (Complex.normSq
        (zetaCompletedExplicitFormulaPhi f ((t : ℂ) * Complex.I)) : ℂ) := by
  let value : ℂ :=
    zetaCompletedExplicitFormulaPhi f ((t : ℂ) * Complex.I)
  calc
    zetaCompletedExplicitFormulaPhi f ((t : ℂ) * Complex.I) *
        star (zetaCompletedExplicitFormulaPhi f ((t : ℂ) * Complex.I)) =
        value * star value := by
      exact Eq.refl _
    _ = (Complex.normSq value : ℂ) := by
      exact Complex.mul_conj value
    _ =
        (Complex.normSq
          (zetaCompletedExplicitFormulaPhi f ((t : ℂ) * Complex.I)) : ℂ) := by
      exact Eq.refl _

/-- Multiplication by a conjugate square retains only the real part of the
archimedean kernel. -/
theorem zetaCompletedArchimedeanHermitianKernel_mul_probeGram_re
    (f : ZetaAdmissibleFunction) (t : ℝ) :
    Complex.re
        (zetaCompletedArchimedeanHermitianKernel t *
          (zetaCompletedExplicitFormulaPhi f ((t : ℂ) * Complex.I) *
            star (zetaCompletedExplicitFormulaPhi f
              ((t : ℂ) * Complex.I)))) =
      zetaCompletedArchimedeanSignedWeight t *
        Complex.normSq
          (zetaCompletedExplicitFormulaPhi f ((t : ℂ) * Complex.I)) := by
  let kernel : ℂ :=
    zetaCompletedArchimedeanHermitianKernel t
  let square : ℝ :=
    Complex.normSq
      (zetaCompletedExplicitFormulaPhi f ((t : ℂ) * Complex.I))
  have gramEquality :
      zetaCompletedExplicitFormulaPhi f ((t : ℂ) * Complex.I) *
          star (zetaCompletedExplicitFormulaPhi f ((t : ℂ) * Complex.I)) =
        (square : ℂ) :=
    zetaCompletedArchimedeanProbeGram_eq_normSq f t
  have productReal : Complex.re (kernel * (square : ℂ)) = kernel.re * square := by
    calc
      Complex.re (kernel * (square : ℂ)) =
          kernel.re * (square : ℂ).re - kernel.im * (square : ℂ).im := by
        exact Complex.mul_re kernel (square : ℂ)
      _ = kernel.re * square - kernel.im * 0 := by
        exact congrArg₂ Sub.sub
          (congrArg (fun right : ℝ => kernel.re * right)
            (Complex.ofReal_re square))
          (congrArg (fun right : ℝ => kernel.im * right)
            (Complex.ofReal_im square))
      _ = kernel.re * square := by
        exact Eq.trans
          (congrArg (fun right : ℝ => kernel.re * square - right)
            (mul_zero kernel.im))
          (sub_zero (kernel.re * square))
  calc
    Complex.re
        (zetaCompletedArchimedeanHermitianKernel t *
          (zetaCompletedExplicitFormulaPhi f ((t : ℂ) * Complex.I) *
            star (zetaCompletedExplicitFormulaPhi f
              ((t : ℂ) * Complex.I)))) =
        Complex.re (kernel * (square : ℂ)) := by
      exact congrArg Complex.re
        (congrArg (fun right : ℂ => kernel * right) gramEquality)
    _ = kernel.re * square :=
      productReal
    _ =
        zetaCompletedArchimedeanSignedWeight t *
          Complex.normSq
            (zetaCompletedExplicitFormulaPhi f ((t : ℂ) * Complex.I)) := by
      exact Eq.refl _

/-- The real part of the Hermitian autocorrelation integrand is the signed
packet coordinate. -/
theorem zetaCompletedArchimedeanHermitianIntegrand_autocorrelation_re
    (f : ZetaAdmissibleFunction) (t : ℝ) :
    (Complex.re
        (zetaCompletedArchimedeanHermitianIntegrand
          (convolutionAutocorrelation f) t) : ℂ) =
      zetaCompletedArchimedeanSignedGramCoordinate f t := by
  have transformEquality :=
    zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation_imaginary f t
  have realEquality :=
    zetaCompletedArchimedeanHermitianKernel_mul_probeGram_re f t
  have gramEquality :=
    zetaCompletedArchimedeanProbeGram_eq_normSq f t
  calc
    (Complex.re
        (zetaCompletedArchimedeanHermitianIntegrand
          (convolutionAutocorrelation f) t) : ℂ) =
        (Complex.re
          (zetaCompletedArchimedeanHermitianKernel t *
            (zetaCompletedExplicitFormulaPhi f ((t : ℂ) * Complex.I) *
              star (zetaCompletedExplicitFormulaPhi f
                ((t : ℂ) * Complex.I)))) : ℂ) := by
      exact congrArg (fun value : ℂ => (Complex.re value : ℂ))
        (congrArg
          (fun value : ℂ =>
            zetaCompletedArchimedeanHermitianKernel t * value)
          transformEquality)
    _ =
        ((zetaCompletedArchimedeanSignedWeight t *
          Complex.normSq
            (zetaCompletedExplicitFormulaPhi f ((t : ℂ) * Complex.I)) : ℝ) : ℂ) := by
      exact congrArg (fun value : ℝ => (value : ℂ)) realEquality
    _ =
        (zetaCompletedArchimedeanSignedWeight t : ℂ) *
          (Complex.normSq
            (zetaCompletedExplicitFormulaPhi f ((t : ℂ) * Complex.I)) : ℂ) := by
      exact Complex.ofReal_mul
        (zetaCompletedArchimedeanSignedWeight t)
        (Complex.normSq
          (zetaCompletedExplicitFormulaPhi f ((t : ℂ) * Complex.I)))
    _ = zetaCompletedArchimedeanSignedGramCoordinate f t := by
      exact congrArg
        (fun right : ℂ =>
          (zetaCompletedArchimedeanSignedWeight t : ℂ) * right)
        gramEquality.symm

/-- The whole-line positive variation of the archimedean packet. -/
noncomputable def zetaCompletedArchimedeanPositiveQuadraticForm
    (f : ZetaAdmissibleFunction) : ℂ :=
  ∫ t : ℝ, zetaCompletedArchimedeanPositiveGramCoordinate f t

/-- The whole-line negative variation of the archimedean packet. -/
noncomputable def zetaCompletedArchimedeanNegativeQuadraticForm
    (f : ZetaAdmissibleFunction) : ℂ :=
  ∫ t : ℝ, zetaCompletedArchimedeanNegativeGramCoordinate f t

/-- The whole-line signed archimedean packet form. -/
noncomputable def zetaCompletedArchimedeanSignedQuadraticForm
    (f : ZetaAdmissibleFunction) : ℂ :=
  ∫ t : ℝ, zetaCompletedArchimedeanSignedGramCoordinate f t

/-- Integral Jordan decomposition of the signed archimedean packet. -/
theorem zetaCompletedArchimedeanSignedQuadraticForm_eq_positive_sub_negative
    (f : ZetaAdmissibleFunction)
    (positiveIntegrable :
      Integrable (zetaCompletedArchimedeanPositiveGramCoordinate f))
    (negativeIntegrable :
      Integrable (zetaCompletedArchimedeanNegativeGramCoordinate f)) :
    zetaCompletedArchimedeanSignedQuadraticForm f =
      zetaCompletedArchimedeanPositiveQuadraticForm f -
        zetaCompletedArchimedeanNegativeQuadraticForm f := by
  have pointwiseEquality :
      (fun t : ℝ => zetaCompletedArchimedeanSignedGramCoordinate f t) =
        fun t : ℝ =>
          zetaCompletedArchimedeanPositiveGramCoordinate f t -
            zetaCompletedArchimedeanNegativeGramCoordinate f t := by
    funext t
    exact
      zetaCompletedArchimedeanSignedGramCoordinate_eq_positive_sub_negative
        f t
  calc
    zetaCompletedArchimedeanSignedQuadraticForm f =
        ∫ t : ℝ,
          zetaCompletedArchimedeanPositiveGramCoordinate f t -
            zetaCompletedArchimedeanNegativeGramCoordinate f t := by
      exact congrArg
        (fun integrand : ℝ → ℂ => ∫ t : ℝ, integrand t)
        pointwiseEquality
    _ =
        (∫ t : ℝ, zetaCompletedArchimedeanPositiveGramCoordinate f t) -
          ∫ t : ℝ, zetaCompletedArchimedeanNegativeGramCoordinate f t := by
      exact integral_sub positiveIntegrable negativeIntegrable
    _ =
        zetaCompletedArchimedeanPositiveQuadraticForm f -
          zetaCompletedArchimedeanNegativeQuadraticForm f := by
      exact Eq.refl _

/-- Once the Hermitian autocorrelation integrand is integrable, its real part
is exactly the signed continuum packet form. -/
theorem zetaCompletedArchimedeanSignedQuadraticForm_eq_archimedeanContribution_re
    (f : ZetaAdmissibleFunction)
    (hermitianIntegrable :
      Integrable
        (zetaCompletedArchimedeanHermitianIntegrand
          (convolutionAutocorrelation f))) :
    zetaCompletedArchimedeanSignedQuadraticForm f =
      (Complex.re
        (zetaCompletedExplicitFormulaArchimedeanContribution
          (convolutionAutocorrelation f)) : ℂ) := by
  have pointwiseEquality :
      (fun t : ℝ =>
        (Complex.re
          (zetaCompletedArchimedeanHermitianIntegrand
            (convolutionAutocorrelation f) t) : ℂ)) =
        zetaCompletedArchimedeanSignedGramCoordinate f := by
    funext t
    exact zetaCompletedArchimedeanHermitianIntegrand_autocorrelation_re f t
  let H : ℝ → ℂ := fun t : ℝ =>
    zetaCompletedArchimedeanHermitianIntegrand
      (convolutionAutocorrelation f) t
  let R : ℝ → ℝ := fun t : ℝ => Complex.re (H t)
  have realIntegralEquality :
      (∫ t : ℝ, R t) =
        Complex.re (∫ t : ℝ, H t) := by
    unfold R
    unfold H
    exact integral_re hermitianIntegrable
  have realIntegralComplexEquality :
      (∫ t : ℝ, (R t : ℂ)) =
        (Complex.re (∫ t : ℝ, H t) : ℂ) := by
    exact Eq.trans
      (_root_.integral_ofReal (𝕜 := ℂ) (f := R))
      (congrArg (fun value : ℝ => (value : ℂ)) realIntegralEquality)
  have pointwiseEqualityR :
      (fun t : ℝ => (R t : ℂ)) =
        zetaCompletedArchimedeanSignedGramCoordinate f := by
    unfold R
    unfold H
    exact pointwiseEquality
  calc
    zetaCompletedArchimedeanSignedQuadraticForm f =
        ∫ t : ℝ, (R t : ℂ) := by
      exact congrArg
        (fun integrand : ℝ → ℂ => ∫ t : ℝ, integrand t)
        pointwiseEqualityR.symm
    _ =
        (Complex.re (∫ t : ℝ, H t) : ℂ) := by
      exact realIntegralComplexEquality
    _ =
        (Complex.re
          (zetaCompletedExplicitFormulaArchimedeanContribution
            (convolutionAutocorrelation f)) : ℂ) := by
      unfold H
      exact Eq.refl _

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
