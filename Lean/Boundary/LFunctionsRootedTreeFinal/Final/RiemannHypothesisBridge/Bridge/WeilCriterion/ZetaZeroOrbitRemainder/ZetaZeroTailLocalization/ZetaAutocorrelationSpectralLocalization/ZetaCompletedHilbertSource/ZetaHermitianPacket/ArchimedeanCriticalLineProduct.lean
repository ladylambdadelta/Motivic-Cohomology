import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.ArchimedeanSignedPacket
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaAdmissibleTransformRegularity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffineKernelMajorantPackage

/-!
# Critical-line product majorants

This file owns the common Paley-Wiener estimate on centered spectral
coordinates. A measurable linearly bounded factor times an admissible transform
on the imaginary axis has an integrable fourth-order majorant.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open MeasureTheory

namespace ZetaAdmissibleFunction

/-- The centered imaginary spectral coordinate has zero real part. -/
theorem zetaCompletedImaginarySpectralCoordinate_re (t : ℝ) :
    ((t : ℂ) * Complex.I).re = 0 := by
  calc
    ((t : ℂ) * Complex.I).re =
        (t : ℂ).re * Complex.I.re - (t : ℂ).im * Complex.I.im := by
      exact Complex.mul_re (t : ℂ) Complex.I
    _ = t * 0 - 0 * 1 := by
      exact congrArg₂ Sub.sub
        (congrArg₂ Mul.mul (Complex.ofReal_re t) Complex.I_re)
        (congrArg₂ Mul.mul (Complex.ofReal_im t) Complex.I_im)
    _ = 0 := by
      exact Eq.trans
        (congrArg₂ Sub.sub (mul_zero t) (zero_mul (1 : ℝ)))
        (sub_zero 0)

/-- The centered imaginary spectral coordinate has imaginary part equal to its
height. -/
theorem zetaCompletedImaginarySpectralCoordinate_im (t : ℝ) :
    ((t : ℂ) * Complex.I).im = t := by
  calc
    ((t : ℂ) * Complex.I).im =
        (t : ℂ).re * Complex.I.im + (t : ℂ).im * Complex.I.re := by
      exact Complex.mul_im (t : ℂ) Complex.I
    _ = t * 1 + 0 * 0 := by
      exact congrArg₂ Add.add
        (congrArg₂ Mul.mul (Complex.ofReal_re t) Complex.I_im)
        (congrArg₂ Mul.mul (Complex.ofReal_im t) Complex.I_re)
    _ = t := by
      exact Eq.trans
        (congrArg₂ Add.add (mul_one t) (zero_mul (0 : ℝ)))
        (add_zero t)

/-- The admissible transform on centered imaginary coordinates is strongly
measurable. -/
theorem zetaCompletedExplicitFormulaPhi_imaginary_aestronglyMeasurable
    (f : ZetaAdmissibleFunction) :
    AEStronglyMeasurable
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaPhi f ((t : ℂ) * Complex.I))
      (volume : Measure ℝ) := by
  have transformDifferentiableAt :
      ∀ z : ℂ,
        DifferentiableAt ℂ (fun z : ℂ => zetaCompletedExplicitFormulaPhi f z) z := by
    intro z
    have hbase :
        DifferentiableAt ℂ
          (fun z : ℂ => Boundary.zetaLaplaceTransform f.toZetaTestFunction' z)
          z :=
      Boundary.zetaLaplaceTransform_differentiableAt f z
    have hphi :
        (fun z : ℂ => zetaCompletedExplicitFormulaPhi f z) =
          (fun z : ℂ => Boundary.zetaLaplaceTransform f.toZetaTestFunction' z) :=
      zetaCompletedExplicitFormulaPhi_eq_laplace f
    exact Eq.subst
      (motive := fun Φ : ℂ → ℂ => DifferentiableAt ℂ Φ z)
      hphi.symm
      hbase
  have transformContinuous :
      Continuous (fun z : ℂ => zetaCompletedExplicitFormulaPhi f z) :=
    continuous_iff_continuousAt.mpr
      (fun z : ℂ => (transformDifferentiableAt z).continuousAt)
  have coordinateContinuous :
      Continuous (fun t : ℝ => (t : ℂ) * Complex.I) :=
    (Complex.continuous_ofReal.comp continuous_id).mul continuous_const
  exact
    (transformContinuous.comp coordinateContinuous).aestronglyMeasurable

/-- A linearly bounded measurable factor times a centered admissible transform
has an integrable majorant package. -/
theorem exists_zetaCompletedCriticalLineProduct_majorantPackage_of_linearFactor
    (f : ZetaAdmissibleFunction)
    (factor : ℝ → ℂ) (bound : ℝ)
    (boundNonnegative : 0 ≤ bound)
    (factorMeasurable :
      AEStronglyMeasurable factor (volume : Measure ℝ))
    (factorBound :
      ∀ t : ℝ, ‖factor t‖ ≤ bound * (1 + ‖t‖)) :
    Nonempty
      ExplicitFormulaAffineKernelMajorantPackage
        (fun t : ℝ =>
          factor t *
            zetaCompletedExplicitFormulaPhi f ((t : ℂ) * Complex.I)) := by
  match zetaPhi_verticalStripRapidDecay f 0 0 4 with
  | ⟨decayConstant, _decayConstantPositive, decayBound⟩ =>
  let majorant : ℝ → ℝ :=
    fun t : ℝ =>
      bound * (decayConstant * (1 + ‖t‖) ^ (-(3 : ℤ)))
  have majorantIntegrable :
      Integrable majorant (volume : Measure ℝ) := by
    have finrankEquality : Module.finrank ℝ ℝ = 1 :=
      Module.finrank_self ℝ
    have finrankCast : ((Module.finrank ℝ ℝ : ℕ) : ℝ) = 1 :=
      Eq.trans
        (congrArg (fun n : ℕ => (n : ℝ)) finrankEquality)
        Nat.cast_one
    have two_add_one_eq_three : (2 : ℝ) + 1 = 3 :=
      two_add_one_eq_three
    have twoLessThanThree : (2 : ℝ) < 3 :=
      Eq.subst
        (motive := fun value : ℝ => (2 : ℝ) < value)
        two_add_one_eq_three
        (lt_add_of_pos_right 2 zero_lt_one)
    have dimensionBound : (Module.finrank ℝ ℝ : ℝ) < 3 :=
      Eq.subst
        (motive := fun value : ℝ => value < 3)
        finrankCast.symm
        (lt_trans one_lt_two twoLessThanThree)
    have baseIntegrable :
        Integrable
          (fun t : ℝ => (1 + ‖t‖) ^ (-(3 : ℝ)))
          (volume : Measure ℝ) :=
      integrable_one_add_norm dimensionBound
    have scaledIntegrable :
        Integrable
          (fun t : ℝ =>
            bound *
              (decayConstant * (1 + ‖t‖) ^ (-(3 : ℝ))))
          (volume : Measure ℝ) :=
      (baseIntegrable.const_mul decayConstant).const_mul bound
    have functionEquality :
        majorant =
          fun t : ℝ =>
            bound *
              (decayConstant * (1 + ‖t‖) ^ (-(3 : ℝ))) := by
      funext t
      have exponentEquality : ((-(3 : ℤ) : ℤ) : ℝ) = -(3 : ℝ) :=
        Int.cast_neg 3
      have powerEquality :
          (1 + ‖t‖) ^ (-(3 : ℤ)) =
            (1 + ‖t‖) ^ (-(3 : ℝ)) :=
        Eq.trans
          (Real.rpow_intCast (1 + ‖t‖) (-(3 : ℤ))).symm
          (congrArg
            (fun exponent : ℝ => (1 + ‖t‖) ^ exponent)
            exponentEquality)
      exact congrArg
        (fun weight : ℝ => bound * (decayConstant * weight))
        powerEquality
    exact Eq.subst
      (motive := fun function : ℝ → ℝ =>
        Integrable function (volume : Measure ℝ))
      functionEquality.symm
      scaledIntegrable
  have transformMeasurable :
      AEStronglyMeasurable
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaPhi f ((t : ℂ) * Complex.I))
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaPhi_imaginary_aestronglyMeasurable f
  have productBound :
      ∀ᵐ t ∂(volume : Measure ℝ),
        ‖factor t‖ *
            ‖zetaCompletedExplicitFormulaPhi f ((t : ℂ) * Complex.I)‖ ≤
          majorant t :=
    Filter.Eventually.of_forall
      (fun t : ℝ =>
        have factorEstimate : ‖factor t‖ ≤ bound * (1 + ‖t‖) :=
          factorBound t
        have transformEstimate :
            ‖zetaCompletedExplicitFormulaPhi f ((t : ℂ) * Complex.I)‖ ≤
              decayConstant * (1 + ‖t‖) ^ (-(4 : ℤ)) :=
          by
            have transformEstimateRaw :
                ‖zetaCompletedExplicitFormulaPhi f ((t : ℂ) * Complex.I)‖ ≤
                  decayConstant *
                    (1 + ‖((t : ℂ) * Complex.I).im‖) ^ (-(4 : ℤ)) :=
              decayBound
                ((t : ℂ) * Complex.I)
                (le_of_eq (zetaCompletedImaginarySpectralCoordinate_re t).symm)
                (le_of_eq (zetaCompletedImaginarySpectralCoordinate_re t))
            have weightEquality :
                (1 + ‖((t : ℂ) * Complex.I).im‖) ^ (-(4 : ℤ)) =
                  (1 + ‖t‖) ^ (-(4 : ℤ)) :=
              congrArg
                (fun value : ℝ => (1 + ‖value‖) ^ (-(4 : ℤ)))
                (zetaCompletedImaginarySpectralCoordinate_im t)
            exact Eq.subst
              (motive := fun weight : ℝ =>
                ‖zetaCompletedExplicitFormulaPhi f ((t : ℂ) * Complex.I)‖ ≤
                  decayConstant * weight)
              weightEquality
              transformEstimateRaw
        have transformNormNonnegative :
            0 ≤
              ‖zetaCompletedExplicitFormulaPhi f ((t : ℂ) * Complex.I)‖ :=
          norm_nonneg _
        have factorMajorantNonnegative : 0 ≤ bound * (1 + ‖t‖) :=
          mul_nonneg boundNonnegative
            (add_nonneg zero_le_one (norm_nonneg t))
        have multipliedEstimate :
            ‖factor t‖ *
                ‖zetaCompletedExplicitFormulaPhi f ((t : ℂ) * Complex.I)‖ ≤
              (bound * (1 + ‖t‖)) *
                (decayConstant * (1 + ‖t‖) ^ (-(4 : ℤ))) :=
          mul_le_mul factorEstimate transformEstimate
            transformNormNonnegative factorMajorantNonnegative
        have baseNonzero : (1 + ‖t‖ : ℝ) ≠ 0 :=
          ne_of_gt
            (lt_of_lt_of_le zero_lt_one
              (le_add_of_nonneg_right (norm_nonneg t)))
        have weightEquality :
            (1 + ‖t‖) * (1 + ‖t‖) ^ (-(4 : ℤ)) =
              (1 + ‖t‖) ^ (-(3 : ℤ)) := by
          calc
            (1 + ‖t‖) * (1 + ‖t‖) ^ (-(4 : ℤ)) =
                (1 + ‖t‖) ^ (1 : ℤ) *
                  (1 + ‖t‖) ^ (-(4 : ℤ)) := by
              exact congrArg
                (fun left : ℝ => left * (1 + ‖t‖) ^ (-(4 : ℤ)))
                (zpow_one (1 + ‖t‖)).symm
            _ = (1 + ‖t‖) ^ ((1 : ℤ) + (-(4 : ℤ))) := by
              exact (zpow_add₀ baseNonzero (1 : ℤ) (-(4 : ℤ))).symm
            _ = (1 + ‖t‖) ^ (-(3 : ℤ)) := by
              exact Eq.refl _
        have scalarEquality :
            (bound * (1 + ‖t‖)) *
                (decayConstant * (1 + ‖t‖) ^ (-(4 : ℤ))) =
              majorant t := by
          calc
            (bound * (1 + ‖t‖)) *
                (decayConstant * (1 + ‖t‖) ^ (-(4 : ℤ))) =
                bound *
                  (decayConstant *
                    ((1 + ‖t‖) *
                      (1 + ‖t‖) ^ (-(4 : ℤ)))) := by
              exact
                Eq.trans
                  (mul_assoc bound (1 + ‖t‖)
                    (decayConstant *
                      (1 + ‖t‖) ^ (-(4 : ℤ))))
                  (congrArg (fun value : ℝ => bound * value)
                    (Eq.trans
                      (mul_assoc (1 + ‖t‖) decayConstant
                        ((1 + ‖t‖) ^ (-(4 : ℤ)))).symm
                      (Eq.trans
                        (congrArg
                          (fun left : ℝ =>
                            left * (1 + ‖t‖) ^ (-(4 : ℤ)))
                          (mul_comm (1 + ‖t‖) decayConstant))
                        (mul_assoc decayConstant (1 + ‖t‖)
                          ((1 + ‖t‖) ^ (-(4 : ℤ)))))))
            _ =
                bound *
                  (decayConstant * (1 + ‖t‖) ^ (-(3 : ℤ))) := by
              exact congrArg
                (fun weight : ℝ => bound * (decayConstant * weight))
                weightEquality
            _ = majorant t := by
              exact Eq.refl _
        multipliedEstimate.trans_eq scalarEquality)
  exact
    ⟨ExplicitFormulaAffineKernelMajorantPackage.of_mul_le
      majorant majorantIntegrable factorMeasurable transformMeasurable
      productBound⟩

/-- The common critical-line majorant directly yields integrability. -/
theorem zetaCompletedCriticalLineProduct_integrable_of_linearFactor
    (f : ZetaAdmissibleFunction)
    (factor : ℝ → ℂ) (bound : ℝ)
    (boundNonnegative : 0 ≤ bound)
    (factorMeasurable :
      AEStronglyMeasurable factor (volume : Measure ℝ))
    (factorBound :
      ∀ t : ℝ, ‖factor t‖ ≤ bound * (1 + ‖t‖)) :
    Integrable
      (fun t : ℝ =>
        factor t *
          zetaCompletedExplicitFormulaPhi f ((t : ℂ) * Complex.I))
      (volume : Measure ℝ) := by
  exact
    match exists_zetaCompletedCriticalLineProduct_majorantPackage_of_linearFactor
        f factor bound boundNonnegative factorMeasurable factorBound with
    | ⟨majorantPackage⟩ => majorantPackage.integrable

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
