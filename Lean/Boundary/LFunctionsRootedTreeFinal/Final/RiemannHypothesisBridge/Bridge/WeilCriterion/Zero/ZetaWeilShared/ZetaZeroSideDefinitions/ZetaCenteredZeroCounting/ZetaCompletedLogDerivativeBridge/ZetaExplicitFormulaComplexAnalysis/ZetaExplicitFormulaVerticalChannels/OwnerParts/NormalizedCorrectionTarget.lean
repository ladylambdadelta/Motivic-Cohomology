import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.NormalizedContourProjection
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.CorrectionContribution

/-!
# Normalized correction-channel target
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- A separated pole-face packet rotates to its real `2 pi` multiple. -/
theorem explicitFormula_twoPiI_mul_neg_mul_I
    (value : ℂ) :
    (explicitFormulaTwoPiI * (-value)) * Complex.I =
      explicitFormulaTwoPi * value := by
  have hrotation : Complex.I * Complex.I = -(1 : ℂ) :=
    Complex.I_mul_I
  calc
    (explicitFormulaTwoPiI * (-value)) * Complex.I =
        ((explicitFormulaTwoPi * Complex.I) * (-value)) * Complex.I := by
      exact Eq.refl _
    _ = (explicitFormulaTwoPi * (Complex.I * (-value))) * Complex.I := by
      exact congrArg (fun factor : ℂ => factor * Complex.I)
        (mul_assoc explicitFormulaTwoPi Complex.I (-value))
    _ = explicitFormulaTwoPi * ((Complex.I * (-value)) * Complex.I) := by
      exact mul_assoc explicitFormulaTwoPi (Complex.I * (-value)) Complex.I
    _ = explicitFormulaTwoPi * ((-value) * (Complex.I * Complex.I)) := by
      exact congrArg (fun factor : ℂ => explicitFormulaTwoPi * factor)
        (Eq.trans
          (congrArg (fun factor : ℂ => factor * Complex.I)
            (mul_comm Complex.I (-value)))
          (mul_assoc (-value) Complex.I Complex.I))
    _ = explicitFormulaTwoPi * ((-value) * (-(1 : ℂ))) := by
      exact congrArg
        (fun factor : ℂ => explicitFormulaTwoPi * ((-value) * factor))
        hrotation
    _ = explicitFormulaTwoPi * value := by
      have hneg : (-value) * (-(1 : ℂ)) = value := by
        calc
          (-value) * (-(1 : ℂ)) = value * (1 : ℂ) := by
            exact neg_mul_neg value 1
          _ = value := mul_one value
      exact congrArg (fun factor : ℂ => explicitFormulaTwoPi * factor) hneg

/-- The two separated correction pole faces combine to `2 pi` times
the completed-pole residue sum. -/
theorem zetaCompletedExplicitFormulaCorrectionStandardContourContribution_eq_twoPi_mul_completedPoleResidueSum
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaCorrectionStandardContourContribution f =
      explicitFormulaTwoPi *
        explicitFormulaRectangle_completedPoleResidueSum f := by
  let leftValue : ℂ :=
    zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))
  let rightValue : ℂ :=
    zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ)
  have hleft :
      (((2 * (Real.pi : ℂ) * Complex.I) * (-leftValue)) * Complex.I) =
        explicitFormulaTwoPi * leftValue := by
    exact explicitFormula_twoPiI_mul_neg_mul_I leftValue
  have hright :
      (((2 * (Real.pi : ℂ) * Complex.I) * (-rightValue)) * Complex.I) =
        explicitFormulaTwoPi * rightValue := by
    exact explicitFormula_twoPiI_mul_neg_mul_I rightValue
  have hpoles :
      explicitFormulaRectangle_completedPoleResidueSum f =
        (-leftValue) + (-rightValue) := by
    exact Eq.trans
      (explicitFormulaRectangle_completedPoleResidueSum_eq f)
      (congrArg₂ HAdd.hAdd
        (explicitFormulaRectangle_zeroPoleResidue_eq f)
        (explicitFormulaRectangle_onePoleResidue_eq f))
  calc
    zetaCompletedExplicitFormulaCorrectionStandardContourContribution f =
        -(((2 * (Real.pi : ℂ) * Complex.I) * (-leftValue)) * Complex.I) -
          (((2 * (Real.pi : ℂ) * Complex.I) * (-rightValue)) * Complex.I) := by
      exact zetaCompletedExplicitFormulaCorrectionStandardContourContribution_eq f
    _ = -(explicitFormulaTwoPi * leftValue) -
          explicitFormulaTwoPi * rightValue := by
      exact congrArg₂ Sub.sub (congrArg Neg.neg hleft) hright
    _ = -(explicitFormulaTwoPi * leftValue) +
          -(explicitFormulaTwoPi * rightValue) := by
      exact sub_eq_add_neg
        (-(explicitFormulaTwoPi * leftValue))
        (explicitFormulaTwoPi * rightValue)
    _ = explicitFormulaTwoPi * ((-leftValue) + (-rightValue)) := by
      calc
        -(explicitFormulaTwoPi * leftValue) +
            -(explicitFormulaTwoPi * rightValue) =
            explicitFormulaTwoPi * (-leftValue) +
              explicitFormulaTwoPi * (-rightValue) := by
          exact congrArg₂ HAdd.hAdd
            (mul_neg explicitFormulaTwoPi leftValue).symm
            (mul_neg explicitFormulaTwoPi rightValue).symm
        _ = explicitFormulaTwoPi * ((-leftValue) + (-rightValue)) := by
          exact (mul_add explicitFormulaTwoPi (-leftValue) (-rightValue)).symm
    _ = explicitFormulaTwoPi *
          explicitFormulaRectangle_completedPoleResidueSum f := by
      exact congrArg (fun value : ℂ => explicitFormulaTwoPi * value) hpoles.symm

/-- The raw standard-contour boundary target assembled from the three raw
vertical-channel limits. -/
noncomputable def zetaCompletedExplicitFormulaStandardContourBoundarySum
    (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution f +
    zetaCompletedExplicitFormulaArchimedeanContribution f +
    zetaCompletedExplicitFormulaCorrectionStandardContourContribution f

/-- The boundary target in the same normalized pole-corrected coordinates as
the residue theorem. -/
noncomputable def zetaCompletedExplicitFormulaNormalizedStandardContourBoundarySum
    (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaStandardContourBoundarySum f /
      explicitFormulaTwoPi -
    explicitFormulaRectangle_completedPoleResidueSum f

/-- The raw standard-contour boundary target unfolds into its three channels. -/
theorem zetaCompletedExplicitFormulaStandardContourBoundarySum_eq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaStandardContourBoundarySum f =
      zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution f +
        zetaCompletedExplicitFormulaArchimedeanContribution f +
        zetaCompletedExplicitFormulaCorrectionStandardContourContribution f := by
  exact Eq.refl _

/-- The normalized standard-contour target unfolds by division and pole
subtraction. -/
theorem zetaCompletedExplicitFormulaNormalizedStandardContourBoundarySum_eq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaNormalizedStandardContourBoundarySum f =
      zetaCompletedExplicitFormulaStandardContourBoundarySum f /
          explicitFormulaTwoPi -
        explicitFormulaRectangle_completedPoleResidueSum f := by
  exact Eq.refl _

/-- After the correction channel is normalized, its pole packet cancels the
explicit pole subtraction. -/
theorem zetaCompletedExplicitFormulaNormalizedStandardContourBoundarySum_eq_prime_add_archimedean_div
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaNormalizedStandardContourBoundarySum f =
      zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution f /
          explicitFormulaTwoPi +
        zetaCompletedExplicitFormulaArchimedeanContribution f /
          explicitFormulaTwoPi := by
  let prime : ℂ :=
    zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution f
  let archimedean : ℂ :=
    zetaCompletedExplicitFormulaArchimedeanContribution f
  let poles : ℂ := explicitFormulaRectangle_completedPoleResidueSum f
  have correction :
      zetaCompletedExplicitFormulaCorrectionStandardContourContribution f =
        explicitFormulaTwoPi * poles :=
    zetaCompletedExplicitFormulaCorrectionStandardContourContribution_eq_twoPi_mul_completedPoleResidueSum
      f
  have cancelCorrection :
      (explicitFormulaTwoPi * poles) / explicitFormulaTwoPi = poles := by
    exact mul_div_cancel_left₀ poles explicitFormulaTwoPi_ne_zero
  calc
    zetaCompletedExplicitFormulaNormalizedStandardContourBoundarySum f =
        (prime + archimedean +
            zetaCompletedExplicitFormulaCorrectionStandardContourContribution f) /
          explicitFormulaTwoPi - poles := by
      exact Eq.refl _
    _ = (prime + archimedean + explicitFormulaTwoPi * poles) /
          explicitFormulaTwoPi - poles := by
      exact congrArg
        (fun value : ℂ => value / explicitFormulaTwoPi - poles)
        (congrArg (fun value : ℂ => prime + archimedean + value) correction)
    _ = ((prime + archimedean) / explicitFormulaTwoPi +
          (explicitFormulaTwoPi * poles) / explicitFormulaTwoPi) - poles := by
      exact congrArg (fun value : ℂ => value - poles)
        (add_div (prime + archimedean)
          (explicitFormulaTwoPi * poles) explicitFormulaTwoPi)
    _ = ((prime + archimedean) / explicitFormulaTwoPi + poles) - poles := by
      exact congrArg
        (fun value : ℂ =>
          (prime + archimedean) / explicitFormulaTwoPi + value - poles)
        cancelCorrection
    _ = (prime + archimedean) / explicitFormulaTwoPi := by
      exact add_sub_cancel_right
        ((prime + archimedean) / explicitFormulaTwoPi) poles
    _ = prime / explicitFormulaTwoPi +
          archimedean / explicitFormulaTwoPi := by
      exact add_div prime archimedean explicitFormulaTwoPi

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
