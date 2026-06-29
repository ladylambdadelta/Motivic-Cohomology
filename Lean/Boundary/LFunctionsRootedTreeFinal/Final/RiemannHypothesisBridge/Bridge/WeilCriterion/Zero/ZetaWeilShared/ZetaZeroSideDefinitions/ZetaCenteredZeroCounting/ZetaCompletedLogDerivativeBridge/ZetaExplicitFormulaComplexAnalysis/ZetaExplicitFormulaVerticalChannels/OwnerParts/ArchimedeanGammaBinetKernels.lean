import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.CorrectionAffineValues
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.InverseGammaAffineKernelEstimate

/-!
# Archimedean Gamma/Binet kernels

This file owns the raw Gamma/Binet archimedean line kernels and the paired
whole-line transform integral names.  It is deliberately below the majorant,
decomposition, and value layers.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open LSeries ArithmeticFunction
open MeasureTheory
open scoped ArithmeticFunction

namespace ZetaAdmissibleFunction

/-- The elementary `π` contribution in the `Gammaℝ` logarithmic derivative.

With the completed-zeta normalization used in this lane,
`Gammaℝ'/Gammaℝ = gammaRealPiLogDerivativeTerm + (1/2) * Gamma'/Gamma(s/2)`. -/
noncomputable def zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm : ℂ :=
  Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ))

/-- Right affine-line Binet main kernel for the archimedean logarithmic
derivative.

The sign is forced by
`explicitFormulaArchimedeanLogDerivative = inverseGammaCompletionLogDeriv -
explicitFormulaCorrectionLogDerivative` and
`inverseGammaCompletionLogDeriv = - Gammaℝ'/Gammaℝ`. -/
noncomputable def zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (t : ℝ) : ℂ :=
  (-(zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
        (1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalMain
            (F.c / 2) (t / 2)) -
      explicitFormulaCorrectionLogDerivative
        (zetaCompletedExplicitFormulaRightAffineLine F t)) *
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)

/-- Right affine-line Binet remainder kernel for the archimedean logarithmic
derivative. -/
noncomputable def zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (t : ℝ) : ℂ :=
  (-((1 / 2 : ℂ) *
      Complex.GammaLogDerivativeFixedVerticalRemainder
        (F.c / 2) (t / 2))) *
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)

/-- The canonical finite Gamma-recurrence shift used on the left affine
archimedean half-line. -/
noncomputable def zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat
    (F : ExplicitFormulaContourFamily) : ℕ :=
  Complex.GammaLogDerivativeFixedVerticalPositiveShiftNat
    ((1 - F.c) / 2)

/-- Left affine-line Binet main kernel for the archimedean logarithmic
derivative. -/
noncomputable def zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (t : ℝ) : ℂ :=
    (-(zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
        (1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalShiftNatMain
            ((1 - F.c) / 2)
            (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
            (t / 2)) -
      explicitFormulaCorrectionLogDerivative
        (zetaCompletedExplicitFormulaLeftAffineLine F t)) *
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)

/-- Left affine-line Binet remainder kernel for the archimedean logarithmic
derivative. -/
noncomputable def zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (t : ℝ) : ℂ :=
  (-((1 / 2 : ℂ) *
      Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder
        ((1 - F.c) / 2)
        (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
        (t / 2))) *
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)

/-- Coupled whole-line right Gamma/Binet transform integral.

The main and differentiated-remainder terms are deliberately kept together:
the owner value theorem evaluates this coupled transform, not either summand
separately. -/
noncomputable def zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransformIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) : ℂ :=
  (∫ t : ℝ,
    zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel f F t) +
    ∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel f F t

/-- Coupled whole-line shifted-left Gamma/Binet transform integral.

The finite Gamma-recurrence shift is part of the coupled left transform and must
not be peeled into a downstream correction term. -/
noncomputable def zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransformIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) : ℂ :=
  (∫ t : ℝ,
    zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel f F t) +
    ∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel f F t

/-- The right coupled whole-line Gamma/Binet transform integral unfolds to the
sum of the main and differentiated-remainder integrals. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransformIntegral_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) :
    zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransformIntegral
        f F =
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel f F t) +
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F t :=
  rfl

/-- The shifted-left coupled whole-line Gamma/Binet transform integral unfolds to
the sum of the shifted main and differentiated-remainder integrals. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransformIntegral_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) :
    zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransformIntegral
        f F =
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel f F t) +
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F t :=
  rfl

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
