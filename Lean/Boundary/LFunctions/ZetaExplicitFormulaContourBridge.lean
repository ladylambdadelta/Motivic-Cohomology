import Boundary.LFunctions.ZetaCompletedExplicitFormulaAssembly
import Boundary.LFunctions.ZetaExplicitFormulaBoundaryTransport
import Boundary.LFunctions.ZetaExplicitFormulaFinalTarget
import Boundary.LFunctions.ZetaExplicitFormulaNormalizationBridge

/-!
# Boundary explicit-formula contour bridge

This file is the owner-level wrapper for the completed contour-shift theorem
in the current repository normalization. The analytic content is carried by
the class-free transport theorem; this file keeps the exact final theorem
shape available in the contour namespace.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The completed explicit-formula target actually used by the quadratic/autocorrelation
positivity lane. -/
def zetaCompletedExplicitFormulaConvolutionAutocorrelationTarget
    (f : ZetaAdmissibleFunction) : Prop :=
  zetaCompletedZeroKreinGram (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
    ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f

/-- The autocorrelation target unfolds to the seed-Krein boundary equality. -/
theorem zetaCompletedExplicitFormulaConvolutionAutocorrelationTarget_iff
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaConvolutionAutocorrelationTarget f ↔
      zetaCompletedZeroKreinGram (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f := by
  rfl

/-- The completed explicit-formula contour bridge for convolution-autocorrelation probes, using
the holographic boundary normalization. -/
theorem zetaCompletedExplicitFormulaContourBridge_convolutionAutocorrelation
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f := by
  let g : ZetaAdmissibleFunction := ZetaAdmissibleFunction.convolutionAutocorrelation f
  have hshift : explicitFormulaContourShiftTarget g ⟨1, 1⟩ :=
    explicitFormulaContourShiftTarget_of_rectangle g ⟨1, 1⟩
  have hboundary :
      zetaCompletedExplicitFormulaBoundarySumAnalytic g =
        (zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f : ℂ) :=
    zetaCompletedExplicitFormulaBoundarySumAnalytic_convolutionAutocorrelation_eq_seedKreinSum f
  exact Complex.ofReal_injective (Eq.trans hshift hboundary)

/-- Historical name for the convolution-autocorrelation contour bridge. -/
theorem zetaCompletedExplicitFormulaContourBridge_autocorrelation
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f := by
  exact zetaCompletedExplicitFormulaContourBridge_convolutionAutocorrelation f

/-- The completed contour bridge proves the named autocorrelation target. -/
theorem zetaCompletedExplicitFormulaConvolutionAutocorrelationTarget_of_contourBridge
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaConvolutionAutocorrelationTarget f := by
  exact zetaCompletedExplicitFormulaContourBridge_convolutionAutocorrelation f

/-- A contour-shift target proves the completed explicit-formula contour bridge once the analytic
boundary sum has been normalized to the signed real boundary sum. -/
theorem zetaCompletedExplicitFormulaContourBridge_of_contourShiftTarget
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle)
    (hshift : explicitFormulaContourShiftTarget f r)
    (hboundary :
      zetaCompletedExplicitFormulaBoundarySumAnalytic f =
        (zetaCompletedExplicitFormulaBoundarySum f : ℂ)) :
    zetaCompletedZeroKreinGram f =
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaBoundarySum f :=
  Complex.ofReal_injective (Eq.trans hshift hboundary)

/-- A proved contour bridge is exactly the completed explicit-formula target. -/
theorem zetaCompletedExplicitFormulaAutocorrelationTarget_of_contourBridge
    (f : ZetaAdmissibleFunction)
    (hbridge :
      zetaCompletedZeroKreinGram f =
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaBoundarySum f) :
    zetaCompletedExplicitFormulaAutocorrelationTarget f :=
  hbridge

/-- The contour-shift theorem plus boundary normalization proves the completed explicit-formula
target. -/
theorem zetaCompletedExplicitFormulaAutocorrelationTarget_of_contourShiftTarget
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle)
    (hshift : explicitFormulaContourShiftTarget f r)
    (hboundary :
      zetaCompletedExplicitFormulaBoundarySumAnalytic f =
        (zetaCompletedExplicitFormulaBoundarySum f : ℂ)) :
    zetaCompletedExplicitFormulaAutocorrelationTarget f :=
  zetaCompletedExplicitFormulaAutocorrelationTarget_of_contourBridge f
    (zetaCompletedExplicitFormulaContourBridge_of_contourShiftTarget
      f r hshift hboundary)

/-- Convolution-autocorrelation specialization of the completed explicit-formula contour bridge
with the seed packet Krein normalization. -/
theorem zetaCompletedExplicitFormulaConvolutionAutocorrelationSeedKrein_of_contourShiftTarget
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle)
    (hshift :
      explicitFormulaContourShiftTarget
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) r)
    (hboundary :
      zetaCompletedExplicitFormulaBoundarySumAnalytic
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
        (zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f : ℂ)) :
    zetaCompletedZeroKreinGram (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f :=
  Complex.ofReal_injective (Eq.trans hshift hboundary)

/-- Historical name for the convolution-autocorrelation contour-shift specialization. -/
theorem zetaCompletedExplicitFormulaAutocorrelationSeedKrein_of_contourShiftTarget
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle)
    (hshift :
      explicitFormulaContourShiftTarget
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) r)
    (hboundary :
      zetaCompletedExplicitFormulaBoundarySumAnalytic
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
        (zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f : ℂ)) :
    zetaCompletedZeroKreinGram (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f :=
  zetaCompletedExplicitFormulaConvolutionAutocorrelationSeedKrein_of_contourShiftTarget
    f r hshift hboundary

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
