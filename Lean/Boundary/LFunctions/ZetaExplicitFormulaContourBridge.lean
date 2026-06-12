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

/-- The completed explicit-formula contour bridge after descent to the completed
ordered-heart scalar.  This is the true payoff theorem for the GNS-positive route: the
contour-side zero sum lands directly in the ordered-heart quotient scalar, not in the raw
time-side representative. -/
theorem zetaCompletedExplicitFormulaContourBridge_convolutionAutocorrelation_orderedHeart
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram (ZetaAdmissibleFunction.convolutionAutocorrelation f) +
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar
        f := by
  let g : ZetaAdmissibleFunction := ZetaAdmissibleFunction.convolutionAutocorrelation f
  have hshift : explicitFormulaContourShiftTarget g ⟨1, 1⟩ :=
    explicitFormulaContourShiftTarget_of_rectangle g ⟨1, 1⟩
  have hboundary :
      zetaCompletedExplicitFormulaBoundarySumAnalytic g +
          (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) : ℂ) =
        (zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar f : ℂ) := by
    exact
      zetaCompletedExplicitFormulaBoundarySumAnalytic_convolutionAutocorrelation_eq_orderedHeartScalar
        f
  apply Complex.ofReal_injective
  calc
    (zetaCompletedZeroKreinGram
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) +
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) : ℂ) =
        (zetaCompletedZeroKreinGram
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) : ℂ) +
          (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) : ℂ) := by
      exact Complex.ofReal_add
        (zetaCompletedZeroKreinGram
          (ZetaAdmissibleFunction.convolutionAutocorrelation f))
        (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))
    _ =
        zetaCompletedExplicitFormulaBoundarySumAnalytic g +
          (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) : ℂ) := by
      exact congrArg
        (fun z : ℂ =>
          z + (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) : ℂ))
        hshift
    _ =
        (zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar f : ℂ) :=
      hboundary

/-- The completed prime diagonal debt is lower-weight radical on the zero side: adding it to
the zero-side Krein scalar does not change the represented zero-side class. -/
theorem zetaCompletedZeroKreinGram_add_primeDiagonalDebt_eq_zeroKreinGram
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram (ZetaAdmissibleFunction.convolutionAutocorrelation f) +
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
      zetaCompletedZeroKreinGram (ZetaAdmissibleFunction.convolutionAutocorrelation f) := by
  have hzero_krein :
      zetaCompletedZeroKreinGram (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum
          f :=
    zetaCompletedExplicitFormulaContourBridge_convolutionAutocorrelation f
  have hkrein_debt :
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum
          f +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
        ZetaAdmissibleFunction
          .zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar f :=
    zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum_add_primeDiagonalDebt_eq_orderedHeartScalar
      f
  have hkrein_ordered :
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum
          f =
        ZetaAdmissibleFunction
          .zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar f :=
    zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum_eq_orderedHeartScalar_by_zeroSideLowerWeightAbsorption
      f
  have hzero_debt :
      zetaCompletedZeroKreinGram (ZetaAdmissibleFunction.convolutionAutocorrelation f) +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
        ZetaAdmissibleFunction
          .zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar f := by
    exact
      (congrArg
        (fun x : ℝ =>
          x + Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))
        hzero_krein).trans
        hkrein_debt
  exact hzero_debt.trans (hkrein_ordered.symm.trans hzero_krein.symm)

/-- The debt-visible ordered-heart contour bridge after zero-side lower-weight absorption. -/
theorem zetaCompletedExplicitFormulaContourBridge_convolutionAutocorrelation_orderedHeart_noDebt
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar
        f := by
  have hdebt :
      zetaCompletedZeroKreinGram (ZetaAdmissibleFunction.convolutionAutocorrelation f) +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
        zetaCompletedZeroKreinGram (ZetaAdmissibleFunction.convolutionAutocorrelation f) :=
    zetaCompletedZeroKreinGram_add_primeDiagonalDebt_eq_zeroKreinGram f
  have hbridge :
      zetaCompletedZeroKreinGram (ZetaAdmissibleFunction.convolutionAutocorrelation f) +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar
          f :=
    zetaCompletedExplicitFormulaContourBridge_convolutionAutocorrelation_orderedHeart f
  exact hdebt.symm.trans hbridge

/-- Historical name for the convolution-autocorrelation contour bridge. -/
theorem zetaCompletedExplicitFormulaContourBridge_autocorrelation
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f := by
  exact zetaCompletedExplicitFormulaContourBridge_convolutionAutocorrelation f

/-- Historical name for the ordered-heart convolution-autocorrelation contour bridge. -/
theorem zetaCompletedExplicitFormulaContourBridge_autocorrelation_orderedHeart
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar
        f := by
  exact zetaCompletedExplicitFormulaContourBridge_convolutionAutocorrelation_orderedHeart_noDebt f

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
