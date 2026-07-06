import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleFourCellCauchyBase

/-!
# Bottom zero-pole four-cell Cauchy cancellation
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology Interval

namespace ZetaAdmissibleFunction

/-- Bottom-cell Cauchy cancellation for the canonical zero-pole puncture. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_canonicalBottomCellBoundary_eq_zero_of_pos_height
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (T : ℝ)
    (hT : 0 < T) :
    zetaExplicitFormulaZeroPoleBottomPunctureCellBoundaryIntegral
      (zetaCompletedExplicitFormulaCorrectionZeroPoleKernelFn f)
      F T (zetaExplicitFormulaZeroPolePunctureRadius F T) = 0 := by
  let R : ℝ := zetaExplicitFormulaZeroPolePunctureRadius F T
  have HcBottom :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleKernel_continuousOn_of_avoids_pole
      f h.phi_control
      ([[ ((1 - F.c : ℝ) + (-T : ℝ) * Complex.I).re,
           (F.c + (-R : ℝ) * Complex.I).re ]] ×ℂ
        [[ ((1 - F.c : ℝ) + (-T : ℝ) * Complex.I).im,
           (F.c + (-R : ℝ) * Complex.I).im ]])
      (zetaExplicitFormulaZeroPole_canonicalBottomCell_avoids_zero_of_pos_height
        F hT)
  have HdBottom :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min ((1 - F.c : ℝ) + (-T : ℝ) * Complex.I).re
                  (F.c + (-R : ℝ) * Complex.I).re)
                (max ((1 - F.c : ℝ) + (-T : ℝ) * Complex.I).re
                  (F.c + (-R : ℝ) * Complex.I).re) ×ℂ
              Set.Ioo
                (min ((1 - F.c : ℝ) + (-T : ℝ) * Complex.I).im
                  (F.c + (-R : ℝ) * Complex.I).im)
                (max ((1 - F.c : ℝ) + (-T : ℝ) * Complex.I).im
                  (F.c + (-R : ℝ) * Complex.I).im) \ ({(0 : ℂ)} : Set ℂ) →
          DifferentiableAt ℂ
            (zetaCompletedExplicitFormulaCorrectionZeroPoleKernelFn f)
            x := by
    intro x hx
    exact
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel_differentiableAt_of_not_mem_singleton
        f h.phi_control hx.2
  exact
    show
      zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral
        (zetaCompletedExplicitFormulaCorrectionZeroPoleKernelFn f)
        ((1 - F.c : ℝ) + (-T : ℝ) * Complex.I)
        (F.c + (-R : ℝ) * Complex.I) = 0 from
      zetaCompletedExplicitFormulaCorrectionZeroPole_cellBoundary_eq_zero_of_regularity
        f ((1 - F.c : ℝ) + (-T : ℝ) * Complex.I)
          (F.c + (-R : ℝ) * Complex.I)
        HcBottom HdBottom

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary
