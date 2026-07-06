import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleFourCellCauchyBase

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology Interval

namespace ZetaAdmissibleFunction

/-- Top-cell Cauchy cancellation for the canonical zero-pole puncture. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_canonicalTopCellBoundary_eq_zero_of_pos_height
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (T : ℝ)
    (hT : 0 < T) :
    zetaExplicitFormulaZeroPoleTopPunctureCellBoundaryIntegral
      (zetaCompletedExplicitFormulaCorrectionZeroPoleKernelFn f)
      F T (zetaExplicitFormulaZeroPolePunctureRadius F T) = 0 := by
  let R : ℝ := zetaExplicitFormulaZeroPolePunctureRadius F T
  have HcTop :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleKernel_continuousOn_of_avoids_pole
      f h.phi_control
      ([[ ((1 - F.c : ℝ) + (R : ℝ) * Complex.I).re,
           (F.c + (T : ℝ) * Complex.I).re ]] ×ℂ
        [[ ((1 - F.c : ℝ) + (R : ℝ) * Complex.I).im,
           (F.c + (T : ℝ) * Complex.I).im ]])
      (zetaExplicitFormulaZeroPole_canonicalTopCell_avoids_zero_of_pos_height
        F hT)
  have HdTop :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min ((1 - F.c : ℝ) + (R : ℝ) * Complex.I).re
                  (F.c + (T : ℝ) * Complex.I).re)
                (max ((1 - F.c : ℝ) + (R : ℝ) * Complex.I).re
                  (F.c + (T : ℝ) * Complex.I).re) ×ℂ
              Set.Ioo
                (min ((1 - F.c : ℝ) + (R : ℝ) * Complex.I).im
                  (F.c + (T : ℝ) * Complex.I).im)
                (max ((1 - F.c : ℝ) + (R : ℝ) * Complex.I).im
                  (F.c + (T : ℝ) * Complex.I).im) \ ({(0 : ℂ)} : Set ℂ) →
          DifferentiableAt ℂ
            (zetaCompletedExplicitFormulaCorrectionZeroPoleKernelFn f)
            x := by
    intro x hx
    exact
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel_differentiableAt_of_not_mem_singleton
        f h.phi_control hx.2
  have hdef :
      zetaExplicitFormulaZeroPoleTopPunctureCellBoundaryIntegral
        (zetaCompletedExplicitFormulaCorrectionZeroPoleKernelFn f)
        F T R =
      zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral
        (zetaCompletedExplicitFormulaCorrectionZeroPoleKernelFn f)
        ((1 - F.c : ℝ) + (R : ℝ) * Complex.I)
        (F.c + (T : ℝ) * Complex.I) :=
    have hleft_re :
        (1 : ℂ) - (F.c : ℂ) = ((1 - F.c : ℝ) : ℂ) :=
      (Complex.ofReal_sub 1 F.c).symm
    congrArg₂
      (fun z w : ℂ =>
        zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral
          (zetaCompletedExplicitFormulaCorrectionZeroPoleKernelFn f)
          z w)
      (congrArg₂ HAdd.hAdd hleft_re (Eq.refl ((R : ℂ) * Complex.I)))
      (Eq.refl ((F.c : ℂ) + (T : ℂ) * Complex.I))
  exact
    Eq.subst
      (motive := fun z : ℂ => z = 0)
      hdef.symm
      (zetaCompletedExplicitFormulaCorrectionZeroPole_cellBoundary_eq_zero_of_regularity
        f ((1 - F.c : ℝ) + (R : ℝ) * Complex.I)
          (F.c + (T : ℝ) * Complex.I)
        HcTop HdTop)

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary
