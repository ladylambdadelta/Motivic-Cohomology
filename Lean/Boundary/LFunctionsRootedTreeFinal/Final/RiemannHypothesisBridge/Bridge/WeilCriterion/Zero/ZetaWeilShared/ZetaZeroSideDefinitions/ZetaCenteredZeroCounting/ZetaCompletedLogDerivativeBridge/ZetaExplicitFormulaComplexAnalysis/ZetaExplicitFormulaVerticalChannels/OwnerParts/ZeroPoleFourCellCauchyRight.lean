import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleFourCellCauchyBase

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology Interval

namespace ZetaAdmissibleFunction

/-- Right-cell Cauchy cancellation for the canonical zero-pole puncture. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_canonicalRightCellBoundary_eq_zero_of_pos_height
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (T : ℝ)
    (hT : 0 < T) :
    zetaExplicitFormulaZeroPoleRightPunctureCellBoundaryIntegral
      (zetaCompletedExplicitFormulaCorrectionZeroPoleKernelFn f)
      F T (zetaExplicitFormulaZeroPolePunctureRadius F T) = 0 := by
  let R : ℝ := zetaExplicitFormulaZeroPolePunctureRadius F T
  have HcRight :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleKernel_continuousOn_of_avoids_pole
      f h.phi_control
      ([[ ((R : ℝ) + (-R : ℝ) * Complex.I).re,
           (F.c + (R : ℝ) * Complex.I).re ]] ×ℂ
        [[ ((R : ℝ) + (-R : ℝ) * Complex.I).im,
           (F.c + (R : ℝ) * Complex.I).im ]])
      (zetaExplicitFormulaZeroPole_canonicalRightCell_avoids_zero_of_pos_height
        F hT)
  have HdRight :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min ((R : ℝ) + (-R : ℝ) * Complex.I).re
                  (F.c + (R : ℝ) * Complex.I).re)
                (max ((R : ℝ) + (-R : ℝ) * Complex.I).re
                  (F.c + (R : ℝ) * Complex.I).re) ×ℂ
              Set.Ioo
                (min ((R : ℝ) + (-R : ℝ) * Complex.I).im
                  (F.c + (R : ℝ) * Complex.I).im)
                (max ((R : ℝ) + (-R : ℝ) * Complex.I).im
                  (F.c + (R : ℝ) * Complex.I).im) \ ({(0 : ℂ)} : Set ℂ) →
          DifferentiableAt ℂ
            (zetaCompletedExplicitFormulaCorrectionZeroPoleKernelFn f)
            x := by
    intro x hx
    exact
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel_differentiableAt_of_not_mem_singleton
        f h.phi_control hx.2
  have hdef :
      zetaExplicitFormulaZeroPoleRightPunctureCellBoundaryIntegral
        (zetaCompletedExplicitFormulaCorrectionZeroPoleKernelFn f)
        F T R =
      zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral
        (zetaCompletedExplicitFormulaCorrectionZeroPoleKernelFn f)
        ((R : ℝ) + (-R : ℝ) * Complex.I)
        (F.c + (R : ℝ) * Complex.I) :=
    have hnegRI :
        (-(R : ℂ)) * Complex.I = ((-R : ℝ) : ℂ) * Complex.I :=
      congrArg (fun z : ℂ => z * Complex.I) (Complex.ofReal_neg R).symm
    congrArg₂
      (fun z w : ℂ =>
        zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral
          (zetaCompletedExplicitFormulaCorrectionZeroPoleKernelFn f)
          z w)
      (congrArg₂ HAdd.hAdd (Eq.refl (R : ℂ)) hnegRI)
      (Eq.refl ((F.c : ℂ) + (R : ℂ) * Complex.I))
  exact
    Eq.subst
      (motive := fun z : ℂ => z = 0)
      hdef.symm
      (zetaCompletedExplicitFormulaCorrectionZeroPole_cellBoundary_eq_zero_of_regularity
        f ((R : ℝ) + (-R : ℝ) * Complex.I)
          (F.c + (R : ℝ) * Complex.I)
        HcRight HdRight)

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary
