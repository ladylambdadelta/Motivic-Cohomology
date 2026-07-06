import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleFourCellCauchyBase

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology Interval

namespace ZetaAdmissibleFunction

/-- Left-cell Cauchy cancellation for the canonical zero-pole puncture. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_canonicalLeftCellBoundary_eq_zero_of_pos_height
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (T : ℝ)
    (hT : 0 < T) :
    zetaExplicitFormulaZeroPoleLeftPunctureCellBoundaryIntegral
      (zetaCompletedExplicitFormulaCorrectionZeroPoleKernelFn f)
      F T (zetaExplicitFormulaZeroPolePunctureRadius F T) = 0 := by
  let R : ℝ := zetaExplicitFormulaZeroPolePunctureRadius F T
  have HcLeft :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleKernel_continuousOn_of_avoids_pole
      f h.phi_control
      ([[ ((1 - F.c : ℝ) + (-(R : ℂ)) * Complex.I).re,
           (-(R : ℂ) + (R : ℝ) * Complex.I).re ]] ×ℂ
        [[ ((1 - F.c : ℝ) + (-(R : ℂ)) * Complex.I).im,
           (-(R : ℂ) + (R : ℝ) * Complex.I).im ]])
      (by
        exact
          show
            ∀ z : ℂ,
              z ∈
                ([[ ((1 - F.c : ℝ) +
                           (-(zetaExplicitFormulaZeroPolePunctureRadius F T : ℂ)) *
                             Complex.I).re,
                         (-(zetaExplicitFormulaZeroPolePunctureRadius F T : ℂ) +
                            (zetaExplicitFormulaZeroPolePunctureRadius F T : ℝ) *
                              Complex.I).re ]] ×ℂ
                  [[ ((1 - F.c : ℝ) +
                           (-(zetaExplicitFormulaZeroPolePunctureRadius F T : ℂ)) *
                             Complex.I).im,
                         (-(zetaExplicitFormulaZeroPolePunctureRadius F T : ℂ) +
                            (zetaExplicitFormulaZeroPolePunctureRadius F T : ℝ) *
                              Complex.I).im ]]) →
                z ≠ 0 from
            zetaExplicitFormulaZeroPole_canonicalLeftCell_avoids_zero_of_pos_height
              F hT)
  have HdLeft :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                  (min ((1 - F.c : ℝ) + (-(R : ℂ)) * Complex.I).re
                    (-(R : ℂ) + (R : ℝ) * Complex.I).re)
                  (max ((1 - F.c : ℝ) + (-(R : ℂ)) * Complex.I).re
                    (-(R : ℂ) + (R : ℝ) * Complex.I).re) ×ℂ
                Set.Ioo
                  (min ((1 - F.c : ℝ) + (-(R : ℂ)) * Complex.I).im
                    (-(R : ℂ) + (R : ℝ) * Complex.I).im)
                  (max ((1 - F.c : ℝ) + (-(R : ℂ)) * Complex.I).im
                    (-(R : ℂ) + (R : ℝ) * Complex.I).im) \ ({(0 : ℂ)} : Set ℂ) →
          DifferentiableAt ℂ
            (zetaCompletedExplicitFormulaCorrectionZeroPoleKernelFn f)
            x := by
    intro x hx
    exact
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel_differentiableAt_of_not_mem_singleton
        f h.phi_control hx.2
  have hdef :
      zetaExplicitFormulaZeroPoleLeftPunctureCellBoundaryIntegral
        (zetaCompletedExplicitFormulaCorrectionZeroPoleKernelFn f)
        F T R =
        zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral
          (zetaCompletedExplicitFormulaCorrectionZeroPoleKernelFn f)
          ((1 - F.c : ℝ) + (-(R : ℂ)) * Complex.I)
          (-(R : ℂ) + (R : ℝ) * Complex.I) :=
    have hleft_re :
        (1 : ℂ) - (F.c : ℂ) = ((1 - F.c : ℝ) : ℂ) :=
      (Complex.ofReal_sub 1 F.c).symm
    have hnegR :
        (-(R : ℂ)) = ((-R : ℝ) : ℂ) :=
      (Complex.ofReal_neg R).symm
    have hnegRI :
        (-(R : ℂ)) * Complex.I = ((-R : ℝ) : ℂ) * Complex.I :=
      congrArg (fun z : ℂ => z * Complex.I) hnegR
    congrArg₂
      (fun z w : ℂ =>
        zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral
          (zetaCompletedExplicitFormulaCorrectionZeroPoleKernelFn f)
          z w)
      (congrArg₂ HAdd.hAdd hleft_re hnegRI)
      (congrArg₂ HAdd.hAdd hnegR (Eq.refl ((R : ℂ) * Complex.I)))
  exact
    Eq.subst
      (motive := fun z : ℂ => z = 0)
      hdef.symm
      (zetaCompletedExplicitFormulaCorrectionZeroPole_cellBoundary_eq_zero_of_regularity
          f ((1 - F.c : ℝ) + (-(R : ℂ)) * Complex.I)
            (-(R : ℂ) + (R : ℝ) * Complex.I)
        HcLeft HdLeft)

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary
