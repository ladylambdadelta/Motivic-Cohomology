import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleFourCellCauchyBase

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology Interval

namespace ZetaAdmissibleFunction

/-- A left zero-pole cell with positive puncture radius avoids the zero pole. -/
theorem zetaExplicitFormulaZeroPole_leftCell_avoids_zero_of_radius_pos
    (F : ExplicitFormulaContourFamily) {R : ℝ} (hR : 0 < R) :
    ∀ z : ℂ,
      z ∈
          ([[ ((1 - F.c : ℝ) + (-R : ℝ) * Complex.I).re,
               ((-R : ℝ) + (R : ℝ) * Complex.I).re ]] ×ℂ
            [[ ((1 - F.c : ℝ) + (-R : ℝ) * Complex.I).im,
               ((-R : ℝ) + (R : ℝ) * Complex.I).im ]]) →
        z ≠ 0 := by
  intro z hz
  have hleft_lower :
      ((1 - F.c : ℝ) + (-R : ℝ) * Complex.I).re < 0 := by
    calc
      ((1 - F.c : ℝ) + (-R : ℝ) * Complex.I).re = 1 - F.c :=
        zetaExplicitFormulaOnePole_verticalAffine_re (1 - F.c) (-R)
      _ < 0 := F.one_sub_c_neg
  have hleft_upper :
      ((-R : ℝ) + (R : ℝ) * Complex.I).re < 0 := by
    calc
      ((-R : ℝ) + (R : ℝ) * Complex.I).re = -R :=
        zetaExplicitFormulaOnePole_verticalAffine_re (-R) R
      _ < 0 := neg_lt_zero.mpr hR
  have hre_mem :
      z.re ∈
        [[ ((1 - F.c : ℝ) + (-R : ℝ) * Complex.I).re,
           ((-R : ℝ) + (R : ℝ) * Complex.I).re ]] :=
    (Complex.mem_reProdIm.mp hz).1
  have hre_sup_lt :
      (((1 - F.c : ℝ) + (-R : ℝ) * Complex.I).re ⊔
        ((-R : ℝ) + (R : ℝ) * Complex.I).re) < 0 :=
    sup_lt_iff.mpr (And.intro hleft_lower hleft_upper)
  have hre_lt_zero : z.re < 0 :=
    lt_of_le_of_lt hre_mem.2 hre_sup_lt
  exact zetaExplicitFormulaZeroPole_ne_zero_of_re_lt_zero hre_lt_zero

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
  have hR_pos : 0 < R :=
    zetaExplicitFormulaZeroPolePunctureRadius_pos F hT
  have HcLeft :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleKernel_continuousOn_of_avoids_pole
      f h.phi_control
      ([[ ((1 - F.c : ℝ) + (-R : ℝ) * Complex.I).re,
           ((-R : ℝ) + (R : ℝ) * Complex.I).re ]] ×ℂ
        [[ ((1 - F.c : ℝ) + (-R : ℝ) * Complex.I).im,
           ((-R : ℝ) + (R : ℝ) * Complex.I).im ]])
      (zetaExplicitFormulaZeroPole_leftCell_avoids_zero_of_radius_pos F hR_pos)
  have HdLeft :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                  (min ((1 - F.c : ℝ) + (-R : ℝ) * Complex.I).re
                    ((-R : ℝ) + (R : ℝ) * Complex.I).re)
                  (max ((1 - F.c : ℝ) + (-R : ℝ) * Complex.I).re
                    ((-R : ℝ) + (R : ℝ) * Complex.I).re) ×ℂ
                Set.Ioo
                  (min ((1 - F.c : ℝ) + (-R : ℝ) * Complex.I).im
                    ((-R : ℝ) + (R : ℝ) * Complex.I).im)
                  (max ((1 - F.c : ℝ) + (-R : ℝ) * Complex.I).im
                    ((-R : ℝ) + (R : ℝ) * Complex.I).im) \ ({(0 : ℂ)} : Set ℂ) →
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
          ((1 - F.c : ℝ) + (-R : ℝ) * Complex.I)
          ((-R : ℝ) + (R : ℝ) * Complex.I) :=
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
          f ((1 - F.c : ℝ) + (-R : ℝ) * Complex.I)
            ((-R : ℝ) + (R : ℝ) * Complex.I)
        HcLeft HdLeft)

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary
