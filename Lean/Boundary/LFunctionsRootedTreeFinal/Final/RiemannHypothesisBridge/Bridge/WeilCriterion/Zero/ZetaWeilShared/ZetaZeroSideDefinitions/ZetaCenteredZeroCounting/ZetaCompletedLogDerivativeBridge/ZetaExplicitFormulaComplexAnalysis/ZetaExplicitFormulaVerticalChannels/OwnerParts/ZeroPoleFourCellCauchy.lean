import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.CorrectionPoleResidues

/-!
# Four-cell Cauchy specialization for the isolated `s = 0` correction pole

This file specializes the generic rectangular Cauchy-Goursat engine to the
zero-centered four-cell contour from `ZeroPoleFourCellContour`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology Interval

namespace ZetaAdmissibleFunction

/-- The one-point exceptional set for the isolated `s = 0` correction kernel is
countable. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_singleton_countable :
    ({(0 : ℂ)} : Set ℂ).Countable :=
  Set.countable_singleton (0 : ℂ)

/-- Membership outside the deleted singleton `{0}` is the off-pole condition
needed by the zero-pole correction-kernel differentiability theorem. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleKernel_differentiableAt_of_not_mem_singleton
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {z : ℂ} (hz : z ∉ ({(0 : ℂ)} : Set ℂ)) :
    DifferentiableAt ℂ
      (fun w : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f w)
      z := by
  have hz_ne_zero : z ≠ 0 := by
    intro hzero
    have hz_mem : z ∈ ({(0 : ℂ)} : Set ℂ) :=
      hzero
    exact hz hz_mem
  exact
    zetaCompletedExplicitFormulaCorrectionZeroPole_differentiableAt_off_pole
      f hPhi hz_ne_zero

/-- The zero-pole correction kernel is continuous on any set that avoids the
pole `0`. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleKernel_continuousOn_of_avoids_pole
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (s : Set ℂ)
    (havoid : ∀ z : ℂ, z ∈ s → z ≠ 0) :
    ContinuousOn
      (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
      s := by
  intro z hz
  exact
    (zetaCompletedExplicitFormulaCorrectionZeroPole_continuousAt_off_pole
      f hPhi (havoid z hz)).continuousWithinAt

/-- Cauchy-Goursat cancellation for one zero-pole cell from continuity on the
closed cell and differentiability on the open cell away from `{0}`. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_cellBoundary_eq_zero_of_regularity
    (f : ZetaAdmissibleFunction) (z w : ℂ)
    (hcontinuous :
      ContinuousOn
        (fun x : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f x)
        ([[ z.re, w.re ]] ×ℂ [[ z.im, w.im ]]))
    (hdifferentiable :
      ∀ x : ℂ,
        x ∈
            Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ
              Set.Ioo (min z.im w.im) (max z.im w.im) \
                ({(0 : ℂ)} : Set ℂ) →
          DifferentiableAt ℂ
            (fun y : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f y)
            x) :
    zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral
      (fun x : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f x)
      z w = 0 :=
  zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral_eq_zero_of_differentiable_on_off_countable
    (fun x : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f x)
    z w ({(0 : ℂ)} : Set ℂ)
    zetaCompletedExplicitFormulaCorrectionZeroPole_singleton_countable
    hcontinuous
    hdifferentiable

/-- Canonical four-cell Cauchy cancellation for the isolated `s = 0`
correction kernel at positive height. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_canonicalFourCellBoundary_eq_zero_of_pos_height
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (T : ℝ)
    (hT : 0 < T) :
    zetaExplicitFormulaZeroPoleFourCellPuncturedRectangleBoundarySum
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        F T (zetaExplicitFormulaZeroPolePunctureRadius F T) = 0 := by
  let R : ℝ := zetaExplicitFormulaZeroPolePunctureRadius F T
  have HcBottom :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        ([[ ((1 - F.c) + (-T) * Complex.I).re,
             (F.c + (-R) * Complex.I).re ]] ×ℂ
          [[ ((1 - F.c) + (-T) * Complex.I).im,
             (F.c + (-R) * Complex.I).im ]]) :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleKernel_continuousOn_of_avoids_pole
      f h.phi_control
      ([[ ((1 - F.c) + (-T) * Complex.I).re,
           (F.c + (-R) * Complex.I).re ]] ×ℂ
        [[ ((1 - F.c) + (-T) * Complex.I).im,
           (F.c + (-R) * Complex.I).im ]])
      (zetaExplicitFormulaZeroPole_canonicalBottomCell_avoids_zero_of_pos_height
        F hT)
  have HdBottom :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min ((1 - F.c) + (-T) * Complex.I).re
                  (F.c + (-R) * Complex.I).re)
                (max ((1 - F.c) + (-T) * Complex.I).re
                  (F.c + (-R) * Complex.I).re) ×ℂ
              Set.Ioo
                (min ((1 - F.c) + (-T) * Complex.I).im
                  (F.c + (-R) * Complex.I).im)
                (max ((1 - F.c) + (-T) * Complex.I).im
                  (F.c + (-R) * Complex.I).im) \ ({(0 : ℂ)} : Set ℂ) →
          DifferentiableAt ℂ
            (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
            x := by
    intro x hx
    exact
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel_differentiableAt_of_not_mem_singleton
        f h.phi_control hx.2
  have HcTop :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        ([[ ((1 - F.c) + R * Complex.I).re,
             (F.c + T * Complex.I).re ]] ×ℂ
          [[ ((1 - F.c) + R * Complex.I).im,
             (F.c + T * Complex.I).im ]]) :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleKernel_continuousOn_of_avoids_pole
      f h.phi_control
      ([[ ((1 - F.c) + R * Complex.I).re,
           (F.c + T * Complex.I).re ]] ×ℂ
        [[ ((1 - F.c) + R * Complex.I).im,
           (F.c + T * Complex.I).im ]])
      (zetaExplicitFormulaZeroPole_canonicalTopCell_avoids_zero_of_pos_height
        F hT)
  have HdTop :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min ((1 - F.c) + R * Complex.I).re
                  (F.c + T * Complex.I).re)
                (max ((1 - F.c) + R * Complex.I).re
                  (F.c + T * Complex.I).re) ×ℂ
              Set.Ioo
                (min ((1 - F.c) + R * Complex.I).im
                  (F.c + T * Complex.I).im)
                (max ((1 - F.c) + R * Complex.I).im
                  (F.c + T * Complex.I).im) \ ({(0 : ℂ)} : Set ℂ) →
          DifferentiableAt ℂ
            (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
            x := by
    intro x hx
    exact
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel_differentiableAt_of_not_mem_singleton
        f h.phi_control hx.2
  have HcLeft :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        ([[ ((1 - F.c) + (-R) * Complex.I).re,
             ((-R) + R * Complex.I).re ]] ×ℂ
          [[ ((1 - F.c) + (-R) * Complex.I).im,
             ((-R) + R * Complex.I).im ]]) :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleKernel_continuousOn_of_avoids_pole
      f h.phi_control
      ([[ ((1 - F.c) + (-R) * Complex.I).re,
           ((-R) + R * Complex.I).re ]] ×ℂ
        [[ ((1 - F.c) + (-R) * Complex.I).im,
           ((-R) + R * Complex.I).im ]])
      (zetaExplicitFormulaZeroPole_canonicalLeftCell_avoids_zero_of_pos_height
        F hT)
  have HdLeft :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min ((1 - F.c) + (-R) * Complex.I).re
                  ((-R) + R * Complex.I).re)
                (max ((1 - F.c) + (-R) * Complex.I).re
                  ((-R) + R * Complex.I).re) ×ℂ
              Set.Ioo
                (min ((1 - F.c) + (-R) * Complex.I).im
                  ((-R) + R * Complex.I).im)
                (max ((1 - F.c) + (-R) * Complex.I).im
                  ((-R) + R * Complex.I).im) \ ({(0 : ℂ)} : Set ℂ) →
          DifferentiableAt ℂ
            (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
            x := by
    intro x hx
    exact
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel_differentiableAt_of_not_mem_singleton
        f h.phi_control hx.2
  have HcRight :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        ([[ (R + (-R) * Complex.I).re,
             (F.c + R * Complex.I).re ]] ×ℂ
          [[ (R + (-R) * Complex.I).im,
             (F.c + R * Complex.I).im ]]) :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleKernel_continuousOn_of_avoids_pole
      f h.phi_control
      ([[ (R + (-R) * Complex.I).re,
           (F.c + R * Complex.I).re ]] ×ℂ
        [[ (R + (-R) * Complex.I).im,
           (F.c + R * Complex.I).im ]])
      (zetaExplicitFormulaZeroPole_canonicalRightCell_avoids_zero_of_pos_height
        F hT)
  have HdRight :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min (R + (-R) * Complex.I).re
                  (F.c + R * Complex.I).re)
                (max (R + (-R) * Complex.I).re
                  (F.c + R * Complex.I).re) ×ℂ
              Set.Ioo
                (min (R + (-R) * Complex.I).im
                  (F.c + R * Complex.I).im)
                (max (R + (-R) * Complex.I).im
                  (F.c + R * Complex.I).im) \ ({(0 : ℂ)} : Set ℂ) →
          DifferentiableAt ℂ
            (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
            x := by
    intro x hx
    exact
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel_differentiableAt_of_not_mem_singleton
        f h.phi_control hx.2
  have hbottom :
      zetaExplicitFormulaZeroPoleBottomPunctureCellBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        F T R = 0 :=
    zetaCompletedExplicitFormulaCorrectionZeroPole_cellBoundary_eq_zero_of_regularity
      f ((1 - F.c) + (-T) * Complex.I) (F.c + (-R) * Complex.I)
      HcBottom HdBottom
  have htop :
      zetaExplicitFormulaZeroPoleTopPunctureCellBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        F T R = 0 :=
    zetaCompletedExplicitFormulaCorrectionZeroPole_cellBoundary_eq_zero_of_regularity
      f ((1 - F.c) + R * Complex.I) (F.c + T * Complex.I)
      HcTop HdTop
  have hleft :
      zetaExplicitFormulaZeroPoleLeftPunctureCellBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        F T R = 0 :=
    zetaCompletedExplicitFormulaCorrectionZeroPole_cellBoundary_eq_zero_of_regularity
      f ((1 - F.c) + (-R) * Complex.I) ((-R) + R * Complex.I)
      HcLeft HdLeft
  have hright :
      zetaExplicitFormulaZeroPoleRightPunctureCellBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        F T R = 0 :=
    zetaCompletedExplicitFormulaCorrectionZeroPole_cellBoundary_eq_zero_of_regularity
      f (R + (-R) * Complex.I) (F.c + R * Complex.I)
      HcRight HdRight
  exact
    zetaExplicitFormulaZeroPoleFourCellPuncturedRectangleBoundarySum_eq_zero_of_cells
      (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
      F T R hbottom htop hleft hright

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary
