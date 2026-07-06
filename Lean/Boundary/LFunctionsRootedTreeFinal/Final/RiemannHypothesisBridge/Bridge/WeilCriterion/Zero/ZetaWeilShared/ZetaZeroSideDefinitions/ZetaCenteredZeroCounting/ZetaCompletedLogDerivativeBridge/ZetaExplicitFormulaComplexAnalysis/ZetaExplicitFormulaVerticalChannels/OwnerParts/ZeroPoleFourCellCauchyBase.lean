import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.CorrectionPoleResidues

/-!
# Base Cauchy facts for the isolated `s = 0` correction pole

This file owns the shared kernel regularity facts used by the four zero-pole
punctured-rectangle cells.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology Interval

namespace ZetaAdmissibleFunction

/-- Named function form of the isolated zero-pole correction kernel. -/
abbrev zetaCompletedExplicitFormulaCorrectionZeroPoleKernelFn
    (f : ZetaAdmissibleFunction) : ℂ → ℂ :=
  fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z

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
      (zetaCompletedExplicitFormulaCorrectionZeroPoleKernelFn f)
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
      (zetaCompletedExplicitFormulaCorrectionZeroPoleKernelFn f)
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
        (zetaCompletedExplicitFormulaCorrectionZeroPoleKernelFn f)
        ([[ z.re, w.re ]] ×ℂ [[ z.im, w.im ]]))
    (hdifferentiable :
      ∀ x : ℂ,
        x ∈
            Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ
              Set.Ioo (min z.im w.im) (max z.im w.im) \
                ({(0 : ℂ)} : Set ℂ) →
          DifferentiableAt ℂ
            (zetaCompletedExplicitFormulaCorrectionZeroPoleKernelFn f)
            x) :
    zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral
      (zetaCompletedExplicitFormulaCorrectionZeroPoleKernelFn f)
      z w = 0 :=
  zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral_eq_zero_of_differentiable_on_off_countable
    (zetaCompletedExplicitFormulaCorrectionZeroPoleKernelFn f)
    z w ({(0 : ℂ)} : Set ℂ)
    zetaCompletedExplicitFormulaCorrectionZeroPole_singleton_countable
    hcontinuous
    hdifferentiable

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary
