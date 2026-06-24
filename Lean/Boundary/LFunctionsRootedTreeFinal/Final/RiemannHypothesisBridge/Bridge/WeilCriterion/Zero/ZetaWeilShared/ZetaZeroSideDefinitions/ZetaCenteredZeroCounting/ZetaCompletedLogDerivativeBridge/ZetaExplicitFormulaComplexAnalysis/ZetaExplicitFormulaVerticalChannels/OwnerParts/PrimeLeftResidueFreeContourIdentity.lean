import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeAffineKernelEstimates
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.HorizontalEdgeBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.InverseGammaAffineKernelEstimate
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.InverseGammaScheduledNormalization
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeLeftResidueFreeFiniteRectangle
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeLeftDeletedCircleNormalization
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ScheduledKernelLimitTransport

/-!
# Left prime residue-free contour identity

This file owns the whole-line contour-value theorem for the left prime
logarithmic-derivative line.  Scheduled-window exhaustion consumes this
whole-line value; it is not part of the analytic contour proof.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open LSeries ArithmeticFunction
open MeasureTheory
open scoped ArithmeticFunction
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The zero-excised left prime logarithmic-derivative affine kernel is
integrable under exactly the hypotheses of the residue-free contour identity.

This is not the contour value theorem; it isolates the measure-theoretic
exhaustion input so the remaining owner proof below is only the finite contour
identity plus horizontal/excision decay. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_integrable_ownerResidueFreeContourIdentity
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (E : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ E.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖)) :
    Integrable
      (zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F)
      (volume : Measure ℝ) :=
  zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_integrable_of_zeroExcisedLine_inverseGamma_bound
    f F h hregular E hline_mem BG hBG_nonneg hinverseGamma_bound

/-- The inverse-Gamma left affine kernel is integrable under the same explicit
factor bound used by the residue-free prime contour theorem. -/
theorem zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_integrable_ownerResidueFreeContourIdentity
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖)) :
    Integrable
      (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_majorantPackage_of_factor_bound
    f F h hregular BG hBG_nonneg hinverseGamma_bound).integrable

/-- Finite-window integrability inputs needed by the prime-left finite
rectangle theorem, derived from the whole-line residue-free majorants. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteWindow_integrable_inputs_ownerResidueFreeContourIdentity
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (E : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ E.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖))
    (T : ℝ) :
    IntegrableOn
        (zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F)
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) ∧
      IntegrableOn
        (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F)
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) :=
  ⟨(zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_integrable_ownerResidueFreeContourIdentity
      f F h hregular E hline_mem BG hBG_nonneg hinverseGamma_bound).integrableOn,
    (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_integrable_ownerResidueFreeContourIdentity
      f F h hregular BG hBG_nonneg hinverseGamma_bound).integrableOn⟩

/-- Scheduled-window exhaustion of the zero-excised left prime
logarithmic-derivative affine kernel to its whole-line integral. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_scheduledWindow_tendsto_integral_ownerResidueFreeContourIdentity
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (E : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ E.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖)) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t)
      atTop
      (𝓝 (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t)) :=
  zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernelIntegral_tendsto_integral_of_zeroExcisedLine_inverseGamma_bound
    f F h hregular E hline_mem BG hBG_nonneg hinverseGamma_bound

/-- Whole-line residue-free value from the scheduled-window contour value.

This is the final non-analytic projection step.  The finite residue-free
contour proof must supply `hscheduled_zero`; exhaustion of the same scheduled
windows supplies convergence to the whole-line integral, and uniqueness of
limits identifies that integral with zero. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_integral_eq_zero_of_scheduledWindow_tendsto_zero_ownerResidueFreeContourIdentity
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (E : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ E.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖))
    (hscheduled_zero :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t)
        atTop
        (𝓝 0)) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) =
      0 := by
  exact
    explicitFormulaScheduledScalar_integral_eq_of_tendsto_integral_and_value
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t)
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t)
      0
      (zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_scheduledWindow_tendsto_integral_ownerResidueFreeContourIdentity
        f F h hregular E hline_mem BG hBG_nonneg hinverseGamma_bound)
      hscheduled_zero

/-- Scheduled zero from a residue-free boundary decomposition.

This is the algebraic contour-assembly step for the left prime residue-free
line.  The finite rectangle proof should identify the scheduled left vertical
window with the negative sum of horizontal and excision errors; the analytic
estimates should prove both errors tend to zero. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledWindow_tendsto_zero_of_error_decomposition
    (leftWindow horizontalError excisionError : ℝ → ℂ)
    (hdecomp :
      ∀ᶠ u in atTop,
        leftWindow u = -(horizontalError u + excisionError u))
    (hhorizontal : Tendsto horizontalError atTop (𝓝 0))
    (hexcision : Tendsto excisionError atTop (𝓝 0)) :
    Tendsto leftWindow atTop (𝓝 0) := by
  have herrors :
      Tendsto
        (fun u : ℝ => horizontalError u + excisionError u)
        atTop
        (𝓝 (0 + 0)) :=
    hhorizontal.add hexcision
  have herrors_zero :
      Tendsto
        (fun u : ℝ => horizontalError u + excisionError u)
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ => horizontalError u + excisionError u)
          atTop
          (𝓝 z))
      (zero_add 0)
      herrors
  have hneg_errors :
      Tendsto
        (fun u : ℝ => -(horizontalError u + excisionError u))
        atTop
        (𝓝 (-0)) :=
    herrors_zero.neg
  have hneg_zero :
      Tendsto
        (fun u : ℝ => -(horizontalError u + excisionError u))
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ => -(horizontalError u + excisionError u))
          atTop
          (𝓝 z))
      (neg_zero : -(0 : ℂ) = 0)
      hneg_errors
  exact
    hneg_zero.congr'
      (hdecomp.mono
        (fun u hu => hu.symm))

/-- Scheduled zero from a finite residue-free boundary identity in the
orientation `left + horizontal + excision = 0`.

This is the same assembly as
`zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledWindow_tendsto_zero_of_error_decomposition`,
but stated in the form produced by a finite-rectangle Cauchy-Goursat theorem. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledWindow_tendsto_zero_of_boundary_sum_eq_zero
    (leftWindow horizontalError excisionError : ℝ → ℂ)
    (hboundary :
      ∀ᶠ u in atTop,
        leftWindow u + horizontalError u + excisionError u = 0)
    (hhorizontal : Tendsto horizontalError atTop (𝓝 0))
    (hexcision : Tendsto excisionError atTop (𝓝 0)) :
    Tendsto leftWindow atTop (𝓝 0) := by
  have hdecomp :
      ∀ᶠ u in atTop,
        leftWindow u = -(horizontalError u + excisionError u) :=
    hboundary.mono
      (fun u hu =>
        have hsum :
            leftWindow u + (horizontalError u + excisionError u) = 0 := by
          exact Eq.trans
            (add_assoc (leftWindow u) (horizontalError u) (excisionError u)).symm
            hu
        eq_neg_of_add_eq_zero_left hsum)
  exact
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledWindow_tendsto_zero_of_error_decomposition
      leftWindow horizontalError excisionError hdecomp hhorizontal hexcision

/-- Scheduled limit from a finite boundary identity in the orientation
`main + error + excision = 0`, allowing the main error to have a nonzero
limit. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledWindow_tendsto_neg_error_of_boundary_sum_eq_zero
    (mainWindow errorPacket excisionError : ℝ → ℂ) (E : ℂ)
    (hboundary :
      ∀ᶠ u in atTop,
        mainWindow u + errorPacket u + excisionError u = 0)
    (herror : Tendsto errorPacket atTop (𝓝 E))
    (hexcision : Tendsto excisionError atTop (𝓝 0)) :
    Tendsto mainWindow atTop (𝓝 (-E)) := by
  have hdecomp :
      ∀ᶠ u in atTop,
        mainWindow u = -(errorPacket u + excisionError u) :=
    hboundary.mono
      (fun u hu =>
        have hsum :
            mainWindow u + (errorPacket u + excisionError u) = 0 := by
          exact Eq.trans
            (add_assoc (mainWindow u) (errorPacket u) (excisionError u)).symm
            hu
        eq_neg_of_add_eq_zero_left hsum)
  have herrors :
      Tendsto
        (fun u : ℝ => errorPacket u + excisionError u)
        atTop
        (𝓝 (E + 0)) :=
    herror.add hexcision
  have herrors_E :
      Tendsto
        (fun u : ℝ => errorPacket u + excisionError u)
        atTop
        (𝓝 E) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ => errorPacket u + excisionError u)
          atTop
          (𝓝 z))
      (add_zero E)
      herrors
  have hneg :
      Tendsto
        (fun u : ℝ => -(errorPacket u + excisionError u))
        atTop
        (𝓝 (-E)) :=
    herrors_E.neg
  exact
    hneg.congr'
      (hdecomp.mono
        (fun u hu => hu.symm))

/-- Scheduled limit from a finite boundary identity in the orientation
`main + error + excision = 0`, allowing both error packets to carry nonzero
limits.

This is the owner-level additive algebra needed before residue-window
cancellation: neither the inverse-Gamma packet nor the deleted-circle packet is
forced to vanish separately. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledWindow_tendsto_neg_error_add_excision_of_boundary_sum_eq_zero
    (mainWindow errorPacket excisionError : ℝ → ℂ) (E R : ℂ)
    (hboundary :
      ∀ᶠ u in atTop,
        mainWindow u + errorPacket u + excisionError u = 0)
    (herror : Tendsto errorPacket atTop (𝓝 E))
    (hexcision : Tendsto excisionError atTop (𝓝 R)) :
    Tendsto mainWindow atTop (𝓝 (-(E + R))) := by
  have hdecomp :
      ∀ᶠ u in atTop,
        mainWindow u = -(errorPacket u + excisionError u) :=
    hboundary.mono
      (fun u hu =>
        have hsum :
            mainWindow u + (errorPacket u + excisionError u) = 0 := by
          exact Eq.trans
            (add_assoc (mainWindow u) (errorPacket u) (excisionError u)).symm
            hu
        eq_neg_of_add_eq_zero_left hsum)
  have herrors :
      Tendsto
        (fun u : ℝ => errorPacket u + excisionError u)
        atTop
        (𝓝 (E + R)) :=
    herror.add hexcision
  have hneg :
      Tendsto
        (fun u : ℝ => -(errorPacket u + excisionError u))
        atTop
        (𝓝 (-(E + R))) :=
    herrors.neg
  exact
    hneg.congr'
      (hdecomp.mono
        (fun u hu => hu.symm))

/-- Scheduled limit from a finite boundary identity in the orientation
`main + vanishingError + excision = 0`, allowing the excision packet to carry
the nonzero residue-window limit before cancellation. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledWindow_tendsto_neg_excision_of_boundary_sum_eq_zero
    (mainWindow vanishingError excisionError : ℝ → ℂ) (E : ℂ)
    (hboundary :
      ∀ᶠ u in atTop,
        mainWindow u + vanishingError u + excisionError u = 0)
    (herror : Tendsto vanishingError atTop (𝓝 0))
    (hexcision : Tendsto excisionError atTop (𝓝 E)) :
    Tendsto mainWindow atTop (𝓝 (-E)) := by
  have hdecomp :
      ∀ᶠ u in atTop,
        mainWindow u = -(vanishingError u + excisionError u) :=
    hboundary.mono
      (fun u hu =>
        have hsum :
            mainWindow u + (vanishingError u + excisionError u) = 0 := by
          exact Eq.trans
            (add_assoc (mainWindow u) (vanishingError u) (excisionError u)).symm
            hu
        eq_neg_of_add_eq_zero_left hsum)
  have herrors :
      Tendsto
        (fun u : ℝ => vanishingError u + excisionError u)
        atTop
        (𝓝 (0 + E)) :=
    herror.add hexcision
  have herrors_E :
      Tendsto
        (fun u : ℝ => vanishingError u + excisionError u)
        atTop
        (𝓝 E) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ => vanishingError u + excisionError u)
          atTop
          (𝓝 z))
      (zero_add E)
      herrors
  have hneg :
      Tendsto
        (fun u : ℝ => -(vanishingError u + excisionError u))
        atTop
        (𝓝 (-E)) :=
    herrors_E.neg
  exact
    hneg.congr'
      (hdecomp.mono
        (fun u hu => hu.symm))

/-- Concrete scheduled-window assembly for the left prime residue-free contour.

This theorem is the exact consumer shape for the finite-rectangle
decomposition theorem: once the scheduled left vertical window plus the
scheduled horizontal and excision errors is zero, and both error terms decay,
the left prime residue-free scheduled window tends to zero. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_scheduledWindow_tendsto_zero_of_boundary_sum_errors
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (horizontalError excisionError : ℝ → ℂ)
    (hboundary_sum :
      ∀ᶠ u in atTop,
        (∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) +
            horizontalError u + excisionError u = 0)
    (hhorizontal : Tendsto horizontalError atTop (𝓝 0))
    (hexcision : Tendsto excisionError atTop (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t)
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledWindow_tendsto_zero_of_boundary_sum_eq_zero
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t)
      horizontalError
      excisionError
      hboundary_sum
      hhorizontal
      hexcision

/-- Scheduled horizontal/right error for the residue-free left-prime contour
after converting the completed-left boundary identity to prime-left
orientation.  It includes the inverse-Gamma left finite window because the
completed left line decomposes as prime plus inverse-Gamma before the boundary
identity is multiplied by `I`. -/
noncomputable def zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledHorizontalInverseGammaError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  (∫ t in Set.Icc
      (-(F.rectangle (h.height_schedule.height u)).T)
      (F.rectangle (h.height_schedule.height u)).T,
    zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t) +
    Complex.I *
      zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteHorizontalRightError
        f F (h.height_schedule.height u)

/-- Scheduled residue-window comparison term between the enlarged zero carrier
at height `T + 1` and the inner height window at the rectangle height `T`. -/
noncomputable def zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledOuterBandResidueError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  explicitFormulaCompletedZeroHeightOuterBandResidueError
    f (h.height_schedule.height u) (h.height_schedule.height u + 1)

/-- The scheduled enlarged completed-zero residue window splits into the inner
scheduled residue window plus the named outer-band residue error. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledEnlargedResidueSum_eq_inner_add_outerBand
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    explicitFormulaCompletedZeroHeightWindowResidueSum f
        (h.height_schedule.height u + 1) =
      explicitFormulaCompletedZeroHeightWindowResidueSum f
          (h.height_schedule.height u) +
        zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledOuterBandResidueError
          f F h u :=
  explicitFormulaCompletedZeroHeightWindowResidueSum_eq_inner_add_outerBandResidueError
    f (h.height_schedule.height u) (h.height_schedule.height u + 1)

/-- The inner completed-zero residue window tends to zero once the enlarged
window and the scheduled outer-band residue packet both tend to zero. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_innerCompletedZeroResidueSum_tendsto_zero_from_enlarged_and_outerBand
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (henlarged :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaCompletedZeroHeightWindowResidueSum f
            (h.height_schedule.height u + 1))
        atTop
        (𝓝 0))
    (houter :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledOuterBandResidueError
          f F h)
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaCompletedZeroHeightWindowResidueSum f
          (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  let Inner : ℝ → ℂ := fun u : ℝ =>
    explicitFormulaCompletedZeroHeightWindowResidueSum f
      (h.height_schedule.height u)
  let Enlarged : ℝ → ℂ := fun u : ℝ =>
    explicitFormulaCompletedZeroHeightWindowResidueSum f
      (h.height_schedule.height u + 1)
  let Outer : ℝ → ℂ :=
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledOuterBandResidueError
      f F h
  have hdiff :
      Tendsto (fun u : ℝ => Enlarged u - Outer u) atTop (𝓝 (0 - 0)) :=
    henlarged.sub houter
  have hzero : (0 : ℂ) - 0 = 0 :=
    sub_zero 0
  have hdiff_zero :
      Tendsto (fun u : ℝ => Enlarged u - Outer u) atTop (𝓝 0) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto (fun u : ℝ => Enlarged u - Outer u) atTop (𝓝 z))
      hzero
      hdiff
  have hpoint :
      Inner = fun u : ℝ => Enlarged u - Outer u := by
    funext u
    let I : ℂ := Inner u
    let E : ℂ := Enlarged u
    let O : ℂ := Outer u
    have hsplit : E = I + O := by
      exact
        zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledEnlargedResidueSum_eq_inner_add_outerBand
          f F h u
    have hsub : E - O = I := by
      calc
        E - O = (I + O) - O := by
          exact congrArg (fun z : ℂ => z - O) hsplit
        _ = I := by
          exact add_sub_cancel_right I O
    exact hsub.symm
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
      hpoint.symm
      hdiff_zero

/-- The scheduled outer-band completed-zero residue packet tends to zero along
any cofinal height schedule when the zero-side residue series is summable. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledOuterBandResidueError_tendsto_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaZeroSideContribution (ρ : ℂ) f)) :
    Tendsto
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledOuterBandResidueError
        f F h)
      atTop
      (𝓝 0) := by
  let L : ℂ :=
    ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
      zetaZeroSideContribution (ρ : ℂ) f
  let W : ℝ → ℂ := fun T : ℝ =>
    explicitFormulaCompletedZeroHeightWindowResidueSum f T
  have hwindow : Tendsto W atTop (𝓝 L) :=
    explicitFormulaCompletedZeroHeightWindowResidueSum_tendsto_zeroSideTsum
      f hsum
  have hinner :
      Tendsto
        (fun u : ℝ => W (h.height_schedule.height u))
        atTop
        (𝓝 L) :=
    hwindow.comp h.height_schedule.cofinal
  have hheight_plus_left :
      Tendsto
        (fun u : ℝ => 1 + h.height_schedule.height u)
        atTop
        atTop :=
    tendsto_atTop_add_const_left atTop (1 : ℝ) h.height_schedule.cofinal
  have henlarged_left :
      Tendsto
        (fun u : ℝ => W (1 + h.height_schedule.height u))
        atTop
        (𝓝 L) :=
    hwindow.comp hheight_plus_left
  have henlarged :
      Tendsto
        (fun u : ℝ => W (h.height_schedule.height u + 1))
        atTop
        (𝓝 L) := by
    have hpoint :
        (fun u : ℝ => W (h.height_schedule.height u + 1)) =
          fun u : ℝ => W (1 + h.height_schedule.height u) := by
      funext u
      exact congrArg W (add_comm (h.height_schedule.height u) 1)
    exact
      Eq.subst
        (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 L))
        hpoint.symm
        henlarged_left
  have hdiff :
      Tendsto
        (fun u : ℝ =>
          W (h.height_schedule.height u + 1) -
            W (h.height_schedule.height u))
        atTop
        (𝓝 (L - L)) :=
    henlarged.sub hinner
  have hzero : L - L = 0 :=
    sub_self L
  have hdiff_zero :
      Tendsto
        (fun u : ℝ =>
          W (h.height_schedule.height u + 1) -
            W (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            W (h.height_schedule.height u + 1) -
              W (h.height_schedule.height u))
          atTop
          (𝓝 z))
      hzero
      hdiff
  have hpoint :
      zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledOuterBandResidueError
          f F h =
        fun u : ℝ =>
          W (h.height_schedule.height u + 1) -
            W (h.height_schedule.height u) := by
    funext u
    rfl
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
      hpoint.symm
      hdiff_zero

/-- The scheduled raw singular indexed residue sum tends to the zero-side
complex contribution plus the two completed-zeta pole residues.  This is the
honest pole-corrected limit; it is not a zero-limit unless a separate
explicit-formula cancellation theorem identifies this target with zero. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRawSingularIndexedResidueSum_tendsto_zeroSide_add_poles
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaZeroSideContribution (ρ : ℂ) f)) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaRectangleRawSingularIndexedResidueSum
          f (h.height_schedule.height u))
      atTop
      (𝓝
        (zetaCompletedZeroSideComplex f +
          explicitFormulaRectangle_completedPoleResidueSum f)) := by
  let W : ℝ → ℂ := fun T : ℝ =>
    explicitFormulaCompletedZeroHeightWindowResidueSum f T
  let P : ℂ := explicitFormulaRectangle_completedPoleResidueSum f
  have hwindow :
      Tendsto
        (fun u : ℝ => W (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedZeroSideComplex f)) :=
    (explicitFormulaCompletedZeroHeightWindowResidueSum_tendsto_zeroSideComplex_ownerZeroLimit
      f hsum).comp h.height_schedule.cofinal
  have hpoles :
      Tendsto (fun _u : ℝ => P) atTop (𝓝 P) :=
    tendsto_const_nhds
  have hsum_limit :
      Tendsto
        (fun u : ℝ => W (h.height_schedule.height u) + P)
        atTop
        (𝓝 (zetaCompletedZeroSideComplex f + P)) :=
    hwindow.add hpoles
  have hpoint :
      (fun u : ℝ =>
        explicitFormulaRectangleRawSingularIndexedResidueSum
          f (h.height_schedule.height u)) =
        fun u : ℝ => W (h.height_schedule.height u) + P := by
    funext u
    calc
      explicitFormulaRectangleRawSingularIndexedResidueSum
          f (h.height_schedule.height u) =
          explicitFormulaRectangle_poleCorrectedResidueSum
            f (h.height_schedule.height u) := by
        exact
          explicitFormulaRectangleRawSingularIndexedResidueSum_eq_poleCorrectedResidueSum
            f (h.height_schedule.height u)
      _ = W (h.height_schedule.height u) + P := by
        exact explicitFormulaRectangle_poleCorrectedResidueSum_eq
          f (h.height_schedule.height u)
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ =>
        Tendsto φ atTop
          (𝓝
            (zetaCompletedZeroSideComplex f +
              explicitFormulaRectangle_completedPoleResidueSum f)))
      hpoint.symm
      hsum_limit

/-- Scheduled excision limit with the honest pole-corrected residue target.

The deleted-circle packet is not zero at this stage.  It is the oriented
`2πi` multiple of the raw singular indexed residue limit, whose target is the
zero-side complex contribution plus the completed-zeta pole residues. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError_tendsto_oriented_zeroSide_add_poles
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (ε : ℝ → ℝ)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaZeroSideContribution (ρ : ℂ) f))
    (hzero :
      ∀ᶠ u in atTop,
        explicitFormulaRectangleRawDeletedCircleBoundary f (ε u) 0 =
          (2 * ↑Real.pi * Complex.I : ℂ) •
            explicitFormulaRectangle_zeroPoleResidue f)
    (hone :
      ∀ᶠ u in atTop,
        explicitFormulaRectangleRawDeletedCircleBoundary f (ε u) 1 =
          (2 * ↑Real.pi * Complex.I : ℂ) •
            explicitFormulaRectangle_onePoleResidue f)
    (hcompleted :
      ∀ᶠ u in atTop,
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ∀ hρ : ρ ∈
              explicitFormulaCompletedZeroHeightWindow
                (h.height_schedule.height u),
            explicitFormulaRectangleRawDeletedCircleBoundary f (ε u)
                (completedZeroResidueCoordinate ρ) =
              (2 * ↑Real.pi * Complex.I : ℂ) •
                explicitFormulaZeroResidue f
                  (explicitFormulaZeroDataOfCompletedZero ρ)) :
    Tendsto
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
        f F h ε)
      atTop
      (𝓝
        (Complex.I *
          (-((2 * ↑Real.pi * Complex.I : ℂ) *
            (zetaCompletedZeroSideComplex f +
              explicitFormulaRectangle_completedPoleResidueSum f))))) := by
  let R : ℂ :=
    zetaCompletedZeroSideComplex f +
      explicitFormulaRectangle_completedPoleResidueSum f
  have hresidue :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaRectangleRawSingularIndexedResidueSum
            f (h.height_schedule.height u))
        atTop
        (𝓝 R) :=
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRawSingularIndexedResidueSum_tendsto_zeroSide_add_poles
      f F h hsum
  have heventually :
      ∀ᶠ u in atTop,
        explicitFormulaRectangleRawDeletedCircleBoundarySum
            f (h.height_schedule.height u) (ε u) =
          (2 * ↑Real.pi * Complex.I : ℂ) *
            explicitFormulaRectangleRawSingularIndexedResidueSum
              f (h.height_schedule.height u) :=
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_eventually_rawDeletedCircleBoundarySum_eq_twoPiI_mul_indexedResidue_of_eventually_values
      f F h ε hzero hone hcompleted
  exact
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError_tendsto_twoPiI_orientedIndexedResidue_of_eventually_rawDeletedCircleBoundarySum_eq
      f F h ε R hresidue heventually

/-- Scheduled vertical packet inside the residue-free horizontal/inverse-Gamma
error: inverse-Gamma on the left finite window minus the completed right
vertical line. -/
noncomputable def zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledVerticalPacketError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  (∫ t in Set.Icc
      (-(F.rectangle (h.height_schedule.height u)).T)
      (F.rectangle (h.height_schedule.height u)).T,
    zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t) -
    zetaCompletedExplicitFormulaRightLineIntegral
      f (F.rectangle (h.height_schedule.height u))

/-- Corrected scheduled inverse-Gamma difference packet for the residue-free
left-prime contour.  Unlike `scheduledVerticalPacketError`, this subtracts
only the right inverse-Gamma affine window, not the full completed right
vertical side. -/
noncomputable def zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledInverseGammaDifferencePacket
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  (∫ t in Set.Icc
      (-(F.rectangle (h.height_schedule.height u)).T)
      (F.rectangle (h.height_schedule.height u)).T,
    zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t) -
    ∫ t in Set.Icc
      (-(F.rectangle (h.height_schedule.height u)).T)
      (F.rectangle (h.height_schedule.height u)).T,
    zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t

/-- Scheduled prime difference packet exposed by the honest right-side split
of the completed boundary identity. -/
noncomputable def zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  (∫ t in Set.Icc
      (-(F.rectangle (h.height_schedule.height u)).T)
      (F.rectangle (h.height_schedule.height u)).T,
    zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) -
    ∫ t in Set.Icc
      (-(F.rectangle (h.height_schedule.height u)).T)
      (F.rectangle (h.height_schedule.height u)).T,
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t

/-- Scheduled rotated top-minus-bottom horizontal packet in the residue-free
left-prime contour proof. -/
noncomputable def zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  Complex.I *
    (zetaCompletedExplicitFormulaTopLineIntegral
        f (F.rectangle (h.height_schedule.height u)) -
      zetaCompletedExplicitFormulaBottomLineIntegral
        f (F.rectangle (h.height_schedule.height u)))

/-- The rotated horizontal packet tends to zero when the two horizontal edges
lie in a common zero-excised strip. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError_tendsto_zero_ownerGap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError
          f F h u)
      atTop
      (𝓝 0) := by
  have hhorizontal :
      Tendsto
        (fun u : ℝ => explicitFormulaScheduledHorizontalSideDifference f F h u)
        atTop
        (𝓝 0) :=
    explicitFormulaScheduledHorizontalSideDifference_tendsto_zero_ownerGap
      f F h E hTopMem hBottomMem
  have hrotated :
      Tendsto
        (fun u : ℝ =>
          Complex.I * explicitFormulaScheduledHorizontalSideDifference f F h u)
        atTop
        (𝓝 (Complex.I * 0)) :=
    tendsto_const_nhds.mul hhorizontal
  have hrotated_zero :
      Tendsto
        (fun u : ℝ =>
          Complex.I * explicitFormulaScheduledHorizontalSideDifference f F h u)
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            Complex.I * explicitFormulaScheduledHorizontalSideDifference f F h u)
          atTop
          (𝓝 z))
      (mul_zero Complex.I)
      hrotated
  exact
    hrotated_zero.congr'
      (Filter.Eventually.of_forall
        (fun u : ℝ => Eq.refl
          (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError
            f F h u)))

/-- The scheduled horizontal/inverse-Gamma error splits into a vertical packet
and a rotated horizontal packet. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledHorizontalInverseGammaError_eq_vertical_add_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledHorizontalInverseGammaError
        f F h u =
      zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledVerticalPacketError
          f F h u +
        zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError
          f F h u := by
  let T : ℝ := h.height_schedule.height u
  let L : ℂ :=
    ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
      zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t
  let R : ℂ := zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T)
  let H : ℂ :=
    zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
      zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T)
  have hrotate :
      Complex.I * (R * Complex.I + H) = -R + Complex.I * H :=
    explicitFormula_rotate_rightTangent_add_horizontal R H
  have hregroup :
      L + (-R + Complex.I * H) = (L - R) + Complex.I * H := by
    calc
      L + (-R + Complex.I * H) =
          (L + -R) + Complex.I * H := by
        exact (add_assoc L (-R) (Complex.I * H)).symm
      _ = (L - R) + Complex.I * H := by
        exact congrArg (fun z : ℂ => z + Complex.I * H)
          (sub_eq_add_neg L R).symm
  calc
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledHorizontalInverseGammaError
        f F h u =
        L + Complex.I * (R * Complex.I + H) := by
      exact Eq.refl _
    _ = L + (-R + Complex.I * H) := by
      exact congrArg (fun z : ℂ => L + z) hrotate
    _ = (L - R) + Complex.I * H := hregroup
    _ =
        zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledVerticalPacketError
            f F h u +
          zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError
            f F h u := by
      exact Eq.refl _

/-- Decay of the scheduled horizontal/inverse-Gamma packet follows from decay
of its vertical packet and rotated horizontal packet. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledHorizontalInverseGammaError_tendsto_zero_of_vertical_and_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hvertical :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledVerticalPacketError
          f F h)
        atTop
        (𝓝 0))
    (hhorizontal :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError
          f F h)
        atTop
        (𝓝 0)) :
    Tendsto
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledHorizontalInverseGammaError
        f F h)
      atTop
      (𝓝 0) := by
  have hsum :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledVerticalPacketError
              f F h u +
            zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError
              f F h u)
        atTop
        (𝓝 (0 + 0)) :=
    hvertical.add hhorizontal
  have hsum_zero :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledVerticalPacketError
              f F h u +
            zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError
              f F h u)
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledVerticalPacketError
                f F h u +
              zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError
                f F h u)
          atTop
          (𝓝 z))
      (zero_add 0)
      hsum
  exact
    hsum_zero.congr'
      (Filter.Eventually.of_forall
        (fun u : ℝ =>
          (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledHorizontalInverseGammaError_eq_vertical_add_horizontal
            f F h u).symm))

/-- Decay of the corrected inverse-Gamma-difference plus horizontal packet
from decay of its two components. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledInverseGammaDifference_add_horizontal_tendsto_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hinverseGamma :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledInverseGammaDifferencePacket
          f F h)
        atTop
        (𝓝 0))
    (hhorizontal :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError
          f F h)
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledInverseGammaDifferencePacket
            f F h u +
          zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError
            f F h u)
      atTop
      (𝓝 0) := by
  have hsum :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledInverseGammaDifferencePacket
              f F h u +
            zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError
              f F h u)
        atTop
        (𝓝 (0 + 0)) :=
    hinverseGamma.add hhorizontal
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledInverseGammaDifferencePacket
                f F h u +
              zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError
                f F h u)
          atTop
          (𝓝 z))
      (zero_add 0)
      hsum

/-- Concrete scheduled-window assembly for the finite prime-left residue-free
boundary identity.

This theorem is the direct bridge from the finite rectangle owner theorem to
the existing scheduled decay consumer.  It still keeps the two analytic decay
inputs explicit: decay of the horizontal/inverse-Gamma packet and decay of the
deleted-circle excision packet. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_scheduledWindow_tendsto_zero_of_finitePrimeBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (ε : ℝ → ℝ)
    (hboundary_sum :
      ∀ᶠ u in atTop,
        (∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) +
          zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledHorizontalInverseGammaError
            f F h u +
          zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
            f F h ε u = 0)
    (hhorizontal :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledHorizontalInverseGammaError
          f F h)
        atTop
        (𝓝 0))
    (hexcision :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
          f F h ε)
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t)
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_scheduledWindow_tendsto_zero_of_boundary_sum_errors
      f F h
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledHorizontalInverseGammaError
        f F h)
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
        f F h ε)
      hboundary_sum
      hhorizontal
      hexcision

/-- Concrete scheduled-window assembly before deleted-circle residue
cancellation.  If the finite boundary identity gives
`left + horizontal + excision = 0`, the horizontal packet vanishes, and the
excision packet has limit `E`, then the left finite window has limit `-E`.

This is the honest intermediate form for the deleted-circle contour: the
deleted-circle packet is not forced to vanish before its residue-window
normalization has been paired with the matching prime/residue term. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_scheduledWindow_tendsto_neg_excision_of_finitePrimeBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (ε : ℝ → ℝ) (E : ℂ)
    (hboundary_sum :
      ∀ᶠ u in atTop,
        (∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) +
          zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledHorizontalInverseGammaError
            f F h u +
          zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
            f F h ε u = 0)
    (hhorizontal :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledHorizontalInverseGammaError
          f F h)
        atTop
        (𝓝 0))
    (hexcision :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
          f F h ε)
        atTop
        (𝓝 E)) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t)
      atTop
      (𝓝 (-E)) := by
  exact
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledWindow_tendsto_neg_excision_of_boundary_sum_eq_zero
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t)
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledHorizontalInverseGammaError
        f F h)
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
        f F h ε)
      E
      hboundary_sum
      hhorizontal
      hexcision

/-- Corrected scheduled prime-difference convergence from the two-sided
finite boundary identity.  The analytic inputs are exactly the decay of the
inverse-Gamma difference plus horizontal packet and the excision packet. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket_tendsto_zero_of_boundary_sum_errors
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (ε : ℝ → ℝ)
    (hboundary_sum :
      ∀ᶠ u in atTop,
        zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket
            f F h u +
          (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledInverseGammaDifferencePacket
              f F h u +
            zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError
              f F h u) +
          zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
            f F h ε u = 0)
    (hinverseGamma_horizontal :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledInverseGammaDifferencePacket
              f F h u +
            zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError
              f F h u)
        atTop
        (𝓝 0))
    (hexcision :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
          f F h ε)
        atTop
        (𝓝 0)) :
    Tendsto
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket
        f F h)
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledWindow_tendsto_zero_of_boundary_sum_eq_zero
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket
        f F h)
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledInverseGammaDifferencePacket
            f F h u +
          zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError
            f F h u)
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
        f F h ε)
      hboundary_sum
      hinverseGamma_horizontal
      hexcision

/-- Corrected scheduled prime-difference convergence from the two-sided
finite boundary identity when the inverse-Gamma plus horizontal error has a
possibly nonzero limit. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket_tendsto_neg_error_of_boundary_sum_errors
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (ε : ℝ → ℝ) (E : ℂ)
    (hboundary_sum :
      ∀ᶠ u in atTop,
        zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket
            f F h u +
          (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledInverseGammaDifferencePacket
              f F h u +
            zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError
              f F h u) +
          zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
            f F h ε u = 0)
    (herror :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledInverseGammaDifferencePacket
              f F h u +
            zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError
              f F h u)
        atTop
        (𝓝 E))
    (hexcision :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
          f F h ε)
        atTop
        (𝓝 0)) :
    Tendsto
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket
        f F h)
      atTop
      (𝓝 (-E)) := by
  exact
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledWindow_tendsto_neg_error_of_boundary_sum_eq_zero
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket
        f F h)
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledInverseGammaDifferencePacket
            f F h u +
          zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError
            f F h u)
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
        f F h ε)
      E
      hboundary_sum
      herror
      hexcision

/-- Corrected scheduled prime-difference convergence from the two-sided
finite boundary identity when both the inverse-Gamma plus horizontal packet
and the deleted-circle excision packet have nonzero limits. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket_tendsto_neg_error_add_excision_of_boundary_sum_errors
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (ε : ℝ → ℝ)
    (Epacket Eexcision : ℂ)
    (hboundary_sum :
      ∀ᶠ u in atTop,
        zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket
            f F h u +
          (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledInverseGammaDifferencePacket
              f F h u +
            zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError
              f F h u) +
          zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
            f F h ε u = 0)
    (herror :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledInverseGammaDifferencePacket
              f F h u +
            zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError
              f F h u)
        atTop
        (𝓝 Epacket))
    (hexcision :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
          f F h ε)
        atTop
        (𝓝 Eexcision)) :
    Tendsto
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket
        f F h)
      atTop
      (𝓝 (-(Epacket + Eexcision))) := by
  exact
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledWindow_tendsto_neg_error_add_excision_of_boundary_sum_eq_zero
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket
        f F h)
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledInverseGammaDifferencePacket
            f F h u +
          zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError
            f F h u)
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
        f F h ε)
      Epacket
      Eexcision
      hboundary_sum
      herror
      hexcision

/-- Left scheduled prime window from the prime-difference packet and the right
prime window.

The prime-difference packet is oriented `left - right`; therefore
`left = (left - right) + right`.  This theorem is pure limit algebra and is
the canonical cancellation step after the finite residue-free boundary has
identified the prime-difference packet and the right/reflected prime inversion
has identified the right packet. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_scheduledWindow_tendsto_of_primeDifference_and_right
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (D R : ℂ)
    (hsum : D + R = 0)
    (hdiff :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket
          f F h)
        atTop
        (𝓝 D))
    (hright :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
              f F t)
        atTop
        (𝓝 R)) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t)
      atTop
      (𝓝 0) := by
  let L : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t
  let Q : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t
  let P : ℝ → ℂ :=
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket
      f F h
  have hpacket :
      P = fun u : ℝ => L u - Q u := by
    funext u
    exact Eq.refl _
  have hdiff' :
      Tendsto (fun u : ℝ => L u - Q u) atTop (𝓝 D) :=
    Eq.subst
      (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 D))
      hpacket
      hdiff
  have hsum_limits :
      Tendsto
        (fun u : ℝ => (L u - Q u) + Q u)
        atTop
        (𝓝 (D + R)) :=
    hdiff'.add hright
  have htarget :
      Tendsto
        (fun u : ℝ => (L u - Q u) + Q u)
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ => (L u - Q u) + Q u)
          atTop
          (𝓝 z))
      hsum
      hsum_limits
  have hleft_eq :
      L = fun u : ℝ => (L u - Q u) + Q u := by
    funext u
    exact (sub_add_cancel (L u) (Q u)).symm
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
      hleft_eq.symm
      htarget

/-- Residue-free left scheduled-window vanishing from a prime-difference packet
that cancels the proved right one-sided von Mangoldt packet.

This theorem isolates the last scalar normalization needed by the
residue-free contour branch: the finite boundary proof must identify the
`left - right` packet with the negative of the right one-sided value.  The
right scheduled limit itself is already owned by the von Mangoldt inversion
file. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_scheduledWindow_tendsto_zero_of_primeDifference_cancels_rightOneSided
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hdiff :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket
          f F h)
        atTop
        (𝓝 (-(zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f)))) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t)
      atTop
      (𝓝 0) := by
  let R : ℂ := zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f
  have hright :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
              f F t)
        atTop
        (𝓝 R) :=
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernelIntegral_tendsto_primeNaturalOneSidedContribution_direct_ownerInversion
      f F h
  have hsum :
      -R + R = 0 :=
    neg_add_cancel R
  exact
    zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_scheduledWindow_tendsto_of_primeDifference_and_right
      f F h (-R) R hsum hdiff hright

/-- Residue-free left scheduled-window vanishing from the canonical
archimedean-plus-correction prime-difference normalization.

The finite boundary branch proves the prime-difference packet with target
`archimedean + correction`.  This theorem isolates the final scalar
normalization needed for cancellation with the right one-sided prime packet. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_scheduledWindow_tendsto_zero_of_primeDifference_archimedean_add_correction
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hdiff :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket
          f F h)
        atTop
        (𝓝
          (zetaCompletedExplicitFormulaArchimedeanContribution f +
            zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)))
    (hscalar :
      zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f =
        -(zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f)) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t)
      atTop
      (𝓝 0) := by
  have hdiff_right :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket
          f F h)
        atTop
        (𝓝 (-(zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f))) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket
            f F h)
          atTop
          (𝓝 z))
      hscalar
      hdiff
  exact
    zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_scheduledWindow_tendsto_zero_of_primeDifference_cancels_rightOneSided
      f F h hdiff_right

/-- Scheduled finite-rectangle boundary identity for the left prime
residue-free contour, with finite-window integrability supplied by the
whole-line residue-free majorants. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledBoundarySum_eq_zero_of_finiteGeometry
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (E : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ E.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖))
    (ε : ℝ → ℝ)
    (hT :
      ∀ᶠ u in atTop,
        0 < h.height_schedule.height u)
    (hinterior :
      ∀ᶠ u in atTop,
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ρ ∈ explicitFormulaCompletedZeroHeightWindow
              (h.height_schedule.height u) ↔
            completedZeroResidueCoordinate ρ ∈
                explicitFormulaContourFamilyInterior F
                  (h.height_schedule.height u) ∧
              completedZeroResidueCoordinate ρ ∈
                completedZetaContourIntegrandSingularSet)
    (hboundary :
      ∀ᶠ u in atTop,
        ∀ z : ℂ,
          z ∈ explicitFormulaContourFamilyBoundary F
              (h.height_schedule.height u) →
            ContinuousAt
                (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
              DifferentiableAt ℂ
                (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hεpos :
      ∀ᶠ u in atTop,
        0 < ε u)
    (hclosed :
      ∀ᶠ u in atTop,
        ∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates
              (h.height_schedule.height u) →
            Metric.closedBall a (ε u) ⊆
              explicitFormulaContourFamilyInterior F
                (h.height_schedule.height u))
    (hsep :
      ∀ᶠ u in atTop,
        ∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates
              (h.height_schedule.height u) →
            ∀ b : ℂ,
              b ∈ explicitFormulaRectangleRawSingularCoordinates
                  (h.height_schedule.height u) →
                a ≠ b → ε u + ε u < dist a b) :
    ∀ᶠ u in atTop,
      (∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) +
        zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledHorizontalInverseGammaError
          f F h u +
        zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
          f F h ε u = 0 := by
  exact
    (hT.and (hinterior.and (hboundary.and (hεpos.and (hclosed.and hsep))))).mono
      (fun u hu =>
        match hu with
        | ⟨hTu, ⟨hinterioru, ⟨hboundaryu, ⟨hεposu, ⟨hclosedu, hsepu⟩⟩⟩⟩⟩ =>
            have hintegrable :
                IntegrableOn
                    (zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F)
                    (Set.Icc
                      (-(F.rectangle (h.height_schedule.height u)).T)
                      (F.rectangle (h.height_schedule.height u)).T) ∧
                  IntegrableOn
                    (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F)
                    (Set.Icc
                      (-(F.rectangle (h.height_schedule.height u)).T)
                      (F.rectangle (h.height_schedule.height u)).T) :=
              zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteWindow_integrable_inputs_ownerResidueFreeContourIdentity
                f F h hregular E hline_mem BG hBG_nonneg hinverseGamma_bound
                (h.height_schedule.height u)
            zetaCompletedExplicitFormulaPrimeLeftResidueFree_primeLeft_add_finitePrimeErrors_eq_zero_ownerFiniteRectangle
              f F h hTu hinterioru hboundaryu hintegrable.1 hintegrable.2
              (ε u) hεposu hclosedu hsepu)

/-- Scheduled finite-rectangle boundary identity after both vertical sides
have been decomposed.  This is the corrected two-sided residue-free assembly:
the right prime contribution remains visible in the prime-difference packet,
and the right inverse-Gamma contribution is subtracted only from the
inverse-Gamma packet. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferenceBoundarySum_eq_zero_of_finiteGeometry
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (E : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ E.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖))
    (ε : ℝ → ℝ)
    (hT :
      ∀ᶠ u in atTop,
        0 < h.height_schedule.height u)
    (hinterior :
      ∀ᶠ u in atTop,
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ρ ∈ explicitFormulaCompletedZeroHeightWindow
              (h.height_schedule.height u) ↔
            completedZeroResidueCoordinate ρ ∈
                explicitFormulaContourFamilyInterior F
                  (h.height_schedule.height u) ∧
              completedZeroResidueCoordinate ρ ∈
                completedZetaContourIntegrandSingularSet)
    (hboundary :
      ∀ᶠ u in atTop,
        ∀ z : ℂ,
          z ∈ explicitFormulaContourFamilyBoundary F
              (h.height_schedule.height u) →
            ContinuousAt
                (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
              DifferentiableAt ℂ
                (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hright_integrable :
      ∀ᶠ u in atTop,
        IntegrableOn
          (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F)
          (Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T) ∧
        IntegrableOn
          (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F)
          (Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T))
    (hεpos :
      ∀ᶠ u in atTop,
        0 < ε u)
    (hclosed :
      ∀ᶠ u in atTop,
        ∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates
              (h.height_schedule.height u) →
            Metric.closedBall a (ε u) ⊆
              explicitFormulaContourFamilyInterior F
                (h.height_schedule.height u))
    (hsep :
      ∀ᶠ u in atTop,
        ∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates
              (h.height_schedule.height u) →
            ∀ b : ℂ,
              b ∈ explicitFormulaRectangleRawSingularCoordinates
                  (h.height_schedule.height u) →
                a ≠ b → ε u + ε u < dist a b) :
    ∀ᶠ u in atTop,
      zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket
          f F h u +
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledInverseGammaDifferencePacket
            f F h u +
          zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError
            f F h u) +
        zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
          f F h ε u = 0 := by
  exact
    (hT.and
      (hinterior.and
        (hboundary.and
          (hright_integrable.and (hεpos.and (hclosed.and hsep)))))).mono
      (fun u hu =>
        match hu with
        | ⟨hTu, ⟨hinterioru, ⟨hboundaryu,
            ⟨hright_integrableu, ⟨hεposu, ⟨hclosedu, hsepu⟩⟩⟩⟩⟩⟩ =>
            have hleft_integrable :
                IntegrableOn
                    (zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F)
                    (Set.Icc
                      (-(F.rectangle (h.height_schedule.height u)).T)
                      (F.rectangle (h.height_schedule.height u)).T) ∧
                  IntegrableOn
                    (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F)
                    (Set.Icc
                      (-(F.rectangle (h.height_schedule.height u)).T)
                      (F.rectangle (h.height_schedule.height u)).T) :=
              zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteWindow_integrable_inputs_ownerResidueFreeContourIdentity
                f F h hregular E hline_mem BG hBG_nonneg hinverseGamma_bound
                (h.height_schedule.height u)
            have hleft_decomp :
                zetaCompletedExplicitFormulaLeftLineIntegral
                    f (F.rectangle (h.height_schedule.height u)) =
                  (∫ t in Set.Icc
                      (-(F.rectangle (h.height_schedule.height u)).T)
                      (F.rectangle (h.height_schedule.height u)).T,
                    zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) +
                  (∫ t in Set.Icc
                      (-(F.rectangle (h.height_schedule.height u)).T)
                      (F.rectangle (h.height_schedule.height u)).T,
                    zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t) :=
              zetaCompletedExplicitFormulaPrimeLeftResidueFree_leftIntegral_eq_prime_add_inverseGamma_of_integrableOn
                f F (h.height_schedule.height u)
                hleft_integrable.1 hleft_integrable.2
            have hright_decomp :
                zetaCompletedExplicitFormulaRightLineIntegral
                    f (F.rectangle (h.height_schedule.height u)) =
                  (∫ t in Set.Icc
                      (-(F.rectangle (h.height_schedule.height u)).T)
                      (F.rectangle (h.height_schedule.height u)).T,
                    zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t) +
                  (∫ t in Set.Icc
                      (-(F.rectangle (h.height_schedule.height u)).T)
                      (F.rectangle (h.height_schedule.height u)).T,
                    zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t) :=
              zetaCompletedExplicitFormulaRightLineIntegral_eq_affinePrime_integral_add_inverseGamma_integral
                f F h u hright_integrableu.1 hright_integrableu.2
            zetaCompletedExplicitFormulaPrimeLeftResidueFree_primeDifference_add_inverseGammaDifference_add_finiteErrors_eq_zero_of_vertical_decompositions
              f F h hTu hinterioru hboundaryu hleft_decomp hright_decomp
              (ε u) hεposu hclosedu hsepu)

/-- Canonical finite-geometry puncture radius for a residue-free rectangle.

When the height and zero-window/interior equivalence hypotheses hold, this
selects a positive radius whose closed disks are contained in the rectangle
interior and are strictly pairwise separated. -/
noncomputable def zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteGeometryRadius
    (F : ExplicitFormulaContourFamily) (T : ℝ) : ℝ :=
  if hT : 0 < T then
    if hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈
              explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈
              completedZetaContourIntegrandSingularSet then
      Classical.choose
        (explicitFormulaRectangleRawSingularCoordinates_exists_closedRadiusControls
          F T
          (fun a ha =>
            explicitFormulaRectangleRawSingularCoordinates_localInterior_ball
              F hT hinterior ha))
    else
      1
  else
    1

/-- The canonical finite-geometry radius satisfies the closed-ball and
separation controls whenever the finite rectangle hypotheses hold. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteGeometryRadius_controls
    (F : ExplicitFormulaContourFamily) {T : ℝ}
    (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈
              explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈
              completedZetaContourIntegrandSingularSet) :
    0 <
        zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteGeometryRadius
          F T ∧
      (∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a
              (zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteGeometryRadius
                F T) ⊆
            explicitFormulaContourFamilyInterior F T) ∧
      (∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b →
                zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteGeometryRadius
                    F T +
                  zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteGeometryRadius
                    F T <
                    dist a b) := by
  let P :
      ∃ ε : ℝ,
        0 < ε ∧
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆
                explicitFormulaContourFamilyInterior F T) ∧
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) :=
    explicitFormulaRectangleRawSingularCoordinates_exists_closedRadiusControls
      F T
      (fun a ha =>
        explicitFormulaRectangleRawSingularCoordinates_localInterior_ball
          F hT hinterior ha)
  have hradius_eq :
      zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteGeometryRadius
          F T =
        Classical.choose P := by
    calc
      zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteGeometryRadius F T =
          (if hinterior' :
            ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
              ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
                completedZeroResidueCoordinate ρ ∈
                    explicitFormulaContourFamilyInterior F T ∧
                  completedZeroResidueCoordinate ρ ∈
                    completedZetaContourIntegrandSingularSet then
            Classical.choose
              (explicitFormulaRectangleRawSingularCoordinates_exists_closedRadiusControls
                F T
                (fun a ha =>
                  explicitFormulaRectangleRawSingularCoordinates_localInterior_ball
                    F hT hinterior' ha))
          else
            1) := by
        exact dif_pos hT
      _ = Classical.choose P := by
        exact dif_pos hinterior
  exact
    Eq.subst
      (motive := fun ε : ℝ =>
        0 < ε ∧
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆
                explicitFormulaContourFamilyInterior F T) ∧
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b))
      hradius_eq.symm
      (Classical.choose_spec P)

/-- Scheduled canonical finite-geometry radius for the prime-left residue-free
contour. -/
noncomputable def zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℝ :=
  zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteGeometryRadius
    F (h.height_schedule.height u)

/-- Eventual positivity, closed-ball containment, and strict separation for the
scheduled canonical finite-geometry radius. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius_controls
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hinterior :
      ∀ᶠ u in atTop,
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ρ ∈ explicitFormulaCompletedZeroHeightWindow
              (h.height_schedule.height u) ↔
            completedZeroResidueCoordinate ρ ∈
                explicitFormulaContourFamilyInterior F
                  (h.height_schedule.height u) ∧
              completedZeroResidueCoordinate ρ ∈
                completedZetaContourIntegrandSingularSet) :
    (∀ᶠ u in atTop,
        0 <
          zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
            f F h u) ∧
      (∀ᶠ u in atTop,
        ∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates
              (h.height_schedule.height u) →
            Metric.closedBall a
                (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
                  f F h u) ⊆
              explicitFormulaContourFamilyInterior F
                (h.height_schedule.height u)) ∧
      (∀ᶠ u in atTop,
        ∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates
              (h.height_schedule.height u) →
            ∀ b : ℂ,
              b ∈ explicitFormulaRectangleRawSingularCoordinates
                  (h.height_schedule.height u) →
                a ≠ b →
                  zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
                      f F h u +
                    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
                      f F h u <
                      dist a b) := by
  have hcombined :
      ∀ᶠ u in atTop,
        0 < h.height_schedule.height u ∧
          (∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
            ρ ∈ explicitFormulaCompletedZeroHeightWindow
                (h.height_schedule.height u) ↔
              completedZeroResidueCoordinate ρ ∈
                  explicitFormulaContourFamilyInterior F
                    (h.height_schedule.height u) ∧
                completedZeroResidueCoordinate ρ ∈
                  completedZetaContourIntegrandSingularSet) :=
    h.height_schedule.eventually_height_pos.and hinterior
  have hpos :
      ∀ᶠ u in atTop,
        0 <
          zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
            f F h u :=
    hcombined.mono
      (fun u hu =>
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteGeometryRadius_controls
          F hu.1 hu.2).1)
  have hclosed :
      ∀ᶠ u in atTop,
        ∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates
              (h.height_schedule.height u) →
            Metric.closedBall a
                (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
                  f F h u) ⊆
              explicitFormulaContourFamilyInterior F
                (h.height_schedule.height u) :=
    hcombined.mono
      (fun u hu =>
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteGeometryRadius_controls
          F hu.1 hu.2).2.1)
  have hsep :
      ∀ᶠ u in atTop,
        ∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates
              (h.height_schedule.height u) →
            ∀ b : ℂ,
              b ∈ explicitFormulaRectangleRawSingularCoordinates
                  (h.height_schedule.height u) →
                a ≠ b →
                  zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
                      f F h u +
                    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
                      f F h u <
                      dist a b :=
    hcombined.mono
      (fun u hu =>
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteGeometryRadius_controls
          F hu.1 hu.2).2.2)
  exact ⟨hpos, hclosed, hsep⟩

/-- Scheduled finite-rectangle boundary identity using the canonical
finite-geometry radius selected from the positive-height rectangle geometry. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledBoundarySum_eq_zero_of_canonicalFiniteGeometryRadius
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (E : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ E.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖))
    (hinterior :
      ∀ᶠ u in atTop,
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ρ ∈ explicitFormulaCompletedZeroHeightWindow
              (h.height_schedule.height u) ↔
            completedZeroResidueCoordinate ρ ∈
                explicitFormulaContourFamilyInterior F
                  (h.height_schedule.height u) ∧
              completedZeroResidueCoordinate ρ ∈
                completedZetaContourIntegrandSingularSet)
    (hboundary :
      ∀ᶠ u in atTop,
        ∀ z : ℂ,
          z ∈ explicitFormulaContourFamilyBoundary F
              (h.height_schedule.height u) →
            ContinuousAt
                (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
              DifferentiableAt ℂ
                (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z) :
    ∀ᶠ u in atTop,
      (∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) +
        zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledHorizontalInverseGammaError
          f F h u +
        zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
          f F h
          (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
            f F h) u = 0 := by
  have hcontrols :
      (∀ᶠ u in atTop,
          0 <
            zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
              f F h u) ∧
        (∀ᶠ u in atTop,
          ∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates
                (h.height_schedule.height u) →
              Metric.closedBall a
                  (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
                    f F h u) ⊆
                explicitFormulaContourFamilyInterior F
                  (h.height_schedule.height u)) ∧
        (∀ᶠ u in atTop,
          ∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates
                (h.height_schedule.height u) →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates
                    (h.height_schedule.height u) →
                  a ≠ b →
                    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
                        f F h u +
                      zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
                        f F h u <
                        dist a b) :=
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius_controls
      f F h hinterior
  exact
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledBoundarySum_eq_zero_of_finiteGeometry
      f F h hregular E hline_mem BG hBG_nonneg hinverseGamma_bound
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
        f F h)
      h.height_schedule.eventually_height_pos
      hinterior
      hboundary
      hcontrols.1
      hcontrols.2.1
      hcontrols.2.2

/-- Corrected two-sided scheduled finite-rectangle boundary identity using the
canonical finite-geometry radius. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferenceBoundarySum_eq_zero_of_canonicalFiniteGeometryRadius
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (E : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ E.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖))
    (hinterior :
      ∀ᶠ u in atTop,
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ρ ∈ explicitFormulaCompletedZeroHeightWindow
              (h.height_schedule.height u) ↔
            completedZeroResidueCoordinate ρ ∈
                explicitFormulaContourFamilyInterior F
                  (h.height_schedule.height u) ∧
              completedZeroResidueCoordinate ρ ∈
                completedZetaContourIntegrandSingularSet)
    (hboundary :
      ∀ᶠ u in atTop,
        ∀ z : ℂ,
          z ∈ explicitFormulaContourFamilyBoundary F
              (h.height_schedule.height u) →
            ContinuousAt
                (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
              DifferentiableAt ℂ
                (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hright_integrable :
      ∀ᶠ u in atTop,
        IntegrableOn
          (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F)
          (Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T) ∧
        IntegrableOn
          (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F)
          (Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T)) :
    ∀ᶠ u in atTop,
      zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket
          f F h u +
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledInverseGammaDifferencePacket
            f F h u +
          zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError
            f F h u) +
        zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
          f F h
          (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
            f F h) u = 0 := by
  have hcontrols :
      (∀ᶠ u in atTop,
          0 <
            zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
              f F h u) ∧
        (∀ᶠ u in atTop,
          ∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates
                (h.height_schedule.height u) →
              Metric.closedBall a
                  (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
                    f F h u) ⊆
                explicitFormulaContourFamilyInterior F
                  (h.height_schedule.height u)) ∧
        (∀ᶠ u in atTop,
          ∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates
                (h.height_schedule.height u) →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates
                    (h.height_schedule.height u) →
                  a ≠ b →
                    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
                        f F h u +
                      zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
                        f F h u <
                        dist a b) :=
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius_controls
      f F h hinterior
  exact
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferenceBoundarySum_eq_zero_of_finiteGeometry
      f F h hregular E hline_mem BG hBG_nonneg hinverseGamma_bound
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
        f F h)
      h.height_schedule.eventually_height_pos
      hinterior
      hboundary
      hright_integrable
      hcontrols.1
      hcontrols.2.1
      hcontrols.2.2

/-- Scheduled boundary regularity for the completed contour integrand follows
from the boundary-avoidance certificate stored in the cofinal height schedule. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledBoundaryRegularity
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ∀ᶠ u in atTop,
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F
            (h.height_schedule.height u) →
          ContinuousAt
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z :=
  Filter.Eventually.of_forall
    (fun u =>
      completedZetaContourIntegrand_regularAt_all_boundary_points_of_avoidsBoundary
        f F h (h.height_schedule.height u)
        (h.height_schedule.avoids_boundary u))

/-- Scheduled finite-rectangle boundary identity using the canonical
finite-geometry radius, with boundary regularity discharged from the schedule's
boundary-avoidance certificate. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledBoundarySum_eq_zero_of_canonicalFiniteGeometryRadius_and_zeroWindow
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (E : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ E.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖))
    (hinterior :
      ∀ᶠ u in atTop,
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ρ ∈ explicitFormulaCompletedZeroHeightWindow
              (h.height_schedule.height u) ↔
            completedZeroResidueCoordinate ρ ∈
                explicitFormulaContourFamilyInterior F
                  (h.height_schedule.height u) ∧
              completedZeroResidueCoordinate ρ ∈
                completedZetaContourIntegrandSingularSet) :
    ∀ᶠ u in atTop,
      (∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) +
        zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledHorizontalInverseGammaError
          f F h u +
        zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
          f F h
          (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
            f F h) u = 0 :=
  zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledBoundarySum_eq_zero_of_canonicalFiniteGeometryRadius
    f F h hregular E hline_mem BG hBG_nonneg hinverseGamma_bound
    hinterior
    (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledBoundaryRegularity
      f F h)

/-- Scheduled-window convergence to zero from the canonical finite-boundary
identity and the two remaining analytic packet-decay inputs. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_scheduledWindow_tendsto_zero_of_canonicalFiniteBoundary_and_packetDecay
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (Eline : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ Eline.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖))
    (hinterior :
      ∀ᶠ u in atTop,
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ρ ∈ explicitFormulaCompletedZeroHeightWindow
              (h.height_schedule.height u) ↔
            completedZeroResidueCoordinate ρ ∈
                explicitFormulaContourFamilyInterior F
                  (h.height_schedule.height u) ∧
              completedZeroResidueCoordinate ρ ∈
                completedZetaContourIntegrandSingularSet)
    (Ehorizontal : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ Ehorizontal.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ Ehorizontal.carrier)
    (hvertical :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledVerticalPacketError
          f F h)
        atTop
        (𝓝 0))
    (hexcision :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
          f F h
          (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
            f F h))
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t)
      atTop
      (𝓝 0) := by
  have hboundary_sum :
      ∀ᶠ u in atTop,
        (∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) +
          zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledHorizontalInverseGammaError
            f F h u +
          zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
            f F h
            (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
              f F h) u = 0 :=
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledBoundarySum_eq_zero_of_canonicalFiniteGeometryRadius_and_zeroWindow
      f F h hregular Eline hline_mem BG hBG_nonneg hinverseGamma_bound
      hinterior
  have hrotated :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError
          f F h)
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError_tendsto_zero_ownerGap
      f F h Ehorizontal hTopMem hBottomMem
  have hhorizontal :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledHorizontalInverseGammaError
          f F h)
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledHorizontalInverseGammaError_tendsto_zero_of_vertical_and_horizontal
      f F h hvertical hrotated
  exact
    zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_scheduledWindow_tendsto_zero_of_finitePrimeBoundary
      f F h
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
        f F h)
      hboundary_sum
      hhorizontal
      hexcision

/-- Scheduled-window convergence from the canonical finite-boundary identity
before deleted-circle residue cancellation.

This keeps the finite excision packet's actual limit `E` visible.  A later
residue-normalization theorem may set the total limit to zero after combining
this with the matching residue-window contribution; this theorem itself does
not assert that the deleted-circle packet vanishes. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_scheduledWindow_tendsto_neg_excision_of_canonicalFiniteBoundary_and_packetDecay
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (Eline : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ Eline.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖))
    (hinterior :
      ∀ᶠ u in atTop,
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ρ ∈ explicitFormulaCompletedZeroHeightWindow
              (h.height_schedule.height u) ↔
            completedZeroResidueCoordinate ρ ∈
                explicitFormulaContourFamilyInterior F
                  (h.height_schedule.height u) ∧
              completedZeroResidueCoordinate ρ ∈
                completedZetaContourIntegrandSingularSet)
    (Ehorizontal : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ Ehorizontal.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ Ehorizontal.carrier)
    (hvertical :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledVerticalPacketError
          f F h)
        atTop
        (𝓝 0))
    (Eexcision : ℂ)
    (hexcision :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
          f F h
          (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
            f F h))
        atTop
        (𝓝 Eexcision)) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t)
      atTop
      (𝓝 (-Eexcision)) := by
  have hboundary_sum :
      ∀ᶠ u in atTop,
        (∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) +
          zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledHorizontalInverseGammaError
            f F h u +
          zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
            f F h
            (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
              f F h) u = 0 :=
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledBoundarySum_eq_zero_of_canonicalFiniteGeometryRadius_and_zeroWindow
      f F h hregular Eline hline_mem BG hBG_nonneg hinverseGamma_bound
      hinterior
  have hrotated :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError
          f F h)
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError_tendsto_zero_ownerGap
      f F h Ehorizontal hTopMem hBottomMem
  have hhorizontal :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledHorizontalInverseGammaError
          f F h)
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledHorizontalInverseGammaError_tendsto_zero_of_vertical_and_horizontal
      f F h hvertical hrotated
  exact
    zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_scheduledWindow_tendsto_neg_excision_of_finitePrimeBoundary
      f F h
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
        f F h)
      Eexcision
      hboundary_sum
      hhorizontal
      hexcision

/-- Scheduled-window convergence to zero from the canonical finite-boundary
identity and the two analytic packet-decay inputs, using the horizontal
zero-excised carrier already stored in the analytic package. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_scheduledWindow_tendsto_zero_of_canonicalFiniteBoundary_and_packagePacketDecay
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (Eline : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ Eline.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖))
    (hinterior :
      ∀ᶠ u in atTop,
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ρ ∈ explicitFormulaCompletedZeroHeightWindow
              (h.height_schedule.height u) ↔
            completedZeroResidueCoordinate ρ ∈
                explicitFormulaContourFamilyInterior F
                  (h.height_schedule.height u) ∧
              completedZeroResidueCoordinate ρ ∈
                completedZetaContourIntegrandSingularSet)
    (hvertical :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledVerticalPacketError
          f F h)
        atTop
        (𝓝 0))
    (hexcision :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
          f F h
          (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
            f F h))
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t)
      atTop
      (𝓝 0) :=
  match ExplicitFormulaFamilyAnalyticPackage.scheduled_horizontalFamilyZeroExcisedStrip h with
  | ⟨Ehorizontal, hhorizontal⟩ =>
      match hhorizontal with
      | ⟨hTopMem, hBottomMem⟩ =>
          zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_scheduledWindow_tendsto_zero_of_canonicalFiniteBoundary_and_packetDecay
            f F h hregular Eline hline_mem BG hBG_nonneg hinverseGamma_bound
            hinterior Ehorizontal hTopMem hBottomMem hvertical hexcision

/-- Package-horizontal wrapper for the nonzero excision form of the scheduled
left-prime finite-window limit. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_scheduledWindow_tendsto_neg_excision_of_canonicalFiniteBoundary_and_packagePacketDecay
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (Eline : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ Eline.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖))
    (hinterior :
      ∀ᶠ u in atTop,
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ρ ∈ explicitFormulaCompletedZeroHeightWindow
              (h.height_schedule.height u) ↔
            completedZeroResidueCoordinate ρ ∈
                explicitFormulaContourFamilyInterior F
                  (h.height_schedule.height u) ∧
              completedZeroResidueCoordinate ρ ∈
                completedZetaContourIntegrandSingularSet)
    (hvertical :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledVerticalPacketError
          f F h)
        atTop
        (𝓝 0))
    (Eexcision : ℂ)
    (hexcision :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
          f F h
          (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
            f F h))
        atTop
        (𝓝 Eexcision)) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t)
      atTop
      (𝓝 (-Eexcision)) :=
  match ExplicitFormulaFamilyAnalyticPackage.scheduled_horizontalFamilyZeroExcisedStrip h with
  | ⟨Ehorizontal, hhorizontal⟩ =>
      match hhorizontal with
      | ⟨hTopMem, hBottomMem⟩ =>
          zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_scheduledWindow_tendsto_neg_excision_of_canonicalFiniteBoundary_and_packetDecay
            f F h hregular Eline hline_mem BG hBG_nonneg hinverseGamma_bound
            hinterior Ehorizontal hTopMem hBottomMem hvertical
            Eexcision hexcision

/-- Scheduled left-prime finite-window limit with the honest oriented
zero-side-plus-poles deleted-circle target inserted.

This is the nonzero residue-normalized form.  The remaining residue-free
zero-limit must combine this theorem with the matching residue-window term
carrying the opposite orientation. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_scheduledWindow_tendsto_neg_oriented_zeroSide_add_poles
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (Eline : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ Eline.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖))
    (hinterior :
      ∀ᶠ u in atTop,
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ρ ∈ explicitFormulaCompletedZeroHeightWindow
              (h.height_schedule.height u) ↔
            completedZeroResidueCoordinate ρ ∈
                explicitFormulaContourFamilyInterior F
                  (h.height_schedule.height u) ∧
              completedZeroResidueCoordinate ρ ∈
                completedZetaContourIntegrandSingularSet)
    (hvertical :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledVerticalPacketError
          f F h)
        atTop
        (𝓝 0))
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaZeroSideContribution (ρ : ℂ) f))
    (hzero :
      ∀ᶠ u in atTop,
        explicitFormulaRectangleRawDeletedCircleBoundary f
            (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
              f F h u) 0 =
          (2 * ↑Real.pi * Complex.I : ℂ) •
            explicitFormulaRectangle_zeroPoleResidue f)
    (hone :
      ∀ᶠ u in atTop,
        explicitFormulaRectangleRawDeletedCircleBoundary f
            (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
              f F h u) 1 =
          (2 * ↑Real.pi * Complex.I : ℂ) •
            explicitFormulaRectangle_onePoleResidue f)
    (hcompleted :
      ∀ᶠ u in atTop,
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ∀ hρ : ρ ∈
              explicitFormulaCompletedZeroHeightWindow
                (h.height_schedule.height u),
            explicitFormulaRectangleRawDeletedCircleBoundary f
                (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
                  f F h u)
                (completedZeroResidueCoordinate ρ) =
              (2 * ↑Real.pi * Complex.I : ℂ) •
                explicitFormulaZeroResidue f
                  (explicitFormulaZeroDataOfCompletedZero ρ)) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t)
      atTop
      (𝓝
        (-(Complex.I *
          (-((2 * ↑Real.pi * Complex.I : ℂ) *
            (zetaCompletedZeroSideComplex f +
              explicitFormulaRectangle_completedPoleResidueSum f)))))) := by
  let Eexcision : ℂ :=
    Complex.I *
      (-((2 * ↑Real.pi * Complex.I : ℂ) *
        (zetaCompletedZeroSideComplex f +
          explicitFormulaRectangle_completedPoleResidueSum f)))
  have hexcision :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
          f F h
          (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
            f F h))
        atTop
        (𝓝 Eexcision) :=
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError_tendsto_oriented_zeroSide_add_poles
      f F h
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
        f F h)
      hsum hzero hone hcompleted
  exact
    zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_scheduledWindow_tendsto_neg_excision_of_canonicalFiniteBoundary_and_packagePacketDecay
      f F h hregular Eline hline_mem BG hBG_nonneg hinverseGamma_bound
      hinterior hvertical Eexcision hexcision

/-- Corrected scheduled prime-difference convergence from the canonical
finite-boundary identity.

This is the honest replacement for the old completed-right vertical packet
route: the right prime packet remains on the prime side, and the analytic
decay input is only the inverse-Gamma difference. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket_tendsto_zero_of_canonicalFiniteBoundary_and_packetDecay
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (Eline : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ Eline.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖))
    (hinterior :
      ∀ᶠ u in atTop,
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ρ ∈ explicitFormulaCompletedZeroHeightWindow
              (h.height_schedule.height u) ↔
            completedZeroResidueCoordinate ρ ∈
                explicitFormulaContourFamilyInterior F
                  (h.height_schedule.height u) ∧
              completedZeroResidueCoordinate ρ ∈
                completedZetaContourIntegrandSingularSet)
    (hright_integrable :
      ∀ᶠ u in atTop,
        IntegrableOn
          (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F)
          (Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T) ∧
        IntegrableOn
          (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F)
          (Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T))
    (Ehorizontal : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ Ehorizontal.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ Ehorizontal.carrier)
    (hinverseGammaDifference :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledInverseGammaDifferencePacket
          f F h)
        atTop
        (𝓝 0))
    (hexcision :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
          f F h
          (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
            f F h))
        atTop
        (𝓝 0)) :
    Tendsto
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket
        f F h)
      atTop
      (𝓝 0) := by
  have hboundary_sum :
      ∀ᶠ u in atTop,
        zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket
            f F h u +
          (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledInverseGammaDifferencePacket
              f F h u +
            zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError
              f F h u) +
          zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
            f F h
            (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
              f F h) u = 0 :=
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferenceBoundarySum_eq_zero_of_canonicalFiniteGeometryRadius
      f F h hregular Eline hline_mem BG hBG_nonneg hinverseGamma_bound
      hinterior
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledBoundaryRegularity
        f F h)
      hright_integrable
  have hrotated :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError
          f F h)
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError_tendsto_zero_ownerGap
      f F h Ehorizontal hTopMem hBottomMem
  have hcombined :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledInverseGammaDifferencePacket
              f F h u +
            zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError
              f F h u)
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledInverseGammaDifference_add_horizontal_tendsto_zero
      f F h hinverseGammaDifference hrotated
  exact
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket_tendsto_zero_of_boundary_sum_errors
      f F h
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
        f F h)
      hboundary_sum
      hcombined
      hexcision

/-- Corrected scheduled prime-difference convergence from the canonical
finite-boundary identity with a nonzero inverse-Gamma-difference limit. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket_tendsto_neg_error_of_canonicalFiniteBoundary_and_packetDecay
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (Eline : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ Eline.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖))
    (hinterior :
      ∀ᶠ u in atTop,
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ρ ∈ explicitFormulaCompletedZeroHeightWindow
              (h.height_schedule.height u) ↔
            completedZeroResidueCoordinate ρ ∈
                explicitFormulaContourFamilyInterior F
                  (h.height_schedule.height u) ∧
              completedZeroResidueCoordinate ρ ∈
                completedZetaContourIntegrandSingularSet)
    (hright_integrable :
      ∀ᶠ u in atTop,
        IntegrableOn
          (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F)
          (Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T) ∧
        IntegrableOn
          (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F)
          (Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T))
    (Ehorizontal : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ Ehorizontal.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ Ehorizontal.carrier)
    (Epacket : ℂ)
    (hinverseGammaDifference :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledInverseGammaDifferencePacket
          f F h)
        atTop
        (𝓝 Epacket))
    (hexcision :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
          f F h
          (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
            f F h))
        atTop
        (𝓝 0)) :
    Tendsto
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket
        f F h)
      atTop
      (𝓝 (-Epacket)) := by
  have hboundary_sum :
      ∀ᶠ u in atTop,
        zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket
            f F h u +
          (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledInverseGammaDifferencePacket
              f F h u +
            zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError
              f F h u) +
          zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
            f F h
            (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
              f F h) u = 0 :=
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferenceBoundarySum_eq_zero_of_canonicalFiniteGeometryRadius
      f F h hregular Eline hline_mem BG hBG_nonneg hinverseGamma_bound
      hinterior
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledBoundaryRegularity
        f F h)
      hright_integrable
  have hrotated :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError
          f F h)
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError_tendsto_zero_ownerGap
      f F h Ehorizontal hTopMem hBottomMem
  have hcombined :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledInverseGammaDifferencePacket
              f F h u +
            zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError
              f F h u)
        atTop
        (𝓝 Epacket) := by
    have hsum :
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledInverseGammaDifferencePacket
                f F h u +
              zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError
                f F h u)
          atTop
          (𝓝 (Epacket + 0)) :=
      hinverseGammaDifference.add hrotated
    exact
      Eq.subst
        (motive := fun z : ℂ =>
          Tendsto
            (fun u : ℝ =>
              zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledInverseGammaDifferencePacket
                  f F h u +
                zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError
                  f F h u)
            atTop
            (𝓝 z))
        (add_zero Epacket)
        hsum
  exact
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket_tendsto_neg_error_of_boundary_sum_errors
      f F h
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
        f F h)
      Epacket
      hboundary_sum
      hcombined
      hexcision

/-- Corrected scheduled prime-difference convergence from the canonical
finite-boundary identity when both error packets have nonzero limits. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket_tendsto_neg_error_add_excision_of_canonicalFiniteBoundary_and_packetDecay
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (Eline : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ Eline.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖))
    (hinterior :
      ∀ᶠ u in atTop,
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ρ ∈ explicitFormulaCompletedZeroHeightWindow
              (h.height_schedule.height u) ↔
            completedZeroResidueCoordinate ρ ∈
                explicitFormulaContourFamilyInterior F
                  (h.height_schedule.height u) ∧
              completedZeroResidueCoordinate ρ ∈
                completedZetaContourIntegrandSingularSet)
    (hright_integrable :
      ∀ᶠ u in atTop,
        IntegrableOn
          (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F)
          (Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T) ∧
        IntegrableOn
          (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F)
          (Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T))
    (Ehorizontal : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ Ehorizontal.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ Ehorizontal.carrier)
    (Epacket Eexcision : ℂ)
    (hinverseGammaDifference :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledInverseGammaDifferencePacket
          f F h)
        atTop
        (𝓝 Epacket))
    (hexcision :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
          f F h
          (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
            f F h))
        atTop
        (𝓝 Eexcision)) :
    Tendsto
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket
        f F h)
      atTop
      (𝓝 (-(Epacket + Eexcision))) := by
  have hboundary_sum :
      ∀ᶠ u in atTop,
        zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket
            f F h u +
          (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledInverseGammaDifferencePacket
              f F h u +
            zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError
              f F h u) +
          zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
            f F h
            (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
              f F h) u = 0 :=
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferenceBoundarySum_eq_zero_of_canonicalFiniteGeometryRadius
      f F h hregular Eline hline_mem BG hBG_nonneg hinverseGamma_bound
      hinterior
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledBoundaryRegularity
        f F h)
      hright_integrable
  have hrotated :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError
          f F h)
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError_tendsto_zero_ownerGap
      f F h Ehorizontal hTopMem hBottomMem
  have hcombined :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledInverseGammaDifferencePacket
              f F h u +
            zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError
              f F h u)
        atTop
        (𝓝 Epacket) := by
    have hsum :
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledInverseGammaDifferencePacket
                f F h u +
              zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError
                f F h u)
          atTop
          (𝓝 (Epacket + 0)) :=
      hinverseGammaDifference.add hrotated
    exact
      Eq.subst
        (motive := fun z : ℂ =>
          Tendsto
            (fun u : ℝ =>
              zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledInverseGammaDifferencePacket
                  f F h u +
                zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledRotatedHorizontalPacketError
                  f F h u)
            atTop
            (𝓝 z))
        (add_zero Epacket)
        hsum
  exact
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket_tendsto_neg_error_add_excision_of_boundary_sum_errors
      f F h
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
        f F h)
      Epacket
      Eexcision
      hboundary_sum
      hcombined
      hexcision

/-- Package-horizontal wrapper for the corrected scheduled prime-difference
convergence theorem. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket_tendsto_zero_of_canonicalFiniteBoundary_and_packagePacketDecay
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (Eline : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ Eline.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖))
    (hinterior :
      ∀ᶠ u in atTop,
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ρ ∈ explicitFormulaCompletedZeroHeightWindow
              (h.height_schedule.height u) ↔
            completedZeroResidueCoordinate ρ ∈
                explicitFormulaContourFamilyInterior F
                  (h.height_schedule.height u) ∧
              completedZeroResidueCoordinate ρ ∈
                completedZetaContourIntegrandSingularSet)
    (hright_integrable :
      ∀ᶠ u in atTop,
        IntegrableOn
          (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F)
          (Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T) ∧
        IntegrableOn
          (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F)
          (Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T))
    (hinverseGammaDifference :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledInverseGammaDifferencePacket
          f F h)
        atTop
        (𝓝 0))
    (hexcision :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
          f F h
          (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
            f F h))
        atTop
        (𝓝 0)) :
    Tendsto
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket
        f F h)
      atTop
      (𝓝 0) :=
  match ExplicitFormulaFamilyAnalyticPackage.scheduled_horizontalFamilyZeroExcisedStrip h with
  | ⟨Ehorizontal, hhorizontal⟩ =>
      match hhorizontal with
      | ⟨hTopMem, hBottomMem⟩ =>
          zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket_tendsto_zero_of_canonicalFiniteBoundary_and_packetDecay
            f F h hregular Eline hline_mem BG hBG_nonneg hinverseGamma_bound
            hinterior hright_integrable Ehorizontal hTopMem hBottomMem
            hinverseGammaDifference hexcision

/-- Eventual finite-window integrability of the two right-side summands used
by the corrected two-sided residue-free boundary identity. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_eventually_rightPrime_inverseGamma_integrableOn
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    ∀ᶠ u in atTop,
      IntegrableOn
        (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F)
        (Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T) ∧
      IntegrableOn
        (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F)
        (Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T) := by
  have hprime :
      Integrable
        (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel_integrable
      f F h
  have hinverseGamma :
      Integrable
        (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_integrable
      f F h hcoh
  exact
    Filter.Eventually.of_forall
      (fun u : ℝ =>
        ⟨hprime.integrableOn, hinverseGamma.integrableOn⟩)

/-- Corrected scheduled prime-difference convergence with right finite-window
integrability supplied by the standard right von Mangoldt and right
inverse-Gamma majorant packages. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket_tendsto_zero_of_canonicalFiniteBoundary_and_coherentPacketDecay
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (Eline : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ Eline.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖))
    (hinterior :
      ∀ᶠ u in atTop,
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ρ ∈ explicitFormulaCompletedZeroHeightWindow
              (h.height_schedule.height u) ↔
            completedZeroResidueCoordinate ρ ∈
                explicitFormulaContourFamilyInterior F
                  (h.height_schedule.height u) ∧
              completedZeroResidueCoordinate ρ ∈
                completedZetaContourIntegrandSingularSet)
    (hinverseGammaDifference :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledInverseGammaDifferencePacket
          f F h)
        atTop
        (𝓝 0))
    (hexcision :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
          f F h
          (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
            f F h))
        atTop
        (𝓝 0)) :
    Tendsto
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket
        f F h)
      atTop
      (𝓝 0) :=
  zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket_tendsto_zero_of_canonicalFiniteBoundary_and_packagePacketDecay
    f F h hregular Eline hline_mem BG hBG_nonneg hinverseGamma_bound
    hinterior
    (zetaCompletedExplicitFormulaPrimeLeftResidueFree_eventually_rightPrime_inverseGamma_integrableOn
      f F h hcoh)
    hinverseGammaDifference
    hexcision

/-- Corrected scheduled prime-difference convergence with the inverse-Gamma
normalization inserted.  The prime-difference packet tends to the
archimedean-plus-correction contribution; this is the nonzero companion to
the residue-free two-sided boundary identity. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket_tendsto_archimedean_add_correction_of_canonicalFiniteBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (Eline : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ Eline.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖))
    (hinterior :
      ∀ᶠ u in atTop,
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ρ ∈ explicitFormulaCompletedZeroHeightWindow
              (h.height_schedule.height u) ↔
            completedZeroResidueCoordinate ρ ∈
                explicitFormulaContourFamilyInterior F
                  (h.height_schedule.height u) ∧
              completedZeroResidueCoordinate ρ ∈
                completedZetaContourIntegrandSingularSet)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t) =
        zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)
    (hexcision :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
          f F h
          (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
            f F h))
        atTop
        (𝓝 0)) :
    Tendsto
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket
        f F h)
      atTop
      (𝓝
        (zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) := by
  let A : ℂ :=
    zetaCompletedExplicitFormulaArchimedeanContribution f +
      zetaCompletedExplicitFormulaCorrectionStandardContourContribution f
  have hinverseGammaDifference :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledInverseGammaDifferencePacket
          f F h)
        atTop
        (𝓝 (-A)) :=
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledInverseGammaDifferencePacket_tendsto_neg_archimedean_add_correction
      f F h hregular hcoh hvalue
  have hprime :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket
          f F h)
        atTop
        (𝓝 (-(-A))) :=
    match ExplicitFormulaFamilyAnalyticPackage.scheduled_horizontalFamilyZeroExcisedStrip h with
    | ⟨Ehorizontal, hhorizontal⟩ =>
        match hhorizontal with
        | ⟨hTopMem, hBottomMem⟩ =>
            zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket_tendsto_neg_error_of_canonicalFiniteBoundary_and_packetDecay
              f F h hregular Eline hline_mem BG hBG_nonneg hinverseGamma_bound
              hinterior
              (zetaCompletedExplicitFormulaPrimeLeftResidueFree_eventually_rightPrime_inverseGamma_integrableOn
                f F h hcoh)
              Ehorizontal hTopMem hBottomMem
              (-A)
              hinverseGammaDifference
              hexcision
  have hneg_neg :
      -(-A) = A :=
    neg_neg A
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket
            f F h)
          atTop
          (𝓝 z))
      hneg_neg
      hprime

/-- Canonical finite-boundary residue-free scheduled-window vanishing after
the nonzero prime-difference packet has been normalized against the proved
right one-sided prime packet.

This is the honest zero theorem for the corrected finite-boundary branch.  The
finite contour argument supplies the `left - right` prime-difference packet as
`archimedean + correction`; the explicit scalar normalization says that this
is the negative of the right one-sided von Mangoldt value. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_scheduledWindow_tendsto_zero_of_canonicalFiniteBoundary_archimedean_cancellation
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (Eline : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ Eline.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖))
    (hinterior :
      ∀ᶠ u in atTop,
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ρ ∈ explicitFormulaCompletedZeroHeightWindow
              (h.height_schedule.height u) ↔
            completedZeroResidueCoordinate ρ ∈
                explicitFormulaContourFamilyInterior F
                  (h.height_schedule.height u) ∧
              completedZeroResidueCoordinate ρ ∈
                completedZetaContourIntegrandSingularSet)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t) =
        zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)
    (hexcision :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
          f F h
          (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
            f F h))
        atTop
        (𝓝 0))
    (hscalar :
      zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f =
        -(zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f)) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t)
      atTop
      (𝓝 0) := by
  have hdiff :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket
          f F h)
        atTop
        (𝓝
          (zetaCompletedExplicitFormulaArchimedeanContribution f +
            zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) :=
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledPrimeDifferencePacket_tendsto_archimedean_add_correction_of_canonicalFiniteBoundary
      f F h hregular hcoh Eline hline_mem BG hBG_nonneg
      hinverseGamma_bound hinterior hvalue hexcision
  exact
    zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_scheduledWindow_tendsto_zero_of_primeDifference_archimedean_add_correction
      f F h hdiff hscalar

/-- Vertically regular canonical finite-boundary residue-free scheduled-window
vanishing.

This wrapper discharges the inverse-Gamma difference value from the
Gamma/Binet owner normalization.  The remaining scalar identity is the
mathematical cancellation between the archimedean-plus-correction packet and
the proved right one-sided prime packet, so it remains visible until its own
owner theorem is proved. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_scheduledWindow_tendsto_zero_of_verticallyRegular_canonicalFiniteBoundary_archimedean_cancellation
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (Eline : CompletedZetaZeroExcisedStrip
      (1 - F.toContourFamily.c) (1 - F.toContourFamily.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F.toContourFamily t ∈
          Eline.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine
              F.toContourFamily t)‖ ≤
          BG * (1 + ‖t‖))
    (hinterior :
      ∀ᶠ u in atTop,
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ρ ∈ explicitFormulaCompletedZeroHeightWindow
              (h.height_schedule.height u) ↔
            completedZeroResidueCoordinate ρ ∈
                explicitFormulaContourFamilyInterior F.toContourFamily
                  (h.height_schedule.height u) ∧
              completedZeroResidueCoordinate ρ ∈
                completedZetaContourIntegrandSingularSet)
    (hexcision :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
          f F.toContourFamily h
          (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
            f F.toContourFamily h))
        atTop
        (𝓝 0))
    (hscalar :
      zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f =
        -(zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f)) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝 0) := by
  have hregular :
      zetaCompletedExplicitFormulaLeftAffineLineGammaRegular
        F.toContourFamily :=
    zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular
      F
  have hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f :=
    zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integral_eq_archimedean_add_correction_of_verticallyRegular_gammaBinet_ownerNormalization
      f F h hcoh
  exact
    zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_scheduledWindow_tendsto_zero_of_canonicalFiniteBoundary_archimedean_cancellation
      f F.toContourFamily h hregular hcoh Eline hline_mem BG hBG_nonneg
      hinverseGamma_bound hinterior hvalue hexcision hscalar

/-- Vertically regular canonical finite-boundary residue-free whole-line value.

This is only the exhaustion projection from the scheduled canonical
finite-boundary theorem above.  The contour normalization and scalar
cancellation remain visible in the scheduled theorem's hypotheses. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_integral_eq_zero_of_verticallyRegular_canonicalFiniteBoundary_archimedean_cancellation
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (Eline : CompletedZetaZeroExcisedStrip
      (1 - F.toContourFamily.c) (1 - F.toContourFamily.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F.toContourFamily t ∈
          Eline.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine
              F.toContourFamily t)‖ ≤
          BG * (1 + ‖t‖))
    (hinterior :
      ∀ᶠ u in atTop,
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ρ ∈ explicitFormulaCompletedZeroHeightWindow
              (h.height_schedule.height u) ↔
            completedZeroResidueCoordinate ρ ∈
                explicitFormulaContourFamilyInterior F.toContourFamily
                  (h.height_schedule.height u) ∧
              completedZeroResidueCoordinate ρ ∈
                completedZetaContourIntegrandSingularSet)
    (hexcision :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
          f F.toContourFamily h
          (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledFiniteGeometryRadius
            f F.toContourFamily h))
        atTop
        (𝓝 0))
    (hscalar :
      zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f =
        -(zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f)) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel
        f F.toContourFamily t) =
      0 := by
  have hregular :
      zetaCompletedExplicitFormulaLeftAffineLineGammaRegular
        F.toContourFamily :=
    zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular
      F
  have hscheduled_zero :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel
              f F.toContourFamily t)
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_scheduledWindow_tendsto_zero_of_verticallyRegular_canonicalFiniteBoundary_archimedean_cancellation
      f F h hcoh Eline hline_mem BG hBG_nonneg hinverseGamma_bound
      hinterior hexcision hscalar
  exact
    zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_integral_eq_zero_of_scheduledWindow_tendsto_zero_ownerResidueFreeContourIdentity
      f F.toContourFamily h hregular Eline hline_mem BG hBG_nonneg
      hinverseGamma_bound hscheduled_zero

/-- Forward scheduled zero-window/interior inclusion for the contour family
heights.

The reverse implication is not true for the current height window
`1 + |Im ρ| ≤ T`: the rectangle interior also contains the outer unit band
`T - 1 < |Im ρ| < T`.  That outer band must be accounted for by a residue-window
error theorem rather than by a false equivalence. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledZeroWindowInterior_forward
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ∀ᶠ u in atTop,
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow
            (h.height_schedule.height u) →
          completedZeroResidueCoordinate ρ ∈
              explicitFormulaContourFamilyInterior F
                (h.height_schedule.height u) ∧
            completedZeroResidueCoordinate ρ ∈
              completedZetaContourIntegrandSingularSet := by
  exact Filter.Eventually.of_forall
    (fun u ρ hρ =>
      have hheight :
          zetaCompletedZeroCenteredHeight ρ ≤ h.height_schedule.height u :=
        explicitFormulaCompletedZeroHeightWindow_centeredHeight_le
          (h.height_schedule.height u) hρ
      have hheight_raw :
          1 + ‖(zetaCenteredZero (ρ : ℂ)).im‖ ≤
            h.height_schedule.height u := hheight
      have him_norm_lt :
          ‖(zetaCenteredZero (ρ : ℂ)).im‖ <
            h.height_schedule.height u :=
        lt_of_lt_of_le
          (lt_add_of_pos_left
            ‖(zetaCenteredZero (ρ : ℂ)).im‖ zero_lt_one)
          hheight_raw
      have him_eq :
          (completedZeroResidueCoordinate ρ).im =
            (zetaCenteredZero (ρ : ℂ)).im := by
        calc
          (completedZeroResidueCoordinate ρ).im =
              ((1 / 2 : ℂ) + (ρ : ℂ)).im := by
            rfl
          _ = (ρ : ℂ).im := by
            exact
              Eq.trans
                (Complex.add_im (1 / 2 : ℂ) (ρ : ℂ))
                (zero_add (ρ : ℂ).im)
          _ = ((ρ : ℂ) - (1 / 2 : ℂ)).im := by
            exact
              (Eq.trans
                (Complex.sub_im (ρ : ℂ) (1 / 2 : ℂ))
                (sub_zero (ρ : ℂ).im)).symm
          _ = (zetaCenteredZero (ρ : ℂ)).im := by
            rfl
      have him_norm_coord_lt :
          ‖(completedZeroResidueCoordinate ρ).im‖ <
            h.height_schedule.height u :=
        Eq.subst
          (motive := fun x : ℝ => ‖x‖ < h.height_schedule.height u)
          him_eq.symm
          him_norm_lt
      have him_abs_lt :
          |(completedZeroResidueCoordinate ρ).im| <
            h.height_schedule.height u :=
        Eq.subst
          (motive := fun x : ℝ => x < h.height_schedule.height u)
          (Real.norm_eq_abs (completedZeroResidueCoordinate ρ).im)
          him_norm_coord_lt
      have him_interval :
          (completedZeroResidueCoordinate ρ).im ∈
            Set.Ioo (-(h.height_schedule.height u))
              (h.height_schedule.height u) :=
        abs_lt.mp him_abs_lt
      have hzero :
          completedRiemannZeta (completedZeroResidueCoordinate ρ) = 0 :=
        completedRiemannZeta_zero_at_completedZeroResidueCoordinate ρ
      have hstrip :
          0 ≤ (completedZeroResidueCoordinate ρ).re ∧
            (completedZeroResidueCoordinate ρ).re ≤ (1 : ℝ) :=
        completedRiemannZeta_zero_re_mem_criticalStrip
          (completedZeroResidueCoordinate ρ) hzero
      have hleft :
          1 - F.c < (completedZeroResidueCoordinate ρ).re :=
        lt_of_lt_of_le F.one_sub_c_neg hstrip.1
      have hright :
          (completedZeroResidueCoordinate ρ).re < F.c :=
        lt_of_le_of_lt hstrip.2 F.c_gt_one
      have hre_interval :
          (completedZeroResidueCoordinate ρ).re ∈
            Set.uIoo F.c (1 - F.c) :=
        Set.mem_uIoo_of_gt hleft hright
      have hinterior :
          completedZeroResidueCoordinate ρ ∈
            explicitFormulaContourFamilyInterior F
              (h.height_schedule.height u) :=
        And.intro hre_interval him_interval
      have hsingular :
          completedZeroResidueCoordinate ρ ∈
            completedZetaContourIntegrandSingularSet :=
        explicitFormulaCompletedZero_mem_contourIntegrandSingularSet_ownerGap
          ρ
      And.intro hinterior hsingular)

/-- Interior completed-zero coordinates at rectangle height `T` are captured by
the completed-zero height window at height `T + 1`.

This is the true replacement for the false reverse direction of the old
zero-window/interior equivalence.  The current completed-zero height is
`1 + |Im ρ|`; therefore the open strip condition `|Im ρ| < T` gives membership
only in the enlarged window `T + 1`, not in the original window `T`. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_interiorZero_mem_enlargedHeightWindow
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hinterior :
      completedZeroResidueCoordinate ρ ∈
        explicitFormulaContourFamilyInterior F T) :
    ρ ∈ explicitFormulaCompletedZeroHeightWindow (T + 1) := by
  have him_interval :
      (completedZeroResidueCoordinate ρ).im ∈ Set.Ioo (-T) T :=
    hinterior.right
  have him_abs_lt :
      |(completedZeroResidueCoordinate ρ).im| < T :=
    abs_lt.mpr him_interval
  have him_eq :
      (completedZeroResidueCoordinate ρ).im =
        (zetaCenteredZero (ρ : ℂ)).im := by
    calc
      (completedZeroResidueCoordinate ρ).im =
          ((1 / 2 : ℂ) + (ρ : ℂ)).im := by
        rfl
      _ = (ρ : ℂ).im := by
        exact
          Eq.trans
            (Complex.add_im (1 / 2 : ℂ) (ρ : ℂ))
            (zero_add (ρ : ℂ).im)
      _ = ((ρ : ℂ) - (1 / 2 : ℂ)).im := by
        exact
          (Eq.trans
            (Complex.sub_im (ρ : ℂ) (1 / 2 : ℂ))
            (sub_zero (ρ : ℂ).im)).symm
      _ = (zetaCenteredZero (ρ : ℂ)).im := by
        rfl
  have him_norm_coord_lt :
      ‖(completedZeroResidueCoordinate ρ).im‖ < T :=
    Eq.subst
      (motive := fun x : ℝ => x < T)
      (Real.norm_eq_abs (completedZeroResidueCoordinate ρ).im).symm
      him_abs_lt
  have him_norm_lt :
      ‖(zetaCenteredZero (ρ : ℂ)).im‖ < T :=
    Eq.subst
      (motive := fun x : ℝ => ‖x‖ < T)
      him_eq
      him_norm_coord_lt
  have hheight_lt :
      zetaCompletedZeroCenteredHeight ρ < T + 1 :=
    add_lt_add_left him_norm_lt 1
  have hheight_le :
      zetaCompletedZeroCenteredHeight ρ ≤ T + 1 :=
    le_of_lt hheight_lt
  exact
    explicitFormulaCompletedZeroHeightWindow_mem_of_centeredHeight_le
      (T + 1) hheight_le

/-- Scheduled form of the enlarged-window capture for completed zeros in the
rectangle interior. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledInteriorZero_mem_enlargedHeightWindow
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ∀ᶠ u in atTop,
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        completedZeroResidueCoordinate ρ ∈
            explicitFormulaContourFamilyInterior F
              (h.height_schedule.height u) →
          ρ ∈ explicitFormulaCompletedZeroHeightWindow
            (h.height_schedule.height u + 1) := by
  exact Filter.Eventually.of_forall
    (fun u ρ hinterior =>
      zetaCompletedExplicitFormulaPrimeLeftResidueFree_interiorZero_mem_enlargedHeightWindow
        F (h.height_schedule.height u) ρ hinterior)

/-- Scheduled inverse-Gamma difference normalization for the corrected
residue-free prime-difference contour.

The packet is oriented `left - right`, while the inverse-Gamma normalization
owner theorem is oriented `right - left`; hence the limit is the negative of
the standard archimedean-plus-correction contribution. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledInverseGammaDifferencePacket_tendsto_neg_archimedean_add_correction
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t) =
        zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f) :
    Tendsto
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledInverseGammaDifferencePacket
        f F h)
      atTop
      (𝓝
        (-(zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f))) := by
  let A : ℂ :=
    zetaCompletedExplicitFormulaArchimedeanContribution f +
      zetaCompletedExplicitFormulaCorrectionStandardContourContribution f
  let D : ℝ → ℂ := fun u : ℝ =>
    (∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t) -
      ∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t
  have hright_left :
      Tendsto D atTop (𝓝 A) :=
    zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_archimedean_add_correction
      f F h hregular hcoh hvalue
  have hneg :
      Tendsto (fun u : ℝ => -(D u)) atTop (𝓝 (-A)) :=
    hright_left.neg
  have hpacket :
      zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledInverseGammaDifferencePacket
          f F h =
        fun u : ℝ => -(D u) := by
    funext u
    let L : ℂ :=
      ∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t
    let R : ℂ :=
      ∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t
    calc
      zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledInverseGammaDifferencePacket
          f F h u = L - R := by
        exact Eq.refl _
      _ = -(R - L) := by
        exact (neg_sub R L).symm
      _ = -(D u) := by
        exact Eq.refl _
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ =>
        Tendsto φ atTop (𝓝 (-A)))
      hpacket.symm
      hneg

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
