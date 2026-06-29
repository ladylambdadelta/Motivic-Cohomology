import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.OnePoleLeftStandardResidueValue
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.OnePoleResidueFreeCauchyValue
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ScheduledKernelLimitTransport

/-!
# One-pole affine whole-line values

This file owns the passage from scheduled one-pole contour values to
whole-line affine-kernel values.  The analytic residue inputs are owned
upstream:

* `OnePoleLeftStandardResidueValue` owns the left standard-residue limit.
* `OnePoleResidueFreeCauchyValue` owns the scheduled right residue-free value.

The affine whole-line statements below are only exhaustion transports.
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

/-- Scheduled left-affine Cauchy value for the isolated `s = 1` correction
pole, transported from the owner left vertical standard-residue theorem. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel_scheduledWindow_tendsto_standardResidue_ownerOnePoleAffine
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F t)
      atTop
      (𝓝 (((2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I)) := by
  have hvertical :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 (((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I)) :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral_tendsto_standardContourResidue_ownerLeftResidueValue
      f F h
  have hpoint :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
          f F (h.height_schedule.height u)) =
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F t) := by
    funext u
    exact
      zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral_eq_affineKernelIntegral_ownerOnePoleVerticalTransport
        f F (h.height_schedule.height u)
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ =>
        Tendsto φ atTop
          (𝓝 (((2 * (Real.pi : ℂ) * Complex.I) *
            (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I)))
      hpoint
      hvertical

/-- Whole-line left-affine Cauchy value for the isolated `s = 1` correction
pole, obtained by scheduled-window exhaustion from the owner left residue
limit. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel_integral_eq_standardResidue_ownerOnePoleAffine
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F t) =
      ((2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I := by
  have hlimit :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F t)
        atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F t)) :=
    explicitFormulaScheduledRectangleWindowIntegral_tendsto_integral
      F
      h.height_schedule.height
      (zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F)
      h.height_schedule.cofinal
      (zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel_integrable_ownerBounds
        f F h)
  have hresidue :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F t)
        atTop
        (𝓝 (((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I)) :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel_scheduledWindow_tendsto_standardResidue_ownerOnePoleAffine
      f F h
  exact
    tendsto_nhds_unique hlimit hresidue

/-- Compatibility wrapper for the left-face standard residue value. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral_tendsto_standardContourResidue_direct_ownerOnePoleAffine
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (((2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral_tendsto_standardContourResidue_ownerLeftResidueValue
      f F h

/-- Scheduled right-affine zero value for the isolated `s = 1` correction
pole, transported from the residue-free Cauchy owner. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_scheduledWindow_tendsto_zero_ownerOnePoleAffine
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t)
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_scheduledWindow_tendsto_zero_ownerResidueFreeCauchy
      f F h

/-- Whole-line right-affine zero value for the isolated `s = 1` correction
kernel, obtained by scheduled-window exhaustion. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_integral_eq_zero_ownerOnePoleAffine
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t) =
      0 := by
  have hlimit :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t)
        atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t)) :=
    explicitFormulaScheduledRectangleWindowIntegral_tendsto_integral
      F
      h.height_schedule.height
      (zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F)
      h.height_schedule.cofinal
      (zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_integrable_ownerBounds
        f F h)
  have hzero :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t)
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_scheduledWindow_tendsto_zero_ownerOnePoleAffine
      f F h
  exact
    tendsto_nhds_unique hlimit hzero

/-- Compatibility wrapper for the right-face off-pole Cauchy limit. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_tendsto_zero_direct_ownerOnePoleAffine
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  have hwindow :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t)
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_scheduledWindow_tendsto_zero_ownerOnePoleAffine
      f F h
  have hpoint :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u)) =
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t) := by
    funext u
    exact
      zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_eq_affineKernelIntegral_ownerOnePoleVerticalTransport
        f F (h.height_schedule.height u)
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
      hpoint.symm
      hwindow

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
