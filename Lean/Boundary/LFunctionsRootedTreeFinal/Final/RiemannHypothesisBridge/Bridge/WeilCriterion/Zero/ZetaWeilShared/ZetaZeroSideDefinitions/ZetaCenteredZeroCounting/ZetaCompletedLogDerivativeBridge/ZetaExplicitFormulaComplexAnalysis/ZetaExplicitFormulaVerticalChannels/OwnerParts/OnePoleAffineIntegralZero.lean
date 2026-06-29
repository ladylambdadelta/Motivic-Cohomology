import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.OnePoleAffineVerticalTransport
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaSinglePoleContour.OwnerParts.CanonicalRawCauchy
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.RightOnePoleCauchyCancellation
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ScheduledKernelLimitTransport

/-!
# Right one-pole affine zero value

This file owns the non-circular analytic input needed before the one-pole
residue-tail estimate: the right `s = 1` correction affine kernel has
whole-line integral `0`.

The zero value is a contour-shift/Cauchy theorem for the isolated right
one-pole correction kernel.  It must not be derived from
`OnePoleResidueTailEstimate`, `OnePoleResidueTransport`, or
`RightOnePoleOffPoleDecayEstimate`; those files consume this value.
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

/-- Raw whole-line left-affine Cauchy residue value for the isolated `s = 1`
correction pole.

This is the local residue theorem on the fixed line `Re s = 1 - c`, after
passing from finite windows to the whole real line. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel_integral_eq_standardResidue_rawCauchy_ownerOnePoleAffine
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F t) =
      ((2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I := by
  sorry

/-- Raw scheduled left-affine Cauchy value for the isolated `s = 1`
correction pole.

This is the affine-window form of the local residue theorem on the line
`Re s = 1 - c`, with the standard vertical orientation factor already
included in the target value. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel_scheduledWindow_tendsto_standardResidue_rawCauchy_ownerOnePoleAffine
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
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            ∫ t in Set.Icc
                (-(F.rectangle (h.height_schedule.height u)).T)
                (F.rectangle (h.height_schedule.height u)).T,
              zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F t)
          atTop
          (𝓝 z))
      (zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel_integral_eq_standardResidue_rawCauchy_ownerOnePoleAffine
        f F h)
      hlimit

/-- Raw left-face standard residue value for the isolated `s = 1` correction
pole, before it is used to cancel the tangent boundary. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral_tendsto_standardContourResidue_rawCauchy_ownerOnePoleAffine
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (((2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I)) := by
  have haffine :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F t)
        atTop
        (𝓝 (((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I)) :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel_scheduledWindow_tendsto_standardResidue_rawCauchy_ownerOnePoleAffine
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
      hpoint.symm
      haffine

/-- Tangent-boundary defect limit for the residue-free right `s = 1` contour.

This is the finite Cauchy cancellation input beneath the right oscillatory
side: after multiplying the tangent rectangle boundary by the vertical
orientation factor, it cancels the left vertical side asymptotically. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleTangentBoundaryDefect_tendsto_zero_rawCauchy_ownerOnePoleAffine
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
            f F (h.height_schedule.height u) -
          zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I)
      atTop
      (𝓝 0) := by
  let B : ℂ :=
    (2 * (Real.pi : ℂ) * Complex.I) *
      (-zetaCompletedExplicitFormulaPhi f (1 / 2))
  have hcancel : B * Complex.I - B * Complex.I = 0 :=
    sub_self (B * Complex.I)
  have hleft :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 (B * Complex.I)) :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral_tendsto_standardContourResidue_rawCauchy_ownerOnePoleAffine
      f F h
  have hstandard :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 B) :=
    ((zetaCompletedExplicitFormulaCorrectionOnePole_eventually_standardBoundaryResidueValue_of_positiveHeight
      f F h B
      (fun T hT =>
        zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_pos_height
          f F h T hT)).tendsto_iff.2 tendsto_const_nhds)
  exact
    zetaCompletedExplicitFormulaCorrectionOnePoleTangentBoundaryDefect_tendsto_zero_of_standardBoundaryResidue
      f F h (B * Complex.I) B hcancel hleft hstandard

/-- Scheduled residue-free Cauchy zero value for the isolated right
`s = 1` correction contour integral.

This is the true upstream analytic sink beneath the right one-pole branch:
the right face is residue-free for the pole at `s = 1`.  The proof is the
scheduled finite-rectangle Cauchy argument: boundary zero, horizontal decay,
and far-side decay leave only this right oscillatory side. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral_tendsto_zero_rawCauchy_ownerOnePoleAffine
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
          f F h u)
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral_tendsto_zero_of_tangentBoundaryDefect
      f F h
      (zetaCompletedExplicitFormulaCorrectionOnePoleTangentBoundaryDefect_tendsto_zero_rawCauchy_ownerOnePoleAffine
        f F h)

/-- Scheduled affine-window form of the residue-free right `s = 1` Cauchy
zero value, transported from the named right oscillatory contour integral. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_scheduledWindow_tendsto_zero_rawCauchy_ownerOnePoleAffine
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
  have hosc :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
            f F h u)
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral_tendsto_zero_rawCauchy_ownerOnePoleAffine
      f F h
  have hpoint :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
          f F h u) =
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
      hpoint
      hosc

/-- Raw right-affine Cauchy zero value for the isolated `s = 1` correction
kernel, transported from the scheduled residue-free Cauchy value by rectangle
exhaustion. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_integral_eq_zero_rawCauchy_ownerOnePoleAffine
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
    zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_scheduledWindow_tendsto_zero_rawCauchy_ownerOnePoleAffine
      f F h
  exact
    tendsto_nhds_unique hlimit hzero

/-- The scheduled right `s = 1` correction affine windows vanish by the
residue-free scheduled Cauchy value. -/
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
    zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_scheduledWindow_tendsto_zero_rawCauchy_ownerOnePoleAffine
      f F h

/-- Independent vanishing of the right `s = 1` off-pole vertical face, proved
from the owner right-affine Cauchy zero value and no left-residue input. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_tendsto_zero_independent_ownerOnePoleAffine
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
  have hfun :
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
      hfun.symm
      hwindow

/-- Compatibility wrapper for the left-face standard residue value after the
raw left Cauchy value has been exposed as the owner leaf. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral_tendsto_standardContourResidue_of_independentRight_ownerOnePoleAffine
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
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral_tendsto_standardContourResidue_rawCauchy_ownerOnePoleAffine
      f F h

/-- Scheduled left-affine Cauchy value for the isolated `s = 1` correction
pole.  This is the contour-limit owner input: the finite standard Cauchy
residue value, horizontal decay, and the right off-pole side together force
the left affine windows to converge to the standard residue. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel_scheduledWindow_tendsto_standardResidue_direct_ownerOnePoleAffine
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
  exact
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel_scheduledWindow_tendsto_standardResidue_rawCauchy_ownerOnePoleAffine
      f F h

/-- Direct whole-line affine residue value for the left `s = 1` correction
kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel_integral_eq_standardResidue_direct_ownerOnePoleAffine
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F t) =
      ((2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I := by
  exact
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel_integral_eq_standardResidue_rawCauchy_ownerOnePoleAffine
      f F h

/-- Direct left-face standard residue value for the isolated `s = 1`
correction pole, before residue-tail estimates consume the right affine
zero-value theorem. -/
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
  let K : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F t
  let B : ℂ :=
    ((2 * (Real.pi : ℂ) * Complex.I) *
      (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I
  have hK_integral :
      Tendsto K atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F t)) := by
    unfold K
    exact
      explicitFormulaScheduledRectangleWindowIntegral_tendsto_integral
        F
        h.height_schedule.height
        (zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F)
        h.height_schedule.cofinal
        (zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel_integrable_ownerBounds
          f F h)
  have hK_residue :
      Tendsto K atTop (𝓝 B) :=
    Eq.subst
      (motive := fun z : ℂ => Tendsto K atTop (𝓝 z))
      (zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel_integral_eq_standardResidue_direct_ownerOnePoleAffine
        f F h)
      hK_integral
  have hpoint :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
          f F (h.height_schedule.height u)) =
      K := by
    funext u
    exact
      zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral_eq_affineKernelIntegral_ownerOnePoleVerticalTransport
        f F (h.height_schedule.height u)
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 B))
      hpoint.symm
      hK_residue

/-- Direct right-face off-pole Cauchy decay for the isolated `s = 1`
correction pole, before residue-tail estimates consume the affine zero value. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_tendsto_zero_direct_ownerOnePoleAffine
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_tendsto_zero_independent_ownerOnePoleAffine
      f F h

/-- The right `s = 1` correction affine kernel has zero whole-line value.

This public owner theorem is a thin wrapper over the raw right-affine Cauchy
zero value. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_integral_eq_zero_ownerOnePoleAffine
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t) =
      0 := by
  exact
    zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_integral_eq_zero_rawCauchy_ownerOnePoleAffine
      f F h

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
