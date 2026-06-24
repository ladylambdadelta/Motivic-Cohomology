import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part34
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.CorrectionPoleSides
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.OrientationAlgebra
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleContourPrimitives
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleFourCellContour

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

/-- The scheduled rectangles eventually enclose the right-face `s = 0`
single-pole residue point. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPole_eventually_mem_interior
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ∀ᶠ u in atTop,
      (0 : ℂ) ∈
        explicitFormulaContourFamilyInterior F (h.height_schedule.height u) :=
  h.eventually_zero_mem_interior

/-- The scheduled rectangles eventually enclose the left-face `s = 1`
single-pole residue point. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftOnePole_eventually_mem_interior
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ∀ᶠ u in atTop,
      (1 : ℂ) ∈
        explicitFormulaContourFamilyInterior F (h.height_schedule.height u) :=
  h.eventually_one_mem_interior

/-- The right face stays strictly to the right of the enclosed `s = 0` pole along
the scheduled rectangles. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPole_scheduledFaceSeparates
    (F : ExplicitFormulaContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F) (u t : ℝ) :
    0 < (zetaCompletedExplicitFormulaRightPath
      (F.rectangle (hSchedule.height u)) t).re := by
  have hre :
      (zetaCompletedExplicitFormulaRightPath
        (F.rectangle (hSchedule.height u)) t).re =
        (F.rectangle (hSchedule.height u)).c :=
    zetaCompletedExplicitFormulaRightPath_re
      (F.rectangle (hSchedule.height u)) t
  exact Eq.symm hre ▸ F.c_pos

/-- The right face stays strictly to the right of the enclosed `s = 1` pole along
the scheduled rectangles. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePole_scheduledFaceSeparates
    (F : ExplicitFormulaContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F) (u t : ℝ) :
    1 < (zetaCompletedExplicitFormulaRightPath
      (F.rectangle (hSchedule.height u)) t).re :=
  zetaCompletedExplicitFormulaCorrectionRightPath_re_gt_one
    F (hSchedule.height u) t

/-- The left face stays strictly to the left of the enclosed `s = 0` pole along
the scheduled rectangles. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPole_scheduledFaceSeparates
    (F : ExplicitFormulaContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F) (u t : ℝ) :
    (zetaCompletedExplicitFormulaLeftPath
      (F.rectangle (hSchedule.height u)) t).re < 0 :=
  zetaCompletedExplicitFormulaCorrectionLeftPath_re_lt_zero
    F (hSchedule.height u) t

/-- The left face stays strictly to the left of the enclosed `s = 1` pole along
the scheduled rectangles. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftOnePole_scheduledFaceSeparates
    (F : ExplicitFormulaContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F) (u t : ℝ) :
    (zetaCompletedExplicitFormulaLeftPath
      (F.rectangle (hSchedule.height u)) t).re < 1 := by
  have hlt_zero :
      (zetaCompletedExplicitFormulaLeftPath
        (F.rectangle (hSchedule.height u)) t).re < 0 :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPole_scheduledFaceSeparates
      F hSchedule u t
  exact lt_trans hlt_zero zero_lt_one

/-- Scheduled top horizontal points never hit the `s = 1` correction pole. -/
theorem zetaCompletedExplicitFormulaCorrectionTopOnePole_scheduledPath_sub_one_ne_zero
    (F : ExplicitFormulaContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ) :
    zetaCompletedExplicitFormulaTopPath
        (F.rectangle (hSchedule.height u)) x - 1 ≠ 0 := by
  intro hzero
  have hpath_eq_one :
      zetaCompletedExplicitFormulaTopPath
          (F.rectangle (hSchedule.height u)) x = 1 :=
    sub_eq_zero.mp hzero
  have him_one :
      (zetaCompletedExplicitFormulaTopPath
          (F.rectangle (hSchedule.height u)) x).im = (1 : ℂ).im :=
    congrArg Complex.im hpath_eq_one
  have him_height :
      (zetaCompletedExplicitFormulaTopPath
          (F.rectangle (hSchedule.height u)) x).im =
        hSchedule.height u :=
    zetaCompletedExplicitFormulaTopPath_im
      (F.rectangle (hSchedule.height u)) x
  have hone_im : (1 : ℂ).im = (0 : ℝ) :=
    Complex.one_im
  have hheight_zero : hSchedule.height u = 0 :=
    Eq.trans him_height.symm (Eq.trans him_one hone_im)
  exact hSchedule.height_ne_zero u hheight_zero

/-- Scheduled bottom horizontal points never hit the `s = 1` correction pole. -/
theorem zetaCompletedExplicitFormulaCorrectionBottomOnePole_scheduledPath_sub_one_ne_zero
    (F : ExplicitFormulaContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ) :
    zetaCompletedExplicitFormulaBottomPath
        (F.rectangle (hSchedule.height u)) x - 1 ≠ 0 := by
  intro hzero
  have hpath_eq_one :
      zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (hSchedule.height u)) x = 1 :=
    sub_eq_zero.mp hzero
  have him_one :
      (zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (hSchedule.height u)) x).im = (1 : ℂ).im :=
    congrArg Complex.im hpath_eq_one
  have him_height :
      (zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (hSchedule.height u)) x).im =
        -hSchedule.height u :=
    zetaCompletedExplicitFormulaBottomPath_im
      (F.rectangle (hSchedule.height u)) x
  have hone_im : (1 : ℂ).im = (0 : ℝ) :=
    Complex.one_im
  have hneg_height_zero : -hSchedule.height u = 0 :=
    Eq.trans him_height.symm (Eq.trans him_one hone_im)
  have hheight_zero : hSchedule.height u = 0 :=
    neg_eq_zero.mp hneg_height_zero
  exact hSchedule.height_ne_zero u hheight_zero

/-- Algebraic residue cancellation for the isolated `s = 0` correction kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_localResidue_algebra
    (z φ : ℂ) (hz : z ≠ 0) :
    z * ((-1 / z) * φ) = -φ := by
  have hdiv_neg :
      -1 / z = -(1 / z) :=
    (neg_div z (1 : ℂ)).symm
  have hcoeff :
      z * (-1 / z) = -1 := by
    calc
      z * (-1 / z) =
          z * (-(1 / z)) := by
        exact congrArg (fun a : ℂ => z * a) hdiv_neg
      _ = -(z * (1 / z)) := by
        exact (mul_neg z (1 / z)).symm
      _ = -(z * z⁻¹) := by
        have hone_div : 1 / z = z⁻¹ := by
          exact one_div z
        exact congrArg (fun a : ℂ => -(z * a)) hone_div
      _ = -1 := by
        exact congrArg Neg.neg (mul_inv_cancel₀ hz)
  calc
    z * ((-1 / z) * φ) =
        (z * (-1 / z)) * φ := by
      exact (mul_assoc z (-1 / z) φ).symm
    _ = (-1) * φ := by
      exact congrArg (fun a : ℂ => a * φ) hcoeff
    _ = -φ := by
      exact neg_one_mul φ

/-- Local residue of the isolated `s = 0` correction kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_localResidue_tendsto
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f) :
    Tendsto
      (fun z : ℂ =>
        z *
          ((-1 / z) *
            zetaCompletedExplicitFormulaPhi f (z - 1 / 2)))
      (𝓝[≠] (0 : ℂ))
      (𝓝 (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))) := by
  have hphi :
      Tendsto
        (fun z : ℂ => zetaCompletedExplicitFormulaPhi f (z - 1 / 2))
        (𝓝[≠] (0 : ℂ))
        (𝓝 (zetaCompletedExplicitFormulaPhi f ((0 : ℂ) - 1 / 2))) := by
    have hcontinuous :
        ContinuousAt
          (fun z : ℂ => zetaCompletedExplicitFormulaPhi f (z - 1 / 2))
          (0 : ℂ) :=
      (zetaCompletedExplicitFormulaPhi_shift_differentiableAt hPhi (0 : ℂ)).continuousAt
    exact hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
  have htarget_arg : (0 : ℂ) - 1 / 2 = -(1 / 2 : ℂ) := by
    exact zero_sub (1 / 2 : ℂ)
  have hneg :
      Tendsto
        (fun z : ℂ => -zetaCompletedExplicitFormulaPhi f (z - 1 / 2))
        (𝓝[≠] (0 : ℂ))
        (𝓝 (-zetaCompletedExplicitFormulaPhi f ((0 : ℂ) - 1 / 2))) :=
    hphi.neg
  have hpointwise :
      (fun z : ℂ =>
        z *
          ((-1 / z) *
            zetaCompletedExplicitFormulaPhi f (z - 1 / 2))) =
       ᶠ[𝓝[≠] (0 : ℂ)]
      (fun z : ℂ => -zetaCompletedExplicitFormulaPhi f (z - 1 / 2)) := by
    exact
      self_mem_nhdsWithin.mono
        (fun z hz_ne =>
          zetaCompletedExplicitFormulaCorrectionZeroPole_localResidue_algebra
            z
            (zetaCompletedExplicitFormulaPhi f (z - 1 / 2))
            hz_ne)
  have hraw :
      Tendsto
        (fun z : ℂ =>
          z *
            ((-1 / z) *
              zetaCompletedExplicitFormulaPhi f (z - 1 / 2)))
        (𝓝[≠] (0 : ℂ))
        (𝓝 (-zetaCompletedExplicitFormulaPhi f ((0 : ℂ) - 1 / 2))) :=
    hpointwise.tendsto_iff.2 hneg
  exact Eq.subst
    (motive := fun w : ℂ =>
      Tendsto
        (fun z : ℂ =>
          z *
            ((-1 / z) *
              zetaCompletedExplicitFormulaPhi f (z - 1 / 2)))
        (𝓝[≠] (0 : ℂ))
        (𝓝 (-zetaCompletedExplicitFormulaPhi f w)))
    htarget_arg
    hraw

/-- The isolated `s = 0` correction kernel is differentiable away from its pole. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_differentiableAt_off_pole
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {z : ℂ} (hz : z ≠ 0) :
    DifferentiableAt ℂ
      (fun w : ℂ =>
        (-1 / w) *
          zetaCompletedExplicitFormulaPhi f (w - 1 / 2))
      z := by
  have hcoeff :
      DifferentiableAt ℂ (fun w : ℂ => -1 / w) z :=
    (differentiableAt_const (-(1 : ℂ))).div differentiableAt_id hz
  have hshift :
      DifferentiableAt ℂ
        (fun w : ℂ => zetaCompletedExplicitFormulaPhi f (w - 1 / 2))
        z :=
    zetaCompletedExplicitFormulaPhi_shift_differentiableAt hPhi z
  exact hcoeff.mul hshift

/-- The isolated `s = 0` correction kernel is continuous away from its pole. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_continuousAt_off_pole
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {z : ℂ} (hz : z ≠ 0) :
    ContinuousAt
      (fun w : ℂ =>
        (-1 / w) *
          zetaCompletedExplicitFormulaPhi f (w - 1 / 2))
      z :=
  (zetaCompletedExplicitFormulaCorrectionZeroPole_differentiableAt_off_pole
    f hPhi hz).continuousAt

/-- Boundary avoidance excludes the isolated `s = 0` correction pole. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_ne_of_avoidsBoundary
    (F : ExplicitFormulaContourFamily) (T : ℝ) {z : ℂ}
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T)
    (hboundary : z ∈ explicitFormulaContourFamilyBoundary F T) :
    z ≠ 0 := by
  intro hz
  have hsingular : explicitFormulaContourSingularPoint z :=
    Or.inl hz
  exact havoid z hsingular hboundary

/-- The isolated `s = 0` correction kernel is regular at every avoided boundary point. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_regularAt_boundary_of_avoidsBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hPhi : ZetaPhiAnalyticControl f) (T : ℝ) {z : ℂ}
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T)
    (hboundary : z ∈ explicitFormulaContourFamilyBoundary F T) :
    ContinuousAt
        (fun w : ℂ =>
          (-1 / w) *
            zetaCompletedExplicitFormulaPhi f (w - 1 / 2))
        z ∧
      DifferentiableAt ℂ
        (fun w : ℂ =>
          (-1 / w) *
            zetaCompletedExplicitFormulaPhi f (w - 1 / 2))
        z := by
  have hz :
      z ≠ 0 :=
    zetaCompletedExplicitFormulaCorrectionZeroPole_ne_of_avoidsBoundary
      F T havoid hboundary
  exact And.intro
    (zetaCompletedExplicitFormulaCorrectionZeroPole_continuousAt_off_pole f hPhi hz)
    (zetaCompletedExplicitFormulaCorrectionZeroPole_differentiableAt_off_pole f hPhi hz)

/-- The isolated `s = 0` correction kernel is regular at every boundary point of
an avoided rectangle. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_regularAt_all_boundary_points_of_avoidsBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hPhi : ZetaPhiAnalyticControl f) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    ∀ z : ℂ,
      z ∈ explicitFormulaContourFamilyBoundary F T →
        ContinuousAt
            (fun w : ℂ =>
              (-1 / w) *
                zetaCompletedExplicitFormulaPhi f (w - 1 / 2))
            z ∧
          DifferentiableAt ℂ
            (fun w : ℂ =>
              (-1 / w) *
                zetaCompletedExplicitFormulaPhi f (w - 1 / 2))
            z :=
  fun _ hz =>
    zetaCompletedExplicitFormulaCorrectionZeroPole_regularAt_boundary_of_avoidsBoundary
      f F hPhi T havoid hz

/-- The scheduled rectangles supply boundary regularity for the isolated `s = 0`
correction kernel at every scheduled height. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_scheduled_regularAt_all_boundary_points
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    ∀ z : ℂ,
      z ∈ explicitFormulaContourFamilyBoundary F (h.height_schedule.height u) →
        ContinuousAt
            (fun w : ℂ =>
              (-1 / w) *
                zetaCompletedExplicitFormulaPhi f (w - 1 / 2))
            z ∧
          DifferentiableAt ℂ
            (fun w : ℂ =>
              (-1 / w) *
                zetaCompletedExplicitFormulaPhi f (w - 1 / 2))
            z :=
  zetaCompletedExplicitFormulaCorrectionZeroPole_regularAt_all_boundary_points_of_avoidsBoundary
    f F h.phi_control (h.height_schedule.height u)
    (h.height_schedule.avoids_boundary u)

/-- The isolated `s = 0` correction kernel is continuous on every avoided rectangle
boundary. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_continuousOn_boundary_of_avoidsBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hPhi : ZetaPhiAnalyticControl f) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    ContinuousOn
      (fun w : ℂ =>
        (-1 / w) *
          zetaCompletedExplicitFormulaPhi f (w - 1 / 2))
      (explicitFormulaContourFamilyBoundary F T) := by
  intro z hz
  exact
    (zetaCompletedExplicitFormulaCorrectionZeroPole_regularAt_all_boundary_points_of_avoidsBoundary
      f F hPhi T havoid z hz).1.continuousWithinAt

/-- The scheduled rectangles supply boundary continuity for the isolated `s = 0`
correction kernel at every scheduled height. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_scheduled_continuousOn_boundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    ContinuousOn
      (fun w : ℂ =>
        (-1 / w) *
          zetaCompletedExplicitFormulaPhi f (w - 1 / 2))
      (explicitFormulaContourFamilyBoundary F (h.height_schedule.height u)) :=
  zetaCompletedExplicitFormulaCorrectionZeroPole_continuousOn_boundary_of_avoidsBoundary
    f F h.phi_control (h.height_schedule.height u)
    (h.height_schedule.avoids_boundary u)

/-- Positive-height residue inputs for the isolated `s = 0` correction kernel:
the pole is inside the rectangle, the kernel is regular on the avoided boundary,
and the local residue is the already computed zero-pole residue. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_tangentResidueInputs_of_pos_height
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hPhi : ZetaPhiAnalyticControl f) (T : ℝ)
    (hT : 0 < T)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    (0 : ℂ) ∈ explicitFormulaContourFamilyInterior F T ∧
      (∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt
              (fun w : ℂ =>
                zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f w)
              z ∧
            DifferentiableAt ℂ
              (fun w : ℂ =>
                zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f w)
              z) ∧
      Tendsto
        (fun z : ℂ =>
          z *
            zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        (𝓝[≠] (0 : ℂ))
        (𝓝 (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))) := by
  have hinterior :
      (0 : ℂ) ∈ explicitFormulaContourFamilyInterior F T :=
    explicitFormulaContourFamilyInterior_zero_mem F T hT
  have hregular :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt
              (fun w : ℂ =>
                zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f w)
              z ∧
            DifferentiableAt ℂ
              (fun w : ℂ =>
                zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f w)
              z :=
    zetaCompletedExplicitFormulaCorrectionZeroPole_regularAt_all_boundary_points_of_avoidsBoundary
      f F hPhi T havoid
  have hlocal :
      Tendsto
        (fun z : ℂ =>
          z *
            zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        (𝓝[≠] (0 : ℂ))
        (𝓝 (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))) :=
    zetaCompletedExplicitFormulaCorrectionZeroPole_localResidue_tendsto
      f hPhi
  exact And.intro hinterior (And.intro hregular hlocal)

/-- Scheduled residue inputs for the isolated `s = 0` correction kernel at
eventually positive heights. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_eventually_tangentResidueInputs
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ∀ᶠ u in atTop,
      (0 : ℂ) ∈ explicitFormulaContourFamilyInterior F (h.height_schedule.height u) ∧
        (∀ z : ℂ,
          z ∈ explicitFormulaContourFamilyBoundary F (h.height_schedule.height u) →
            ContinuousAt
                (fun w : ℂ =>
                  zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f w)
                z ∧
              DifferentiableAt ℂ
                (fun w : ℂ =>
                  zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f w)
                z) ∧
        Tendsto
          (fun z : ℂ =>
            z *
              zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
          (𝓝[≠] (0 : ℂ))
          (𝓝 (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))) := by
  exact h.height_schedule.eventually_height_pos.mono
    (fun u hu =>
      zetaCompletedExplicitFormulaCorrectionZeroPole_tangentResidueInputs_of_pos_height
        f F h.phi_control (h.height_schedule.height u) hu
        (h.height_schedule.avoids_boundary u))

/-- The residue coefficient `z * g(z)` of the zero-pole correction kernel is
continuous on every set with the pole removed. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_deletedCoefficient_continuousOn_deletedSet
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (s : Set ℂ) :
    ContinuousOn
      (fun z : ℂ =>
        z * zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
      (s \ ({(0 : ℂ)} : Set ℂ)) := by
  intro z hz
  have hz_not_mem : z ∉ ({(0 : ℂ)} : Set ℂ) :=
    hz.2
  have hz_ne : z ≠ 0 := by
    intro hzero
    have hz_mem : z ∈ ({(0 : ℂ)} : Set ℂ) :=
      hzero
    exact hz_not_mem hz_mem
  have hleft :
      ContinuousAt (fun w : ℂ => w) z :=
    continuous_id.continuousAt
  have hright :
      ContinuousAt
        (fun w : ℂ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f w)
        z :=
    zetaCompletedExplicitFormulaCorrectionZeroPole_continuousAt_off_pole
      f hPhi hz_ne
  exact (hleft.mul hright).continuousWithinAt

/-- The residue coefficient `z * g(z)` of the zero-pole correction kernel is
differentiable away from the removed singleton. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_deletedCoefficient_differentiableAt_of_not_mem_singleton
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {z : ℂ} (hz : z ∉ ({(0 : ℂ)} : Set ℂ)) :
    DifferentiableAt ℂ
      (fun w : ℂ =>
        w * zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f w)
      z := by
  have hz_ne : z ≠ 0 := by
    intro hzero
    have hz_mem : z ∈ ({(0 : ℂ)} : Set ℂ) :=
      hzero
    exact hz hz_mem
  have hleft :
      DifferentiableAt ℂ (fun w : ℂ => w) z :=
    differentiableAt_id
  have hright :
      DifferentiableAt ℂ
        (fun w : ℂ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f w)
        z :=
    zetaCompletedExplicitFormulaCorrectionZeroPole_differentiableAt_off_pole
      f hPhi hz_ne
  exact hleft.mul hright

/-- Zero-centered finite square boundary residue for the isolated `s = 0`
correction kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_finiteSquareBoundaryIntegral_eq_residue
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {R : ℝ} (hR : 0 < R) :
    finiteRectangleSquareBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        (0 : ℂ) R =
      (2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) := by
  have hcontinuous :
      ContinuousOn
        (fun z : ℂ =>
          (z - (0 : ℂ)) *
            zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        (([[(0 : ℂ).re - R, (0 : ℂ).re + R]] ×ℂ
          [[(0 : ℂ).im - R, (0 : ℂ).im + R]]) \
            ({(0 : ℂ)} : Set ℂ)) := by
    have hcoeff :
        (fun z : ℂ =>
          (z - (0 : ℂ)) *
            zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z) =
        (fun z : ℂ =>
          z * zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z) := by
      funext z
      exact congrArg
        (fun x : ℂ => x * zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        (sub_zero z)
    exact
      Eq.subst
        (motive := fun φ : ℂ → ℂ =>
          ContinuousOn φ
            (([[(0 : ℂ).re - R, (0 : ℂ).re + R]] ×ℂ
              [[(0 : ℂ).im - R, (0 : ℂ).im + R]]) \
                ({(0 : ℂ)} : Set ℂ)))
        hcoeff.symm
        (zetaCompletedExplicitFormulaCorrectionZeroPole_deletedCoefficient_continuousOn_deletedSet
          f hPhi
          ([[ (0 : ℂ).re - R, (0 : ℂ).re + R ]] ×ℂ
            [[ (0 : ℂ).im - R, (0 : ℂ).im + R ]]))
  have hdifferentiable :
      ∀ z : ℂ,
        z ∈
            ((Set.Ioo ((0 : ℂ).re - R) ((0 : ℂ).re + R) ×ℂ
                Set.Ioo ((0 : ℂ).im - R) ((0 : ℂ).im + R)) \
                ({(0 : ℂ)} : Set ℂ)) \ (∅ : Set ℂ) →
          DifferentiableAt ℂ
            (fun w : ℂ =>
              (w - (0 : ℂ)) *
                zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f w)
            z := by
    intro z hz
    have hcoeff :
        (fun w : ℂ =>
            (w - (0 : ℂ)) *
              zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f w) =
          (fun w : ℂ =>
            w * zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f w) := by
      funext w
      exact congrArg
        (fun x : ℂ => x * zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f w)
        (sub_zero w)
    exact
      Eq.subst
        (motive := fun φ : ℂ → ℂ => DifferentiableAt ℂ φ z)
        hcoeff.symm
        (zetaCompletedExplicitFormulaCorrectionZeroPole_deletedCoefficient_differentiableAt_of_not_mem_singleton
          f hPhi hz.1.2)
  have hfinite_square :
      finiteRectangleSquareBoundaryIntegral
          (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
          (0 : ℂ) R =
        (2 * (Real.pi : ℂ) * Complex.I) •
          (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) := by
    have hlocal :
        Tendsto
          (fun z : ℂ =>
            (z - (0 : ℂ)) *
              zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
          (𝓝[≠] (0 : ℂ))
          (𝓝 (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))) := by
      have hcoeff :
          (fun z : ℂ =>
            (z - (0 : ℂ)) *
              zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z) =
          (fun z : ℂ =>
            z * zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z) := by
        funext z
        exact congrArg
          (fun x : ℂ => x * zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
          (sub_zero z)
      exact
        Eq.subst
          (motive := fun φ : ℂ → ℂ =>
            Tendsto φ (𝓝[≠] (0 : ℂ))
              (𝓝 (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))))
          hcoeff.symm
          (zetaCompletedExplicitFormulaCorrectionZeroPole_localResidue_tendsto
            f hPhi)
    exact
      finiteRectangleSquareBoundaryIntegral_eq_twoPiI_smul_residue
        (0 : ℂ) hR
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))
        (∅ : Set ℂ)
        Set.countable_empty
        hcontinuous
        hdifferentiable
        hlocal
  calc
    finiteRectangleSquareBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        (0 : ℂ) R =
        (2 * (Real.pi : ℂ) * Complex.I) •
          (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) := hfinite_square
    _ = (2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) := by
      exact
        smul_eq_mul
          (2 * (Real.pi : ℂ) * Complex.I)
          (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))

/-- Radius-parametrized inner-square residue value for the isolated `s = 0`
correction kernel.

This is the inner-square component needed by the eventual zero-pole
standard-rectangle Cauchy assembly.  It deliberately does not assert the full
outer standard-boundary theorem; the square-punctured rectangle cancellation is
a separate contour input. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_innerSquareBoundary_eq_residue_of_radius
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {R : ℝ} (hR : 0 < R) :
    finiteRectangleSquareBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        (0 : ℂ) R =
      (2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) :=
  zetaCompletedExplicitFormulaCorrectionZeroPole_finiteSquareBoundaryIntegral_eq_residue
    f hPhi hR

/-- The normalized local residue value for the isolated `s = 0` correction
kernel.  This is the residue value that any finite single-pole rectangle theorem
for `zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral`
must return in the project normalization. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_localResidueValue
    (f : ZetaAdmissibleFunction) :
    -zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)) =
      -zetaCompletedExplicitFormulaPhi f ((0 : ℂ) - 1 / 2) := by
  exact congrArg (fun z : ℂ => -zetaCompletedExplicitFormulaPhi f z)
    (zero_sub (1 / 2 : ℂ)).symm

/-- The local residue target written at the literal pole coordinate is the same
as the corrected project-normalized residue value. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_localResidueCoordinateTarget_eq_projectTarget
    (f : ZetaAdmissibleFunction) :
    -zetaCompletedExplicitFormulaPhi f ((0 : ℂ) - 1 / 2) =
      -zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)) :=
  (zetaCompletedExplicitFormulaCorrectionZeroPole_localResidueValue f).symm

/-- The normalized local residue value for the isolated `s = 1` correction
kernel, written at the literal pole coordinate. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_localResidueValue
    (f : ZetaAdmissibleFunction) :
    -zetaCompletedExplicitFormulaPhi f (1 / 2) =
      -zetaCompletedExplicitFormulaPhi f ((1 : ℂ) - 1 / 2) := by
  exact congrArg (fun z : ℂ => -zetaCompletedExplicitFormulaPhi f z)
    (sub_half (1 : ℂ)).symm

/-- The local residue target written at the literal one-pole coordinate is the
same as the project-normalized `s = 1` residue value. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_localResidueCoordinateTarget_eq_projectTarget
    (f : ZetaAdmissibleFunction) :
    -zetaCompletedExplicitFormulaPhi f ((1 : ℂ) - 1 / 2) =
      -zetaCompletedExplicitFormulaPhi f (1 / 2) :=
  (zetaCompletedExplicitFormulaCorrectionOnePole_localResidueValue f).symm

/-- In the pole-enclosing geometry, the unordered horizontal span is the
left-to-right closed interval used by a standard rectangle boundary. -/
theorem zetaCompletedExplicitFormulaCorrectionPoleHorizontal_uIcc_eq_Icc
    (F : ExplicitFormulaContourFamily) :
    Set.uIcc F.c (1 - F.c) = Set.Icc (1 - F.c) F.c := by
  have hleft_le_right : 1 - F.c ≤ F.c :=
    le_of_lt
      (lt_trans F.one_sub_c_neg F.c_pos)
  exact Set.uIcc_of_ge hleft_le_right

/-- The top tangent edge of the isolated `s = 0` correction contour can be read
over the left-to-right horizontal interval. -/
theorem zetaCompletedExplicitFormulaCorrectionTopZeroPoleTangentIntegral_eq_Icc
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionTopZeroPoleTangentIntegral f F T =
      ∫ x in Set.Icc (1 - F.c) F.c,
        zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
          (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x) := by
  exact congrArg
    (fun s : Set ℝ =>
      ∫ x in s,
        zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
          (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x))
    (zetaCompletedExplicitFormulaCorrectionPoleHorizontal_uIcc_eq_Icc F)

/-- The bottom tangent edge of the isolated `s = 0` correction contour can be
read over the left-to-right horizontal interval. -/
theorem zetaCompletedExplicitFormulaCorrectionBottomZeroPoleTangentIntegral_eq_Icc
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionBottomZeroPoleTangentIntegral f F T =
      ∫ x in Set.Icc (1 - F.c) F.c,
        zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
          (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x) := by
  exact congrArg
    (fun s : Set ℝ =>
      ∫ x in s,
          zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
            (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x))
    (zetaCompletedExplicitFormulaCorrectionPoleHorizontal_uIcc_eq_Icc F)

/-- The isolated `s = 0` tangent rectangle boundary with the horizontal sides
written in left-to-right rectangle coordinates. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral_eq_IccHorizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral f F T =
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleTangentIntegral f F T -
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleTangentIntegral f F T +
          (∫ x in Set.Icc (1 - F.c) F.c,
            zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
              (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x)) -
            (∫ x in Set.Icc (1 - F.c) F.c,
              zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
                (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x)) := by
  let R : ℂ := zetaCompletedExplicitFormulaCorrectionRightZeroPoleTangentIntegral f F T
  let L : ℂ := zetaCompletedExplicitFormulaCorrectionLeftZeroPoleTangentIntegral f F T
  let U : ℂ := zetaCompletedExplicitFormulaCorrectionTopZeroPoleTangentIntegral f F T
  let B : ℂ := zetaCompletedExplicitFormulaCorrectionBottomZeroPoleTangentIntegral f F T
  let U' : ℂ :=
    ∫ x in Set.Icc (1 - F.c) F.c,
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
        (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x)
  let B' : ℂ :=
    ∫ x in Set.Icc (1 - F.c) F.c,
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x)
  have hU : U = U' :=
    zetaCompletedExplicitFormulaCorrectionTopZeroPoleTangentIntegral_eq_Icc
      f F T
  have hB : B = B' :=
    zetaCompletedExplicitFormulaCorrectionBottomZeroPoleTangentIntegral_eq_Icc
      f F T
  calc
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral f F T =
        R - L + U - B := by
      rfl
    _ = R - L + U' - B := by
      exact congrArg (fun x : ℂ => R - L + x - B) hU
    _ = R - L + U' - B' := by
      exact congrArg (fun x : ℂ => R - L + U' - x) hB

/-- The standard positively oriented rectangle boundary expression for the
isolated `s = 0` kernel, in Mathlib's rectangle-Cauchy convention. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  (∫ x in Set.Icc (1 - F.c) F.c,
    zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
      (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x)) -
    (∫ x in Set.Icc (1 - F.c) F.c,
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
        (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x)) +
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleTangentIntegral f F T -
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleTangentIntegral f F T

/-- The standard rectangle boundary expression unfolds to Mathlib's
bottom-minus-top plus right-minus-left tangent convention. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral f F T =
      (∫ x in Set.Icc (1 - F.c) F.c,
        zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
          (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x)) -
        (∫ x in Set.Icc (1 - F.c) F.c,
          zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
            (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x)) +
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleTangentIntegral f F T -
            zetaCompletedExplicitFormulaCorrectionLeftZeroPoleTangentIntegral f F T :=
  rfl

/-- The project-normalized standard rectangle boundary for the isolated
`s = 0` kernel.  The raw positively oriented contour has the usual `2πi`
factor; this object is the one whose finite Cauchy residue value is the local
residue itself. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionZeroPoleNormalizedStandardRectangleBoundaryIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral f F T

/-- The normalized standard rectangle boundary unfolds to `(2πi)⁻¹` times the
raw standard contour boundary. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleNormalizedStandardRectangleBoundaryIntegral_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleNormalizedStandardRectangleBoundaryIntegral
        f F T =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
          f F T :=
  rfl

/-- Transport from the raw standard finite Cauchy theorem, with its `2πi`
factor, to the project-normalized residue value. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleNormalizedStandardRectangleBoundaryIntegral_eq_residue_of_rawCauchy
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hraw :
      zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
        f F T =
        (2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleNormalizedStandardRectangleBoundaryIntegral
        f F T =
      -zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)) := by
  let C : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  let R : ℂ := -zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))
  have hnorm :
      zetaCompletedExplicitFormulaCorrectionZeroPoleNormalizedStandardRectangleBoundaryIntegral
          f F T =
        C⁻¹ *
          zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
            f F T := by
    rfl
  have hraw' :
      zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
        f F T = C * R :=
    hraw
  have hC_ne : C ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero
        (Complex.ofReal_ne_zero.mpr (show (2 : ℝ) ≠ 0 from two_ne_zero))
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  calc
    zetaCompletedExplicitFormulaCorrectionZeroPoleNormalizedStandardRectangleBoundaryIntegral
        f F T =
        C⁻¹ *
          zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
            f F T := hnorm
    _ = C⁻¹ * (C * R) := by
      exact congrArg (fun z : ℂ => C⁻¹ * z) hraw'
    _ = (C⁻¹ * C) * R := by
      exact (mul_assoc C⁻¹ C R).symm
    _ = 1 * R := by
      exact congrArg (fun z : ℂ => z * R) (inv_mul_cancel₀ hC_ne)
    _ = R := by
      exact one_mul R

/-- The zero-pole square-punctured boundary expression attached to a chosen
inner square radius.

This is only the algebraic outer-minus-inner boundary object.  Its vanishing is
the geometric Cauchy theorem still to be proved by a zero-pole punctured
rectangle owner. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionZeroPoleSquarePuncturedBoundaryIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T R : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral f F T -
    finiteRectangleSquareBoundaryIntegral
      (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
      (0 : ℂ) R

/-- The zero-pole square-punctured boundary unfolds to outer standard boundary
minus the zero-centered inner square boundary. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleSquarePuncturedBoundaryIntegral_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T R : ℝ) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleSquarePuncturedBoundaryIntegral
        f F T R =
      zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral f F T -
        finiteRectangleSquareBoundaryIntegral
          (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
          (0 : ℂ) R :=
  rfl

/-- If the zero-pole square-punctured boundary vanishes, the outer standard
boundary equals the zero-centered inner square boundary. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleStandardBoundary_eq_innerSquare_of_squarePunctured_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T R : ℝ)
    (hcauchy :
      zetaCompletedExplicitFormulaCorrectionZeroPoleSquarePuncturedBoundaryIntegral
        f F T R = 0) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
        f F T =
      finiteRectangleSquareBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        (0 : ℂ) R := by
  let S : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
      f F T
  let I : ℂ :=
    finiteRectangleSquareBoundaryIntegral
      (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
      (0 : ℂ) R
  have hsub : S - I = 0 := by
    calc
      S - I =
          zetaCompletedExplicitFormulaCorrectionZeroPoleSquarePuncturedBoundaryIntegral
            f F T R := by
        rfl
      _ = 0 := hcauchy
  calc
    zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
        f F T = S := by
      rfl
    _ = (S - I) + I := by
      exact (sub_add_cancel S I).symm
    _ = 0 + I := by
      exact congrArg (fun z : ℂ => z + I) hsub
    _ =
      finiteRectangleSquareBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        (0 : ℂ) R := by
      exact zero_add I

/-- Algebraic raw Cauchy assembly for the isolated `s = 0` correction kernel
from an outer-boundary/inner-square identification.

The missing contour theorem for `s = 0` is precisely the boundary
identification supplied here as `hboundary`.  Once that geometric
square-punctured cancellation has been proved in its owner layer, this lemma
turns it into the raw standard rectangle Cauchy value. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_boundary_eq_innerSquare
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hPhi : ZetaPhiAnalyticControl f) (T : ℝ) {R : ℝ}
    (hR : 0 < R)
    (hboundary :
      zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
        f F T =
      finiteRectangleSquareBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        (0 : ℂ) R) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
      f F T =
      (2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) := by
  exact
    Eq.trans hboundary
      (zetaCompletedExplicitFormulaCorrectionZeroPole_innerSquareBoundary_eq_residue_of_radius
        f hPhi hR)

/-- Scheduled form of the zero-pole raw Cauchy assembly from an eventual
outer-boundary/inner-square identification.

This theorem is the exact consumer needed by the scheduled transport layer
after the zero-pole square-punctured contour identity has been established. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_eventually_standardBoundaryResidueValue_of_eventual_boundary_eq_innerSquare
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (R : ℝ)
    (hR : 0 < R)
    (hboundary :
      ∀ᶠ u in atTop,
        zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
          f F (h.height_schedule.height u) =
        finiteRectangleSquareBoundaryIntegral
          (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
          (0 : ℂ) R) :
    ∀ᶠ u in atTop,
      zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
        f F (h.height_schedule.height u) =
      (2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) := by
  exact hboundary.mono
    (fun u hu =>
      zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_boundary_eq_innerSquare
        f F h.phi_control (h.height_schedule.height u) hR hu)

/-- Raw Cauchy assembly for the isolated `s = 0` correction kernel from
square-punctured boundary cancellation and the inner-square residue value. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_squarePunctured_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hPhi : ZetaPhiAnalyticControl f) (T : ℝ) {R : ℝ}
    (hR : 0 < R)
    (hcauchy :
      zetaCompletedExplicitFormulaCorrectionZeroPoleSquarePuncturedBoundaryIntegral
        f F T R = 0) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
      f F T =
      (2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) := by
  have hboundary :
      zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
        f F T =
      finiteRectangleSquareBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        (0 : ℂ) R :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleStandardBoundary_eq_innerSquare_of_squarePunctured_zero
      f F T R hcauchy
  exact
    zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_boundary_eq_innerSquare
      f F hPhi T hR hboundary

/-- The canonical zero-pole puncture radius attached to a positive-height
rectangle is positive. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_punctureRadius_pos_of_pos_height
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T) :
    0 < zetaExplicitFormulaZeroPolePunctureRadius F T :=
  zetaExplicitFormulaZeroPolePunctureRadius_pos F hT

/-- The canonical zero-pole puncture radius lies inside the right horizontal
margin of a positive-height contour. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_punctureRadius_lt_rightMargin_of_pos_height
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T) :
    zetaExplicitFormulaZeroPolePunctureRadius F T < F.c :=
  zetaExplicitFormulaZeroPolePunctureRadius_lt_rightMargin F hT

/-- The canonical zero-pole puncture radius lies inside the left horizontal
margin of a positive-height contour. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_punctureRadius_lt_leftMargin_of_pos_height
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T) :
    zetaExplicitFormulaZeroPolePunctureRadius F T < F.c - 1 :=
  zetaExplicitFormulaZeroPolePunctureRadius_lt_leftMargin F hT

/-- The canonical zero-pole puncture radius is strictly below the contour
height. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_punctureRadius_lt_height_of_pos_height
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T) :
    zetaExplicitFormulaZeroPolePunctureRadius F T < T :=
  zetaExplicitFormulaZeroPolePunctureRadius_lt_height F hT

/-- Canonical inner-square residue value for the isolated `s = 0` correction
kernel at positive height. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_canonicalInnerSquareBoundary_eq_residue_of_pos_height
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hPhi : ZetaPhiAnalyticControl f)
    {T : ℝ}
    (hT : 0 < T) :
    finiteRectangleSquareBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        (0 : ℂ)
        (zetaExplicitFormulaZeroPolePunctureRadius F T) =
      (2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) := by
  have hR :
      0 < zetaExplicitFormulaZeroPolePunctureRadius F T :=
    zetaCompletedExplicitFormulaCorrectionZeroPole_punctureRadius_pos_of_pos_height
      F hT
  exact
    zetaCompletedExplicitFormulaCorrectionZeroPole_innerSquareBoundary_eq_residue_of_radius
      f hPhi hR

/-- Positive-height raw standard Cauchy assembly from canonical zero-pole
square-punctured cancellation. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_pos_height_canonicalSquarePunctured_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hPhi : ZetaPhiAnalyticControl f) {T : ℝ}
    (hT : 0 < T)
    (hcauchy :
      zetaCompletedExplicitFormulaCorrectionZeroPoleSquarePuncturedBoundaryIntegral
        f F T (zetaExplicitFormulaZeroPolePunctureRadius F T) = 0) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
      f F T =
      (2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) := by
  have hR :
      0 < zetaExplicitFormulaZeroPolePunctureRadius F T :=
    zetaCompletedExplicitFormulaCorrectionZeroPole_punctureRadius_pos_of_pos_height
      F hT
  exact
    zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_squarePunctured_zero
      f F hPhi T hR hcauchy

/-- Scheduled raw Cauchy assembly for the isolated `s = 0` correction kernel
from eventual square-punctured boundary cancellation. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_eventually_standardBoundaryResidueValue_of_eventual_squarePunctured_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (R : ℝ)
    (hR : 0 < R)
    (hcauchy :
      ∀ᶠ u in atTop,
        zetaCompletedExplicitFormulaCorrectionZeroPoleSquarePuncturedBoundaryIntegral
          f F (h.height_schedule.height u) R = 0) :
    ∀ᶠ u in atTop,
      zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
        f F (h.height_schedule.height u) =
      (2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) := by
  exact hcauchy.mono
    (fun u hu =>
      zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_squarePunctured_zero
        f F h.phi_control (h.height_schedule.height u) hR hu)

/-- Scheduled raw Cauchy assembly for the isolated `s = 0` correction kernel
from eventual cancellation at the canonical zero-pole puncture radius. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_eventually_standardBoundaryResidueValue_of_eventual_canonicalSquarePunctured_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hcauchy :
      ∀ᶠ u in atTop,
        zetaCompletedExplicitFormulaCorrectionZeroPoleSquarePuncturedBoundaryIntegral
          f F (h.height_schedule.height u)
          (zetaExplicitFormulaZeroPolePunctureRadius
            F (h.height_schedule.height u)) = 0) :
    ∀ᶠ u in atTop,
      zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
        f F (h.height_schedule.height u) =
      (2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) := by
  have hboth :
      ∀ᶠ u in atTop,
        0 < h.height_schedule.height u ∧
          zetaCompletedExplicitFormulaCorrectionZeroPoleSquarePuncturedBoundaryIntegral
            f F (h.height_schedule.height u)
            (zetaExplicitFormulaZeroPolePunctureRadius
              F (h.height_schedule.height u)) = 0 :=
    h.height_schedule.eventually_height_pos.and hcauchy
  exact hboth.mono
    (fun u hu =>
      match hu with
      | ⟨hT, hcauchy_u⟩ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_pos_height_canonicalSquarePunctured_zero
            f F h.phi_control hT hcauchy_u)

/-- A positive-height raw standard Cauchy theorem supplies the corresponding
scheduled raw zero-pole standard boundary value eventually. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_eventually_standardBoundaryResidueValue_of_positiveHeight_rawCauchy
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hpositive :
      ∀ T : ℝ,
        0 < T →
          zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
            f F T =
            (2 * (Real.pi : ℂ) * Complex.I) *
              (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))) :
    ∀ᶠ u in atTop,
      zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
        f F (h.height_schedule.height u) =
        (2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) := by
  exact h.height_schedule.eventually_height_pos.mono
    (fun u hu =>
      hpositive (h.height_schedule.height u) hu)

/-- A positive-height raw standard Cauchy theorem gives the scheduled normalized
zero-pole standard boundary value equal to the local residue. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_eventually_normalizedStandardBoundaryResidueValue_of_positiveHeight_rawCauchy
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hpositive :
      ∀ T : ℝ,
        0 < T →
          zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
            f F T =
            (2 * (Real.pi : ℂ) * Complex.I) *
              (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))) :
    ∀ᶠ u in atTop,
      zetaCompletedExplicitFormulaCorrectionZeroPoleNormalizedStandardRectangleBoundaryIntegral
        f F (h.height_schedule.height u) =
        -zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)) := by
  exact h.height_schedule.eventually_height_pos.mono
    (fun u hu =>
      zetaCompletedExplicitFormulaCorrectionZeroPoleNormalizedStandardRectangleBoundaryIntegral_eq_residue_of_rawCauchy
        f F (h.height_schedule.height u)
        (hpositive (h.height_schedule.height u) hu))

/-- The exact orientation defect between the project's tangent side convention
and the standard positively oriented rectangle boundary. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral f F T -
    zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral f F T

/-- The project tangent boundary is the standard rectangle-Cauchy boundary plus
the explicit orientation defect. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral_eq_standard_add_orientationDefect
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral f F T =
      zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral f F T +
        zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect f F T := by
  let P : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral f F T
  let S : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral f F T
  have hsum : S + (P - S) = P := by
    calc
      S + (P - S) = (P - S) + S := by
        exact add_comm S (P - S)
      _ = P := by
        exact sub_add_cancel P S
  calc
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral f F T = P := by
      rfl
    _ = S + (P - S) := by
      exact hsum.symm
    _ =
        zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral f F T +
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect f F T := by
      rfl

/-- Scheduled form of the project/standard tangent-boundary orientation
decomposition for the isolated `s = 0` kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledTangentBoundary_eq_standard_add_orientationDefect
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
        f F (h.height_schedule.height u) =
      zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
          f F (h.height_schedule.height u) +
        zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect
          f F (h.height_schedule.height u) :=
  zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral_eq_standard_add_orientationDefect
    f F (h.height_schedule.height u)

/-- Additive algebra for the project/standard horizontal orientation defect. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_orientationDefect_horizontal_algebra
    (A H : ℂ) :
    (A + H) - (A - H) = H + H :=
  explicitFormula_orientationDefect_horizontal_algebra A H

/-- Additive algebra putting the standard rectangle horizontal convention in
`right-minus-left` plus negative horizontal-remainder form. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_standardBoundary_horizontal_algebra
    (R L U B : ℂ) :
    B - U + R - L = R - L - (U - B) :=
  explicitFormula_standardBoundary_horizontal_algebra R L U B

/-- The scheduled project/standard orientation defect is exactly two copies of
the scheduled horizontal zero-pole remainder. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledOrientationDefect_eq_horizontal_add_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect
        f F (h.height_schedule.height u) =
      zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u +
        zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u := by
  let T : ℝ := h.height_schedule.height u
  let R : ℂ := zetaCompletedExplicitFormulaCorrectionRightZeroPoleTangentIntegral f F T
  let L : ℂ := zetaCompletedExplicitFormulaCorrectionLeftZeroPoleTangentIntegral f F T
  let U : ℂ := zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral f F T
  let B : ℂ := zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral f F T
  let P : ℂ := zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral f F T
  let S : ℂ := zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral f F T
  let H : ℂ := zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference f F h u
  have hP : P = R - L + U - B :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral_eq_verticalTangent_add_horizontal
      f F T
  have hS : S = B - U + R - L := by
    rfl
  have hH : H = U - B := by
    rfl
  let A : ℂ := R - L
  have hP_AH : P = A + H := by
    calc
      P = R - L + U - B := hP
      _ = (R - L) + (U - B) := by
        exact (add_sub_assoc (R - L) U B).symm
      _ = A + (U - B) := by
        rfl
      _ = A + H := by
        exact congrArg (fun x : ℂ => A + x) hH.symm
  have hS_AH : S = A - H := by
    calc
      S = B - U + R - L := hS
      _ = R - L - (U - B) := by
        exact
          zetaCompletedExplicitFormulaCorrectionZeroPole_standardBoundary_horizontal_algebra
            R L U B
      _ = A - (U - B) := by
        rfl
      _ = A - H := by
        exact congrArg (fun x : ℂ => A - x) hH.symm
  have hdef : zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect f F T = P - S := by
    rfl
  have hmain : P - S = H + H := by
    calc
      P - S = (A + H) - S := by
        exact congrArg (fun x : ℂ => x - S) hP_AH
      _ = (A + H) - (A - H) := by
        exact congrArg (fun x : ℂ => (A + H) - x) hS_AH
      _ = H + H :=
        zetaCompletedExplicitFormulaCorrectionZeroPole_orientationDefect_horizontal_algebra
          A H
  calc
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect
        f F (h.height_schedule.height u) =
        P - S := hdef
    _ = H + H := hmain
    _ =
      zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u +
        zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u := by
      rfl

/-- The scheduled project/standard orientation defect tends to zero because it
is two copies of the already controlled scheduled horizontal zero-pole
remainder. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect_tendsto_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  have hhorizontal :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u)
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_tendsto_zero
      f F h
  have hsum :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u +
            zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u)
        atTop
        (𝓝 (0 + 0)) :=
    hhorizontal.add hhorizontal
  have hsum_zero :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u +
            zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u)
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
                f F h u +
              zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
                f F h u)
          atTop
          (𝓝 z))
      (zero_add 0)
      hsum
  have heq :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect
          f F (h.height_schedule.height u)) =
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u +
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u) := by
    funext u
    exact
      zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledOrientationDefect_eq_horizontal_add_horizontal
        f F h u
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    heq.symm
    hsum_zero

/-- The scheduled rectangles supply boundary regularity for the isolated `s = 1`
correction kernel at every scheduled height. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_scheduled_regularAt_all_boundary_points
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    ∀ z : ℂ,
      z ∈ explicitFormulaContourFamilyBoundary F (h.height_schedule.height u) →
        ContinuousAt
            (fun w : ℂ =>
              (-1 / (w - 1)) *
                zetaCompletedExplicitFormulaPhi f (w - 1 / 2))
            z ∧
          DifferentiableAt ℂ
            (fun w : ℂ =>
              (-1 / (w - 1)) *
                zetaCompletedExplicitFormulaPhi f (w - 1 / 2))
            z :=
  zetaCompletedExplicitFormulaCorrectionOnePole_regularAt_all_boundary_points_of_avoidsBoundary
    f F h.phi_control (h.height_schedule.height u)
    (h.height_schedule.avoids_boundary u)

/-- The scheduled rectangles supply boundary regularity for the named isolated
`s = 1` correction kernel at every scheduled height. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleKernel_scheduled_regularAt_all_boundary_points
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    ∀ z : ℂ,
      z ∈ explicitFormulaContourFamilyBoundary F (h.height_schedule.height u) →
        ContinuousAt
            (fun w : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f w)
            z ∧
          DifferentiableAt ℂ
            (fun w : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f w)
            z :=
  zetaCompletedExplicitFormulaCorrectionOnePoleKernel_regularAt_all_boundary_points_of_avoidsBoundary
    f F h.phi_control (h.height_schedule.height u)
    (h.height_schedule.avoids_boundary u)

/-- The scheduled rectangles supply boundary continuity for the isolated `s = 1`
correction kernel at every scheduled height. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_scheduled_continuousOn_boundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    ContinuousOn
      (fun w : ℂ =>
        (-1 / (w - 1)) *
          zetaCompletedExplicitFormulaPhi f (w - 1 / 2))
      (explicitFormulaContourFamilyBoundary F (h.height_schedule.height u)) :=
  zetaCompletedExplicitFormulaCorrectionOnePole_continuousOn_boundary_of_avoidsBoundary
    f F h.phi_control (h.height_schedule.height u)
    (h.height_schedule.avoids_boundary u)

/-- The scheduled rectangles supply boundary continuity for the named isolated
`s = 1` correction kernel at every scheduled height. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleKernel_scheduled_continuousOn_boundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    ContinuousOn
      (fun w : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f w)
      (explicitFormulaContourFamilyBoundary F (h.height_schedule.height u)) :=
  zetaCompletedExplicitFormulaCorrectionOnePoleKernel_continuousOn_boundary_of_avoidsBoundary
    f F h.phi_control (h.height_schedule.height u)
    (h.height_schedule.avoids_boundary u)

/-- Scheduled residue inputs for the isolated `s = 1` correction kernel at
eventually positive heights. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_eventually_tangentResidueInputs
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ∀ᶠ u in atTop,
      (1 : ℂ) ∈ explicitFormulaContourFamilyInterior F (h.height_schedule.height u) ∧
        (∀ z : ℂ,
          z ∈ explicitFormulaContourFamilyBoundary F (h.height_schedule.height u) →
            ContinuousAt
                (fun w : ℂ =>
                  zetaCompletedExplicitFormulaCorrectionOnePoleKernel f w)
                z ∧
              DifferentiableAt ℂ
                (fun w : ℂ =>
                  zetaCompletedExplicitFormulaCorrectionOnePoleKernel f w)
                z) ∧
        Tendsto
          (fun z : ℂ =>
            (z - 1) *
              zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
          (𝓝[≠] (1 : ℂ))
          (𝓝 (-zetaCompletedExplicitFormulaPhi f (1 / 2))) := by
  exact h.height_schedule.eventually_height_pos.mono
    (fun u hu =>
      zetaCompletedExplicitFormulaCorrectionOnePole_tangentResidueInputs_of_pos_height
        f F h.phi_control (h.height_schedule.height u) hu
        (h.height_schedule.avoids_boundary u))

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
