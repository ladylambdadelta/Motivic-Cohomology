import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.CorrectionPoleSides

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
    (A + H) - (A - H) = H + H := by
  have hsum :
      (A - H) + (H + H) = A + H := by
    calc
      (A - H) + (H + H) = (A + -H) + (H + H) := by
        exact congrArg (fun x : ℂ => x + (H + H)) (sub_eq_add_neg A H)
      _ = A + (-H + (H + H)) := by
        exact add_assoc A (-H) (H + H)
      _ = A + ((-H + H) + H) := by
        exact congrArg (fun x : ℂ => A + x) (add_assoc (-H) H H).symm
      _ = A + (0 + H) := by
        exact congrArg (fun x : ℂ => A + (x + H)) (neg_add_cancel H)
      _ = A + H := by
        exact congrArg (fun x : ℂ => A + x) (zero_add H)
  exact eq_sub_of_add_eq' hsum

/-- Additive algebra putting the standard rectangle horizontal convention in
`right-minus-left` plus negative horizontal-remainder form. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_standardBoundary_horizontal_algebra
    (R L U B : ℂ) :
    B - U + R - L = R - L - (U - B) := by
  calc
    B - U + R - L = (B + -U) + R - L := by
      exact congrArg (fun x : ℂ => x + R - L) (sub_eq_add_neg B U)
    _ = R + (B + -U) - L := by
      exact congrArg (fun x : ℂ => x - L) (add_comm (B + -U) R)
    _ = R + (B - U) - L := by
      exact congrArg (fun x : ℂ => R + x - L) (sub_eq_add_neg B U).symm
    _ = R + (B - U + -L) := by
      exact sub_eq_add_neg (R + (B - U)) L
    _ = R + (-L + (B - U)) := by
      exact congrArg (fun x : ℂ => R + x) (add_comm (B - U) (-L))
    _ = R + -L + (B - U) := by
      exact (add_assoc R (-L) (B - U)).symm
    _ = R - L + (B - U) := by
      exact congrArg (fun x : ℂ => x + (B - U)) (sub_eq_add_neg R L).symm
    _ = R - L + -(U - B) := by
      exact congrArg (fun x : ℂ => R - L + x) (neg_sub U B).symm
    _ = R - L - (U - B) := by
      exact (sub_eq_add_neg (R - L) (U - B)).symm

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

/-- Right-face one-pole Cauchy limit for the `s = 0` correction pole. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral_tendsto_centeredPolePhi_ownerChannelTransportAnalytic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 ((1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0)) := by
  sorry

/-- The scheduled right-face off-pole `s = 1` correction integral, isolated as
the object controlled by the contour-cancellation argument. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  ∫ t in
      Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      (-1 /
          (zetaCompletedExplicitFormulaRightPath
              (F.rectangle (h.height_schedule.height u)) t - 1)) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath
              (F.rectangle (h.height_schedule.height u)) t - 1 / 2)

/-- The scheduled Cauchy/oscillatory cancellation package for the right-face
off-pole `s = 1` correction integral.

This is the analytic step obtained by applying the scheduled contour
cancellation or integration-by-parts package to the fixed-displacement
vertical face.  The inverse-quadratic decay is not a pointwise
denominator-separation consequence. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePole_scheduledRectangleCauchyCancellation_ownerGap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
          f F h u‖
          ≤
            ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖ +
              A *
                (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  sorry


end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
