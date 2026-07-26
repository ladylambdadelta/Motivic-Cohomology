import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleTangentResidueTransport
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleHorizontalEdgeBounds

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

/-- The late left-face off-pole `s = 0` vertical integral isolated from the
single-pole rectangle boundary identity. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_eq_right_add_horizontal_sub_boundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
        f F (h.height_schedule.height u) =
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
          f F (h.height_schedule.height u) +
        zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u -
        zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
          f F (h.height_schedule.height u) := by
  let R : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
      f F (h.height_schedule.height u)
  let L : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
      f F (h.height_schedule.height u)
  let H : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
      f F h u
  let C : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
      f F (h.height_schedule.height u)
  have hC : C = R - L + H :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledRectangleBoundaryIntegral_eq_vertical_add_horizontal
      f F h u
  change L = R + H - C
  exact leftSide_eq_right_add_horizontal_sub_boundary_of_boundary_eq R L H C hC

/-- The late left-face off-pole `s = 0` vertical integral is bounded by the
right-boundary defect and the `s = 0` horizontal remainder. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_norm_le_boundaryDefect_add_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
        f F (h.height_schedule.height u)‖
      ≤
        ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u) -
          zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
            f F (h.height_schedule.height u)‖ +
        ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u‖ := by
  let R : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
      f F (h.height_schedule.height u)
  let L : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
      f F (h.height_schedule.height u)
  let H : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
      f F h u
  let C : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
      f F (h.height_schedule.height u)
  have hL : L = R + H - C :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_eq_right_add_horizontal_sub_boundary
      f F h u
  have hrepack : R + H - C = (R - C) + H := by
    calc
      R + H - C = (R + H) + -C := by
        exact sub_eq_add_neg (R + H) C
      _ = R + H + -C := by
        rfl
      _ = R + (H + -C) := by
        exact add_assoc R H (-C)
      _ = R + (-C + H) := by
        exact congrArg (fun x : ℂ => R + x) (add_comm H (-C))
      _ = (R + -C) + H := by
        exact (add_assoc R (-C) H).symm
      _ = (R - C) + H := by
        exact congrArg (fun x : ℂ => x + H) (sub_eq_add_neg R C).symm
  have hL_repack : L = (R - C) + H :=
    Eq.trans hL hrepack
  have hnorm :
      ‖(R - C) + H‖ ≤ ‖R - C‖ + ‖H‖ :=
    norm_add_le (R - C) H
  exact Eq.subst
    (motive := fun z : ℂ => ‖z‖ ≤ ‖R - C‖ + ‖H‖)
    hL_repack.symm
    hnorm

/-- Finite zero-pole Cauchy bookkeeping: the boundary defect of the right
zero-pole face is exactly the left face minus the isolated zero-pole horizontal
remainder. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleBoundaryDefect_eq_left_sub_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
        f F (h.height_schedule.height u) -
      zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
        f F (h.height_schedule.height u) =
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
        f F (h.height_schedule.height u) -
      zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
        f F h u := by
  let R : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
      f F (h.height_schedule.height u)
  let L : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
      f F (h.height_schedule.height u)
  let H : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
      f F h u
  let C : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
      f F (h.height_schedule.height u)
  have hC : C = R - L + H :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledRectangleBoundaryIntegral_eq_vertical_add_horizontal
      f F h u
  change R - C = L - H
  calc
    R - C = R + -C := by
      exact sub_eq_add_neg R C
    _ = R + -(R - L + H) := by
      exact congrArg (fun x : ℂ => R + -x) hC
    _ = R + -((R - L) + H) := by
      rfl
    _ = R + (-(R - L) + -H) := by
      exact congrArg (fun x : ℂ => R + x) (neg_add (R - L) H)
    _ = R + (-(R + -L) + -H) := by
      exact congrArg
        (fun x : ℂ => R + (-x + -H))
        (sub_eq_add_neg R L)
    _ = R + ((-(R + -L)) + -H) := by
      rfl
    _ = R + ((-R + -(-L)) + -H) := by
      exact congrArg
        (fun x : ℂ => R + (x + -H))
        (neg_add R (-L))
    _ = R + ((-R + L) + -H) := by
      exact congrArg
        (fun x : ℂ => R + ((-R + x) + -H))
        (neg_neg L)
    _ = (R + (-R + L)) + -H := by
      exact (add_assoc R (-R + L) (-H)).symm
    _ = ((R + -R) + L) + -H := by
      exact congrArg (fun x : ℂ => x + -H) (add_assoc R (-R) L).symm
    _ = (0 + L) + -H := by
      exact congrArg (fun x : ℂ => (x + L) + -H) (add_right_neg R)
    _ = L + -H := by
      exact congrArg (fun x : ℂ => x + -H) (zero_add L)
    _ = L - H := by
      exact (sub_eq_add_neg L H).symm

/-- Norm bound for the finite zero-pole boundary defect exposed by the
single-pole rectangle identity. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleBoundaryDefect_norm_le_left_add_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
        f F (h.height_schedule.height u) -
      zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
        f F (h.height_schedule.height u)‖
      ≤
        ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
          f F (h.height_schedule.height u)‖ +
        ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u‖ := by
  let R : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
      f F (h.height_schedule.height u)
  let L : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
      f F (h.height_schedule.height u)
  let H : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
      f F h u
  let C : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
      f F (h.height_schedule.height u)
  have hdefect : R - C = L - H :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleBoundaryDefect_eq_left_sub_horizontal
      f F h u
  have hnorm : ‖L - H‖ ≤ ‖L‖ + ‖H‖ :=
    norm_sub_le L H
  exact Eq.subst
    (motive := fun z : ℂ => ‖z‖ ≤ ‖L‖ + ‖H‖)
    hdefect.symm
    hnorm

/-- Quantitative bookkeeping for the finite zero-pole boundary defect.

Once the true single-pole Cauchy estimate gives an inverse-quadratic bound for
the left off-pole face, this lemma combines it with the isolated horizontal
estimate and produces the exact right-boundary defect bound needed by the
scheduled rectangle cancellation theorem. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleBoundaryDefect_inverseQuadratic_of_left_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (A B : ℝ)
    (hApos : 0 < A)
    (hBpos : 0 < B)
    (hleft :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
          f F (h.height_schedule.height u)‖
          ≤ A *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)))
    (hhorizontal :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u‖
          ≤ B *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u) -
          zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
            f F (h.height_schedule.height u)‖
          ≤ C *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  refine ⟨A + B, add_pos hApos hBpos, ?_⟩
  intro u
  let q : ℝ :=
    (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))
  let D : ℝ :=
    ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
        f F (h.height_schedule.height u) -
      zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
        f F (h.height_schedule.height u)‖
  let L : ℝ :=
    ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
      f F (h.height_schedule.height u)‖
  let H : ℝ :=
    ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
      f F h u‖
  have hdefect : D ≤ L + H :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleBoundaryDefect_norm_le_left_add_horizontal
      f F h u
  have hL : L ≤ A * q :=
    hleft u
  have hH : H ≤ B * q :=
    hhorizontal u
  have hsum : L + H ≤ A * q + B * q :=
    add_le_add hL hH
  have hfactor : A * q + B * q = (A + B) * q :=
    (add_mul A B q).symm
  exact le_trans hdefect (le_trans hsum (le_of_eq hfactor))

/-- The finite zero-pole boundary defect tends to zero once the left off-pole
face tends to zero.  The only additional input is the isolated horizontal
remainder, already proved above. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleBoundaryDefect_tendsto_zero_of_leftZeroPole
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hleft :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u) -
          zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
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
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_tendsto_zero_ownerZeroPoleHorizontal
      f F h
  have hsub :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u)
        atTop
        (𝓝 (0 - 0)) :=
    hleft.sub hhorizontal
  have hsub_zero :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u)
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
                f F (h.height_schedule.height u) -
              zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
                f F h u)
          atTop
          (𝓝 z))
      (sub_zero (0 : ℂ))
      hsub
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u) -
          zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
            f F (h.height_schedule.height u)) =
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u) := by
    funext u
    exact
      zetaCompletedExplicitFormulaCorrectionZeroPoleBoundaryDefect_eq_left_sub_horizontal
        f F h u
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    hsub_zero

/-- The finite zero-pole boundary defect and the left off-pole face have the
same scheduled limit behavior, since their difference is the isolated horizontal
remainder and that remainder vanishes. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleBoundaryDefect_tendsto_zero_iff_leftZeroPole
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u) -
          zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
            f F (h.height_schedule.height u))
      atTop
      (𝓝 0) ↔
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  constructor
  · intro hboundary
    have hhorizontal :
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u)
          atTop
          (𝓝 0) :=
      zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_tendsto_zero_ownerZeroPoleHorizontal
        f F h
    have hadd :
        Tendsto
          (fun u : ℝ =>
            (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
                f F (h.height_schedule.height u) -
              zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
                f F (h.height_schedule.height u)) +
            zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u)
          atTop
          (𝓝 (0 + 0)) :=
      hboundary.add hhorizontal
    have hadd_zero :
        Tendsto
          (fun u : ℝ =>
            (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
                f F (h.height_schedule.height u) -
              zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
                f F (h.height_schedule.height u)) +
            zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u)
          atTop
          (𝓝 0) :=
      Eq.subst
        (motive := fun z : ℂ =>
          Tendsto
            (fun u : ℝ =>
              (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
                  f F (h.height_schedule.height u) -
                zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
                  f F (h.height_schedule.height u)) +
              zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
                f F h u)
            atTop
            (𝓝 z))
        (zero_add 0)
        hadd
    have hpointwise :
        (fun u : ℝ =>
          (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
              f F (h.height_schedule.height u)) +
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u) =
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
              f F (h.height_schedule.height u)) := by
      funext u
      let R : ℂ :=
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
          f F (h.height_schedule.height u)
      let L : ℂ :=
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
          f F (h.height_schedule.height u)
      let H : ℂ :=
        zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u
      let C : ℂ :=
        zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
          f F (h.height_schedule.height u)
      have hdefect : R - C = L - H :=
        zetaCompletedExplicitFormulaCorrectionZeroPoleBoundaryDefect_eq_left_sub_horizontal
          f F h u
      change (R - C) + H = L
      calc
        (R - C) + H = (L - H) + H := by
          exact congrArg (fun x : ℂ => x + H) hdefect
        _ = (L + -H) + H := by
          exact congrArg (fun x : ℂ => x + H) (sub_eq_add_neg L H)
        _ = L + (-H + H) := by
          exact add_assoc L (-H) H
        _ = L + 0 := by
          exact congrArg (fun x : ℂ => L + x) (neg_add_cancel H)
        _ = L := by
          exact add_zero L
    exact Eq.subst
      (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
      hpointwise
      hadd_zero
  · intro hleft
    exact
      zetaCompletedExplicitFormulaCorrectionZeroPoleBoundaryDefect_tendsto_zero_of_leftZeroPole
        f F h hleft

/-- The named scheduled left-face `s = 0` oscillatory integral satisfies the same
boundary-defect plus horizontal-remainder bound as the corresponding vertical integral. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_norm_le_boundaryDefect_add_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
        f F h u‖
      ≤
        ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u) -
          zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
            f F (h.height_schedule.height u)‖ +
        ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u‖ := by
  have hnamed :
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
          f F (h.height_schedule.height u) =
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u :=
    rfl
  exact Eq.subst
    (motive := fun z : ℂ =>
      ‖z‖
        ≤
          ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
              f F (h.height_schedule.height u)‖ +
          ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u‖)
    hnamed
    (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_norm_le_boundaryDefect_add_horizontal
      f F h u)

/-- The left-zero scheduled cancellation follows from the true remaining
single-pole residue defect, because the isolated `s = 0` horizontal remainder
has already been proved to vanish. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_tendsto_zero_of_zeroPoleBoundaryDefect
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hboundary :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
              f F (h.height_schedule.height u))
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u)
      atTop
      (𝓝 0) := by
  have hhorizontal :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u)
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_tendsto_zero_ownerZeroPoleHorizontal
      f F h
  have hboundary_norm :
      Tendsto
        (fun u : ℝ =>
          ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
              f F (h.height_schedule.height u)‖)
        atTop
        (𝓝 0) :=
    tendsto_norm_zero.comp hboundary
  have hhorizontal_norm :
      Tendsto
        (fun u : ℝ =>
          ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u‖)
        atTop
        (𝓝 0) :=
    tendsto_norm_zero.comp hhorizontal
  have hmajorant :
      Tendsto
        (fun u : ℝ =>
          ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
              f F (h.height_schedule.height u)‖ +
          ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u‖)
        atTop
        (𝓝 (0 + 0)) :=
    hboundary_norm.add hhorizontal_norm
  have hmajorant_zero :
      Tendsto
        (fun u : ℝ =>
          ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
              f F (h.height_schedule.height u)‖ +
          ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u‖)
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun x : ℝ =>
        Tendsto
          (fun u : ℝ =>
            ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
                f F (h.height_schedule.height u) -
              zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
                f F (h.height_schedule.height u)‖ +
            ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u‖)
          atTop
          (𝓝 x))
      (zero_add 0)
      hmajorant
  exact
    squeeze_zero_norm'
      (Eventually.of_forall
        (fun u =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_norm_le_boundaryDefect_add_horizontal
            f F h u))
      hmajorant_zero

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
