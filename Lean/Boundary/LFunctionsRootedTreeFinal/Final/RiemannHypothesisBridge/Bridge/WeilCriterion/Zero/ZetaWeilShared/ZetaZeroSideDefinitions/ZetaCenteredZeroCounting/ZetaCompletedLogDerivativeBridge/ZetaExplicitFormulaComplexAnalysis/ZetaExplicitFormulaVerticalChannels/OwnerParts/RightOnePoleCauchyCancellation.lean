import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.RightOnePoleBoundaryIdentities
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.OnePoleHorizontalEdgeBounds

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

/-- Additive form of the horizontal orientation-defect algebra. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_orientationDefect_horizontal_add_algebra
    (A H : ℂ) :
    A + H = (A - H) + (H + H) :=
  explicitFormula_orientationDefect_horizontal_add_algebra A H

/-- Algebraic assembly of the right one-pole scheduled rectangle cancellation
from the two analytic estimates produced by the Cauchy rectangle argument. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePole_scheduledRectangleCauchyCancellation_of_boundaryDefect_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (A B : ℝ)
    (hApos : 0 < A)
    (hBpos : 0 < B)
    (hboundary :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
            f F (h.height_schedule.height u) +
          zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
            f F (h.height_schedule.height u)‖
          ≤ A *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)))
    (hhorizontal :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
          f F h u‖
          ≤ ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖ +
            B *
              (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
          f F h u‖
          ≤
            ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖ +
              C *
                (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  refine ⟨A + B, add_pos hApos hBpos, ?_⟩
  intro u
  let q : ℝ :=
    (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))
  let D : ℝ :=
    ‖zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
        f F (h.height_schedule.height u) +
      zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
        f F (h.height_schedule.height u)‖
  let H : ℝ :=
    ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
      f F h u‖
  let S : ℝ :=
    ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖
  have hdecomp :
      ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
        f F h u‖ ≤ D + H :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral_norm_le_boundaryDefect_add_horizontal
      f F h u
  have hD : D ≤ A * q :=
    hboundary u
  have hH : H ≤ S + B * q :=
    hhorizontal u
  have hsum : D + H ≤ A * q + (S + B * q) :=
    add_le_add hD hH
  have hrotate :
      A * q + (S + B * q) = S + (A * q + B * q) := by
    calc
      A * q + (S + B * q) = (A * q + S) + B * q := by
        exact (add_assoc (A * q) S (B * q)).symm
      _ = (S + A * q) + B * q := by
        exact congrArg (fun x : ℝ => x + B * q) (add_comm (A * q) S)
      _ = S + (A * q + B * q) := by
        exact add_assoc S (A * q) (B * q)
  have hfactor :
      A * q + B * q = (A + B) * q :=
    (add_mul A B q).symm
  have htarget :
      A * q + (S + B * q) = S + (A + B) * q :=
    Eq.trans hrotate (congrArg (fun x : ℝ => S + x) hfactor)
  exact le_trans hdecomp (le_trans hsum (le_of_eq htarget))

/-- Adding a nonnegative explicit horizontal side term preserves an isolated
one-pole horizontal inverse-quadratic estimate. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference_norm_le_explicit_add_of_inverseQuadratic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (B : ℝ)
    (hhorizontal :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
          f F h u‖
          ≤ B *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))) :
    ∀ u : ℝ,
      ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
        f F h u‖
        ≤ ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖ +
          B *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  intro u
  let S : ℝ :=
    ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖
  let q : ℝ :=
    (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))
  let H : ℝ :=
    ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
      f F h u‖
  have hH : H ≤ B * q :=
    hhorizontal u
  have hnonneg : 0 ≤ S :=
    norm_nonneg (explicitFormulaScheduledHorizontalSideDifference f F h u)
  have hadd : B * q ≤ S + B * q := by
    calc
      B * q = 0 + B * q := by
        exact (zero_add (B * q)).symm
      _ ≤ S + B * q := by
        exact add_le_add_right hnonneg (B * q)
  exact le_trans hH hadd

/-- Exact sink for the right one-pole scheduled rectangle cancellation from the
genuine tangent-contour Cauchy defect. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePole_scheduledRectangleCauchyCancellation_of_tangentCauchy_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (A B : ℝ)
    (hApos : 0 < A)
    (hBpos : 0 < B)
    (htangent :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
            f F (h.height_schedule.height u) -
          zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I‖
          ≤ A *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)))
    (hhorizontal :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
          f F h u‖
          ≤ B *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
          f F h u‖
          ≤
            ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖ +
              C *
                (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  refine ⟨A + B, add_pos hApos hBpos, ?_⟩
  intro u
  let q : ℝ :=
    (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))
  let E : ℝ :=
    ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖
  let R : ℝ :=
    ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
      f F h u‖
  let D : ℝ :=
    ‖zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
        f F (h.height_schedule.height u) -
      zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
        f F (h.height_schedule.height u) * Complex.I‖
  let H : ℝ :=
    ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
      f F h u‖
  have hdecomp : R ≤ D + H :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral_norm_le_tangentBoundaryDefect_add_horizontal
      f F h u
  have hD : D ≤ A * q :=
    htangent u
  have hH : H ≤ B * q :=
    hhorizontal u
  have hsum : D + H ≤ A * q + B * q :=
    add_le_add hD hH
  have hfactor : A * q + B * q = (A + B) * q :=
    (add_mul A B q).symm
  have htail : R ≤ (A + B) * q :=
    le_trans hdecomp (le_trans hsum (le_of_eq hfactor))
  have hEnonneg : 0 ≤ E :=
    norm_nonneg (explicitFormulaScheduledHorizontalSideDifference f F h u)
  have hadd : (A + B) * q ≤ E + (A + B) * q := by
    calc
      (A + B) * q = 0 + (A + B) * q := by
        exact (zero_add ((A + B) * q)).symm
      _ ≤ E + (A + B) * q := by
        exact add_le_add_right hEnonneg ((A + B) * q)
  exact le_trans htail hadd

/-- Eventual version of the right one-pole tangent Cauchy assembly.

This is the exact shape supported by the existing horizontal decay API: the
analytic tangent defect and the isolated one-pole horizontal term are each
eventually inverse-quadratic, hence so is the scheduled right one-pole
oscillatory integral, up to the explicit horizontal side term. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePole_eventually_scheduledRectangleCauchyCancellation_of_tangentCauchy_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (A B : ℝ)
    (hApos : 0 < A)
    (hBpos : 0 < B)
    (htangent :
      ∀ᶠ u in atTop,
        ‖zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
            f F (h.height_schedule.height u) -
          zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I‖
          ≤ A *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)))
    (hhorizontal :
      ∀ᶠ u in atTop,
        ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
          f F h u‖
          ≤ B *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))) :
    ∀ᶠ u in atTop,
      ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
        f F h u‖
      ≤
        ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖ +
          (A + B) *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  exact (htangent.and hhorizontal).mono
    (fun u hpair =>
      let q : ℝ :=
        (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))
      let E : ℝ :=
        ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖
      let R : ℝ :=
        ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
          f F h u‖
      let D : ℝ :=
        ‖zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
            f F (h.height_schedule.height u) -
          zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I‖
      let H : ℝ :=
        ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
          f F h u‖
      have hdecomp : R ≤ D + H :=
        zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral_norm_le_tangentBoundaryDefect_add_horizontal
          f F h u
      have hD : D ≤ A * q :=
        hpair.1
      have hH : H ≤ B * q :=
        hpair.2
      have hsum : D + H ≤ A * q + B * q :=
        add_le_add hD hH
      have hfactor : A * q + B * q = (A + B) * q :=
        (add_mul A B q).symm
      have htail : R ≤ (A + B) * q :=
        le_trans hdecomp (le_trans hsum (le_of_eq hfactor))
      have hEnonneg : 0 ≤ E :=
        norm_nonneg (explicitFormulaScheduledHorizontalSideDifference f F h u)
      have hadd : (A + B) * q ≤ E + (A + B) * q := by
        calc
          (A + B) * q = 0 + (A + B) * q := by
            exact (zero_add ((A + B) * q)).symm
          _ ≤ E + (A + B) * q := by
            exact add_le_add_right hEnonneg ((A + B) * q)
      le_trans htail hadd)

/-- Eventual right one-pole Cauchy assembly from the genuine tangent defect and
the owner-level one-pole horizontal estimate. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePole_eventually_scheduledRectangleCauchyCancellation_of_eventual_tangentCauchy
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (A : ℝ)
    (hApos : 0 < A)
    (htangent :
      ∀ᶠ u in atTop,
        ‖zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
            f F (h.height_schedule.height u) -
          zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I‖
          ≤ A *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ᶠ u in atTop,
        ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
          f F h u‖
        ≤
          ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖ +
            C *
              (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  match
    zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference_eventually_norm_le_inverseQuadratic_pos
      f F h with
  | ⟨B, hBpos, hhorizontal⟩ =>
      exact
        ⟨A + B, add_pos hApos hBpos,
          zetaCompletedExplicitFormulaCorrectionRightOnePole_eventually_scheduledRectangleCauchyCancellation_of_tangentCauchy_horizontal
            f F h A B hApos hBpos htangent hhorizontal⟩

/-- Tangent-defect convergence is the exact non-rate analytic input needed for
the right one-pole scheduled off-pole face to vanish.  The horizontal remainder
is already controlled by the one-pole horizontal owner. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral_tendsto_zero_of_tangentBoundaryDefect
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (htangent :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
              f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
              f F (h.height_schedule.height u) * Complex.I)
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
          f F h u)
      atTop
      (𝓝 0) := by
  let D : ℝ → ℝ := fun u : ℝ =>
    ‖zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
        f F (h.height_schedule.height u) -
      zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
        f F (h.height_schedule.height u) * Complex.I‖
  let H : ℝ → ℝ := fun u : ℝ =>
    ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
      f F h u‖
  have hD : Tendsto D atTop (𝓝 0) :=
    htangent.norm
  have hH_complex :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
            f F h u)
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference_tendsto_zero
      f F h
  have hH : Tendsto H atTop (𝓝 0) :=
    hH_complex.norm
  have hsum : Tendsto (fun u : ℝ => D u + H u) atTop (𝓝 (0 + 0)) :=
    hD.add hH
  have hsum_zero : Tendsto (fun u : ℝ => D u + H u) atTop (𝓝 0) :=
    Eq.subst
      (motive := fun z : ℝ =>
        Tendsto (fun u : ℝ => D u + H u) atTop (𝓝 z))
      (zero_add (0 : ℝ))
      hsum
  have hbound :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
          f F h u‖ ≤ D u + H u := by
    intro u
    exact
      zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral_norm_le_tangentBoundaryDefect_add_horizontal
        f F h u
  exact squeeze_zero_norm hbound hsum_zero

/-- Definition transport from the scheduled right one-pole oscillatory integral
to the corresponding right vertical channel, under the tangent-defect
convergence hypothesis. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_tendsto_zero_of_tangentBoundaryDefect
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (htangent :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
              f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
              f F (h.height_schedule.height u) * Complex.I)
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  have hsched :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
            f F h u)
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral_tendsto_zero_of_tangentBoundaryDefect
      f F h htangent
  have hfun :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u)) =
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
          f F h u) := by
    funext u
    rfl
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ =>
        Tendsto φ atTop (𝓝 0))
      hfun.symm
      hsched

/-- A positive-height finite standard-residue theorem supplies the corresponding
scheduled `s = 1` standard boundary value eventually. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_eventually_standardBoundaryResidueValue_of_positiveHeight
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (B : ℂ)
    (hpositive :
      ∀ T : ℝ,
        0 < T →
          zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
            f F T = B) :
    ∀ᶠ u in atTop,
      zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
        f F (h.height_schedule.height u) = B := by
  exact h.height_schedule.eventually_height_pos.mono
    (fun u hu =>
      hpositive (h.height_schedule.height u) hu)

/-- Pointwise orientation identity comparing the scheduled tangent boundary
with the standard rectangle-Cauchy boundary.  The discrepancy is exactly two
copies of the scheduled horizontal orientation remainder. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleScheduledTangentRectangleBoundaryIntegral_eq_standard_add_twice_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
        f F (h.height_schedule.height u) =
      zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
          f F (h.height_schedule.height u) +
        (zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
            f F h u +
          zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
            f F h u) := by
  let R : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleTangentIntegral
      f F (h.height_schedule.height u)
  let L : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleTangentIntegral
      f F (h.height_schedule.height u)
  let U : ℂ :=
    zetaCompletedExplicitFormulaCorrectionTopOnePoleTangentIntegral
      f F (h.height_schedule.height u)
  let D : ℂ :=
    zetaCompletedExplicitFormulaCorrectionBottomOnePoleTangentIntegral
      f F (h.height_schedule.height u)
  let S : ℂ :=
    zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
      f F (h.height_schedule.height u)
  let H : ℂ :=
    zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
      f F h u
  have hU :
      U =
        zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral
          f F (h.height_schedule.height u) := by
    exact zetaCompletedExplicitFormulaCorrectionTopOnePoleTangentIntegral_eq_horizontal
      f F (h.height_schedule.height u)
  have hD :
      D =
        zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral
          f F (h.height_schedule.height u) := by
    exact zetaCompletedExplicitFormulaCorrectionBottomOnePoleTangentIntegral_eq_horizontal
      f F (h.height_schedule.height u)
  have hH : H = U - D := by
    calc
      H =
          zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral
              f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral
              f F (h.height_schedule.height u) := by
        rfl
      _ = U - D := by
        exact congrArg₂ HSub.hSub hU.symm hD.symm
  have hS : S = D - U + R - L := by
    calc
      S =
          (∫ x in Set.Icc (1 - F.c) F.c,
            zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
              (zetaCompletedExplicitFormulaBottomPath
                (F.rectangle (h.height_schedule.height u)) x)) -
            (∫ x in Set.Icc (1 - F.c) F.c,
              zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
                (zetaCompletedExplicitFormulaTopPath
                  (F.rectangle (h.height_schedule.height u)) x)) +
            R - L := by
        rfl
      _ = D - U + R - L := by
        exact congrArg
          (fun z : ℂ => z + R - L)
          (congrArg₂ HSub.hSub hD.symm hU.symm)
  let A : ℂ := R - L
  have htangent_AH : R - L + U - D = A + H := by
    calc
      R - L + U - D = (R - L) + (U - D) := by
        exact (add_sub_assoc (R - L) U D).symm
      _ = A + (U - D) := by
        rfl
      _ = A + H := by
        exact congrArg (fun z : ℂ => A + z) hH.symm
  have hstandard_AH : S = A - H := by
    calc
      S = D - U + R - L := hS
      _ = R - L - (U - D) := by
        exact
          explicitFormula_standardBoundary_horizontal_algebra
            R L U D
      _ = A - (U - D) := by
        rfl
      _ = A - H := by
        exact congrArg (fun z : ℂ => A - z) hH.symm
  change R - L + U - D = S + (H + H)
  calc
    R - L + U - D = A + H := htangent_AH
    _ = (A - H) + (H + H) := by
      exact
        zetaCompletedExplicitFormulaCorrectionOnePole_orientationDefect_horizontal_add_algebra A H
    _ = S + (H + H) := by
      exact congrArg
        (fun z : ℂ => z + (H + H))
        hstandard_AH.symm

/-- The scheduled tangent-boundary value has the same limit as the standard
finite boundary value, because the only orientation discrepancy is the
one-pole horizontal remainder, which vanishes along the schedule. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral_tendsto_of_standardBoundaryResidue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (B : ℂ)
    (hstandard :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 B)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 B) := by
  have hhorizontal :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
            f F h u)
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference_tendsto_zero
      f F h
  have htwice_horizontal :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
            f F h u +
          zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
            f F h u)
        atTop
        (𝓝 (0 + 0)) :=
    hhorizontal.add hhorizontal
  have htwice_horizontal_zero :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
            f F h u +
          zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
            f F h u)
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
              f F h u +
            zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
              f F h u)
          atTop
          (𝓝 z))
      (zero_add (0 : ℂ))
      htwice_horizontal
  have hsum :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
              f F (h.height_schedule.height u) +
            (zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
                f F h u +
              zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
                f F h u))
        atTop
        (𝓝 (B + 0)) :=
    hstandard.add htwice_horizontal_zero
  have hsumB :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
              f F (h.height_schedule.height u) +
            (zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
                f F h u +
              zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
                f F h u))
        atTop
        (𝓝 B) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
                f F (h.height_schedule.height u) +
              (zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
                  f F h u +
                zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
                  f F h u))
          atTop
          (𝓝 z))
      (add_zero B)
      hsum
  have hfun :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
          f F (h.height_schedule.height u)) =
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
            f F (h.height_schedule.height u) +
          (zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
              f F h u +
            zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
              f F h u)) := by
    funext u
    let R : ℂ :=
      zetaCompletedExplicitFormulaCorrectionRightOnePoleTangentIntegral
        f F (h.height_schedule.height u)
    let L : ℂ :=
      zetaCompletedExplicitFormulaCorrectionLeftOnePoleTangentIntegral
        f F (h.height_schedule.height u)
    let U : ℂ :=
      zetaCompletedExplicitFormulaCorrectionTopOnePoleTangentIntegral
        f F (h.height_schedule.height u)
    let D : ℂ :=
      zetaCompletedExplicitFormulaCorrectionBottomOnePoleTangentIntegral
        f F (h.height_schedule.height u)
    let S : ℂ :=
      zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
        f F (h.height_schedule.height u)
    let H : ℂ :=
      zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
        f F h u
    have hU :
        U =
          zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral
            f F (h.height_schedule.height u) := by
      exact zetaCompletedExplicitFormulaCorrectionTopOnePoleTangentIntegral_eq_horizontal
        f F (h.height_schedule.height u)
    have hD :
        D =
          zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral
            f F (h.height_schedule.height u) := by
      exact zetaCompletedExplicitFormulaCorrectionBottomOnePoleTangentIntegral_eq_horizontal
        f F (h.height_schedule.height u)
    have hH : H = U - D := by
      calc
        H =
            zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral
                f F (h.height_schedule.height u) -
              zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral
                f F (h.height_schedule.height u) := by
          rfl
        _ = U - D := by
          exact congrArg₂ HSub.hSub hU.symm hD.symm
    have hS : S = D - U + R - L := by
      calc
        S =
            (∫ x in Set.Icc (1 - F.c) F.c,
              zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
                (zetaCompletedExplicitFormulaBottomPath
                  (F.rectangle (h.height_schedule.height u)) x)) -
              (∫ x in Set.Icc (1 - F.c) F.c,
                zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
                  (zetaCompletedExplicitFormulaTopPath
                    (F.rectangle (h.height_schedule.height u)) x)) +
              R - L := by
          rfl
        _ = D - U + R - L := by
          exact congrArg
            (fun z : ℂ => z + R - L)
            (congrArg₂ HSub.hSub hD.symm hU.symm)
    let A : ℂ := R - L
    have htangent_AH : R - L + U - D = A + H := by
      calc
        R - L + U - D = (R - L) + (U - D) := by
          exact (add_sub_assoc (R - L) U D).symm
        _ = A + (U - D) := by
          rfl
        _ = A + H := by
          exact congrArg (fun z : ℂ => A + z) hH.symm
    have hstandard_AH : S = A - H := by
      calc
        S = D - U + R - L := hS
        _ = R - L - (U - D) := by
          exact
            explicitFormula_standardBoundary_horizontal_algebra
              R L U D
        _ = A - (U - D) := by
          rfl
        _ = A - H := by
          exact congrArg (fun z : ℂ => A - z) hH.symm
    change R - L + U - D = S + (H + H)
    calc
      R - L + U - D = A + H := htangent_AH
      _ = (A - H) + (H + H) := by
        exact
          zetaCompletedExplicitFormulaCorrectionOnePole_orientationDefect_horizontal_add_algebra A H
      _ = S + (H + H) := by
        exact congrArg
          (fun z : ℂ => z + (H + H))
          hstandard_AH.symm
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ =>
        Tendsto φ atTop (𝓝 B))
      hfun.symm
      hsumB

/-- Constant-valued finite standard residue transport for the one-pole tangent
defect.  The standard raw boundary value is the contour-residue input; the
tangent boundary has the same scheduled limit because the horizontal
orientation defect tends to zero. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleTangentBoundaryDefect_tendsto_zero_of_standardBoundaryResidue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (A B : ℂ)
    (hcancel : A - B * Complex.I = 0)
    (hleft :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 A))
    (hstandard :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 B)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
            f F (h.height_schedule.height u) -
          zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I)
      atTop
      (𝓝 0) := by
  have htangent :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 B) :=
    zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral_tendsto_of_standardBoundaryResidue
      f F h B hstandard
  have htangent_mul :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I)
        atTop
        (𝓝 (B * Complex.I)) :=
    htangent.mul tendsto_const_nhds
  have hdiff :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
              f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I)
        atTop
        (𝓝 (A - B * Complex.I)) :=
    hleft.sub htangent_mul
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
                f F (h.height_schedule.height u) -
              zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
                f F (h.height_schedule.height u) * Complex.I)
          atTop
          (𝓝 z))
      hcancel
      hdiff

/-- Positive-height standard-boundary residue transport for the right one-pole
vanishing theorem.  This consumes the honest standard finite Cauchy theorem and
the horizontal orientation-defect decay, not a false all-height tangent
boundary constant. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_tendsto_zero_of_positiveHeight_standardBoundaryResidueValue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (A B : ℂ)
    (hcancel : A - B * Complex.I = 0)
    (hleft :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 A))
    (hpositive :
      ∀ T : ℝ,
        0 < T →
          zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
            f F T = B) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_tendsto_zero_of_tangentBoundaryDefect
      f F h
      (zetaCompletedExplicitFormulaCorrectionOnePoleTangentBoundaryDefect_tendsto_zero_of_standardBoundaryResidue
        f F h A B hcancel hleft
        ((zetaCompletedExplicitFormulaCorrectionOnePole_eventually_standardBoundaryResidueValue_of_positiveHeight
          f F h B hpositive).tendsto_iff.2 tendsto_const_nhds))

/-- Positive-height projection-boundary residue transport for the right
one-pole value.  This is the nonzero projection form of the Cauchy transport:
the left face tends to the standard residue plus the projection, while the
finite standard boundary remains the standard residue. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_tendsto_projection_of_positiveHeight_projectionBoundaryResidueValue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (B : ℂ)
    (hleft :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 (B * Complex.I +
          zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c)))
    (hpositive :
      ∀ T : ℝ,
        0 < T →
          zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
            f F T = B) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c)) := by
  let P : ℂ := zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c
  have hstandard :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 B) :=
    ((zetaCompletedExplicitFormulaCorrectionOnePole_eventually_standardBoundaryResidueValue_of_positiveHeight
      f F h B hpositive).tendsto_iff.2 tendsto_const_nhds)
  have htangent :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 B) :=
    zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral_tendsto_of_standardBoundaryResidue
      f F h B hstandard
  have htangent_mul :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I)
        atTop
        (𝓝 (B * Complex.I)) :=
    htangent.mul tendsto_const_nhds
  have hdefect_raw :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
              f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
              f F (h.height_schedule.height u) * Complex.I)
        atTop
        (𝓝 ((B * Complex.I + P) - B * Complex.I)) :=
    hleft.sub htangent_mul
  have hdefect_value : (B * Complex.I + P) - B * Complex.I = P := by
    calc
      (B * Complex.I + P) - B * Complex.I =
          (B * Complex.I + P) + -(B * Complex.I) := by
        exact sub_eq_add_neg (B * Complex.I + P) (B * Complex.I)
      _ = P + (B * Complex.I + -(B * Complex.I)) := by
        exact add_right_comm (B * Complex.I) P (-(B * Complex.I))
      _ = P + 0 := by
        exact congrArg (fun z : ℂ => P + z) (add_right_neg (B * Complex.I))
      _ = P := by
        exact add_zero P
  have hdefect :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
              f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
              f F (h.height_schedule.height u) * Complex.I)
        atTop
        (𝓝 P) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
                f F (h.height_schedule.height u) -
              zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
                f F (h.height_schedule.height u) * Complex.I)
          atTop
          (𝓝 z))
      hdefect_value
      hdefect_raw
  have hdefect_norm :
      Tendsto
        (fun u : ℝ =>
          ‖zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
              f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
              f F (h.height_schedule.height u) * Complex.I - P‖)
        atTop
        (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 hdefect
  have hhorizontal_complex :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
            f F h u)
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference_tendsto_zero
      f F h
  have hhorizontal :
      Tendsto
        (fun u : ℝ =>
          ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
            f F h u‖)
        atTop
        (𝓝 0) :=
    hhorizontal_complex.norm
  have hsum_zero :
      Tendsto
        (fun u : ℝ =>
          ‖zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
              f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
              f F (h.height_schedule.height u) * Complex.I - P‖ +
          ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
            f F h u‖)
        atTop
        (𝓝 (0 + 0)) :=
    hdefect_norm.add hhorizontal
  have hsum :
      Tendsto
        (fun u : ℝ =>
          ‖zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
              f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
              f F (h.height_schedule.height u) * Complex.I - P‖ +
          ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
            f F h u‖)
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun z : ℝ =>
        Tendsto
          (fun u : ℝ =>
            ‖zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
                f F (h.height_schedule.height u) -
              zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
                f F (h.height_schedule.height u) * Complex.I - P‖ +
            ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
              f F h u‖)
          atTop
          (𝓝 z))
      (zero_add (0 : ℝ))
      hsum_zero
  have hbound :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
            f F h u - P‖
          ≤
          ‖zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
              f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
              f F (h.height_schedule.height u) * Complex.I - P‖ +
          ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
            f F h u‖ := by
    intro u
    exact
      zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral_sub_projection_norm_le_tangentBoundaryProjectionDefect_add_horizontal
        f F h u P
  have hnorm_zero :
      Tendsto
        (fun u : ℝ =>
          ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
              f F h u - P‖)
        atTop
        (𝓝 0) :=
    squeeze_zero_norm' hbound hsum
  have hsched :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
            f F h u)
        atTop
        (𝓝 P) :=
    tendsto_iff_norm_sub_tendsto_zero.2 hnorm_zero
  have hfun :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u)) =
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
          f F h u) := by
    funext u
    rfl
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 P))
      hfun.symm
      hsched

/-- Eventual explicit-horizontal form of the isolated one-pole horizontal
inverse-quadratic estimate. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference_eventually_norm_le_explicit_add_inverseQuadratic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ∃ B : ℝ,
      0 < B ∧
      ∀ᶠ u in atTop,
        ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
          f F h u‖
          ≤ ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖ +
            B *
              (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  match
    zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference_eventually_norm_le_inverseQuadratic_pos
      f F h with
  | ⟨B, hBpos, hB⟩ =>
      refine ⟨B, hBpos, ?_⟩
      exact hB.mono
        (fun u hu =>
          let S : ℝ :=
            ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖
          let q : ℝ :=
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))
          have hnonneg : 0 ≤ S :=
            norm_nonneg (explicitFormulaScheduledHorizontalSideDifference f F h u)
          have hadd : B * q ≤ S + B * q := by
            calc
              B * q = 0 + B * q := by
                exact (zero_add (B * q)).symm
              _ ≤ S + B * q := by
                exact add_le_add_right hnonneg (B * q)
          le_trans hu hadd)

/-- The scheduled Cauchy/oscillatory cancellation package for the right-face
off-pole `s = 1` correction integral.

This is the analytic step obtained by applying the scheduled contour
cancellation or integration-by-parts package to the fixed-displacement
vertical face.  The inverse-quadratic decay is not a pointwise
denominator-separation consequence. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePole_scheduledRectangleCauchyCancellation_of_positiveHeightRawCauchy
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (A : ℝ)
    (hApos : 0 < A)
    (htangent :
      ∀ᶠ u in atTop,
        ‖zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
            f F (h.height_schedule.height u) -
          zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I‖
          ≤ A *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ᶠ u in atTop,
        ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
          f F h u‖
          ≤
            ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖ +
              A *
                (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionRightOnePole_eventually_scheduledRectangleCauchyCancellation_of_eventual_tangentCauchy
      f F h A hApos htangent

/-- Compatibility name for the scheduled right-face one-pole Cauchy package. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePole_scheduledRectangleCauchyCancellation_ownerGap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (A : ℝ)
    (hApos : 0 < A)
    (htangent :
      ∀ᶠ u in atTop,
        ‖zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
            f F (h.height_schedule.height u) -
          zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I‖
          ≤ A *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ᶠ u in atTop,
        ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
          f F h u‖
          ≤
            ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖ +
              A *
                (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) :=
  zetaCompletedExplicitFormulaCorrectionRightOnePole_scheduledRectangleCauchyCancellation_of_positiveHeightRawCauchy
    f F h A hApos htangent

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
