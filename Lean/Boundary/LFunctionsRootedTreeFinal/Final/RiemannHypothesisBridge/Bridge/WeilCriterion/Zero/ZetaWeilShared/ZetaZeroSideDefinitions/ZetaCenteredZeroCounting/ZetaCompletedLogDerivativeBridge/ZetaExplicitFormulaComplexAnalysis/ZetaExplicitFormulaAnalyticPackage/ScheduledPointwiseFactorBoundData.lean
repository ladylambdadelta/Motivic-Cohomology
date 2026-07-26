import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaAnalyticPackage.ScheduledFiniteFactorBoundData
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaAnalyticPackage.ScheduledPointwiseRegularity
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaCompletedLogDerivativeControl.SingularSeparation
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaCompletedLogDerivativeControl.CauchyBoundData

/-!
# Scheduled pointwise factor-bound carriers

This file applies the singleton singular-separation owner to the already-owned
scheduled horizontal pointwise regularity package.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-! The following two owners are deliberately stated for an arbitrary contour
family and schedule.  The compactness arguments below must not depend on the
special autocorrelation schedule: their only input is the scheduled
zero-excision theorem owned by `ScheduledPointwiseRegularity`. -/

theorem ExplicitFormulaCofinalHeightSchedule.topPath_zetaSideFactor_continuousOn_owner
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u : ℝ) :
    ContinuousOn
      (fun x : ℝ => zetaSideFactor
        (zetaCompletedExplicitFormulaTopPath
          (F.rectangle (schedule.height u)) x))
      (Set.uIcc F.c (1 - F.c)) := by
  intro x hx
  let z : ℂ :=
    zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x
  have hp := schedule.topPath_zeroExcisedPointwise u x hx
  have hfactor : ContinuousAt zetaSideFactor z := by
    change DifferentiableAt ℂ
      (fun w : ℂ => completedRiemannZeta w * (Complex.Gammaℝ w)⁻¹) z
    exact (differentiableAt_completedZeta_factorized hp.2.1 hp.2.2.1 hp.2.2.2.2.1).continuousAt
  have hpath : ContinuousAt
      (fun y : ℝ => zetaCompletedExplicitFormulaTopPath
        (F.rectangle (schedule.height u)) y) x :=
    (zetaCompletedExplicitFormulaTopPath_continuous
      (F.rectangle (schedule.height u))).continuousAt
  exact hfactor.comp x hpath

theorem ExplicitFormulaCofinalHeightSchedule.bottomPath_zetaSideFactor_continuousOn_owner
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u : ℝ) :
    ContinuousOn
      (fun x : ℝ => zetaSideFactor
        (zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (schedule.height u)) x))
      (Set.uIcc F.c (1 - F.c)) := by
  intro x hx
  let z : ℂ :=
    zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x
  have hp := schedule.bottomPath_zeroExcisedPointwise u x hx
  have hfactor : ContinuousAt zetaSideFactor z := by
    change DifferentiableAt ℂ
      (fun w : ℂ => completedRiemannZeta w * (Complex.Gammaℝ w)⁻¹) z
    exact (differentiableAt_completedZeta_factorized hp.2.1 hp.2.2.1 hp.2.2.2.2.1).continuousAt
  have hpath : ContinuousAt
      (fun y : ℝ => zetaCompletedExplicitFormulaBottomPath
        (F.rectangle (schedule.height u)) y) x :=
    (zetaCompletedExplicitFormulaBottomPath_continuous
      (F.rectangle (schedule.height u))).continuousAt
  exact hfactor.comp x hpath

theorem ExplicitFormulaCofinalHeightSchedule.topPath_completedZero_separation
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ρ : {ρ : ℂ // _root_.Boundary.LFunctions.ZetaCompletedZero ρ},
        δ ≤
          ‖zetaCompletedExplicitFormulaTopPath
            (F.rectangle (schedule.height u)) x -
              ((1 / 2 : ℂ) + (ρ : ℂ))‖ :=
  let pointwise := schedule.topPath_zeroExcisedPointwise u x hx
  completedZeroResidueCoordinate_norm_separation_of_completedRiemannZeta_ne_zero
    (zetaCompletedExplicitFormulaTopPath
      (F.rectangle (schedule.height u)) x)
    pointwise.2.1
    pointwise.2.2.1
    pointwise.2.2.2.1

theorem ExplicitFormulaCofinalHeightSchedule.topPath_gammaPole_separation
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ n : ℕ,
        δ ≤
          ‖zetaCompletedExplicitFormulaTopPath
            (F.rectangle (schedule.height u)) x - (-(2 * (n : ℂ)))‖ :=
  let pointwise := schedule.topPath_zeroExcisedPointwise u x hx
  gammaPole_norm_separation_of_Gammaℝ_ne_zero
    (zetaCompletedExplicitFormulaTopPath
      (F.rectangle (schedule.height u)) x)
    pointwise.2.2.2.2.1

theorem ExplicitFormulaCofinalHeightSchedule.bottomPath_completedZero_separation
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ρ : {ρ : ℂ // _root_.Boundary.LFunctions.ZetaCompletedZero ρ},
        δ ≤
          ‖zetaCompletedExplicitFormulaBottomPath
            (F.rectangle (schedule.height u)) x -
              ((1 / 2 : ℂ) + (ρ : ℂ))‖ :=
  let pointwise := schedule.bottomPath_zeroExcisedPointwise u x hx
  completedZeroResidueCoordinate_norm_separation_of_completedRiemannZeta_ne_zero
    (zetaCompletedExplicitFormulaBottomPath
      (F.rectangle (schedule.height u)) x)
    pointwise.2.1
    pointwise.2.2.1
    pointwise.2.2.2.1

theorem ExplicitFormulaCofinalHeightSchedule.bottomPath_gammaPole_separation
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ n : ℕ,
        δ ≤
          ‖zetaCompletedExplicitFormulaBottomPath
            (F.rectangle (schedule.height u)) x - (-(2 * (n : ℂ)))‖ :=
  let pointwise := schedule.bottomPath_zeroExcisedPointwise u x hx
  gammaPole_norm_separation_of_Gammaℝ_ne_zero
    (zetaCompletedExplicitFormulaBottomPath
      (F.rectangle (schedule.height u)) x)
    pointwise.2.2.2.2.1

theorem ExplicitFormulaCofinalHeightSchedule.topPath_inverseGamma_cauchy_bound
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x R : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c))
    (hR_pos : 0 < R)
    (hR : R <
      (contourSingularPoint_norm_separation_of_factor_nonzero
        (zetaCompletedExplicitFormulaTopPath
          (F.rectangle (schedule.height u)) x)
        (schedule.topPath_zeroExcisedPointwise u x hx).2.1
        (schedule.topPath_zeroExcisedPointwise u x hx).2.2.1
        (schedule.topPath_zeroExcisedPointwise u x hx).2.2.2.1
        (schedule.topPath_zeroExcisedPointwise u x hx).2.2.2.2.1
        (schedule.topPath_zeroExcisedPointwise u x hx).2.2.2.2.2).choose) :
    ∃ B : ℝ, 0 < B ∧
      ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
          (zetaCompletedExplicitFormulaTopPath
            (F.rectangle (schedule.height u)) x) /
          (Complex.Gammaℝ
            (zetaCompletedExplicitFormulaTopPath
              (F.rectangle (schedule.height u)) x))⁻¹‖ ≤ B := by
  let pointwise := schedule.topPath_zeroExcisedPointwise u x hx
  let hsep := contourSingularPoint_norm_separation_of_factor_nonzero
    (zetaCompletedExplicitFormulaTopPath
      (F.rectangle (schedule.height u)) x)
    pointwise.2.1 pointwise.2.2.1 pointwise.2.2.2.1
    pointwise.2.2.2.2.1 pointwise.2.2.2.2.2
  exact inverseGamma_cauchy_log_derivative_bound_of_singular_separation_owner
    (zetaCompletedExplicitFormulaTopPath
      (F.rectangle (schedule.height u)) x)
    R hsep.choose hR_pos hsep.choose_spec.2 hR

theorem ExplicitFormulaCofinalHeightSchedule.bottomPath_inverseGamma_cauchy_bound
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x R : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c))
    (hR_pos : 0 < R)
    (hR : R <
      (contourSingularPoint_norm_separation_of_factor_nonzero
        (zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (schedule.height u)) x)
        (schedule.bottomPath_zeroExcisedPointwise u x hx).2.1
        (schedule.bottomPath_zeroExcisedPointwise u x hx).2.2.1
        (schedule.bottomPath_zeroExcisedPointwise u x hx).2.2.2.1
        (schedule.bottomPath_zeroExcisedPointwise u x hx).2.2.2.2.1
        (schedule.bottomPath_zeroExcisedPointwise u x hx).2.2.2.2.2).choose) :
    ∃ B : ℝ, 0 < B ∧
      ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
          (zetaCompletedExplicitFormulaBottomPath
            (F.rectangle (schedule.height u)) x) /
          (Complex.Gammaℝ
            (zetaCompletedExplicitFormulaBottomPath
              (F.rectangle (schedule.height u)) x))⁻¹‖ ≤ B := by
  let pointwise := schedule.bottomPath_zeroExcisedPointwise u x hx
  let hsep := contourSingularPoint_norm_separation_of_factor_nonzero
    (zetaCompletedExplicitFormulaBottomPath
      (F.rectangle (schedule.height u)) x)
    pointwise.2.1 pointwise.2.2.1 pointwise.2.2.2.1
    pointwise.2.2.2.2.1 pointwise.2.2.2.2.2
  exact inverseGamma_cauchy_log_derivative_bound_of_singular_separation_owner
    (zetaCompletedExplicitFormulaBottomPath
      (F.rectangle (schedule.height u)) x)
    R hsep.choose hR_pos hsep.choose_spec.2 hR

/-! Choose half the actual singular separation.  This is the canonical local
radius used by the variable-radius Cauchy package. -/
theorem ExplicitFormulaCofinalHeightSchedule.topPath_zetaSideFactor_canonical_local_carrier
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ R : ℝ, 0 < R ∧
      R <
        (contourSingularPoint_norm_separation_of_factor_nonzero
          (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x)
          (schedule.topPath_zeroExcisedPointwise u x hx).2.1
          (schedule.topPath_zeroExcisedPointwise u x hx).2.2.1
          (schedule.topPath_zeroExcisedPointwise u x hx).2.2.2.1
          (schedule.topPath_zeroExcisedPointwise u x hx).2.2.2.2.1
          (schedule.topPath_zeroExcisedPointwise u x hx).2.2.2.2.2).choose ∧
      DiffContOnCl ℂ zetaSideFactor
        (Metric.ball
          (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x) R) ∧
      (∀ w : ℂ, w ∈ Metric.closedBall
        (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x) R →
        zetaSideFactor w ≠ 0) := by
  let pointwise := schedule.topPath_zeroExcisedPointwise u x hx
  let hsep := contourSingularPoint_norm_separation_of_factor_nonzero
    (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x)
    pointwise.2.1 pointwise.2.2.1 pointwise.2.2.2.1
    pointwise.2.2.2.2.1 pointwise.2.2.2.2.2
  let R : ℝ := hsep.choose / 2
  have hR_pos : 0 < R := half_pos hsep.choose_spec.1
  have hR : R < hsep.choose := half_lt_self hsep.choose_spec.1
  exact ⟨R, hR_pos,
    hR,
    zetaSideFactor_diffContOnCl_of_singular_separation
      (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x)
      R hsep.choose hsep.choose_spec.2 hR,
    zetaSideFactor_ne_zero_on_closedBall_of_singular_separation
      (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x)
      R hsep.choose hsep.choose_spec.2 hR⟩

theorem ExplicitFormulaCofinalHeightSchedule.bottomPath_zetaSideFactor_canonical_local_carrier
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ R : ℝ, 0 < R ∧
      R <
        (contourSingularPoint_norm_separation_of_factor_nonzero
          (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x)
          (schedule.bottomPath_zeroExcisedPointwise u x hx).2.1
          (schedule.bottomPath_zeroExcisedPointwise u x hx).2.2.1
          (schedule.bottomPath_zeroExcisedPointwise u x hx).2.2.2.1
          (schedule.bottomPath_zeroExcisedPointwise u x hx).2.2.2.2.1
          (schedule.bottomPath_zeroExcisedPointwise u x hx).2.2.2.2.2).choose ∧
      DiffContOnCl ℂ zetaSideFactor
        (Metric.ball
          (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x) R) ∧
      (∀ w : ℂ, w ∈ Metric.closedBall
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x) R →
        zetaSideFactor w ≠ 0) := by
  let pointwise := schedule.bottomPath_zeroExcisedPointwise u x hx
  let hsep := contourSingularPoint_norm_separation_of_factor_nonzero
    (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x)
    pointwise.2.1 pointwise.2.2.1 pointwise.2.2.2.1
    pointwise.2.2.2.2.1 pointwise.2.2.2.2.2
  let R : ℝ := hsep.choose / 2
  have hR_pos : 0 < R := half_pos hsep.choose_spec.1
  have hR : R < hsep.choose := half_lt_self hsep.choose_spec.1
  exact ⟨R, hR_pos, hR,
    zetaSideFactor_diffContOnCl_of_singular_separation
      (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x)
      R hsep.choose hsep.choose_spec.2 hR,
    zetaSideFactor_ne_zero_on_closedBall_of_singular_separation
      (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x)
      R hsep.choose hsep.choose_spec.2 hR⟩

theorem ExplicitFormulaCofinalHeightSchedule.topPath_zetaSideFactor_canonical_center_lower_bound
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ R ε : ℝ, 0 < R ∧ 0 < ε ∧
      (∀ w : ℂ, w ∈ Metric.closedBall
        (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x) R →
        ε ≤ ‖zetaSideFactor w‖) := by
  obtain ⟨R, hR, _, hDiff, hne⟩ :=
    schedule.topPath_zetaSideFactor_canonical_local_carrier u x hx
  obtain ⟨ε, hε, hbound⟩ :=
    zetaSideFactor_positive_lower_bound_on_closedBall_of_diffContOnCl
      (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x)
      R hR hDiff hne
  exact ⟨R, ε, hR, hε, hbound⟩

theorem ExplicitFormulaCofinalHeightSchedule.topPath_zetaSideFactor_canonical_two_sided_carrier_bound
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ R ε A : ℝ, 0 < R ∧ 0 < ε ∧
      (∀ w : ℂ, w ∈ Metric.closedBall
        (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x) R →
        ε ≤ ‖zetaSideFactor w‖) ∧
      (∀ w : ℂ, w ∈ Metric.closedBall
        (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x) R →
        ‖zetaSideFactor w‖ ≤ A) := by
  obtain ⟨R, ε, hR, hε, hlower⟩ :=
    schedule.topPath_zetaSideFactor_canonical_center_lower_bound u x hx
  obtain ⟨A, hA, hupper⟩ :=
    exists_norm_upper_bound_of_isCompact_of_continuousOn
      (isCompact_closedBall
        (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x) R)
      ((closedBall_continuousOn_of_diffContOnCl
        (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x)
        R hR
        (schedule.topPath_zetaSideFactor_canonical_local_carrier u x hx).choose_spec.2.2.1)
  exact ⟨R, ε, A, hR, hε, hlower, hupper⟩

theorem ExplicitFormulaCofinalHeightSchedule.bottomPath_zetaSideFactor_canonical_two_sided_carrier_bound
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ R ε A : ℝ, 0 < R ∧ 0 < ε ∧
      (∀ w : ℂ, w ∈ Metric.closedBall
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x) R →
        ε ≤ ‖zetaSideFactor w‖) ∧
      (∀ w : ℂ, w ∈ Metric.closedBall
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x) R →
        ‖zetaSideFactor w‖ ≤ A) := by
  obtain ⟨R, hR, _, hDiff, hne⟩ :=
    schedule.bottomPath_zetaSideFactor_canonical_local_carrier u x hx
  obtain ⟨ε, hε, hlower⟩ :=
    zetaSideFactor_positive_lower_bound_on_closedBall_of_diffContOnCl
      (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x)
      R hR hDiff hne
  obtain ⟨A, hA, hupper⟩ :=
    exists_norm_upper_bound_of_isCompact_of_continuousOn
      (isCompact_closedBall
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x) R)
      ((closedBall_continuousOn_of_diffContOnCl
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x)
        R hR
        (schedule.bottomPath_zetaSideFactor_canonical_local_carrier u x hx).choose_spec.2.2.1)
  exact ⟨R, ε, A, hR, hε, hlower, hupper⟩

theorem ExplicitFormulaCofinalHeightSchedule.topPath_zetaSideFactor_canonical_carrier_package
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ R ε A : ℝ, 0 < R ∧ 0 < ε ∧ 0 < A ∧
      DiffContOnCl ℂ zetaSideFactor
        (Metric.ball
          (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x) R) ∧
      (∀ w : ℂ, w ∈ Metric.sphere
        (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x) R →
        ‖zetaSideFactor w‖ ≤ A) ∧
      (∀ w : ℂ, w ∈ Metric.closedBall
        (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x) R →
        ε ≤ ‖zetaSideFactor w‖) := by
  obtain ⟨R, hR, hDiff, hne⟩ :=
    schedule.topPath_zetaSideFactor_canonical_local_carrier u x hx
  obtain ⟨ε, hε, hεbound⟩ :=
    zetaSideFactor_positive_lower_bound_on_closedBall_of_diffContOnCl
      (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x)
      R hR hDiff hne
  obtain ⟨A, hA, hAbound⟩ :=
    exists_norm_upper_bound_of_isCompact_of_continuousOn
      (isCompact_closedBall
        (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x) R)
      (closedBall_continuousOn_of_diffContOnCl
        (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x)
        R hR hDiff)
  have hApos : 0 < A := lt_of_lt_of_le hε
    (hAbound
      (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x)
      (Metric.mem_closedBall_self hR.le))
  exact ⟨R, ε, A, hR, hε, hApos, hDiff,
    (fun w hw => hAbound w (Metric.mem_closedBall.mpr hw.le)), hεbound⟩

theorem ExplicitFormulaCofinalHeightSchedule.bottomPath_zetaSideFactor_canonical_carrier_package
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ R ε A : ℝ, 0 < R ∧ 0 < ε ∧ 0 < A ∧
      DiffContOnCl ℂ zetaSideFactor
        (Metric.ball
          (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x) R) ∧
      (∀ w : ℂ, w ∈ Metric.sphere
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x) R →
        ‖zetaSideFactor w‖ ≤ A) ∧
      (∀ w : ℂ, w ∈ Metric.closedBall
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x) R →
        ε ≤ ‖zetaSideFactor w‖) := by
  obtain ⟨R, hR, hDiff, hne⟩ :=
    schedule.bottomPath_zetaSideFactor_canonical_local_carrier u x hx
  obtain ⟨ε, hε, hεbound⟩ :=
    zetaSideFactor_positive_lower_bound_on_closedBall_of_diffContOnCl
      (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x)
      R hR hDiff hne
  obtain ⟨A, hA, hAbound⟩ :=
    exists_norm_upper_bound_of_isCompact_of_continuousOn
      (isCompact_closedBall
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x) R)
      (closedBall_continuousOn_of_diffContOnCl
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x)
        R hR hDiff)
  have hApos : 0 < A := lt_of_lt_of_le hε
    (hAbound
      (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x)
      (Metric.mem_closedBall_self hR.le))
  exact ⟨R, ε, A, hR, hε, hApos, hDiff,
    (fun w hw => hAbound w (Metric.mem_closedBall.mpr hw.le)), hεbound⟩

theorem ExplicitFormulaCofinalHeightSchedule.topPath_zetaSideFactor_canonical_cauchy_quotient_data
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ R A ε : ℝ, 0 < R ∧ 0 < A ∧ 0 < ε ∧
      (∀ w : ℂ, w ∈ Metric.sphere
        (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x) R →
        ‖zetaSideFactor w‖ ≤ A) ∧
      ε ≤ ‖zetaSideFactor
        (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x)‖ ∧
      0 < (A / R) / ε := by
  obtain ⟨R, ε, A, hR, hε, hlower, hupper⟩ :=
    schedule.topPath_zetaSideFactor_canonical_two_sided_carrier_bound u x hx
  have hcenter := hlower
    (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x)
    (Metric.mem_closedBall_self hR.le)
  have hA : 0 < A := lt_of_lt_of_le hε
    (hcenter.trans
      (hupper
        (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x)
        (Metric.mem_closedBall_self hR.le)))
  have hsphere : ∀ w : ℂ, w ∈ Metric.sphere
      (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x) R →
      ‖zetaSideFactor w‖ ≤ A := by
    intro w hw
    exact hupper w (Metric.mem_closedBall.mpr hw.le)
  exact ⟨R, A, ε, hR, hA, hε, hsphere, hcenter,
    div_pos (div_pos hA hR) hε⟩

theorem ExplicitFormulaCofinalHeightSchedule.bottomPath_zetaSideFactor_canonical_cauchy_quotient_data
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ R A ε : ℝ, 0 < R ∧ 0 < A ∧ 0 < ε ∧
      (∀ w : ℂ, w ∈ Metric.sphere
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x) R →
        ‖zetaSideFactor w‖ ≤ A) ∧
      ε ≤ ‖zetaSideFactor
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x)‖ ∧
      0 < (A / R) / ε := by
  obtain ⟨R, ε, A, hR, hε, hlower, hupper⟩ :=
    schedule.bottomPath_zetaSideFactor_canonical_two_sided_carrier_bound u x hx
  have hcenter := hlower
    (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x)
    (Metric.mem_closedBall_self hR.le)
  have hA : 0 < A := lt_of_lt_of_le hε
    (hcenter.trans
      (hupper
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x)
        (Metric.mem_closedBall_self hR.le)))
  have hsphere : ∀ w : ℂ, w ∈ Metric.sphere
      (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x) R →
      ‖zetaSideFactor w‖ ≤ A := by
    intro w hw
    exact hupper w (Metric.mem_closedBall.mpr hw.le)
  exact ⟨R, A, ε, hR, hA, hε, hsphere, hcenter,
    div_pos (div_pos hA hR) hε⟩

theorem ExplicitFormulaCofinalHeightSchedule.scheduled_pair_zetaSideFactor_canonical_quotient_constant
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ q : ℝ, 0 < q ∧
      (∃ R A ε : ℝ, 0 < R ∧ 0 < A ∧ 0 < ε ∧
        (∀ w : ℂ, w ∈ Metric.sphere
          (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x) R →
          ‖zetaSideFactor w‖ ≤ A) ∧
        ε ≤ ‖zetaSideFactor
          (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x)‖ ∧
        (A / R) / ε ≤ q) ∧
      (∃ R A ε : ℝ, 0 < R ∧ 0 < A ∧ 0 < ε ∧
        (∀ w : ℂ, w ∈ Metric.sphere
          (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x) R →
          ‖zetaSideFactor w‖ ≤ A) ∧
        ε ≤ ‖zetaSideFactor
          (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x)‖ ∧
        (A / R) / ε ≤ q) := by
  obtain ⟨RTop, ATop, εTop, hRTop, hATop, hεTop, hTopSphere, hTopCenter, hTopQ⟩ :=
    schedule.topPath_zetaSideFactor_canonical_cauchy_quotient_data u x hx
  obtain ⟨RBottom, ABottom, εBottom, hRBottom, hABottom, hεBottom,
      hBottomSphere, hBottomCenter, hBottomQ⟩ :=
    schedule.bottomPath_zetaSideFactor_canonical_cauchy_quotient_data u x hx
  let qTop : ℝ := (ATop / RTop) / εTop
  let qBottom : ℝ := (ABottom / RBottom) / εBottom
  let q : ℝ := max qTop qBottom
  have hqTop : 0 < qTop := div_pos (div_pos hATop hRTop) hεTop
  have hqBottom : 0 < qBottom := div_pos (div_pos hABottom hRBottom) hεBottom
  exact ⟨q, lt_max hqTop hqBottom,
    ⟨RTop, ATop, εTop, hRTop, hATop, hεTop, hTopSphere, hTopCenter,
      le_max_left qTop qBottom⟩,
    ⟨RBottom, ABottom, εBottom, hRBottom, hABottom, hεBottom,
      hBottomSphere, hBottomCenter, le_max_right qTop qBottom⟩⟩

theorem ExplicitFormulaCofinalHeightSchedule.bottomPath_zetaSideFactor_canonical_center_lower_bound
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ R ε : ℝ, 0 < R ∧ 0 < ε ∧
      (∀ w : ℂ, w ∈ Metric.closedBall
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x) R →
        ε ≤ ‖zetaSideFactor w‖) := by
  obtain ⟨R, hR, _, hDiff, hne⟩ :=
    schedule.bottomPath_zetaSideFactor_canonical_local_carrier u x hx
  obtain ⟨ε, hε, hbound⟩ :=
    zetaSideFactor_positive_lower_bound_on_closedBall_of_diffContOnCl
      (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x)
      R hR hDiff hne
  exact ⟨R, ε, hR, hε, hbound⟩

theorem ExplicitFormulaCofinalHeightSchedule.topPath_inverseGamma_canonical_local_cauchy_data
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ R B : ℝ, 0 < R ∧ 0 < B ∧
      R <
        (contourSingularPoint_norm_separation_of_factor_nonzero
          (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x)
          (schedule.topPath_zeroExcisedPointwise u x hx).2.1
          (schedule.topPath_zeroExcisedPointwise u x hx).2.2.1
          (schedule.topPath_zeroExcisedPointwise u x hx).2.2.2.1
          (schedule.topPath_zeroExcisedPointwise u x hx).2.2.2.2.1
          (schedule.topPath_zeroExcisedPointwise u x hx).2.2.2.2.2).choose ∧
      ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
          (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x) /
          (Complex.Gammaℝ
            (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x))⁻¹‖ ≤ B := by
  let pointwise := schedule.topPath_zeroExcisedPointwise u x hx
  let hsep := contourSingularPoint_norm_separation_of_factor_nonzero
    (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x)
    pointwise.2.1 pointwise.2.2.1 pointwise.2.2.2.1
    pointwise.2.2.2.2.1 pointwise.2.2.2.2.2
  let R : ℝ := hsep.choose / 2
  have hR_pos : 0 < R := half_pos hsep.choose_spec.1
  have hR : R < hsep.choose := half_lt_self hsep.choose_spec.1
  obtain ⟨B, hB, hbound⟩ := schedule.topPath_inverseGamma_cauchy_bound
    u x R hx hR_pos hR
  exact ⟨R, B, hR_pos, hB, hR, hbound⟩

theorem ExplicitFormulaCofinalHeightSchedule.topPath_inverseGamma_canonical_two_sided_carrier_bound
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c))
    (hcx : F.c ≤ x) (hc : 0 < F.c) :
    ∃ R ε A : ℝ, 0 < R ∧ 0 < ε ∧ 0 < A ∧
      (∀ w : ℂ, w ∈ Metric.closedBall
        (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x) R →
        ε ≤ ‖(Complex.Gammaℝ w)⁻¹‖) ∧
      (∀ w : ℂ, w ∈ Metric.closedBall
        (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x) R →
        ‖(Complex.Gammaℝ w)⁻¹‖ ≤ A) := by
  let r := F.rectangle (schedule.height u)
  let z := zetaCompletedExplicitFormulaTopPath (r) x
  let pointwise := schedule.topPath_zeroExcisedPointwise u x hx
  let hsep := contourSingularPoint_norm_separation_of_factor_nonzero z
    pointwise.2.1 pointwise.2.2.1 pointwise.2.2.2.1
    pointwise.2.2.2.2.1 pointwise.2.2.2.2.2
  let R : ℝ := min (hsep.choose / 2) (r.c / 2)
  have hsep_pos : 0 < hsep.choose / 2 := half_pos hsep.choose_spec.1
  have hc2_pos : 0 < r.c / 2 := half_pos hc
  have hR_pos : 0 < R := lt_min hsep_pos hc2_pos
  have hR_sep : R < hsep.choose := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hsep.choose_spec.1)
  have hR_c : R < r.c := lt_of_le_of_lt (min_le_right _ _) (half_lt_self hc)
  obtain ⟨ε, hε, hεbound⟩ :=
    inverseGamma_positive_lower_bound_on_topPath_ball_of_radius_lt_c_owner
      r x R (le_trans hcx (le_rfl)) hR_pos hR_c
  have hdiff : DiffContOnCl ℂ (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
      (Metric.ball z R) := inverseGamma_diffContOnCl_on_ball_owner z R
  obtain ⟨A, hA, hAbound⟩ :=
    exists_norm_upper_bound_of_isCompact_of_continuousOn
      (isCompact_closedBall z R)
      (closedBall_continuousOn_of_diffContOnCl z R hR_pos hdiff)
  exact ⟨R, ε, A, hR_pos, hε, hA, hεbound, hAbound⟩

theorem ExplicitFormulaCofinalHeightSchedule.bottomPath_inverseGamma_canonical_local_cauchy_data
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ R B : ℝ, 0 < R ∧ 0 < B ∧
      R <
        (contourSingularPoint_norm_separation_of_factor_nonzero
          (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x)
          (schedule.bottomPath_zeroExcisedPointwise u x hx).2.1
          (schedule.bottomPath_zeroExcisedPointwise u x hx).2.2.1
          (schedule.bottomPath_zeroExcisedPointwise u x hx).2.2.2.1
          (schedule.bottomPath_zeroExcisedPointwise u x hx).2.2.2.2.1
          (schedule.bottomPath_zeroExcisedPointwise u x hx).2.2.2.2.2).choose ∧
      ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
          (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x) /
          (Complex.Gammaℝ
            (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x))⁻¹‖ ≤ B := by
  let pointwise := schedule.bottomPath_zeroExcisedPointwise u x hx
  let hsep := contourSingularPoint_norm_separation_of_factor_nonzero
    (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x)
    pointwise.2.1 pointwise.2.2.1 pointwise.2.2.2.1
    pointwise.2.2.2.2.1 pointwise.2.2.2.2.2
  let R : ℝ := hsep.choose / 2
  have hR_pos : 0 < R := half_pos hsep.choose_spec.1
  have hR : R < hsep.choose := half_lt_self hsep.choose_spec.1
  obtain ⟨B, hB, hbound⟩ := schedule.bottomPath_inverseGamma_cauchy_bound
    u x R hx hR_pos hR
  exact ⟨R, B, hR_pos, hB, hR, hbound⟩

theorem ExplicitFormulaCofinalHeightSchedule.bottomPath_inverseGamma_canonical_two_sided_carrier_bound
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c))
    (hcx : F.c ≤ x) (hc : 0 < F.c) :
    ∃ R ε A : ℝ, 0 < R ∧ 0 < ε ∧ 0 < A ∧
      (∀ w : ℂ, w ∈ Metric.closedBall
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x) R →
        ε ≤ ‖(Complex.Gammaℝ w)⁻¹‖) ∧
      (∀ w : ℂ, w ∈ Metric.closedBall
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x) R →
        ‖(Complex.Gammaℝ w)⁻¹‖ ≤ A) := by
  let r := F.rectangle (schedule.height u)
  let z := zetaCompletedExplicitFormulaBottomPath r x
  let pointwise := schedule.bottomPath_zeroExcisedPointwise u x hx
  let hsep := contourSingularPoint_norm_separation_of_factor_nonzero z
    pointwise.2.1 pointwise.2.2.1 pointwise.2.2.2.1
    pointwise.2.2.2.2.1 pointwise.2.2.2.2.2
  let R : ℝ := min (hsep.choose / 2) (r.c / 2)
  have hR_pos : 0 < R := by
    exact lt_min (half_pos hsep.choose_spec.1) (half_pos hc)
  have hR_c : R < r.c := by
    exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self hc)
  obtain ⟨ε, hε, hεbound⟩ :=
    inverseGamma_positive_lower_bound_on_bottomPath_ball_of_radius_lt_c_owner
      r x hcx hR_pos hR_c
  have hdiff : DiffContOnCl ℂ (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
      (Metric.ball z R) := inverseGamma_diffContOnCl_on_ball_owner z R
  obtain ⟨A, hA, hAbound⟩ :=
    exists_norm_upper_bound_of_isCompact_of_continuousOn
      (isCompact_closedBall z R)
      (closedBall_continuousOn_of_diffContOnCl z R hR_pos hdiff)
  exact ⟨R, ε, A, hR_pos, hε, hA, hεbound, hAbound⟩

theorem ExplicitFormulaCofinalHeightSchedule.topPath_inverseGamma_canonical_carrier_package
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) (hcx : F.c ≤ x) (hc : 0 < F.c) :
    ∃ R ε A : ℝ, 0 < R ∧ 0 < ε ∧ 0 < A ∧
      DiffContOnCl ℂ (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
        (Metric.ball
          (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x) R) ∧
      (∀ w : ℂ, w ∈ Metric.sphere
        (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x) R →
        ‖(Complex.Gammaℝ w)⁻¹‖ ≤ A) ∧
      (∀ w : ℂ, w ∈ Metric.closedBall
        (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x) R →
        ε ≤ ‖(Complex.Gammaℝ w)⁻¹‖) := by
  obtain ⟨R, ε, A, hR, hε, hA, hεbound, hAbound⟩ :=
    schedule.topPath_inverseGamma_canonical_two_sided_carrier_bound u x hx hcx hc
  have hDiff := inverseGamma_diffContOnCl_on_ball_owner
    (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x) R
  exact ⟨R, ε, A, hR, hε, hA, hDiff,
    (fun w hw => hAbound w (Metric.mem_closedBall.mpr hw.le)), hεbound⟩

theorem ExplicitFormulaCofinalHeightSchedule.bottomPath_inverseGamma_canonical_carrier_package
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) (hcx : F.c ≤ x) (hc : 0 < F.c) :
    ∃ R ε A : ℝ, 0 < R ∧ 0 < ε ∧ 0 < A ∧
      DiffContOnCl ℂ (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
        (Metric.ball
          (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x) R) ∧
      (∀ w : ℂ, w ∈ Metric.sphere
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x) R →
        ‖(Complex.Gammaℝ w)⁻¹‖ ≤ A) ∧
      (∀ w : ℂ, w ∈ Metric.closedBall
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x) R →
        ε ≤ ‖(Complex.Gammaℝ w)⁻¹‖) := by
  obtain ⟨R, ε, A, hR, hε, hA, hεbound, hAbound⟩ :=
    schedule.bottomPath_inverseGamma_canonical_two_sided_carrier_bound u x hx hcx hc
  have hDiff := inverseGamma_diffContOnCl_on_ball_owner
    (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x) R
  exact ⟨R, ε, A, hR, hε, hA, hDiff,
    (fun w hw => hAbound w (Metric.mem_closedBall.mpr hw.le)), hεbound⟩

theorem inverseGamma_positive_quotient_constant_owner
    {R A ε : ℝ} (hR : 0 < R) (hA : 0 < A) (hε : 0 < ε) :
    0 < (A / R) / ε :=
  div_pos (div_pos hA hR) hε

theorem ExplicitFormulaCofinalHeightSchedule.topPath_inverseGamma_canonical_cauchy_quotient_data
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) (hcx : F.c ≤ x) (hc : 0 < F.c) :
    ∃ R A ε : ℝ, 0 < R ∧ 0 < A ∧ 0 < ε ∧
      (∀ w : ℂ, w ∈ Metric.sphere
        (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x) R →
        ‖(Complex.Gammaℝ w)⁻¹‖ ≤ A) ∧
      ε ≤ ‖(Complex.Gammaℝ
        (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x))⁻¹‖ ∧
      0 < (A / R) / ε := by
  obtain ⟨R, ε, A, hR, hε, hA, _, hSphere, hLower⟩ :=
    schedule.topPath_inverseGamma_canonical_carrier_package u x hx hcx hc
  have hquot : 0 < (A / R) / ε :=
    inverseGamma_positive_quotient_constant_owner hR hA hε
  exact ⟨R, A, ε, hR, hA, hε, hSphere, hLower, hquot⟩

theorem ExplicitFormulaCofinalHeightSchedule.bottomPath_inverseGamma_canonical_cauchy_quotient_data
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) (hcx : F.c ≤ x) (hc : 0 < F.c) :
    ∃ R A ε : ℝ, 0 < R ∧ 0 < A ∧ 0 < ε ∧
      (∀ w : ℂ, w ∈ Metric.sphere
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x) R →
        ‖(Complex.Gammaℝ w)⁻¹‖ ≤ A) ∧
      ε ≤ ‖(Complex.Gammaℝ
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x))⁻¹‖ ∧
      0 < (A / R) / ε := by
  obtain ⟨R, ε, A, hR, hε, hA, _, hSphere, hLower⟩ :=
    schedule.bottomPath_inverseGamma_canonical_carrier_package u x hx hcx hc
  have hquot : 0 < (A / R) / ε :=
    inverseGamma_positive_quotient_constant_owner hR hA hε
  exact ⟨R, A, ε, hR, hA, hε, hSphere, hLower, hquot⟩

theorem ExplicitFormulaCofinalHeightSchedule.scheduled_pair_inverseGamma_canonical_quotient_constant
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) (hcx : F.c ≤ x) (hc : 0 < F.c) :
    ∃ q : ℝ, 0 < q ∧
      (∃ R A ε : ℝ, 0 < R ∧ 0 < A ∧ 0 < ε ∧
        (∀ w : ℂ, w ∈ Metric.sphere
          (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x) R →
          ‖(Complex.Gammaℝ w)⁻¹‖ ≤ A) ∧
        ε ≤ ‖(Complex.Gammaℝ
          (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x))⁻¹‖ ∧
        (A / R) / ε ≤ q) ∧
      (∃ R A ε : ℝ, 0 < R ∧ 0 < A ∧ 0 < ε ∧
        (∀ w : ℂ, w ∈ Metric.sphere
          (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x) R →
          ‖(Complex.Gammaℝ w)⁻¹‖ ≤ A) ∧
        ε ≤ ‖(Complex.Gammaℝ
          (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x))⁻¹‖ ∧
        (A / R) / ε ≤ q) := by
  obtain ⟨RTop, ATop, εTop, hRTop, hATop, hεTop, hTopSphere, hTopCenter, hTopQ⟩ :=
    schedule.topPath_inverseGamma_canonical_cauchy_quotient_data u x hx hcx hc
  obtain ⟨RBottom, ABottom, εBottom, hRBottom, hABottom, hεBottom,
      hBottomSphere, hBottomCenter, hBottomQ⟩ :=
    schedule.bottomPath_inverseGamma_canonical_cauchy_quotient_data u x hx hcx hc
  let qTop : ℝ := (ATop / RTop) / εTop
  let qBottom : ℝ := (ABottom / RBottom) / εBottom
  let q : ℝ := max qTop qBottom
  have hqTop : 0 < qTop := hTopQ
  have hqBottom : 0 < qBottom := hBottomQ
  exact ⟨q, lt_max hqTop hqBottom,
    ⟨RTop, ATop, εTop, hRTop, hATop, hεTop, hTopSphere, hTopCenter,
      le_max_left qTop qBottom⟩,
    ⟨RBottom, ABottom, εBottom, hRBottom, hABottom, hεBottom,
      hBottomSphere, hBottomCenter, le_max_right qTop qBottom⟩⟩

theorem positive_quotient_polynomial_height_bound_owner
    {q : ℝ} (hq : 0 < q) (height : ℝ) (K : ℕ) :
    q ≤ q * (1 + ‖height‖) ^ K :=
  le_mul_of_one_le_right (le_of_lt hq)
    (one_le_one_add_norm_pow height K)

theorem ExplicitFormulaCofinalHeightSchedule.topPath_inverseGamma_uniform_lower_bound
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        δ ≤ ‖(Complex.Gammaℝ
          (zetaCompletedExplicitFormulaTopPath
            (F.rectangle (schedule.height u)) x))⁻¹‖ := by
  let s : Set ℝ := Set.uIcc F.c (1 - F.c)
  have hs : IsCompact s := isCompact_uIcc
  have hs_nonempty : s.Nonempty :=
    ⟨F.c, Set.right_mem_uIcc⟩
  have hcontinuous : ContinuousOn
      (fun x : ℝ => (Complex.Gammaℝ
        (zetaCompletedExplicitFormulaTopPath
          (F.rectangle (schedule.height u)) x))⁻¹) s := by
    exact
      (Complex.differentiable_Gammaℝ_inv.continuous.comp
        (zetaCompletedExplicitFormulaTopPath_continuous
          (F.rectangle (schedule.height u)))).continuousOn
  obtain ⟨x₀, hx₀, hx₀_min⟩ :=
    hs.exists_isMinOn hs_nonempty hcontinuous.norm
  have hx₀_pos : 0 < ‖(Complex.Gammaℝ
      (zetaCompletedExplicitFormulaTopPath
        (F.rectangle (schedule.height u)) x₀))⁻¹‖ := by
    exact norm_pos_iff.mpr (inv_ne_zero
      ((schedule.topPath_zeroExcisedPointwise u x₀ hx₀).2.2.2.2.1))
  refine ⟨‖(Complex.Gammaℝ
      (zetaCompletedExplicitFormulaTopPath
        (F.rectangle (schedule.height u)) x₀))⁻¹‖, hx₀_pos, ?_⟩
  intro x hx
  exact hx₀_min hx

theorem ExplicitFormulaCofinalHeightSchedule.bottomPath_inverseGamma_uniform_lower_bound
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        δ ≤ ‖(Complex.Gammaℝ
          (zetaCompletedExplicitFormulaBottomPath
            (F.rectangle (schedule.height u)) x))⁻¹‖ := by
  let s : Set ℝ := Set.uIcc F.c (1 - F.c)
  have hs : IsCompact s := isCompact_uIcc
  have hs_nonempty : s.Nonempty :=
    ⟨F.c, Set.right_mem_uIcc⟩
  have hcontinuous : ContinuousOn
      (fun x : ℝ => (Complex.Gammaℝ
        (zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (schedule.height u)) x))⁻¹) s := by
    exact
      (Complex.differentiable_Gammaℝ_inv.continuous.comp
        (zetaCompletedExplicitFormulaBottomPath_continuous
          (F.rectangle (schedule.height u)))).continuousOn
  obtain ⟨x₀, hx₀, hx₀_min⟩ :=
    hs.exists_isMinOn hs_nonempty hcontinuous.norm
  have hx₀_pos : 0 < ‖(Complex.Gammaℝ
      (zetaCompletedExplicitFormulaBottomPath
        (F.rectangle (schedule.height u)) x₀))⁻¹‖ := by
    exact norm_pos_iff.mpr (inv_ne_zero
      ((schedule.bottomPath_zeroExcisedPointwise u x₀ hx₀).2.2.2.2.1))
  refine ⟨‖(Complex.Gammaℝ
      (zetaCompletedExplicitFormulaBottomPath
        (F.rectangle (schedule.height u)) x₀))⁻¹‖, hx₀_pos, ?_⟩
  intro x hx
  exact hx₀_min hx

theorem ExplicitFormulaCofinalHeightSchedule.topPath_zetaSideFactor_uniform_lower_bound
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        δ ≤ ‖zetaSideFactor
          (zetaCompletedExplicitFormulaTopPath
            (F.rectangle (schedule.height u)) x)‖ := by
  let s : Set ℝ := Set.uIcc F.c (1 - F.c)
  have hs : IsCompact s := isCompact_uIcc
  have hs_nonempty : s.Nonempty :=
    ⟨F.c, Set.right_mem_uIcc⟩
  have hcontinuous : ContinuousOn
      (fun x : ℝ => zetaSideFactor
        (zetaCompletedExplicitFormulaTopPath
          (F.rectangle (schedule.height u)) x)) s := by
    exact schedule.topPath_zetaSideFactor_continuousOn_owner u
  obtain ⟨x₀, hx₀, hx₀_min⟩ :=
    hs.exists_isMinOn hs_nonempty hcontinuous.norm
  have hx₀_pos : 0 < ‖zetaSideFactor
      (zetaCompletedExplicitFormulaTopPath
        (F.rectangle (schedule.height u)) x₀)‖ := by
    exact norm_pos_iff.mpr
      (zetaSideFactor_ne_zero
        ((schedule.topPath_zeroExcisedPointwise u x₀ hx₀).2.2.2.1)
        ((schedule.topPath_zeroExcisedPointwise u x₀ hx₀).2.2.2.2.1))
  refine ⟨‖zetaSideFactor
      (zetaCompletedExplicitFormulaTopPath
        (F.rectangle (schedule.height u)) x₀)‖, hx₀_pos, ?_⟩
  intro x hx
  exact hx₀_min hx

theorem ExplicitFormulaCofinalHeightSchedule.bottomPath_zetaSideFactor_uniform_lower_bound
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        δ ≤ ‖zetaSideFactor
          (zetaCompletedExplicitFormulaBottomPath
            (F.rectangle (schedule.height u)) x)‖ := by
  let s : Set ℝ := Set.uIcc F.c (1 - F.c)
  have hs : IsCompact s := isCompact_uIcc
  have hs_nonempty : s.Nonempty :=
    ⟨F.c, Set.right_mem_uIcc⟩
  have hcontinuous : ContinuousOn
      (fun x : ℝ => zetaSideFactor
        (zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (schedule.height u)) x)) s := by
    exact schedule.bottomPath_zetaSideFactor_continuousOn_owner u
  obtain ⟨x₀, hx₀, hx₀_min⟩ :=
    hs.exists_isMinOn hs_nonempty hcontinuous.norm
  have hx₀_pos : 0 < ‖zetaSideFactor
      (zetaCompletedExplicitFormulaBottomPath
        (F.rectangle (schedule.height u)) x₀)‖ := by
    exact norm_pos_iff.mpr
      (zetaSideFactor_ne_zero
        ((schedule.bottomPath_zeroExcisedPointwise u x₀ hx₀).2.2.2.1)
        ((schedule.bottomPath_zeroExcisedPointwise u x₀ hx₀).2.2.2.2.1))
  refine ⟨‖zetaSideFactor
      (zetaCompletedExplicitFormulaBottomPath
        (F.rectangle (schedule.height u)) x₀)‖, hx₀_pos, ?_⟩
  intro x hx
  exact hx₀_min hx

theorem ExplicitFormulaCofinalHeightSchedule.topPath_inverseGamma_logDeriv_continuousOn
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u : ℝ) :
    ContinuousOn
      (fun x : ℝ =>
        deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
            (zetaCompletedExplicitFormulaTopPath
              (F.rectangle (schedule.height u)) x) /
          (Complex.Gammaℝ
            (zetaCompletedExplicitFormulaTopPath
              (F.rectangle (schedule.height u)) x))⁻¹)
      (Set.uIcc F.c (1 - F.c)) := by
  intro x hx
  let s : ℂ := zetaCompletedExplicitFormulaTopPath
    (F.rectangle (schedule.height u)) x
  have hgammaAnalytic :
      AnalyticAt ℂ (fun z : ℂ => (Complex.Gammaℝ z)⁻¹) s :=
    Complex.differentiable_Gammaℝ_inv.analyticAt s
  have hderiv :
      ContinuousAt
        (fun z : ℂ => deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z) s :=
    analyticAt_deriv_continuousAt hgammaAnalytic
  have hgammaInv :
      ContinuousAt (fun z : ℂ => (Complex.Gammaℝ z)⁻¹) s :=
    Complex.differentiable_Gammaℝ_inv.continuous.continuousAt
  have hgamma : Complex.Gammaℝ s ≠ 0 := by
    exact (schedule.topPath_zeroExcisedPointwise u x hx).2.2.2.2.1
  have hquot :
      ContinuousAt
        (fun z : ℂ =>
          deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
            (Complex.Gammaℝ z)⁻¹) s :=
    hderiv.div hgammaInv (inv_ne_zero hgamma)
  have hpath :
      ContinuousAt
        (fun y : ℝ =>
          zetaCompletedExplicitFormulaTopPath
            (F.rectangle (schedule.height u)) y) x :=
    (zetaCompletedExplicitFormulaTopPath_continuous
      (F.rectangle (schedule.height u))).continuousAt
  exact (hquot.comp hpath).continuousWithinAt

theorem ExplicitFormulaCofinalHeightSchedule.topPath_inverseGamma_logDeriv_uniform_bound
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
            (zetaCompletedExplicitFormulaTopPath
              (F.rectangle (schedule.height u)) x) /
          (Complex.Gammaℝ
            (zetaCompletedExplicitFormulaTopPath
              (F.rectangle (schedule.height u)) x))⁻¹‖ ≤ B := by
  let s : Set ℝ := Set.uIcc F.c (1 - F.c)
  have hs : IsCompact s := isCompact_uIcc
  obtain ⟨B, hB, hbound⟩ :=
    exists_norm_upper_bound_of_isCompact_of_continuousOn
      hs
      (schedule.topPath_inverseGamma_logDeriv_continuousOn u)
  exact ⟨B, hB, hbound⟩

theorem ExplicitFormulaCofinalHeightSchedule.bottomPath_inverseGamma_logDeriv_continuousOn
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u : ℝ) :
    ContinuousOn
      (fun x : ℝ =>
        deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
            (zetaCompletedExplicitFormulaBottomPath
              (F.rectangle (schedule.height u)) x) /
          (Complex.Gammaℝ
            (zetaCompletedExplicitFormulaBottomPath
              (F.rectangle (schedule.height u)) x))⁻¹)
      (Set.uIcc F.c (1 - F.c)) := by
  intro x hx
  let s : ℂ := zetaCompletedExplicitFormulaBottomPath
    (F.rectangle (schedule.height u)) x
  have hgammaAnalytic :
      AnalyticAt ℂ (fun z : ℂ => (Complex.Gammaℝ z)⁻¹) s :=
    Complex.differentiable_Gammaℝ_inv.analyticAt s
  have hderiv :
      ContinuousAt
        (fun z : ℂ => deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z) s :=
    analyticAt_deriv_continuousAt hgammaAnalytic
  have hgammaInv :
      ContinuousAt (fun z : ℂ => (Complex.Gammaℝ z)⁻¹) s :=
    Complex.differentiable_Gammaℝ_inv.continuous.continuousAt
  have hgamma : Complex.Gammaℝ s ≠ 0 := by
    exact (schedule.bottomPath_zeroExcisedPointwise u x hx).2.2.2.2.1
  have hquot :
      ContinuousAt
        (fun z : ℂ =>
          deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
            (Complex.Gammaℝ z)⁻¹) s :=
    hderiv.div hgammaInv (inv_ne_zero hgamma)
  have hpath :
      ContinuousAt
        (fun y : ℝ =>
          zetaCompletedExplicitFormulaBottomPath
            (F.rectangle (schedule.height u)) y) x :=
    (zetaCompletedExplicitFormulaBottomPath_continuous
      (F.rectangle (schedule.height u))).continuousAt
  exact (hquot.comp hpath).continuousWithinAt

theorem ExplicitFormulaCofinalHeightSchedule.bottomPath_inverseGamma_logDeriv_uniform_bound
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
            (zetaCompletedExplicitFormulaBottomPath
              (F.rectangle (schedule.height u)) x) /
          (Complex.Gammaℝ
            (zetaCompletedExplicitFormulaBottomPath
              (F.rectangle (schedule.height u)) x))⁻¹‖ ≤ B := by
  let s : Set ℝ := Set.uIcc F.c (1 - F.c)
  have hs : IsCompact s := isCompact_uIcc
  obtain ⟨B, hB, hbound⟩ :=
    exists_norm_upper_bound_of_isCompact_of_continuousOn
      hs
      (schedule.bottomPath_inverseGamma_logDeriv_continuousOn u)
  exact ⟨B, hB, hbound⟩

/- Assemble both horizontal faces only after their individual compact bounds
   have been proved. -/
theorem ExplicitFormulaCofinalHeightSchedule.inverseGamma_logDeriv_uniform_bound_pair
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
            (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x) /
          (Complex.Gammaℝ
            (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x))⁻¹‖ ≤ B) ∧
      (∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
            (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x) /
          (Complex.Gammaℝ
            (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x))⁻¹‖ ≤ B) := by
  obtain ⟨Btop, hBtop, htop⟩ := schedule.topPath_inverseGamma_logDeriv_uniform_bound u
  obtain ⟨Bbottom, hBbottom, hbottom⟩ := schedule.bottomPath_inverseGamma_logDeriv_uniform_bound u
  refine ⟨max Btop Bbottom, le_max hBtop hBbottom, ?_, ?_⟩
  · intro x hx
    exact (htop x hx).trans (le_max_left Btop Bbottom)
  · intro x hx
    exact (hbottom x hx).trans (le_max_right Btop Bbottom)

theorem ExplicitFormulaScheduledFamilyAnalyticPackage.topPath_completedZero_separation
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ρ : {ρ : ℂ // _root_.Boundary.LFunctions.ZetaCompletedZero ρ},
        δ ≤
          ‖zetaCompletedExplicitFormulaTopPath
            (F.rectangle (h.height_schedule.height u)) x -
              ((1 / 2 : ℂ) + (ρ : ℂ))‖ :=
  h.height_schedule.topPath_completedZero_separation u x hx

theorem ExplicitFormulaScheduledFamilyAnalyticPackage.topPath_gammaPole_separation
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ n : ℕ,
        δ ≤
          ‖zetaCompletedExplicitFormulaTopPath
            (F.rectangle (h.height_schedule.height u)) x -
              (-(2 * (n : ℂ)))‖ :=
  h.height_schedule.topPath_gammaPole_separation u x hx

theorem ExplicitFormulaScheduledFamilyAnalyticPackage.bottomPath_completedZero_separation
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ρ : {ρ : ℂ // _root_.Boundary.LFunctions.ZetaCompletedZero ρ},
        δ ≤
          ‖zetaCompletedExplicitFormulaBottomPath
            (F.rectangle (h.height_schedule.height u)) x -
              ((1 / 2 : ℂ) + (ρ : ℂ))‖ :=
  h.height_schedule.bottomPath_completedZero_separation u x hx

theorem ExplicitFormulaScheduledFamilyAnalyticPackage.bottomPath_gammaPole_separation
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ n : ℕ,
        δ ≤
          ‖zetaCompletedExplicitFormulaBottomPath
            (F.rectangle (h.height_schedule.height u)) x -
              (-(2 * (n : ℂ)))‖ :=
  h.height_schedule.bottomPath_gammaPole_separation u x hx

theorem ExplicitFormulaFamilyAnalyticPackage.scheduled_topPath_completedZero_separation
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ρ : {ρ : ℂ // _root_.Boundary.LFunctions.ZetaCompletedZero ρ},
        δ ≤
          ‖zetaCompletedExplicitFormulaTopPath
            (F.rectangle (h.height_schedule.height u)) x -
              ((1 / 2 : ℂ) + (ρ : ℂ))‖ :=
  h.height_schedule.topPath_completedZero_separation u x hx

theorem ExplicitFormulaFamilyAnalyticPackage.scheduled_topPath_gammaPole_separation
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ n : ℕ,
        δ ≤
          ‖zetaCompletedExplicitFormulaTopPath
            (F.rectangle (h.height_schedule.height u)) x -
              (-(2 * (n : ℂ)))‖ :=
  h.height_schedule.topPath_gammaPole_separation u x hx

theorem ExplicitFormulaFamilyAnalyticPackage.scheduled_bottomPath_completedZero_separation
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ρ : {ρ : ℂ // _root_.Boundary.LFunctions.ZetaCompletedZero ρ},
        δ ≤
          ‖zetaCompletedExplicitFormulaBottomPath
            (F.rectangle (h.height_schedule.height u)) x -
              ((1 / 2 : ℂ) + (ρ : ℂ))‖ :=
  h.height_schedule.bottomPath_completedZero_separation u x hx

theorem ExplicitFormulaFamilyAnalyticPackage.scheduled_bottomPath_gammaPole_separation
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ n : ℕ,
        δ ≤
          ‖zetaCompletedExplicitFormulaBottomPath
            (F.rectangle (h.height_schedule.height u)) x -
              (-(2 * (n : ℂ)))‖ :=
  h.height_schedule.bottomPath_gammaPole_separation u x hx

theorem ExplicitFormulaCofinalHeightSchedule.topPath_singletonFactorBoundedCarrier
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ boundedCarrier :
        CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
          (min F.c (1 - F.c)) (max F.c (1 - F.c)),
      zetaCompletedExplicitFormulaTopPath
          (F.rectangle (schedule.height u)) x ∈
        boundedCarrier.carrier.carrier :=
  Exists.elim
    (schedule.topPath_completedZero_separation u x hx)
    (fun δCompleted hCompleted =>
      Exists.elim
        (schedule.topPath_gammaPole_separation u x hx)
        (fun δGamma hGamma =>
          let z : ℂ :=
            zetaCompletedExplicitFormulaTopPath
              (F.rectangle (schedule.height u)) x
          let pointwise := schedule.topPath_zeroExcisedPointwise u x hx
          let boundedCarrier :
              CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
                (min F.c (1 - F.c)) (max F.c (1 - F.c)) :=
            CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.singleton_of_singular_component_lower_bounds
              z pointwise.1 pointwise.2.1 pointwise.2.2.1
              pointwise.2.2.2.1 pointwise.2.2.2.2.1
              δCompleted δGamma hCompleted.1 hGamma.1
              hCompleted.2 hGamma.2
          Exists.intro boundedCarrier
            (CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.singleton_of_singular_component_lower_bounds_mem
              z pointwise.1 pointwise.2.1 pointwise.2.2.1
              pointwise.2.2.2.1 pointwise.2.2.2.2.1
              δCompleted δGamma hCompleted.1 hGamma.1
              hCompleted.2 hGamma.2)))

theorem ExplicitFormulaCofinalHeightSchedule.bottomPath_singletonFactorBoundedCarrier
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ boundedCarrier :
        CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
          (min F.c (1 - F.c)) (max F.c (1 - F.c)),
      zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (schedule.height u)) x ∈
        boundedCarrier.carrier.carrier :=
  Exists.elim
    (schedule.bottomPath_completedZero_separation u x hx)
    (fun δCompleted hCompleted =>
      Exists.elim
        (schedule.bottomPath_gammaPole_separation u x hx)
        (fun δGamma hGamma =>
          let z : ℂ :=
            zetaCompletedExplicitFormulaBottomPath
              (F.rectangle (schedule.height u)) x
          let pointwise := schedule.bottomPath_zeroExcisedPointwise u x hx
          let boundedCarrier :
              CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
                (min F.c (1 - F.c)) (max F.c (1 - F.c)) :=
            CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.singleton_of_singular_component_lower_bounds
              z pointwise.1 pointwise.2.1 pointwise.2.2.1
              pointwise.2.2.2.1 pointwise.2.2.2.2.1
              δCompleted δGamma hCompleted.1 hGamma.1
              hCompleted.2 hGamma.2
          Exists.intro boundedCarrier
            (CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.singleton_of_singular_component_lower_bounds_mem
              z pointwise.1 pointwise.2.1 pointwise.2.2.1
              pointwise.2.2.2.1 pointwise.2.2.2.2.1
              δCompleted δGamma hCompleted.1 hGamma.1
              hCompleted.2 hGamma.2)))

theorem ExplicitFormulaCofinalHeightSchedule.horizontalPairFactorBoundedCarrier
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ boundedCarrier :
        CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
          (min F.c (1 - F.c)) (max F.c (1 - F.c)),
      zetaCompletedExplicitFormulaTopPath
          (F.rectangle (schedule.height u)) x ∈
        boundedCarrier.carrier.carrier ∧
      zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (schedule.height u)) x ∈
        boundedCarrier.carrier.carrier :=
  Exists.elim
    (schedule.topPath_singletonFactorBoundedCarrier u x hx)
    (fun topBounded topMem =>
      Exists.elim
        (schedule.bottomPath_singletonFactorBoundedCarrier u x hx)
        (fun bottomBounded bottomMem =>
          let combinedCarrier :
              CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
                (min F.c (1 - F.c)) (max F.c (1 - F.c)) :=
            CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.union
              topBounded bottomBounded
          Exists.intro combinedCarrier
            (And.intro
              (CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.mem_union_left
                topBounded bottomBounded topMem)
              (CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.mem_union_right
                topBounded bottomBounded bottomMem))))

theorem ExplicitFormulaScheduledFamilyAnalyticPackage.topPath_singletonFactorBoundedCarrier
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ boundedCarrier :
        CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
          (min F.c (1 - F.c)) (max F.c (1 - F.c)),
      zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈
        boundedCarrier.carrier.carrier :=
  h.height_schedule.topPath_singletonFactorBoundedCarrier u x hx

theorem ExplicitFormulaScheduledFamilyAnalyticPackage.bottomPath_singletonFactorBoundedCarrier
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ boundedCarrier :
        CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
          (min F.c (1 - F.c)) (max F.c (1 - F.c)),
      zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈
        boundedCarrier.carrier.carrier :=
  h.height_schedule.bottomPath_singletonFactorBoundedCarrier u x hx

theorem ExplicitFormulaScheduledFamilyAnalyticPackage.horizontalPairFactorBoundedCarrier
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ boundedCarrier :
        CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
          (min F.c (1 - F.c)) (max F.c (1 - F.c)),
      zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈
        boundedCarrier.carrier.carrier ∧
      zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈
        boundedCarrier.carrier.carrier :=
  h.height_schedule.horizontalPairFactorBoundedCarrier u x hx

theorem ExplicitFormulaFamilyAnalyticPackage.scheduled_topPath_singletonFactorBoundedCarrier
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ boundedCarrier :
        CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
          (min F.c (1 - F.c)) (max F.c (1 - F.c)),
      zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈
        boundedCarrier.carrier.carrier :=
  h.height_schedule.topPath_singletonFactorBoundedCarrier u x hx

theorem ExplicitFormulaFamilyAnalyticPackage.scheduled_bottomPath_singletonFactorBoundedCarrier
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ boundedCarrier :
        CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
          (min F.c (1 - F.c)) (max F.c (1 - F.c)),
      zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈
        boundedCarrier.carrier.carrier :=
  h.height_schedule.bottomPath_singletonFactorBoundedCarrier u x hx

theorem ExplicitFormulaFamilyAnalyticPackage.scheduled_horizontalPairFactorBoundedCarrier
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ boundedCarrier :
        CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
          (min F.c (1 - F.c)) (max F.c (1 - F.c)),
      zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈
        boundedCarrier.carrier.carrier ∧
      zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈
        boundedCarrier.carrier.carrier :=
  h.height_schedule.horizontalPairFactorBoundedCarrier u x hx

theorem ExplicitFormulaFamilyAnalyticPackage.scheduled_horizontalFiniteWindowFactorBoundedCarrier_of_pointwise
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (xs : List ℝ)
    (hx : ∀ x : ℝ, x ∈ xs → x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ boundedCarrier :
        CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
          (min F.c (1 - F.c)) (max F.c (1 - F.c)),
      (∀ x : ℝ, x ∈ xs →
        zetaCompletedExplicitFormulaTopPath
            (F.rectangle (h.height_schedule.height u)) x ∈
          boundedCarrier.carrier.carrier) ∧
      (∀ x : ℝ, x ∈ xs →
        zetaCompletedExplicitFormulaBottomPath
            (F.rectangle (h.height_schedule.height u)) x ∈
          boundedCarrier.carrier.carrier) :=
  ExplicitFormulaFamilyAnalyticPackage.scheduled_horizontalFiniteWindowFactorBoundedCarrier
    h u xs
    (fun x hxmem =>
      ExplicitFormulaFamilyAnalyticPackage.scheduled_horizontalPairFactorBoundedCarrier
        h u x (hx x hxmem))

theorem ExplicitFormulaCofinalHeightSchedule.topPath_singularPoint_separation
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ q : ℂ,
        explicitFormulaContourSingularPoint q →
          δ ≤ ‖zetaCompletedExplicitFormulaTopPath
            (F.rectangle (schedule.height u)) x - q‖ := by
  let pointwise := schedule.topPath_zeroExcisedPointwise u x hx
  exact contourSingularPoint_norm_separation_of_factor_nonzero
    (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x)
    pointwise.2.1 pointwise.2.2.1 pointwise.2.2.2.1
    pointwise.2.2.2.2.1 pointwise.2.2.2.2.2

theorem ExplicitFormulaCofinalHeightSchedule.bottomPath_singularPoint_separation
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ q : ℂ,
        explicitFormulaContourSingularPoint q →
          δ ≤ ‖zetaCompletedExplicitFormulaBottomPath
            (F.rectangle (schedule.height u)) x - q‖ := by
  let pointwise := schedule.bottomPath_zeroExcisedPointwise u x hx
  exact contourSingularPoint_norm_separation_of_factor_nonzero
    (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x)
    pointwise.2.1 pointwise.2.2.1 pointwise.2.2.2.1
    pointwise.2.2.2.2.1 pointwise.2.2.2.2.2

theorem ExplicitFormulaCofinalHeightSchedule.topPath_singularPoint_canonical_carrier
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ R : ℝ, 0 < R ∧
      DiffContOnCl ℂ zetaSideFactor
        (Metric.ball
          (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x) R) ∧
      (∀ w : ℂ, w ∈ Metric.closedBall
        (zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x) R →
        zetaSideFactor w ≠ 0) := by
  let z : ℂ :=
    zetaCompletedExplicitFormulaTopPath (F.rectangle (schedule.height u)) x
  obtain ⟨R, δ, hR, hδ, hRδ, hseparated, hnonsingular⟩ :=
    singularSeparation_halfRadius z
      (schedule.topPath_singularPoint_separation u x hx)
  exact ⟨R, hR,
    zetaSideFactor_diffContOnCl_of_closedBall_nonsingular z R
      hnonsingular,
    zetaSideFactor_ne_zero_on_closedBall_of_singular_separation z R δ
      hseparated hRδ⟩

theorem ExplicitFormulaCofinalHeightSchedule.bottomPath_singularPoint_canonical_carrier
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ R : ℝ, 0 < R ∧
      DiffContOnCl ℂ zetaSideFactor
        (Metric.ball
          (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x) R) ∧
      (∀ w : ℂ, w ∈ Metric.closedBall
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x) R →
        zetaSideFactor w ≠ 0) := by
  let z : ℂ :=
    zetaCompletedExplicitFormulaBottomPath (F.rectangle (schedule.height u)) x
  obtain ⟨R, δ, hR, hδ, hRδ, hseparated, hnonsingular⟩ :=
    singularSeparation_halfRadius z
      (schedule.bottomPath_singularPoint_separation u x hx)
  exact ⟨R, hR,
    zetaSideFactor_diffContOnCl_of_closedBall_nonsingular z R
      hnonsingular,
    zetaSideFactor_ne_zero_on_closedBall_of_singular_separation z R δ
      hseparated hRδ⟩

theorem ExplicitFormulaFamilyAnalyticPackage.scheduled_horizontalFiniteSampleFactorBoundedCarrier_of_pointwise
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (samples : List (ℝ × ℝ))
    (hx : ∀ p : ℝ × ℝ, p ∈ samples → p.2 ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ boundedCarrier :
        CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
          (min F.c (1 - F.c)) (max F.c (1 - F.c)),
      (∀ p : ℝ × ℝ, p ∈ samples →
        zetaCompletedExplicitFormulaTopPath
            (F.rectangle (h.height_schedule.height p.1)) p.2 ∈
          boundedCarrier.carrier.carrier) ∧
      (∀ p : ℝ × ℝ, p ∈ samples →
        zetaCompletedExplicitFormulaBottomPath
            (F.rectangle (h.height_schedule.height p.1)) p.2 ∈
          boundedCarrier.carrier.carrier) :=
  ExplicitFormulaFamilyAnalyticPackage.scheduled_horizontalFiniteSampleFactorBoundedCarrier_of_owner_separation
    h samples hx

theorem scheduled_pair_positive_quotient_constant_owner
    {qTop qBottom : ℝ} (hTop : 0 < qTop) (hBottom : 0 < qBottom) :
    ∃ q : ℝ, 0 < q ∧ qTop ≤ q ∧ qBottom ≤ q := by
  refine ⟨max qTop qBottom, ?_, ?_, ?_⟩
  · exact lt_max hTop hBottom
  · exact le_max_left qTop qBottom
  · exact le_max_right qTop qBottom

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
