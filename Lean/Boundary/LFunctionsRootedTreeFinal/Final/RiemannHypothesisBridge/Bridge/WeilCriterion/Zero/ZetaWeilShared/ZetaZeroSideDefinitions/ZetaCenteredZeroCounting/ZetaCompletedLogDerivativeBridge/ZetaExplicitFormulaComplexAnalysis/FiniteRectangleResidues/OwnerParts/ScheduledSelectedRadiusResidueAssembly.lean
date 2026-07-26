import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part29
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.ScheduledSelectedRadiusCauchy
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaAnalyticPackage.ScheduledLogDerivControl

/-!
# Scheduled selected-radius residue assembly

This file owns the scheduled-package pointwise raw Cauchy residue theorem
after the finite-hole Cauchy zero and all deleted-circle local regularity data
have been supplied explicitly.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- At a scheduled height, finite-hole Cauchy plus explicit deleted-circle local
regularity gives the raw tangent `2πi` residue identity. -/
theorem zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_scheduledPackage_localRegularity
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F) (u ε : ℝ)
    (hε_pos : 0 < ε)
    (s0 s1 : Set ℂ) (hs0 : s0.Countable) (hs1 : s1.Countable)
    (szero : {ρ : ℂ // ZetaCompletedZero ρ} → Set ℂ)
    (hszero :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow
            (h.height_schedule.height u) →
          (szero ρ).Countable)
    (hcauchy :
      explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
        f F (h.height_schedule.height u) ε = 0)
    (hzero_continuous :
      ContinuousOn
        (fun z : ℂ => (z - 0) * zetaCompletedExplicitFormulaContourIntegrand f z)
        (Metric.closedBall (0 : ℂ) ε \ {(0 : ℂ)}))
    (hzero_differentiable :
      ∀ z : ℂ,
        z ∈ (Metric.ball (0 : ℂ) ε \ {(0 : ℂ)}) \ s0 →
          DifferentiableAt ℂ
            (fun w : ℂ => (w - 0) * zetaCompletedExplicitFormulaContourIntegrand f w)
            z)
    (hone_continuous :
      ContinuousOn
        (fun z : ℂ => (z - 1) * zetaCompletedExplicitFormulaContourIntegrand f z)
        (Metric.closedBall (1 : ℂ) ε \ {(1 : ℂ)}))
    (hone_differentiable :
      ∀ z : ℂ,
        z ∈ (Metric.ball (1 : ℂ) ε \ {(1 : ℂ)}) \ s1 →
          DifferentiableAt ℂ
            (fun w : ℂ => (w - 1) * zetaCompletedExplicitFormulaContourIntegrand f w)
            z)
    (hcompleted_continuous :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow
            (h.height_schedule.height u) →
          ContinuousOn
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate ρ) *
                zetaCompletedExplicitFormulaContourIntegrand f z)
            (Metric.closedBall (completedZeroResidueCoordinate ρ) ε \
              {completedZeroResidueCoordinate ρ}))
    (hcompleted_differentiable :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ∀ _hρ : ρ ∈ explicitFormulaCompletedZeroContourHeightWindow
            (h.height_schedule.height u),
          ∀ z : ℂ,
            z ∈ (Metric.ball (completedZeroResidueCoordinate ρ) ε \
                {completedZeroResidueCoordinate ρ}) \ szero ρ →
              DifferentiableAt ℂ
                (fun w : ℂ =>
                  (w - completedZeroResidueCoordinate ρ) *
                    zetaCompletedExplicitFormulaContourIntegrand f w)
                z)
    (hlocal :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow
            (h.height_schedule.height u) →
          Tendsto
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate ρ) *
                zetaCompletedExplicitFormulaContourIntegrand f z)
            (𝓝[≠] (completedZeroResidueCoordinate ρ))
            (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ)))) :
    zetaCompletedExplicitFormulaTangentContourIntegral f
        (F.rectangle (h.height_schedule.height u)) =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaRectangle_poleCorrectedResidueSum f
          (h.height_schedule.height u) :=
  zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_finiteRadiusPuncturedBoundary_and_localRegularity
    f F (h.height_schedule.height u) ε
    h.phi_control
    hε_pos
    s0
    s1
    hs0
    hs1
    szero
    hszero
    hcauchy
    hzero_continuous
    hzero_differentiable
    hone_continuous
    hone_differentiable
    hcompleted_continuous
    hcompleted_differentiable
    hlocal

/- The deleted-circle limit is an owner theorem: once the scheduled package's
   transform control is unfolded, the corrected completed-zero coordinate has
   the required residue limit.  This keeps the scheduled assembly from asking
   its callers to re-prove that local analytic fact. -/
theorem zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_scheduledPackage_localRegularity_ownerLocal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F) (u ε : ℝ)
    (hT : 0 < h.height_schedule.height u) (hε_pos : 0 < ε)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow
            (h.height_schedule.height u) ↔
          completedZeroResidueCoordinate ρ ∈
              explicitFormulaContourFamilyInterior F (h.height_schedule.height u) ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hboundaryRegular :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F (h.height_schedule.height u) →
          ContinuousAt
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hboundaryAvoidance :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F (h.height_schedule.height u) →
          z ∉ completedZetaContourIntegrandSingularSet)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
          Metric.closedBall a ε ⊆
            explicitFormulaContourFamilyInterior F (h.height_schedule.height u))
    (hseparated :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
              a ≠ b → ε + ε < dist a b)
    (hregular :
      ε ∉ finiteRectangleSquareSideForbiddenRadii
        (explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u)))
    (s0 s1 : Set ℂ) (hs0 : s0.Countable) (hs1 : s1.Countable)
    (szero : {ρ : ℂ // ZetaCompletedZero ρ} → Set ℂ)
    (hszero :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow
            (h.height_schedule.height u) →
          (szero ρ).Countable)
    (hzero_continuous :
      ContinuousOn
        (fun z : ℂ => (z - 0) * zetaCompletedExplicitFormulaContourIntegrand f z)
        (Metric.closedBall (0 : ℂ) ε \ {(0 : ℂ)}))
    (hzero_differentiable :
      ∀ z : ℂ,
        z ∈ (Metric.ball (0 : ℂ) ε \ {(0 : ℂ)}) \ s0 →
          DifferentiableAt ℂ
            (fun w : ℂ => (w - 0) * zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hone_continuous :
      ContinuousOn
        (fun z : ℂ => (z - 1) * zetaCompletedExplicitFormulaContourIntegrand f z)
        (Metric.closedBall (1 : ℂ) ε \ {(1 : ℂ)}))
    (hone_differentiable :
      ∀ z : ℂ,
        z ∈ (Metric.ball (1 : ℂ) ε \ {(1 : ℂ)}) \ s1 →
          DifferentiableAt ℂ
            (fun w : ℂ => (w - 1) * zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hcompleted_continuous :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow
            (h.height_schedule.height u) →
          ContinuousOn
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate ρ) *
                zetaCompletedExplicitFormulaContourIntegrand f z)
            (Metric.closedBall (completedZeroResidueCoordinate ρ) ε \
              {completedZeroResidueCoordinate ρ}))
    (hcompleted_differentiable :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ∀ hρ : ρ ∈ explicitFormulaCompletedZeroContourHeightWindow
            (h.height_schedule.height u),
          ∀ z : ℂ,
            z ∈ (Metric.ball (completedZeroResidueCoordinate ρ) ε \
                {completedZeroResidueCoordinate ρ}) \ szero ρ →
              DifferentiableAt ℂ
                (fun w : ℂ =>
                  (w - completedZeroResidueCoordinate ρ) *
                    zetaCompletedExplicitFormulaContourIntegrand f w) z) :
    zetaCompletedExplicitFormulaTangentContourIntegral f
        (F.rectangle (h.height_schedule.height u)) =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaRectangle_poleCorrectedResidueSum f
          (h.height_schedule.height u) := by
  have hlocal :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow
            (h.height_schedule.height u) →
          Tendsto
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate ρ) *
                zetaCompletedExplicitFormulaContourIntegrand f z)
            (𝓝[≠] (completedZeroResidueCoordinate ρ))
            (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ))) :=
    fun ρ hρ =>
      zetaCompletedExplicitFormulaRectangle_localCompletedZeroResidue_owner
        f F h.phi_control (h.height_schedule.height u) hT ρ hρ
  exact zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_scheduledPackage_localRegularity
    f F h u ε hT hε_pos hinterior hboundaryRegular hboundaryAvoidance hclosed
    hseparated hregular s0 s1 hs0 hs1 szero hszero hzero_continuous
    hzero_differentiable hone_continuous hone_differentiable hcompleted_continuous
    hcompleted_differentiable hlocal

/-- At a scheduled height, selected-radius finite-hole Cauchy plus explicit
deleted-circle local regularity gives the raw tangent `2πi` residue identity. -/
theorem zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_scheduledPackage_selectedRegularRadius_localRegularity
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F) (u ε : ℝ)
    (hT : 0 < h.height_schedule.height u) (hε_pos : 0 < ε)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow
            (h.height_schedule.height u) ↔
          completedZeroResidueCoordinate ρ ∈
              explicitFormulaContourFamilyInterior F (h.height_schedule.height u) ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hboundaryRegular :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F (h.height_schedule.height u) →
          ContinuousAt
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hboundaryAvoidance :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F (h.height_schedule.height u) →
          z ∉ completedZetaContourIntegrandSingularSet)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
          Metric.closedBall a ε ⊆
            explicitFormulaContourFamilyInterior F (h.height_schedule.height u))
    (hseparated :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
              a ≠ b → ε + ε < dist a b)
    (hregular :
      ε ∉ finiteRectangleSquareSideForbiddenRadii
        (explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u)))
    (s0 s1 : Set ℂ) (hs0 : s0.Countable) (hs1 : s1.Countable)
    (szero : {ρ : ℂ // ZetaCompletedZero ρ} → Set ℂ)
    (hszero :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow
            (h.height_schedule.height u) →
          (szero ρ).Countable)
    (hzero_continuous :
      ContinuousOn
        (fun z : ℂ => (z - 0) * zetaCompletedExplicitFormulaContourIntegrand f z)
        (Metric.closedBall (0 : ℂ) ε \ {(0 : ℂ)}))
    (hzero_differentiable :
      ∀ z : ℂ,
        z ∈ (Metric.ball (0 : ℂ) ε \ {(0 : ℂ)}) \ s0 →
          DifferentiableAt ℂ
            (fun w : ℂ => (w - 0) * zetaCompletedExplicitFormulaContourIntegrand f w)
            z)
    (hone_continuous :
      ContinuousOn
        (fun z : ℂ => (z - 1) * zetaCompletedExplicitFormulaContourIntegrand f z)
        (Metric.closedBall (1 : ℂ) ε \ {(1 : ℂ)}))
    (hone_differentiable :
      ∀ z : ℂ,
        z ∈ (Metric.ball (1 : ℂ) ε \ {(1 : ℂ)}) \ s1 →
          DifferentiableAt ℂ
            (fun w : ℂ => (w - 1) * zetaCompletedExplicitFormulaContourIntegrand f w)
            z)
    (hcompleted_continuous :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow
            (h.height_schedule.height u) →
          ContinuousOn
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate ρ) *
                zetaCompletedExplicitFormulaContourIntegrand f z)
            (Metric.closedBall (completedZeroResidueCoordinate ρ) ε \
              {completedZeroResidueCoordinate ρ}))
    (hcompleted_differentiable :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ∀ hρ : ρ ∈ explicitFormulaCompletedZeroContourHeightWindow
            (h.height_schedule.height u),
          ∀ z : ℂ,
            z ∈ (Metric.ball (completedZeroResidueCoordinate ρ) ε \
                {completedZeroResidueCoordinate ρ}) \ szero ρ →
              DifferentiableAt ℂ
                (fun w : ℂ =>
                  (w - completedZeroResidueCoordinate ρ) *
                    zetaCompletedExplicitFormulaContourIntegrand f w)
                z)
    (hlocal :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow
            (h.height_schedule.height u) →
          Tendsto
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate ρ) *
                zetaCompletedExplicitFormulaContourIntegrand f z)
            (𝓝[≠] (completedZeroResidueCoordinate ρ))
            (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ)))) :
    zetaCompletedExplicitFormulaTangentContourIntegral f
        (F.rectangle (h.height_schedule.height u)) =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaRectangle_poleCorrectedResidueSum f
          (h.height_schedule.height u) :=
  let hcauchy :
      explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
        f F (h.height_schedule.height u) ε = 0 :=
    explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_scheduledPackage_selectedRegularRadius
      f F h hT hε_pos hinterior hboundaryRegular hboundaryAvoidance hclosed hseparated hregular
  zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_scheduledPackage_localRegularity
    f F h u ε hε_pos s0 s1 hs0 hs1 szero hszero hcauchy
    hzero_continuous
    hzero_differentiable
    hone_continuous
    hone_differentiable
    hcompleted_continuous
    hcompleted_differentiable
    hlocal

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
