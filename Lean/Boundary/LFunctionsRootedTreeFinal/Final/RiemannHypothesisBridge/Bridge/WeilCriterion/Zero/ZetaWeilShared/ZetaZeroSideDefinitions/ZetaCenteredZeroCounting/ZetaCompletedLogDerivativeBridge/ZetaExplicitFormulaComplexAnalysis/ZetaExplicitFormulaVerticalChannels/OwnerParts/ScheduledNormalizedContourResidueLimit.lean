import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.NormalizedContourResidueLimit
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaHorizontalEdgeBounds.Scheduled
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.ScheduledSelectedRadiusResidueClosedGeometry

/-!
# Scheduled normalized contour residue limit

This file owns the scheduled-package version of the normalized contour
zero-side limit.  The only remaining input is the selected tangent-residue
identity along the same height schedule.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The scheduled-package normalized vertical side with the completed-pole
residue packet removed. -/
noncomputable def explicitFormulaScheduledPackageNormalizedPoleCorrectedVerticalDifference
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  (zetaCompletedExplicitFormulaRightLineIntegral f
        (F.rectangle (h.height_schedule.height u)) -
      zetaCompletedExplicitFormulaLeftLineIntegral f
        (F.rectangle (h.height_schedule.height u))) /
      explicitFormulaTwoPi -
    explicitFormulaRectangle_completedPoleResidueSum f

theorem explicitFormulaScheduledPackage_poleCorrectedResidueSum_eq_normalizedTangentContourIntegral_eventually_canonical_owner
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F) :
    ∀ᶠ u in atTop,
      explicitFormulaRectangle_poleCorrectedResidueSum f
          (h.height_schedule.height u) =
        zetaCompletedExplicitFormulaNormalizedTangentContourIntegral f
          (F.rectangle (h.height_schedule.height u)) := by
  filter_upwards [h.height_schedule.eventually_height_pos] with u hu
  exact
    (zetaCompletedExplicitFormulaNormalizedTangentContourIntegral_eq_poleCorrectedResidueSum_canonicalInterior_owner
      f F h hu).symm

/-- Forgetting a full analytic package to a scheduled package does not change
the normalized pole-corrected vertical expression. -/
theorem explicitFormulaScheduledPackageNormalizedPoleCorrectedVerticalDifference_of_fullPackage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    explicitFormulaScheduledPackageNormalizedPoleCorrectedVerticalDifference
        f F h.toScheduledFamilyAnalyticPackage u =
      explicitFormulaScheduledNormalizedPoleCorrectedVerticalDifference
        f F h u :=
  Eq.refl _

/-- A normalized tangent residue limit and scheduled-package horizontal decay
imply the same residue limit for the normalized project-oriented contour. -/
theorem zetaCompletedExplicitFormulaNormalizedContourIntegral_tendsto_of_scheduledPackage_tangent_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F) (residueSum : ℂ)
    (htangent :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaNormalizedTangentContourIntegral f
            (F.rectangle (h.height_schedule.height u)))
        atTop (𝓝 residueSum))
    (hhorizontal :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledPackageHorizontalSideDifference h u)
        atTop (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaNormalizedContourIntegral f
          (F.rectangle (h.height_schedule.height u)))
      atTop (𝓝 residueSum) := by
  have htangentRaw :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaTangentContourIntegral f
            (F.rectangle (h.height_schedule.height u)))
        atTop
        (𝓝 (explicitFormulaTwoPiI * residueSum)) := by
    have hscaled := htangent.const_mul explicitFormulaTwoPiI
    have hpointwise :
        (fun u : ℝ =>
          explicitFormulaTwoPiI *
            zetaCompletedExplicitFormulaNormalizedTangentContourIntegral f
              (F.rectangle (h.height_schedule.height u))) =
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaTangentContourIntegral f
            (F.rectangle (h.height_schedule.height u))) := by
      exact funext (fun u : ℝ => by
        have hright :
            zetaCompletedExplicitFormulaNormalizedTangentContourIntegral f
                (F.rectangle (h.height_schedule.height u)) * explicitFormulaTwoPiI =
              zetaCompletedExplicitFormulaTangentContourIntegral f
                (F.rectangle (h.height_schedule.height u)) :=
          (eq_div_iff explicitFormulaTwoPiI_ne_zero).mp (Eq.refl
            (zetaCompletedExplicitFormulaNormalizedTangentContourIntegral f
              (F.rectangle (h.height_schedule.height u))))
        exact Eq.trans
          (mul_comm explicitFormulaTwoPiI
            (zetaCompletedExplicitFormulaNormalizedTangentContourIntegral f
              (F.rectangle (h.height_schedule.height u))))
          hright)
    exact Eq.subst
      (motive := fun values : ℝ → ℂ =>
        Tendsto values atTop (𝓝 (explicitFormulaTwoPiI * residueSum)))
      hpointwise hscaled
  have hrotated :
      Tendsto
        (fun u : ℝ =>
          (-Complex.I) *
            zetaCompletedExplicitFormulaTangentContourIntegral f
              (F.rectangle (h.height_schedule.height u)))
        atTop
        (𝓝 (explicitFormulaTwoPi * residueSum)) := by
    have hbase := htangentRaw.const_mul (-Complex.I)
    exact Eq.subst
      (motive := fun target : ℂ =>
        Tendsto
          (fun u : ℝ =>
            (-Complex.I) *
              zetaCompletedExplicitFormulaTangentContourIntegral f
                (F.rectangle (h.height_schedule.height u)))
          atTop (𝓝 target))
      (explicitFormula_negI_mul_twoPiI_mul residueSum)
      hbase
  have hcorrection :
      Tendsto
        (fun u : ℝ =>
          ((1 : ℂ) - Complex.I) *
            explicitFormulaScheduledPackageHorizontalSideDifference h u)
        atTop (𝓝 0) := by
    have hbase := hhorizontal.const_mul ((1 : ℂ) - Complex.I)
    exact Eq.subst
      (motive := fun target : ℂ =>
        Tendsto
          (fun u : ℝ =>
            ((1 : ℂ) - Complex.I) *
              explicitFormulaScheduledPackageHorizontalSideDifference h u)
          atTop (𝓝 target))
      (mul_zero ((1 : ℂ) - Complex.I)) hbase
  have hprojectRaw :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaContourIntegral f
            (F.rectangle (h.height_schedule.height u)))
        atTop (𝓝 (explicitFormulaTwoPi * residueSum)) := by
    have hsum := hrotated.add hcorrection
    have hpointwise :
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaContourIntegral f
            (F.rectangle (h.height_schedule.height u))) =
        (fun u : ℝ =>
          (-Complex.I) *
              zetaCompletedExplicitFormulaTangentContourIntegral f
                (F.rectangle (h.height_schedule.height u)) +
            ((1 : ℂ) - Complex.I) *
              explicitFormulaScheduledPackageHorizontalSideDifference h u) := by
      exact funext (fun u : ℝ =>
        zetaCompletedExplicitFormulaContourIntegral_eq_negI_mul_tangent_add_horizontalCorrection
          f (F.rectangle (h.height_schedule.height u)))
    have htarget : explicitFormulaTwoPi * residueSum + 0 =
        explicitFormulaTwoPi * residueSum := add_zero _
    exact Eq.subst
      (motive := fun values : ℝ → ℂ =>
        Tendsto values atTop (𝓝 (explicitFormulaTwoPi * residueSum)))
      hpointwise.symm
      (Eq.subst
        (motive := fun target : ℂ =>
          Tendsto
            (fun u : ℝ =>
              (-Complex.I) *
                  zetaCompletedExplicitFormulaTangentContourIntegral f
                    (F.rectangle (h.height_schedule.height u)) +
                ((1 : ℂ) - Complex.I) *
                  explicitFormulaScheduledPackageHorizontalSideDifference h u)
            atTop (𝓝 target))
        htarget hsum)
  have hnormalized := hprojectRaw.div_const explicitFormulaTwoPi
  have htarget :
      (explicitFormulaTwoPi * residueSum) / explicitFormulaTwoPi = residueSum := by
    calc
      (explicitFormulaTwoPi * residueSum) / explicitFormulaTwoPi =
          (residueSum * explicitFormulaTwoPi) / explicitFormulaTwoPi := by
        exact congrArg (fun value : ℂ => value / explicitFormulaTwoPi)
          (mul_comm explicitFormulaTwoPi residueSum)
      _ = residueSum := mul_div_cancel_right₀ residueSum explicitFormulaTwoPi_ne_zero
  exact Eq.subst
    (motive := fun target : ℂ =>
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaNormalizedContourIntegral f
            (F.rectangle (h.height_schedule.height u)))
        atTop (𝓝 target))
    htarget hnormalized

/-- Pointwise selected-radius tangent residue equality at positive scheduled
heights supplies the eventual tangent-residue equality consumed by the
scheduled zero-side endpoint. -/
theorem explicitFormulaRectangle_poleCorrectedResidueSum_eventually_eq_normalizedTangent_of_scheduledPackage_pointwise
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F)
    (hpointwise :
      ∀ u : ℝ,
        0 < h.height_schedule.height u →
          zetaCompletedExplicitFormulaNormalizedTangentContourIntegral f
              (F.rectangle (h.height_schedule.height u)) =
            explicitFormulaRectangle_poleCorrectedResidueSum f
              (h.height_schedule.height u)) :
    ∀ᶠ u in atTop,
      explicitFormulaRectangle_poleCorrectedResidueSum f
          (h.height_schedule.height u) =
        zetaCompletedExplicitFormulaNormalizedTangentContourIntegral f
          (F.rectangle (h.height_schedule.height u)) :=
  h.height_schedule.eventually_height_pos.mono
    (fun u hu =>
      (hpointwise u hu).symm)

/-- Pointwise raw Cauchy tangent-residue equality at positive scheduled heights
supplies the eventual normalized tangent-residue equality consumed by the
scheduled zero-side endpoint. -/
theorem explicitFormulaRectangle_poleCorrectedResidueSum_eventually_eq_normalizedTangent_of_scheduledPackage_rawPointwise
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F)
    (hraw :
      ∀ u : ℝ,
        0 < h.height_schedule.height u →
          zetaCompletedExplicitFormulaTangentContourIntegral f
              (F.rectangle (h.height_schedule.height u)) =
            explicitFormulaTwoPiI •
              explicitFormulaRectangle_poleCorrectedResidueSum f
                (h.height_schedule.height u)) :
    ∀ᶠ u in atTop,
      explicitFormulaRectangle_poleCorrectedResidueSum f
          (h.height_schedule.height u) =
        zetaCompletedExplicitFormulaNormalizedTangentContourIntegral f
          (F.rectangle (h.height_schedule.height u)) :=
  explicitFormulaRectangle_poleCorrectedResidueSum_eventually_eq_normalizedTangent_of_scheduledPackage_pointwise
    f F h
    (fun u hu =>
      zetaCompletedExplicitFormulaNormalizedTangentContourIntegral_eq_residueSum
        f
        (F.rectangle (h.height_schedule.height u))
        (explicitFormulaRectangle_poleCorrectedResidueSum f
          (h.height_schedule.height u))
        (hraw u hu))

/-- Scheduled boundary/interior data supply the eventual normalized tangent-residue
equality consumed by the zero-side endpoint theorem. -/
theorem explicitFormulaRectangle_poleCorrectedResidueSum_eventually_eq_normalizedTangent_of_scheduledPackage_boundaryData
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F)
    (hinterior :
      ∀ u : ℝ,
        0 < h.height_schedule.height u →
          ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
            rho ∈ explicitFormulaCompletedZeroContourHeightWindow
                (h.height_schedule.height u) ↔
              completedZeroResidueCoordinate rho ∈
                  explicitFormulaContourFamilyInterior F (h.height_schedule.height u) ∧
                completedZeroResidueCoordinate rho ∈ completedZetaContourIntegrandSingularSet)
    (hboundaryRegular :
      ∀ u : ℝ,
        0 < h.height_schedule.height u →
          ∀ z : ℂ,
            z ∈ explicitFormulaContourFamilyBoundary F (h.height_schedule.height u) →
              ContinuousAt
                  (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
                DifferentiableAt ℂ
                  (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hboundaryAvoidance :
      ∀ u : ℝ,
        0 < h.height_schedule.height u →
          ∀ z : ℂ,
            z ∈ explicitFormulaContourFamilyBoundary F (h.height_schedule.height u) →
              z ∉ completedZetaContourIntegrandSingularSet) :
    ∀ᶠ u in atTop,
      explicitFormulaRectangle_poleCorrectedResidueSum f
          (h.height_schedule.height u) =
        zetaCompletedExplicitFormulaNormalizedTangentContourIntegral f
          (F.rectangle (h.height_schedule.height u)) :=
  explicitFormulaRectangle_poleCorrectedResidueSum_eventually_eq_normalizedTangent_of_scheduledPackage_rawPointwise
    f F h
    (fun u hu =>
      zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_scheduledPackage_owner
        f F h hu (hinterior u hu))

/-- The scheduled package supplies boundary avoidance at each scheduled height. -/
theorem explicitFormulaScheduledPackageRectangle_avoidsSingularBoundary
    {f : ZetaAdmissibleFunction} (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F) (u : ℝ) :
    explicitFormulaContourFamilyAvoidsSingularBoundary F
      (h.height_schedule.height u) :=
  h.height_schedule.avoids_boundary u

/-- A scheduled-package boundary point is off the completed contour-integrand
singular set. -/
theorem completedZetaContourIntegrand_not_mem_singularSet_of_scheduledPackageBoundary
    {f : ZetaAdmissibleFunction} (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F) (u : ℝ) {z : ℂ}
    (hboundary :
      z ∈ explicitFormulaContourFamilyBoundary F
        (h.height_schedule.height u)) :
    z ∉ completedZetaContourIntegrandSingularSet :=
    completedZetaContourIntegrand_not_mem_singularSet_of_avoidsBoundary
    F
    (h.height_schedule.height u)
    (explicitFormulaScheduledPackageRectangle_avoidsSingularBoundary F h u)
    hboundary

/-- The completed contour integrand is regular at every scheduled-package
boundary point. -/
theorem completedZetaContourIntegrand_regularAt_scheduledPackageBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F) (u : ℝ) {z : ℂ}
    (hboundary :
      z ∈ explicitFormulaContourFamilyBoundary F
        (h.height_schedule.height u)) :
    ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
      DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z :=
  let hoff :
      z ∉ completedZetaContourIntegrandSingularSet :=
    completedZetaContourIntegrand_not_mem_singularSet_of_scheduledPackageBoundary
      F h u hboundary
  And.intro
    (completedZetaContourIntegrand_continuousAt_off_singularSet h.phi_control hoff)
    (completedZetaContourIntegrand_differentiableAt_off_singularSet h.phi_control hoff)

/-- Scheduled-package boundary regularity in the pointwise form consumed by the
selected-radius residue theorem. -/
theorem explicitFormulaRectangleContourIntegrand_boundaryRegular_of_scheduledPackage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F) (u : ℝ) :
    ∀ z : ℂ,
      z ∈ explicitFormulaContourFamilyBoundary F (h.height_schedule.height u) →
        ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
          DifferentiableAt ℂ
            (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z :=
  fun z hboundary =>
    completedZetaContourIntegrand_regularAt_scheduledPackageBoundary f F h u hboundary

/-- Scheduled-package boundary avoidance in the pointwise form consumed by the
selected-radius residue theorem. -/
theorem explicitFormulaRectangleContourIntegrand_boundaryAvoidance_of_scheduledPackage
    {f : ZetaAdmissibleFunction} (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F) (u : ℝ) :
    ∀ z : ℂ,
      z ∈ explicitFormulaContourFamilyBoundary F (h.height_schedule.height u) →
        z ∉ completedZetaContourIntegrandSingularSet :=
  fun z hboundary =>
    completedZetaContourIntegrand_not_mem_singularSet_of_scheduledPackageBoundary
      F h u hboundary

/-- The completed-zero contour height window is exactly the scheduled-package
interior singular carrier at the scheduled height. -/
theorem explicitFormulaCompletedZeroContourHeightWindow_mem_iff_scheduledPackageInteriorSingular
    {f : ZetaAdmissibleFunction} (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F) (u : ℝ)
    (rho : {rho : ℂ // ZetaCompletedZero rho}) :
    rho ∈ explicitFormulaCompletedZeroContourHeightWindow
        (h.height_schedule.height u) ↔
      completedZeroResidueCoordinate rho ∈
          explicitFormulaContourFamilyInterior F (h.height_schedule.height u) ∧
        completedZeroResidueCoordinate rho ∈
          completedZetaContourIntegrandSingularSet :=
  explicitFormulaCompletedZeroContourHeightWindow_mem_iff_interiorSingular
    F
    (h.height_schedule.height u)
    rho

/-- A scheduled package supplies all boundary and interior data needed for the
eventual normalized tangent-residue equality. -/
theorem explicitFormulaRectangle_poleCorrectedResidueSum_eventually_eq_normalizedTangent_of_scheduledPackage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F) :
    ∀ᶠ u in atTop,
      explicitFormulaRectangle_poleCorrectedResidueSum f
          (h.height_schedule.height u) =
        zetaCompletedExplicitFormulaNormalizedTangentContourIntegral f
          (F.rectangle (h.height_schedule.height u)) :=
  explicitFormulaRectangle_poleCorrectedResidueSum_eventually_eq_normalizedTangent_of_scheduledPackage_boundaryData
    f
    F
    h
    (fun u heightPositive rho =>
      explicitFormulaCompletedZeroContourHeightWindow_mem_iff_scheduledPackageInteriorSingular
        F h u rho)
    (fun u heightPositive =>
      explicitFormulaRectangleContourIntegrand_boundaryRegular_of_scheduledPackage
        f F h u)
    (fun u heightPositive =>
      explicitFormulaRectangleContourIntegrand_boundaryAvoidance_of_scheduledPackage
        F h u)

/-- The scheduled-package normalized vertical side is the normalized
pole-corrected project contour minus the normalized horizontal side. -/
theorem explicitFormulaScheduledPackageNormalizedPoleCorrectedVerticalDifference_eq_contour_sub_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F) (u : ℝ) :
    explicitFormulaScheduledPackageNormalizedPoleCorrectedVerticalDifference f F h u =
      explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral
          f F (h.height_schedule.height u) -
        explicitFormulaScheduledPackageHorizontalSideDifference h u /
          explicitFormulaTwoPi := by
  let vertical : ℂ :=
    zetaCompletedExplicitFormulaRightLineIntegral f
        (F.rectangle (h.height_schedule.height u)) -
      zetaCompletedExplicitFormulaLeftLineIntegral f
        (F.rectangle (h.height_schedule.height u))
  let horizontal : ℂ :=
    explicitFormulaScheduledPackageHorizontalSideDifference h u
  let poles : ℂ := explicitFormulaRectangle_completedPoleResidueSum f
  have hcontour :
      zetaCompletedExplicitFormulaContourIntegral f
          (F.rectangle (h.height_schedule.height u)) =
        vertical + horizontal := by
    calc
      zetaCompletedExplicitFormulaContourIntegral f
          (F.rectangle (h.height_schedule.height u)) =
          zetaCompletedExplicitFormulaRightLineIntegral f
                (F.rectangle (h.height_schedule.height u)) -
            zetaCompletedExplicitFormulaLeftLineIntegral f
                (F.rectangle (h.height_schedule.height u)) +
            zetaCompletedExplicitFormulaTopLineIntegral f
                (F.rectangle (h.height_schedule.height u)) -
            zetaCompletedExplicitFormulaBottomLineIntegral f
                (F.rectangle (h.height_schedule.height u)) := by
        exact zetaCompletedExplicitFormulaContourIntegral_eq
          f (F.rectangle (h.height_schedule.height u))
      _ =
          vertical +
            (zetaCompletedExplicitFormulaTopLineIntegral f
                (F.rectangle (h.height_schedule.height u)) -
              zetaCompletedExplicitFormulaBottomLineIntegral f
                (F.rectangle (h.height_schedule.height u))) := by
        exact explicitFormula_four_side_project_split
          (zetaCompletedExplicitFormulaRightLineIntegral f
            (F.rectangle (h.height_schedule.height u)))
          (zetaCompletedExplicitFormulaLeftLineIntegral f
            (F.rectangle (h.height_schedule.height u)))
          (zetaCompletedExplicitFormulaTopLineIntegral f
            (F.rectangle (h.height_schedule.height u)))
          (zetaCompletedExplicitFormulaBottomLineIntegral f
            (F.rectangle (h.height_schedule.height u)))
      _ = vertical + horizontal := Eq.refl _
  have hdivision :
      (vertical + horizontal) / explicitFormulaTwoPi =
        vertical / explicitFormulaTwoPi +
          horizontal / explicitFormulaTwoPi := by
    exact add_div vertical horizontal explicitFormulaTwoPi
  calc
    explicitFormulaScheduledPackageNormalizedPoleCorrectedVerticalDifference f F h u =
        vertical / explicitFormulaTwoPi - poles := Eq.refl _
    _ = (vertical / explicitFormulaTwoPi +
          horizontal / explicitFormulaTwoPi - poles) -
        horizontal / explicitFormulaTwoPi := by
      exact
        (explicitFormula_add_sub_sub_right
          (vertical / explicitFormulaTwoPi)
          (horizontal / explicitFormulaTwoPi)
          poles).symm
    _ = ((vertical + horizontal) / explicitFormulaTwoPi - poles) -
          horizontal / explicitFormulaTwoPi := by
      exact congrArg
        (fun value : ℂ => (value - poles) -
          horizontal / explicitFormulaTwoPi)
        hdivision.symm
    _ =
        (zetaCompletedExplicitFormulaContourIntegral f
            (F.rectangle (h.height_schedule.height u)) /
            explicitFormulaTwoPi - poles) -
          horizontal / explicitFormulaTwoPi := by
      exact congrArg
        (fun value : ℂ => (value / explicitFormulaTwoPi - poles) -
          horizontal / explicitFormulaTwoPi)
        hcontour.symm
    _ = explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral
          f F (h.height_schedule.height u) -
        explicitFormulaScheduledPackageHorizontalSideDifference h u /
          explicitFormulaTwoPi := Eq.refl _

/-- Schedule-native normalized project-contour convergence from a supplied
eventual selected-radius tangent-residue equality. -/
theorem explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral_tendsto_zeroSideComplex_of_scheduledPackage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F)
    (htangentEventual :
      ∀ᶠ u in atTop,
        explicitFormulaRectangle_poleCorrectedResidueSum f
            (h.height_schedule.height u) =
          zetaCompletedExplicitFormulaNormalizedTangentContourIntegral f
            (F.rectangle (h.height_schedule.height u)))
    (hsum :
      Summable
        (fun rho : {rho : ℂ // ZetaCompletedZero rho} =>
          zetaZeroSideContribution (rho : ℂ) f)) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral
          f F (h.height_schedule.height u))
      atTop (𝓝 (zetaCompletedZeroSideComplex f)) := by
  have hpole :
      Tendsto
        (fun _u : ℝ => explicitFormulaRectangle_completedPoleResidueSum f)
        atTop (𝓝 (explicitFormulaRectangle_completedPoleResidueSum f)) :=
    tendsto_const_nhds
  have hpoleCorrected :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaRectangle_poleCorrectedResidueSum f
            (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedZeroSideComplex f +
          explicitFormulaRectangle_completedPoleResidueSum f)) := by
      exact
        explicitFormulaRectangle_poleCorrectedResidueSum_tendsto_zeroSideComplex_add_poles
        f F h.height_schedule hsum
  have htangent :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaNormalizedTangentContourIntegral f
            (F.rectangle (h.height_schedule.height u)))
        atTop
        (𝓝 (zetaCompletedZeroSideComplex f +
          explicitFormulaRectangle_completedPoleResidueSum f)) :=
    hpoleCorrected.congr' htangentEventual
  have hhorizontal :
      Tendsto
        (fun u : ℝ => explicitFormulaScheduledPackageHorizontalSideDifference h u)
        atTop (𝓝 0) :=
    explicitFormulaScheduledPackageHorizontalSideDifference_tendsto_zero h 1
  have hproject :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaNormalizedContourIntegral f
            (F.rectangle (h.height_schedule.height u)))
        atTop
        (𝓝 (zetaCompletedZeroSideComplex f +
          explicitFormulaRectangle_completedPoleResidueSum f)) :=
    zetaCompletedExplicitFormulaNormalizedContourIntegral_tendsto_of_scheduledPackage_tangent_horizontal
      f F h
      (zetaCompletedZeroSideComplex f + explicitFormulaRectangle_completedPoleResidueSum f)
      htangent hhorizontal
  have hcorrected := hproject.sub hpole
  have htarget :
      zetaCompletedZeroSideComplex f + explicitFormulaRectangle_completedPoleResidueSum f -
          explicitFormulaRectangle_completedPoleResidueSum f =
        zetaCompletedZeroSideComplex f :=
    add_sub_cancel_right
      (zetaCompletedZeroSideComplex f)
      (explicitFormulaRectangle_completedPoleResidueSum f)
  exact Eq.subst
    (motive := fun target : ℂ =>
      Tendsto
        (fun u : ℝ =>
          explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral
            f F (h.height_schedule.height u))
        atTop (𝓝 target))
    htarget hcorrected

/-- The scheduled-package normalized vertical side converges to the completed
zero side once the selected tangent-residue identity holds eventually. -/
theorem explicitFormulaScheduledPackageNormalizedPoleCorrectedVerticalDifference_tendsto_zeroSideComplex
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F)
    (htangentEventual :
      ∀ᶠ u in atTop,
        explicitFormulaRectangle_poleCorrectedResidueSum f
            (h.height_schedule.height u) =
          zetaCompletedExplicitFormulaNormalizedTangentContourIntegral f
            (F.rectangle (h.height_schedule.height u)))
    (hsum :
      Summable
        (fun rho : {rho : ℂ // ZetaCompletedZero rho} =>
          zetaZeroSideContribution (rho : ℂ) f)) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaScheduledPackageNormalizedPoleCorrectedVerticalDifference
          f F h u)
      atTop (𝓝 (zetaCompletedZeroSideComplex f)) := by
  have hcontour :=
    explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral_tendsto_zeroSideComplex_of_scheduledPackage
      f F h htangentEventual hsum
  have hhorizontal :
      Tendsto
        (fun u : ℝ => explicitFormulaScheduledPackageHorizontalSideDifference h u)
        atTop (𝓝 0) :=
    explicitFormulaScheduledPackageHorizontalSideDifference_tendsto_zero h 1
  have hnormalizedHorizontal :=
    hhorizontal.div_const explicitFormulaTwoPi
  have hdifference := hcontour.sub hnormalizedHorizontal
  have hzeroDiv :
      (0 : ℂ) / explicitFormulaTwoPi = 0 :=
    zero_div explicitFormulaTwoPi
  have htarget :
      zetaCompletedZeroSideComplex f - 0 / explicitFormulaTwoPi =
        zetaCompletedZeroSideComplex f :=
    Eq.trans (congrArg (fun term : ℂ => zetaCompletedZeroSideComplex f - term) hzeroDiv)
      (sub_zero _)
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral
            f F (h.height_schedule.height u) -
          explicitFormulaScheduledPackageHorizontalSideDifference h u /
            explicitFormulaTwoPi) =
        (fun u : ℝ =>
          explicitFormulaScheduledPackageNormalizedPoleCorrectedVerticalDifference
            f F h u) := by
    exact funext (fun u : ℝ =>
      (explicitFormulaScheduledPackageNormalizedPoleCorrectedVerticalDifference_eq_contour_sub_horizontal
        f F h u).symm)
  exact Eq.subst
    (motive := fun values : ℝ → ℂ =>
      Tendsto values atTop (𝓝 (zetaCompletedZeroSideComplex f)))
    hpointwise
    (Eq.subst
      (motive := fun target : ℂ =>
        Tendsto
          (fun u : ℝ =>
            explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral
                f F (h.height_schedule.height u) -
              explicitFormulaScheduledPackageHorizontalSideDifference h u /
                explicitFormulaTwoPi)
          atTop (𝓝 target))
      htarget hdifference)

theorem explicitFormulaScheduledPackageNormalizedFullTangentPoleCorrectedContourIntegral_eq_zeroWindowResidueSum_owner
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F) {u : ℝ}
    (hT : 0 < h.height_schedule.height u) :
    explicitFormulaRectangleNormalizedFullTangentPoleCorrectedContourIntegral
        f F (h.height_schedule.height u) =
      explicitFormulaCompletedZeroContourHeightWindowResidueSum f
        (h.height_schedule.height u) := by
  exact explicitFormulaRectangleNormalizedFullTangentPoleCorrectedContourIntegral_eq_zeroWindowResidueSum_of_tangentResidue
    f F (h.height_schedule.height u)
    (zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_scheduledPackage_canonicalInterior_owner
      f F h hT)

theorem explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral_tendsto_zeroSideComplex_of_scheduledPackage_canonicalTangent_owner
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F)
    (hsum :
      Summable
        (fun rho : {rho : ℂ // ZetaCompletedZero rho} =>
          zetaZeroSideContribution (rho : ℂ) f)) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral
          f F (h.height_schedule.height u))
      atTop (𝓝 (zetaCompletedZeroSideComplex f)) := by
  apply explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral_tendsto_zeroSideComplex_of_scheduledPackage
    f F h
  · filter_upwards [h.height_schedule.eventually_height_pos] with u hT
    have hfull :=
      explicitFormulaScheduledPackageNormalizedFullTangentPoleCorrectedContourIntegral_eq_zeroWindowResidueSum_owner
        f F h hT
    have hnorm :
        zetaCompletedExplicitFormulaNormalizedTangentContourIntegral f
            (F.rectangle (h.height_schedule.height u)) =
          explicitFormulaCompletedZeroContourHeightWindowResidueSum f
            (h.height_schedule.height u) +
            explicitFormulaRectangle_completedPoleResidueSum f :=
      sub_eq_iff_eq_add.mp hfull
    have hsplit := explicitFormulaRectangle_poleCorrectedResidueSum_eq f
      (h.height_schedule.height u)
    exact hnorm.trans hsplit.symm
  · exact hsum

theorem zetaCompletedExplicitFormulaNormalizedContourIntegral_tendsto_of_scheduledPackage_canonical_owner
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F)
    (hsum :
      Summable
        (fun rho : {rho : ℂ // ZetaCompletedZero rho} =>
          zetaZeroSideContribution (rho : ℂ) f)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaNormalizedContourIntegral f
          (F.rectangle (h.height_schedule.height u)))
      atTop (𝓝 (zetaCompletedZeroSideComplex f +
        explicitFormulaRectangle_completedPoleResidueSum f)) := by
  apply zetaCompletedExplicitFormulaNormalizedContourIntegral_tendsto_of_scheduledPackage_tangent_horizontal
    f F h
    (zetaCompletedZeroSideComplex f +
      explicitFormulaRectangle_completedPoleResidueSum f)
  · have hpoleCorrected :
        Tendsto
          (fun u : ℝ =>
            explicitFormulaRectangle_poleCorrectedResidueSum f
              (h.height_schedule.height u))
          atTop
          (𝓝 (zetaCompletedZeroSideComplex f +
            explicitFormulaRectangle_completedPoleResidueSum f)) :=
      explicitFormulaRectangle_poleCorrectedResidueSum_tendsto_zeroSideComplex_add_poles
        f F h.height_schedule hsum
    have heq :
        ∀ᶠ u in atTop,
          explicitFormulaRectangle_poleCorrectedResidueSum f
              (h.height_schedule.height u) =
            zetaCompletedExplicitFormulaNormalizedTangentContourIntegral f
              (F.rectangle (h.height_schedule.height u)) := by
      filter_upwards [h.height_schedule.eventually_height_pos] with u hT
      have hfull :=
        explicitFormulaScheduledPackageNormalizedFullTangentPoleCorrectedContourIntegral_eq_zeroWindowResidueSum_owner
          f F h hT
      have hnorm :
          zetaCompletedExplicitFormulaNormalizedTangentContourIntegral f
              (F.rectangle (h.height_schedule.height u)) =
            explicitFormulaCompletedZeroContourHeightWindowResidueSum f
              (h.height_schedule.height u) +
              explicitFormulaRectangle_completedPoleResidueSum f :=
        sub_eq_iff_eq_add.mp hfull
      exact hnorm.trans
        (explicitFormulaRectangle_poleCorrectedResidueSum_eq f
          (h.height_schedule.height u)).symm
    exact hpoleCorrected.congr' heq
  · exact explicitFormulaScheduledPackageHorizontalSideDifference_tendsto_zero h 1

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
