import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.SelectedRadiusCauchy

/-!
# Selected-radius tangent residue assembly
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The contour-coordinate and public completed-zero residue data have the same residue
value after both are unfolded at the corrected true pole coordinate. -/
theorem explicitFormulaContourZeroResidue_eq_completedZeroResidue
    (f : ZetaAdmissibleFunction) (rho : {rho : ℂ // ZetaCompletedZero rho}) :
    explicitFormulaZeroResidue f (explicitFormulaContourZeroDataOfCompletedZero rho) =
      explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero rho) := by
  exact Eq.trans
    (explicitFormulaContourZeroDataOfCompletedZero_residue_unfold f rho)
    (explicitFormulaZeroDataOfCompletedZero_residue_unfold f rho).symm

/-- The selected regular radius closes the tangent finite residue theorem at a scheduled
positive height. -/
theorem zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_selectedRegularRadius
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) {u : ℝ}
    (hT : 0 < h.height_schedule.height u)
    (hinterior :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow (h.height_schedule.height u) ↔
          completedZeroResidueCoordinate rho ∈
              explicitFormulaContourFamilyInterior F (h.height_schedule.height u) ∧
            completedZeroResidueCoordinate rho ∈ completedZetaContourIntegrandSingularSet)
    (hlocal :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow (h.height_schedule.height u) →
          Tendsto
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate rho) *
                zetaCompletedExplicitFormulaContourIntegrand f z)
            (𝓝[≠] (completedZeroResidueCoordinate rho))
            (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero rho)))) :
    zetaCompletedExplicitFormulaTangentContourIntegral f
        (F.rectangle (h.height_schedule.height u)) =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaRectangle_poleCorrectedResidueSum f (h.height_schedule.height u) := by
  have hlocalInterior :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
          ∃ radius : ℝ,
            0 < radius ∧
              Metric.ball a radius ⊆
                explicitFormulaContourFamilyInterior F (h.height_schedule.height u) :=
    fun a ha =>
      explicitFormulaRectangleRawSingularCoordinates_localInterior_ball
        F hT hinterior ha
  match explicitFormulaRectangleRawSingularCoordinates_exists_squareSideRegular_closedRadiusControls
      F (h.height_schedule.height u) hlocalInterior with
  | ⟨epsilon, hepsilon, hclosed, hseparated, hregular⟩ =>
      have hcauchy :
          explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
            f F (h.height_schedule.height u) epsilon = 0 :=
        explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_selectedRegularRadius
          f F h hT hepsilon hinterior hclosed hseparated hregular
      exact
        zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_finiteRadiusPuncturedBoundary_and_closedRadiusControls
          f F h (h.height_schedule.height u) epsilon hT hepsilon hinterior
          hclosed hseparated hcauchy hlocal

/-- Canonical selected-radius tangent residue assembly with the completed-zero local
residue limits discharged from the corrected contour coordinate. -/
theorem zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_selected
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) {u : ℝ}
    (hT : 0 < h.height_schedule.height u)
    (hinterior :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow (h.height_schedule.height u) ↔
          completedZeroResidueCoordinate rho ∈
              explicitFormulaContourFamilyInterior F (h.height_schedule.height u) ∧
            completedZeroResidueCoordinate rho ∈ completedZetaContourIntegrandSingularSet) :
    zetaCompletedExplicitFormulaTangentContourIntegral f
        (F.rectangle (h.height_schedule.height u)) =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaRectangle_poleCorrectedResidueSum f (h.height_schedule.height u) := by
  have hlocal :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow (h.height_schedule.height u) →
          Tendsto
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate rho) *
                zetaCompletedExplicitFormulaContourIntegrand f z)
            (𝓝[≠] (completedZeroResidueCoordinate rho))
            (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero rho))) :=
    fun rho hrho =>
      have hphi :
          zetaCompletedExplicitFormulaPhi f (rho : ℂ) =
            zetaCompletedExplicitFormulaPhi f (rho : ℂ) :=
        explicitFormulaRectangle_completedZeroResidueWindow_phiConventionCorrection
          f (h.height_schedule.height u) rho hrho
      have hnormalize :
          explicitFormulaZeroResidue f (explicitFormulaContourZeroDataOfCompletedZero rho) =
            explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero rho) :=
        explicitFormulaRectangle_completedZeroResidueWindow_contourToZeroSideResidueEquality
          f (h.height_schedule.height u) rho hrho hphi
      Eq.subst
        (motive := fun residue : ℂ =>
          Tendsto
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate rho) *
                zetaCompletedExplicitFormulaContourIntegrand f z)
            (𝓝[≠] (completedZeroResidueCoordinate rho))
            (𝓝 residue))
        hnormalize
        (explicitFormulaRectangle_completedZero_localResidue_tendsto_contourSummand
          f h.phi_control rho)
  exact
    zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_selectedRegularRadius
      f F h hT hinterior hlocal

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
