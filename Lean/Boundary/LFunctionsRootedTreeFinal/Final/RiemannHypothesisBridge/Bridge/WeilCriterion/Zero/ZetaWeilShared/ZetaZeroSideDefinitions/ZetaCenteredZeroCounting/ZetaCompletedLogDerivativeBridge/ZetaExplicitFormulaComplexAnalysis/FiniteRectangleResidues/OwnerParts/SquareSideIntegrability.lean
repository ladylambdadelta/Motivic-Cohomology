import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.SquareSideRegularity

/-!
# Regular affine side integrability

Affine side segments avoiding the completed singular carrier are integrable.  This is the
analytic leaf used by the square-side regular radius construction.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

namespace ZetaAdmissibleFunction

/-- A horizontal affine segment avoiding the completed singular set is interval-integrable. -/
theorem explicitFormulaRectangle_horizontal_intervalIntegrable_of_avoidsSingularSet
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (y a b : ℝ)
    (havoid :
      ∀ x : ℝ,
        x ∈ Set.uIcc a b →
          (x : ℂ) + (y : ℂ) * Complex.I ∉ completedZetaContourIntegrandSingularSet) :
    IntervalIntegrable
      (fun x : ℝ =>
        zetaCompletedExplicitFormulaContourIntegrand f
          ((x : ℂ) + (y : ℂ) * Complex.I))
      volume a b := by
  let parameter : ℝ → ℂ :=
    fun x : ℝ => (x : ℂ) + (y : ℂ) * Complex.I
  let image : Set ℂ := parameter '' Set.uIcc a b
  have hintegrand :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
        image := by
    intro z hz
    match hz with
    | ⟨x, hx, hzx⟩ =>
        have hregular :
            ContinuousAt
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w)
              (parameter x) :=
          completedZetaContourIntegrand_continuousAt_off_singularSet
            hPhi (havoid x hx)
        exact Eq.subst
          (motive := fun value : ℂ =>
            ContinuousWithinAt
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w)
              image value)
          hzx
          hregular.continuousWithinAt
  have hparameter : ContinuousOn parameter (Set.uIcc a b) :=
    explicitFormulaRectangle_horizontalEdgeParameter_continuousOn y a b
  have hmaps : Set.MapsTo parameter (Set.uIcc a b) image :=
    fun x hx => Exists.intro x (And.intro hx (Eq.refl (parameter x)))
  exact (hintegrand.comp hparameter hmaps).intervalIntegrable

/-- A vertical affine segment avoiding the completed singular set is interval-integrable. -/
theorem explicitFormulaRectangle_vertical_intervalIntegrable_of_avoidsSingularSet
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (x a b : ℝ)
    (havoid :
      ∀ y : ℝ,
        y ∈ Set.uIcc a b →
          (x : ℂ) + (y : ℂ) * Complex.I ∉ completedZetaContourIntegrandSingularSet) :
    IntervalIntegrable
      (fun y : ℝ =>
        zetaCompletedExplicitFormulaContourIntegrand f
          ((x : ℂ) + (y : ℂ) * Complex.I))
      volume a b := by
  let parameter : ℝ → ℂ :=
    fun y : ℝ => (x : ℂ) + (y : ℂ) * Complex.I
  let image : Set ℂ := parameter '' Set.uIcc a b
  have hintegrand :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
        image := by
    intro z hz
    match hz with
    | ⟨y, hy, hzy⟩ =>
        have hregular :
            ContinuousAt
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w)
              (parameter y) :=
          completedZetaContourIntegrand_continuousAt_off_singularSet
            hPhi (havoid y hy)
        exact Eq.subst
          (motive := fun value : ℂ =>
            ContinuousWithinAt
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w)
              image value)
          hzy
          hregular.continuousWithinAt
  have hparameter : ContinuousOn parameter (Set.uIcc a b) :=
    explicitFormulaRectangle_verticalEdgeParameter_continuousOn x a b
  have hmaps : Set.MapsTo parameter (Set.uIcc a b) image :=
    fun y hy => Exists.intro y (And.intro hy (Eq.refl (parameter y)))
  exact (hintegrand.comp hparameter hmaps).intervalIntegrable

/-- Pointwise singular-set avoidance on every sorted horizontal adjacent interval gives
the complete sorted-side integrability package. -/
theorem explicitFormulaRectangleSortedXHorizontalSideIntegrable_of_avoidsSingularSet
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hPhi : ZetaPhiAnalyticControl f) (T radius y : ℝ)
    (havoid :
      ∀ k : ℕ,
        k < (explicitFormulaRectangleSortedXEndpoints F T radius).length - 1 →
          ∀ x : ℝ,
            x ∈ Set.uIcc
              (explicitFormulaRectangleSortedXEndpointAt F T radius k)
              (explicitFormulaRectangleSortedXEndpointAt F T radius (k + 1)) →
              (x : ℂ) + (y : ℂ) * Complex.I ∉
                completedZetaContourIntegrandSingularSet) :
    explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T radius y := by
  intro k hk
  exact
    explicitFormulaRectangle_horizontal_intervalIntegrable_of_avoidsSingularSet
      f hPhi y
      (explicitFormulaRectangleSortedXEndpointAt F T radius k)
      (explicitFormulaRectangleSortedXEndpointAt F T radius (k + 1))
      (havoid k hk)

/-- Pointwise singular-set avoidance on every sorted vertical adjacent interval gives
the complete sorted-side integrability package. -/
theorem explicitFormulaRectangleSortedYVerticalSideIntegrable_of_avoidsSingularSet
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (T radius x : ℝ)
    (havoid :
      ∀ k : ℕ,
        k < (explicitFormulaRectangleSortedYEndpoints T radius).length - 1 →
          ∀ y : ℝ,
            y ∈ Set.uIcc
              (explicitFormulaRectangleSortedYEndpointAt T radius k)
              (explicitFormulaRectangleSortedYEndpointAt T radius (k + 1)) →
              (x : ℂ) + (y : ℂ) * Complex.I ∉
                completedZetaContourIntegrandSingularSet) :
    explicitFormulaRectangleSortedYVerticalSideIntegrable f T radius x := by
  intro k hk
  exact
    explicitFormulaRectangle_vertical_intervalIntegrable_of_avoidsSingularSet
      f hPhi x
      (explicitFormulaRectangleSortedYEndpointAt T radius k)
      (explicitFormulaRectangleSortedYEndpointAt T radius (k + 1))
      (havoid k hk)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
