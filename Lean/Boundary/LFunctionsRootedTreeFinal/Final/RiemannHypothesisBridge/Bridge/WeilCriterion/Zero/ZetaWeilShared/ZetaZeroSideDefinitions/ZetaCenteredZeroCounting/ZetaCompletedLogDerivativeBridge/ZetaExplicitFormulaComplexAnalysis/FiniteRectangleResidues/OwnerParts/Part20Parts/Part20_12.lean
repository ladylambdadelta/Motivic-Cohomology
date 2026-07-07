import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part20Parts.Part20_11

/-!
# Explicit-formula finite rectangle residues

This owner layer contains finite-rectangle residue equalities, scheduled avoidance, and residue-window error transport.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

/-!
## Part20 12: VerticalGlobalSums
-/

theorem explicitFormulaRectangleSelectedVerticalEdgeCoordinatesOfFixedY_integralSum_eq_outerSlice_sub_holeSlice
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ρ + ρ < dist a b)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          if _homit :
              explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
              f ((ypair.y₀, ypair.y₁), xpair.x₁)
          else
            0)
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) -
      explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          if _homit :
              explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
            explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
              f ((ypair.y₀, ypair.y₁), xpair.x₀)
          else
            0)
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
      explicitFormulaRectangleVerticalOuterSliceContribution f F T ypair -
        explicitFormulaRectangleVerticalHoleSliceContribution f T ρ ypair := by
  exact
    explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution_eq_outerSlice_sub_holeSlice
      f F hT_nonneg hρ hclosed hsep ypair

/-- The local outer vertical slices over the sorted vertical subdivision assemble to the
oriented outer vertical side sum. -/
theorem explicitFormulaRectangleVerticalOuterSliceContributionSum_eq_outerSideSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ρ : ℝ)
    (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hright :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ F.c)
    (hleft :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ (1 - F.c)) :
    explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          explicitFormulaRectangleVerticalOuterSliceContribution f F T ypair)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      explicitFormulaRectangleSelectedBoxCoordinatesVerticalOuterSideSum f F T := by
  let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
    explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
  have hsplit :
      explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            explicitFormulaRectangleVerticalOuterSliceContribution f F T ypair)
          ypairs =
        explicitFormulaRectangleListSum
            (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
              explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
                f ((ypair.y₀, ypair.y₁), F.c))
            ypairs -
          explicitFormulaRectangleListSum
            (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
                f ((ypair.y₀, ypair.y₁), 1 - F.c))
            ypairs :=
    explicitFormulaRectangleListSum_sub
      (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
        explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
          f ((ypair.y₀, ypair.y₁), F.c))
      (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
        explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
          f ((ypair.y₀, ypair.y₁), 1 - F.c))
      ypairs
  have hrightEq :
      explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
              f ((ypair.y₀, ypair.y₁), F.c))
          ypairs =
        zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I :=
    explicitFormulaRectangleVerticalOuterRightSliceContributionSum_eq_outerRightSide
      f F hT_nonneg hρ hclosed hright hleft
  have hleftEq :
      explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
              f ((ypair.y₀, ypair.y₁), 1 - F.c))
          ypairs =
        zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I :=
    explicitFormulaRectangleVerticalOuterLeftSliceContributionSum_eq_outerLeftSide
      f F hT_nonneg hρ hclosed hright hleft
  calc
    explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          explicitFormulaRectangleVerticalOuterSliceContribution f F T ypair)
        ypairs =
        explicitFormulaRectangleListSum
            (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
              explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
                f ((ypair.y₀, ypair.y₁), F.c))
            ypairs -
          explicitFormulaRectangleListSum
            (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
                f ((ypair.y₀, ypair.y₁), 1 - F.c))
            ypairs := by
      exact hsplit
    _ =
        zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
          explicitFormulaRectangleListSum
            (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
                f ((ypair.y₀, ypair.y₁), 1 - F.c))
            ypairs := by
      exact congrArg
        (fun z : ℂ =>
          z -
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
                  f ((ypair.y₀, ypair.y₁), 1 - F.c))
              ypairs)
        hrightEq
    _ =
        zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
          zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I := by
      exact congrArg
        (fun z : ℂ =>
          zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I - z)
        hleftEq
    _ =
        explicitFormulaRectangleSelectedBoxCoordinatesVerticalOuterSideSum f F T := by
      exact Eq.refl _

/-- The local raw square-hole vertical slices over the sorted vertical subdivision
assemble to the grouped raw square-hole vertical side sum. -/
theorem explicitFormulaRectangleVerticalHoleSliceContributionSum_eq_holeSideSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hrightHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
    (hleftHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ρ + ρ < dist a b) :
    explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          explicitFormulaRectangleVerticalHoleSliceContribution f T ρ ypair)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      explicitFormulaRectangleSelectedBoxCoordinatesVerticalHoleSideSum f T ρ := by
  let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
    explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
  let rightSlice : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ → ℂ :=
    fun ypair =>
      ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
        if _hspan :
            explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
              ρ ypair a then
          explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
            ((ypair.y₀, ypair.y₁),
              (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
        else
          0
  let leftSlice : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ → ℂ :=
    fun ypair =>
      ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
        if _hspan :
            explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
              ρ ypair a then
          explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
            ((ypair.y₀, ypair.y₁),
              (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
        else
          0
  have hpoint :
      ∀ ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ,
        explicitFormulaRectangleVerticalHoleSliceContribution f T ρ ypair =
          rightSlice ypair - leftSlice ypair :=
    fun ypair =>
      explicitFormulaRectangleVerticalHoleSliceContribution_eq_right_sub_left
        f T ρ ypair
  have hreplace :
      explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            explicitFormulaRectangleVerticalHoleSliceContribution f T ρ ypair)
          ypairs =
        explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            rightSlice ypair - leftSlice ypair)
          ypairs := by
    exact congrArg
      (fun g : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ → ℂ =>
        explicitFormulaRectangleListSum g ypairs)
      (funext hpoint)
  have hsplit :
      explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            rightSlice ypair - leftSlice ypair)
          ypairs =
        explicitFormulaRectangleListSum rightSlice ypairs -
          explicitFormulaRectangleListSum leftSlice ypairs :=
    explicitFormulaRectangleListSum_sub rightSlice leftSlice ypairs
  have hright :
      explicitFormulaRectangleListSum rightSlice ypairs =
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum f T ρ :=
    explicitFormulaRectangleVerticalHoleRightSliceContributionSum_eq_holeRightSide
      f F hT_nonneg hρ hclosed hrightHole hsep
  have hleft :
      explicitFormulaRectangleListSum leftSlice ypairs =
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum f T ρ :=
    explicitFormulaRectangleVerticalHoleLeftSliceContributionSum_eq_holeLeftSide
      f F hT_nonneg hρ hclosed hleftHole hsep
  calc
    explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          explicitFormulaRectangleVerticalHoleSliceContribution f T ρ ypair)
        ypairs =
        explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            rightSlice ypair - leftSlice ypair)
          ypairs := by
      exact hreplace
    _ =
        explicitFormulaRectangleListSum rightSlice ypairs -
          explicitFormulaRectangleListSum leftSlice ypairs := by
      exact hsplit
    _ =
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum f T ρ -
          explicitFormulaRectangleListSum leftSlice ypairs := by
      exact congrArg
        (fun z : ℂ => z - explicitFormulaRectangleListSum leftSlice ypairs)
        hright
    _ =
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum f T ρ -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum f T ρ := by
      exact congrArg
        (fun z : ℂ =>
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum f T ρ - z)
        hleft
    _ =
        explicitFormulaRectangleSelectedBoxCoordinatesVerticalHoleSideSum f T ρ := by
      exact Eq.refl _

/-- The recursive vertical column-contribution sum is the recursive list sum over its
fixed-column contributions. -/
theorem explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum_eq_listSum
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ)) :
    ∀ ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ),
      explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum
          f xpairs ypairs =
        explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
              f xpairs ypair)
          ypairs
  | [] => by
      exact Eq.refl _
  | ypair :: rest => by
      have htail :
          explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum
              f xpairs rest =
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
                  f xpairs ypair)
              rest :=
        explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum_eq_listSum
          f xpairs rest
      calc
        explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum
            f xpairs (ypair :: rest) =
            explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
                f xpairs ypair +
              explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum
                f xpairs rest := by
          exact Eq.refl _
        _ =
            explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
                f xpairs ypair +
              explicitFormulaRectangleListSum
                (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                  explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
                    f xpairs ypair)
                rest := by
          exact congrArg
            (fun z : ℂ =>
              explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
                f xpairs ypair + z)
            htail
        _ =
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
                  f xpairs ypair)
              (ypair :: rest) := by
          exact Eq.refl _

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
