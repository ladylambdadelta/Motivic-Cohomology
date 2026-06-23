import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part20Parts.Part20_21

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
## Part20 22: FinalSubdivisionConstructors
-/

theorem explicitFormulaRectangleSelectedEndpointData_edgeAccounting_closedRadiusControls
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ε : ℝ} (hT_nonneg : 0 ≤ T) (hε : 0 < ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    (hbottom :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2) (-T))
    (htop :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2) T)
    (hbottomHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2)
            (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a).im)
    (htopHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2)
            (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a).im)
    (hright :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2) F.c)
    (hleft :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2) (1 - F.c))
    (hrightHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2)
            (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a).re)
    (hleftHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2)
            (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a).re)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ε + ε < dist a b) :
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
        (explicitFormulaRectangleSelectedEndpointData F T (ε / 2)) -
      explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
        (explicitFormulaRectangleSelectedEndpointData F T (ε / 2)) +
        (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
            (explicitFormulaRectangleSelectedEndpointData F T (ε / 2)) -
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
            (explicitFormulaRectangleSelectedEndpointData F T (ε / 2))) =
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
          zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) +
          (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
            zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I)) -
        ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a)
            (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a) :=
  explicitFormulaRectangleSelectedEndpointData_edgeAccounting_of_tangentBoxBoundary
    f F T (ε / 2)
    (explicitFormulaRectangleSelectedEndpointData_tangentBoxBoundary_closedRadiusControls
      f F hT_nonneg hε hclosed hbottom htop hbottomHole htopHole hright hleft hrightHole hleftHole hsep)

/-- Selected endpoint-data edge accounting over a cons horizontal adjacent-pair list
splits into the selected row for the head pair and the selected remaining rows. -/
theorem explicitFormulaRectangleSelectedEndpointData_edgeAccounting_pairLists_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (rest : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    let firstRow : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
          xpair ypairs)
    let remaining : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          rest ypairs)
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
              (xpair :: rest) ypairs)) -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
              (xpair :: rest) ypairs)) +
          (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
              (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
                  (xpair :: rest) ypairs)) -
            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
              (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
                  (xpair :: rest) ypairs))) =
      (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f firstRow -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f firstRow +
            (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f firstRow -
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f firstRow)) +
        (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f remaining -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f remaining +
            (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f remaining -
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f remaining)) := by
  let whole : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
        (xpair :: rest) ypairs)
  let firstRow : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
        xpair ypairs)
  let remaining : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
        rest ypairs)
  have hcells :
      explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          (xpair :: rest) ypairs =
        explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
          xpair ypairs ++
          explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
            rest ypairs := by
    rfl
  have hmap :
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
            xpair ypairs ++
            explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
              rest ypairs) =
        firstRow ++ remaining := by
    exact
      List.map_append
        (fun c : ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε =>
          c.toEndpointData)
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
          xpair ypairs)
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          rest ypairs)
  have hlist : whole = firstRow ++ remaining := by
    exact
      Eq.trans
        (congrArg
          (fun cells : List (ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε) =>
            explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells cells)
          hcells)
        hmap
  have hbottom :
      explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f whole =
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f firstRow +
          explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f remaining := by
    exact
      Eq.trans
        (congrArg
          (fun data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) =>
            explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data)
          hlist)
        (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum_append
          f firstRow remaining)
  have htop :
      explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f whole =
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f firstRow +
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f remaining := by
    exact
      Eq.trans
        (congrArg
          (fun data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) =>
            explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data)
          hlist)
        (explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum_append
          f firstRow remaining)
  have hright :
      explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f whole =
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f firstRow +
          explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f remaining := by
    exact
      Eq.trans
        (congrArg
          (fun data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) =>
            explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data)
          hlist)
        (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum_append
          f firstRow remaining)
  have hleft :
      explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f whole =
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f firstRow +
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f remaining := by
    exact
      Eq.trans
        (congrArg
          (fun data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) =>
            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data)
          hlist)
        (explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum_append
          f firstRow remaining)
  calc
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f whole -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f whole +
          (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f whole -
            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f whole) =
        (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f firstRow +
            explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f remaining) -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f whole +
            (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f whole -
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f whole) := by
      exact
        congrArg
          (fun z : ℂ =>
            z -
              explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f whole +
                (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f whole -
                  explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f whole))
          hbottom
    _ =
      (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f firstRow +
          explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f remaining) -
        (explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f firstRow +
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f remaining) +
          (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f whole -
            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f whole) := by
      exact
        congrArg
          (fun z : ℂ =>
            (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f firstRow +
              explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f remaining) -
              z +
                (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f whole -
                  explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f whole))
          htop
    _ =
      (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f firstRow +
          explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f remaining) -
        (explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f firstRow +
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f remaining) +
          ((explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f firstRow +
              explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f remaining) -
            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f whole) := by
      exact
        congrArg
          (fun z : ℂ =>
            (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f firstRow +
              explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f remaining) -
              (explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f firstRow +
                explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f remaining) +
                (z - explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f whole))
          hright
    _ =
      (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f firstRow +
          explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f remaining) -
        (explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f firstRow +
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f remaining) +
          ((explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f firstRow +
              explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f remaining) -
            (explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f firstRow +
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f remaining)) := by
      exact
        congrArg
          (fun z : ℂ =>
            (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f firstRow +
              explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f remaining) -
              (explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f firstRow +
                explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f remaining) +
                ((explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f firstRow +
                    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f remaining) -
                  z))
          hleft
    _ =
      (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f firstRow -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f firstRow +
            (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f firstRow -
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f firstRow)) +
        (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f remaining -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f remaining +
            (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f remaining -
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f remaining)) := by
      exact
        (finiteRectangleSubdivisionEndpointBoundary_consEdgeAlgebra
          (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f firstRow)
          (explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f firstRow)
          (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f firstRow)
          (explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f firstRow)
          (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f remaining)
          (explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f remaining)
          (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f remaining)
          (explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f remaining)).symm

/-- Splitting four grouped edge sums across an appended endpoint-data row gives the sum of
the two grouped edge-accounting expressions. -/
theorem finiteRectangleSubdivisionEndpointBoundary_appendEdgeAlgebra
    (bottom₁ top₁ right₁ left₁ bottom₂ top₂ right₂ left₂ : ℂ) :
    (bottom₁ + bottom₂) - (top₁ + top₂) +
        ((right₁ + right₂) - (left₁ + left₂)) =
      (bottom₁ - top₁ + (right₁ - left₁)) +
        (bottom₂ - top₂ + (right₂ - left₂)) := by
  exact
    (finiteRectangleSubdivisionEndpointBoundary_consEdgeAlgebra
      bottom₁ top₁ right₁ left₁ bottom₂ top₂ right₂ left₂).symm

/-- The four-edge accounting expression for a cons horizontal adjacent-pair list splits
into the first fixed-horizontal row and the recursively constructed remaining rows. -/
theorem explicitFormulaRectangleRegularGridEndpointData_edgeAccounting_adjacentPairLists_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (rest : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))
    (homit :
      ∀ xpair' : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε,
        xpair' ∈ xpair :: rest →
          ∀ ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε,
            ypair ∈ ypairs →
              ∀ a : ℂ,
                a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a.re ∉ [[xpair'.x₀, xpair'.x₁]] ∨
                    a.im ∉ [[ypair.y₀, ypair.y₁]]) :
    let firstRow : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
          xpair ypairs
          (fun ypair hy =>
            homit xpair (List.mem_cons_self xpair rest) ypair hy))
    let remaining : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
        rest ypairs
        (fun xpair' hx' ypair hy =>
          homit xpair' (List.mem_cons_of_mem xpair hx') ypair hy)
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
            (xpair :: rest) ypairs homit) -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
            (xpair :: rest) ypairs homit) +
          (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
              (explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
                (xpair :: rest) ypairs homit) -
            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
              (explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
                (xpair :: rest) ypairs homit)) =
      (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f firstRow -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f firstRow +
            (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f firstRow -
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f firstRow)) +
        (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f remaining -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f remaining +
            (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f remaining -
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f remaining)) := by
  let whole : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
    explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
      (xpair :: rest) ypairs homit
  let firstRow : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
        xpair ypairs
        (fun ypair hy =>
          homit xpair (List.mem_cons_self xpair rest) ypair hy))
  let remaining : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
    explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
      rest ypairs
      (fun xpair' hx' ypair hy =>
        homit xpair' (List.mem_cons_of_mem xpair hx') ypair hy)
  have hbottom :
      explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f whole =
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f firstRow +
          explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f remaining :=
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum_adjacentPairLists_cons
      f xpair rest ypairs homit
  have htop :
      explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f whole =
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f firstRow +
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f remaining :=
    explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum_adjacentPairLists_cons
      f xpair rest ypairs homit
  have hright :
      explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f whole =
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f firstRow +
          explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f remaining :=
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum_adjacentPairLists_cons
      f xpair rest ypairs homit
  have hleft :
      explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f whole =
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f firstRow +
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f remaining :=
    explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum_adjacentPairLists_cons
      f xpair rest ypairs homit
  calc
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f whole -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f whole +
          (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f whole -
            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f whole) =
        (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f firstRow +
            explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f remaining) -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f whole +
            (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f whole -
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f whole) := by
      exact congrArg
        (fun z : ℂ =>
          z - explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f whole +
            (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f whole -
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f whole))
        hbottom
    _ =
        (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f firstRow +
            explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f remaining) -
          (explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f firstRow +
            explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f remaining) +
            (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f whole -
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f whole) := by
      exact congrArg
        (fun z : ℂ =>
          (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f firstRow +
              explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f remaining) -
            z +
              (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f whole -
                explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f whole))
        htop
    _ =
        (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f firstRow +
            explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f remaining) -
          (explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f firstRow +
            explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f remaining) +
            ((explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f firstRow +
                explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f remaining) -
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f whole) := by
      exact congrArg
        (fun z : ℂ =>
          (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f firstRow +
              explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f remaining) -
            (explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f firstRow +
              explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f remaining) +
              (z - explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f whole))
        hright
    _ =
        (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f firstRow +
            explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f remaining) -
          (explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f firstRow +
            explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f remaining) +
            ((explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f firstRow +
                explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f remaining) -
              (explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f firstRow +
                explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f remaining)) := by
      exact congrArg
        (fun z : ℂ =>
          (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f firstRow +
              explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f remaining) -
            (explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f firstRow +
              explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f remaining) +
              ((explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f firstRow +
                  explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f remaining) - z))
        hleft
    _ =
      (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f firstRow -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f firstRow +
            (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f firstRow -
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f firstRow)) +
        (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f remaining -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f remaining +
            (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f remaining -
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f remaining)) := by
      exact
        finiteRectangleSubdivisionEndpointBoundary_appendEdgeAlgebra
          (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f firstRow)
          (explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f firstRow)
          (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f firstRow)
          (explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f firstRow)
          (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f remaining)
          (explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f remaining)
          (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f remaining)
          (explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f remaining)

/-- Internal duplicate of the endpoint-data boundary decomposition retained near the
row-recursive lemmas that historically owned this proof.  The public theorem is stated
earlier because selected edge-accounting consumes it above. -/
theorem explicitFormulaRectangleRegularGridEndpointDataBoundarySum_eq_edgeSums_late
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)) :
    explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data =
      explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data +
          (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data) := by
  induction data with
  | nil =>
      calc
        explicitFormulaRectangleRegularGridEndpointDataBoundarySum f [] = 0 := by
          rfl
        _ =
          explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f [] -
            explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f [] +
              (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f [] -
                explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f []) := by
          rfl
  | cons d rest ih =>
      let b : ℂ := explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f d
      let t : ℂ := explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f d
      let r : ℂ := explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f d
      let l : ℂ := explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f d
      let B : ℂ := explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f rest
      let U : ℂ := explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f rest
      let R : ℂ := explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f rest
      let L : ℂ := explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f rest
      have hd :
          explicitFormulaRectangleRegularGridCellEndpointDataBoundary f d =
            b - t + (r - l) := by
        exact explicitFormulaRectangleRegularGridCellEndpointDataBoundary_eq_edges f d
      have hrest :
          explicitFormulaRectangleRegularGridEndpointDataBoundarySum f rest =
            B - U + (R - L) := by
        exact ih
      calc
        explicitFormulaRectangleRegularGridEndpointDataBoundarySum f (d :: rest) =
            explicitFormulaRectangleRegularGridCellEndpointDataBoundary f d +
              explicitFormulaRectangleRegularGridEndpointDataBoundarySum f rest := by
          exact explicitFormulaRectangleRegularGridEndpointDataBoundarySum_cons f d rest
        _ = (b - t + (r - l)) +
              explicitFormulaRectangleRegularGridEndpointDataBoundarySum f rest := by
          exact congrArg
            (fun z : ℂ =>
              z + explicitFormulaRectangleRegularGridEndpointDataBoundarySum f rest)
            hd
        _ = (b - t + (r - l)) + (B - U + (R - L)) := by
          exact congrArg
            (fun z : ℂ => (b - t + (r - l)) + z)
            hrest
        _ = (b + B) - (t + U) + ((r + R) - (l + L)) := by
          exact
            finiteRectangleSubdivisionEndpointBoundary_consEdgeAlgebra
              b t r l B U R L
        _ =
          explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f (d :: rest) -
            explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f (d :: rest) +
              (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f (d :: rest) -
                explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f (d :: rest)) := by
          rfl

/-- Endpoint-data edge-sum algebra for the punctured subdivision target: once the grouped
bottom, top, and vertical edge sums have been proved to assemble to the tangent outer
rectangle boundary minus the finite inscribed-square hole boundary sum, the endpoint-data
boundary sum is exactly that outer-minus-hole expression. -/
theorem explicitFormulaRectangle_tangentContour_sub_rawInscribedSquareCellBoundarySum_eq_endpointDataBoundarySum_of_edgeSums
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε))
    (hedges :
      explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data +
          (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data) =
        zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
          ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
            finiteRectangleSubdivisionCellBoundaryIntegral
              (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
              (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a)
              (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a)) :
      zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
        ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a)
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a) =
      explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data := by
  have hboundary :
      explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data =
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data +
            (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data) :=
    explicitFormulaRectangleRegularGridEndpointDataBoundarySum_eq_edgeSums f data
  calc
    zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
        ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a)
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a) =
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data +
            (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data) := by
      exact hedges.symm
    _ = explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data := by
      exact hboundary.symm

/-- Endpoint-data subdivision equality from separate grouped edge identifications.  This is
the concrete finite row/column cancellation output expected from a regular-grid endpoint
enumeration: the four endpoint-data edge sums are first collapsed, then their grouped
boundary is identified with the outer tangent rectangle minus the inscribed-square holes. -/
theorem explicitFormulaRectangle_tangentContour_sub_rawInscribedSquareCellBoundarySum_eq_endpointDataBoundarySum_of_collapsedEdges
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε))
    (bottom top right left : ℂ)
    (hbottom :
      explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data = bottom)
    (htop :
      explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data = top)
    (hright :
      explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data = right)
    (hleft :
      explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data = left)
    (hedges :
      bottom - top + (right - left) =
        zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
          ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
            finiteRectangleSubdivisionCellBoundaryIntegral
              (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
              (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a)
              (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a)) :
    zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
        ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a)
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a) =
      explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data := by
  have hassembled :
      explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data +
          (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data) =
        zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
          ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
            finiteRectangleSubdivisionCellBoundaryIntegral
              (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
              (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a)
              (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a) := by
    calc
      explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data +
            (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data) =
          bottom -
            explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data +
              (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
                explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data) := by
        exact congrArg
          (fun z : ℂ =>
            z - explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data +
              (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
                explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data))
          hbottom
      _ =
          bottom - top +
            (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data) := by
        exact congrArg
          (fun z : ℂ =>
            bottom - z +
              (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
                explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data))
          htop
      _ =
          bottom - top +
            (right - explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data) := by
        exact congrArg
          (fun z : ℂ =>
            bottom - top +
              (z - explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data))
          hright
      _ = bottom - top + (right - left) := by
        exact congrArg
          (fun z : ℂ => bottom - top + (right - z))
          hleft
      _ =
        zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
          ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
            finiteRectangleSubdivisionCellBoundaryIntegral
              (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
              (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a)
              (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a) := by
        exact hedges
  exact
    explicitFormulaRectangle_tangentContour_sub_rawInscribedSquareCellBoundarySum_eq_endpointDataBoundarySum_of_edgeSums
      f data hassembled

/-- One-radius constructor for the endpoint-data subdivision equality from collapsed edge
data.  This is the exact finite-radius output required by the endpoint-data `hgrid`
interface, with the edge-cancellation proof kept in the four concrete edge sums. -/
theorem explicitFormulaRectangle_regularGridEndpointDataSubdivisionEquality_of_collapsedEdges
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε))
    (bottom top right left : ℂ)
    (hbottom :
      explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data = bottom)
    (htop :
      explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data = top)
    (hright :
      explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data = right)
    (hleft :
      explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data = left)
    (hedges :
      bottom - top + (right - left) =
        zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
          ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
            finiteRectangleSubdivisionCellBoundaryIntegral
              (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
              (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a)
              (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a)) :
    zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
        ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a)
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a) =
      explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data :=
  explicitFormulaRectangle_tangentContour_sub_rawInscribedSquareCellBoundarySum_eq_endpointDataBoundarySum_of_collapsedEdges
    f data bottom top right left hbottom htop hright hleft hedges

/-- Family-level constructor for the endpoint-data `hgrid` subdivision equality from
collapsed edge data at every admissible radius.  The hypotheses are precisely the
finite-grid construction outputs: a concrete endpoint-data list, its four collapsed edge
sums, and the final outer-minus-hole edge accounting. -/
theorem explicitFormulaRectangle_regularGridEndpointDataSubdivision_hgrid_of_collapsedEdges
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hcollapsed :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            ∃ data : List
                (ExplicitFormulaRectangleRegularGridCellEndpointData F T (ε / 2)),
              ∃ bottom : ℂ,
                ∃ top : ℂ,
                  ∃ right : ℂ,
                    ∃ left : ℂ,
                      explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum
                          f data = bottom ∧
                        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum
                          f data = top ∧
                          explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum
                            f data = right ∧
                            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum
                              f data = left ∧
                              bottom - top + (right - left) =
                                zetaCompletedExplicitFormulaTangentContourIntegral
                                  f (F.rectangle T) -
                                  ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
                                    finiteRectangleSubdivisionCellBoundaryIntegral
                                      (fun z : ℂ =>
                                        zetaCompletedExplicitFormulaContourIntegrand f z)
                                      (explicitFormulaRectangleRawInscribedSquareLowerCorner
                                        (ε / 2) a)
                                      (explicitFormulaRectangleRawInscribedSquareUpperCorner
                                        (ε / 2) a))) :
    ∀ ε : ℝ,
      0 < ε →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            ∀ b : ℂ,
              b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a ≠ b → ε + ε < dist a b) →
          ∃ data : List
              (ExplicitFormulaRectangleRegularGridCellEndpointData F T (ε / 2)),
            zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
                ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
                  finiteRectangleSubdivisionCellBoundaryIntegral
                    (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
                    (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a)
                    (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a) =
              explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data := by
  intro ε hε hclosed hsep
  match hcollapsed ε hε hclosed hsep with
  | ⟨data, bottom, top, right, left, hbottom, htop, hright, hleft, hedges⟩ =>
      exact
        ⟨data,
          explicitFormulaRectangle_regularGridEndpointDataSubdivisionEquality_of_collapsedEdges
            f data bottom top right left hbottom htop hright hleft hedges⟩

/-- Family-level endpoint-data `hgrid` constructor from the actual four edge sums.  This
removes the bookkeeping witnesses from the collapsed-edge interface: the only remaining
subdivision content is the outer-minus-hole edge accounting for the endpoint-data list. -/
theorem explicitFormulaRectangle_regularGridEndpointDataSubdivision_hgrid_of_edgeAccounting
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hedges :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            ∃ data : List
                (ExplicitFormulaRectangleRegularGridCellEndpointData F T (ε / 2)),
              explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data -
                  explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data +
                    (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
                      explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data) =
                zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
                  ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
                    finiteRectangleSubdivisionCellBoundaryIntegral
                      (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
                      (explicitFormulaRectangleRawInscribedSquareLowerCorner
                        (ε / 2) a)
                      (explicitFormulaRectangleRawInscribedSquareUpperCorner
                        (ε / 2) a)) :
    ∀ ε : ℝ,
      0 < ε →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            ∀ b : ℂ,
              b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a ≠ b → ε + ε < dist a b) →
          ∃ data : List
              (ExplicitFormulaRectangleRegularGridCellEndpointData F T (ε / 2)),
            zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
                ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
                  finiteRectangleSubdivisionCellBoundaryIntegral
                    (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
                    (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a)
                    (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a) =
              explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data := by
  have hcollapsed :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            ∃ data : List
                (ExplicitFormulaRectangleRegularGridCellEndpointData F T (ε / 2)),
              ∃ bottom : ℂ,
                ∃ top : ℂ,
                  ∃ right : ℂ,
                    ∃ left : ℂ,
                      explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum
                          f data = bottom ∧
                        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum
                          f data = top ∧
                          explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum
                            f data = right ∧
                            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum
                              f data = left ∧
                              bottom - top + (right - left) =
                                zetaCompletedExplicitFormulaTangentContourIntegral
                                  f (F.rectangle T) -
                                  ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
                                    finiteRectangleSubdivisionCellBoundaryIntegral
                                      (fun z : ℂ =>
                                        zetaCompletedExplicitFormulaContourIntegrand f z)
                                      (explicitFormulaRectangleRawInscribedSquareLowerCorner
                                        (ε / 2) a)
                                      (explicitFormulaRectangleRawInscribedSquareUpperCorner
                                        (ε / 2) a) := by
    intro ε hε hclosed hsep
    match hedges ε hε hclosed hsep with
    | ⟨data, hedge⟩ =>
        exact
          ⟨data,
            explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data,
            explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data,
            explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data,
            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data,
            rfl, rfl, rfl, rfl, hedge⟩
  exact
    explicitFormulaRectangle_regularGridEndpointDataSubdivision_hgrid_of_collapsedEdges
      f F T hcollapsed

/-- Strong endpoint-data `hgrid` constructor from collapsed edge data, retaining the
pointwise cell-boundary vanishing proof for each listed endpoint datum. -/
theorem explicitFormulaRectangle_regularGridEndpointDataSubdivision_hgridWithCellZero_of_collapsedEdges
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hcollapsed :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            ∃ data : List
                (ExplicitFormulaRectangleRegularGridCellEndpointData F T (ε / 2)),
              ∃ bottom : ℂ,
                ∃ top : ℂ,
                  ∃ right : ℂ,
                    ∃ left : ℂ,
                      explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum
                          f data = bottom ∧
                        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum
                          f data = top ∧
                          explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum
                            f data = right ∧
                            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum
                              f data = left ∧
                              bottom - top + (right - left) =
                                zetaCompletedExplicitFormulaTangentContourIntegral
                                  f (F.rectangle T) -
                                  ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
                                    finiteRectangleSubdivisionCellBoundaryIntegral
                                      (fun z : ℂ =>
                                        zetaCompletedExplicitFormulaContourIntegrand f z)
                                      (explicitFormulaRectangleRawInscribedSquareLowerCorner
                                        (ε / 2) a)
                                      (explicitFormulaRectangleRawInscribedSquareUpperCorner
                                        (ε / 2) a) ∧
                                (∀ d : ExplicitFormulaRectangleRegularGridCellEndpointData
                                      F T (ε / 2),
                                    d ∈ data →
                                      explicitFormulaRectangleRegularGridCellEndpointDataBoundary
                                        f d = 0))) :
    ∀ ε : ℝ,
      0 < ε →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            ∀ b : ℂ,
              b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a ≠ b → ε + ε < dist a b) →
          ∃ data : List
              (ExplicitFormulaRectangleRegularGridCellEndpointData F T (ε / 2)),
            zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
                ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
                  finiteRectangleSubdivisionCellBoundaryIntegral
                    (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
                    (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a)
                    (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a) =
              explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data ∧
            (∀ d : ExplicitFormulaRectangleRegularGridCellEndpointData F T (ε / 2),
              d ∈ data →
                explicitFormulaRectangleRegularGridCellEndpointDataBoundary f d = 0) := by
  intro ε hε hclosed hsep
  match hcollapsed ε hε hclosed hsep with
  | ⟨data, bottom, top, right, left,
      hbottom, htop, hright, hleft, hedges, hcell⟩ =>
      have hsubdivision :
          zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
              ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
                finiteRectangleSubdivisionCellBoundaryIntegral
                  (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
                  (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a)
                  (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a) =
            explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data :=
        explicitFormulaRectangle_regularGridEndpointDataSubdivisionEquality_of_collapsedEdges
          f data bottom top right left hbottom htop hright hleft hedges
      exact ⟨data, hsubdivision, hcell⟩


end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
