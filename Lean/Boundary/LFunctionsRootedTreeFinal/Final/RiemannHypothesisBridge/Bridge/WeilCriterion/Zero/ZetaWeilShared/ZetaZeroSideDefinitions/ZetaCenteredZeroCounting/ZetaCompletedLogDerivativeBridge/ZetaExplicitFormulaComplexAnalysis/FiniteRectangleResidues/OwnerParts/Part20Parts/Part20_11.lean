import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part20Parts.Part20_10

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
## Part20 11: VerticalRejectedAndSelectedScan
-/

theorem explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution_eq_rightScan_sub_leftScan
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ}
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :
    explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
        f
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)
        ypair =
      explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          if homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
              ({ x₀ := xpair.x₀
                x₁ := xpair.x₁
                y₀ := ypair.y₀
                y₁ := ypair.y₁
                hx₀ := xpair.hx₀
                hx₁ := xpair.hx₁
                hy₀ := ypair.hy₀
                hy₁ := ypair.hy₁
                hx_order := xpair.hx_order
                hy_order := ypair.hy_order
                hx_adj := xpair.hx_adj
                hy_adj := ypair.hy_adj
                homit := homit } :
                  ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ)
          else
            0)
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) -
      explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          if homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f
              ({ x₀ := xpair.x₀
                x₁ := xpair.x₁
                y₀ := ypair.y₀
                y₁ := ypair.y₁
                hx₀ := xpair.hx₀
                hx₁ := xpair.hx₁
                hy₀ := ypair.hy₀
                hy₁ := ypair.hy₁
                hx_order := xpair.hx_order
                hy_order := ypair.hy_order
                hx_adj := xpair.hx_adj
                hy_adj := ypair.hy_adj
                homit := homit } :
                  ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ)
          else
            0)
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) := by
  let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
    explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
  let rightScan : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → ℂ :=
    fun xpair =>
      if homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
          ({ x₀ := xpair.x₀
            x₁ := xpair.x₁
            y₀ := ypair.y₀
            y₁ := ypair.y₁
            hx₀ := xpair.hx₀
            hx₁ := xpair.hx₁
            hy₀ := ypair.hy₀
            hy₁ := ypair.hy₁
            hx_order := xpair.hx_order
            hy_order := ypair.hy_order
            hx_adj := xpair.hx_adj
            hy_adj := ypair.hy_adj
            homit := homit } :
              ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ)
      else
        0
  let leftScan : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → ℂ :=
    fun xpair =>
      if homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f
          ({ x₀ := xpair.x₀
            x₁ := xpair.x₁
            y₀ := ypair.y₀
            y₁ := ypair.y₁
            hx₀ := xpair.hx₀
            hx₁ := xpair.hx₁
            hy₀ := ypair.hy₀
            hy₁ := ypair.hy₁
            hx_order := xpair.hx_order
            hy_order := ypair.hy_order
            hx_adj := xpair.hx_adj
            hy_adj := ypair.hy_adj
            homit := homit } :
              ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ)
      else
        0
  have hcolumn :
      explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution f xpairs ypair =
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
              f xpair ypair)
          xpairs :=
    explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution_eq_listSum
      f ypair xpairs
  have hpoint :
      ∀ xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ,
        explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
            f xpair ypair =
          rightScan xpair - leftScan xpair := by
    intro xpair
    by_cases homit :
        explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair
    · rfl
    · exact (sub_zero (0 : ℂ)).symm
  have hreplace :
      explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
              f xpair ypair)
          xpairs =
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            rightScan xpair - leftScan xpair)
          xpairs := by
    exact congrArg
      (fun g : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → ℂ =>
        explicitFormulaRectangleListSum g xpairs)
      (funext hpoint)
  calc
    explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution f xpairs ypair =
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
              f xpair ypair)
          xpairs := by
      exact hcolumn
    _ =
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            rightScan xpair - leftScan xpair)
          xpairs := by
      exact hreplace
    _ =
        explicitFormulaRectangleListSum rightScan xpairs -
          explicitFormulaRectangleListSum leftScan xpairs := by
      exact explicitFormulaRectangleListSum_sub rightScan leftScan xpairs

/-- The paired selected vertical coordinate-label sums are exactly the selected
fixed-column endpoint-data contribution.  This isolates the remaining geometric
exposure work from the coordinate/list transport. -/
theorem explicitFormulaRectangleSelectedVerticalEdgeCoordinatesOfFixedY_integralSum_eq_columnContribution
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ}
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :
    explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegralSum f
        (explicitFormulaRectangleSelectedRightEdgeCoordinatesOfFixedY
          (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)
          ypair) -
      explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegralSum f
        (explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfFixedY
          (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)
          ypair) =
      explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
        f
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)
        ypair := by
  let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
    explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
  let rightScan : ℂ :=
    explicitFormulaRectangleListSum
      (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
        if homit :
            explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
          explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
            ({ x₀ := xpair.x₀
              x₁ := xpair.x₁
              y₀ := ypair.y₀
              y₁ := ypair.y₁
              hx₀ := xpair.hx₀
              hx₁ := xpair.hx₁
              hy₀ := ypair.hy₀
              hy₁ := ypair.hy₁
              hx_order := xpair.hx_order
              hy_order := ypair.hy_order
              hx_adj := xpair.hx_adj
              hy_adj := ypair.hy_adj
              homit := homit } :
                ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ)
        else
          0)
      xpairs
  let leftScan : ℂ :=
    explicitFormulaRectangleListSum
      (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
        if homit :
            explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
          explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f
            ({ x₀ := xpair.x₀
              x₁ := xpair.x₁
              y₀ := ypair.y₀
              y₁ := ypair.y₁
              hx₀ := xpair.hx₀
              hx₁ := xpair.hx₁
              hy₀ := ypair.hy₀
              hy₁ := ypair.hy₁
              hx_order := xpair.hx_order
              hy_order := ypair.hy_order
              hx_adj := xpair.hx_adj
              hy_adj := ypair.hy_adj
              homit := homit } :
                ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ)
        else
          0)
      xpairs
  have hright :
      rightScan =
        explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegralSum f
          (explicitFormulaRectangleSelectedRightEdgeCoordinatesOfFixedY xpairs ypair) :=
    explicitFormulaRectangleSelectedFixedY_rightScan_eq_coordinateIntegralSum
      f xpairs ypair
  have hleft :
      leftScan =
        explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegralSum f
          (explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfFixedY xpairs ypair) :=
    explicitFormulaRectangleSelectedFixedY_leftScan_eq_coordinateIntegralSum
      f xpairs ypair
  have hcolumn :
      explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
          f xpairs ypair =
        rightScan - leftScan :=
    explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution_eq_rightScan_sub_leftScan
      f F ypair
  calc
    explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegralSum f
        (explicitFormulaRectangleSelectedRightEdgeCoordinatesOfFixedY xpairs ypair) -
      explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegralSum f
        (explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfFixedY xpairs ypair) =
        rightScan -
          explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegralSum f
            (explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfFixedY xpairs ypair) := by
      exact congrArg
        (fun z : ℂ =>
          z -
            explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegralSum f
              (explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfFixedY xpairs ypair))
        hright.symm
    _ = rightScan - leftScan := by
      exact congrArg (fun z : ℂ => rightScan - z) hleft.symm
    _ =
        explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
          f xpairs ypair := by
      exact hcolumn.symm

/-- Fixed-column rejected vertical scan grouping.  The non-selected right-minus-left
horizontal adjacent-pair scan is exactly the sum of raw-hole right-minus-left slices
whose vertical span contains the fixed `ypair`. -/
theorem explicitFormulaRectangleRejectedEndpointDataVerticalColumnScanSub_eq_holeSub
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hρ : 0 < ρ)
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
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            0
          else
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
                f ((ypair.y₀, ypair.y₁), xpair.x₁) -
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
                f ((ypair.y₀, ypair.y₁), xpair.x₀))
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
      (∑ a in explicitFormulaRectangleRawSingularCoordinates T,
        if _hspan :
            explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
          explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
            ((ypair.y₀, ypair.y₁),
              (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
        else
          0) -
        (∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
            explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
              ((ypair.y₀, ypair.y₁),
                (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
          else
            0) := by
  let S : Finset ℂ := explicitFormulaRectangleRawSingularCoordinates T
  let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
    explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
  let contribution : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → ℂ :=
    fun xpair =>
      explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
          f ((ypair.y₀, ypair.y₁), xpair.x₁) -
        explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
          f ((ypair.y₀, ypair.y₁), xpair.x₀)
  let rawContribution : ℂ → ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → ℂ :=
    fun a xpair =>
      if _hspan :
          explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a ∧
            explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
        contribution xpair
      else
        0
  have hclassified :
      explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            if _homit :
                explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
              0
            else
              contribution xpair)
          xpairs =
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            ∑ a in S, rawContribution a xpair)
          xpairs := by
    exact congrArg
      (fun g : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → ℂ =>
        explicitFormulaRectangleListSum g xpairs)
      (funext
        (fun xpair =>
          explicitFormulaRectangleRejectedCoordinateOmission_pairContribution_eq_rawHoleSubspanFinsetSum
            hρ hsep xpair ypair
            (explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
              f ((ypair.y₀, ypair.y₁), xpair.x₁))
            (explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
              f ((ypair.y₀, ypair.y₁), xpair.x₀)))
  have hcommute :
      explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            ∑ a in S, rawContribution a xpair)
          xpairs =
        ∑ a in S,
          explicitFormulaRectangleListSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              rawContribution a xpair)
            xpairs :=
    explicitFormulaRectangleListSum_finset_sum
      S
      (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
        fun a : ℂ => rawContribution a xpair)
      xpairs
  have hraw :
      (∑ a in S,
          explicitFormulaRectangleListSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              rawContribution a xpair)
            xpairs) =
        ∑ a in S,
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re) -
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
          else
            0 := by
    exact Finset.sum_congr rfl
      (fun a ha =>
        by
          by_cases hy :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a
          · let xOnly : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → ℂ :=
              fun xpair =>
                if _hx :
                    explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a then
                  contribution xpair
                else
                  0
            have hreduce :
                explicitFormulaRectangleListSum
                    (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                      rawContribution a xpair)
                    xpairs =
                  explicitFormulaRectangleListSum xOnly xpairs := by
              exact congrArg
                (fun g : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → ℂ =>
                  explicitFormulaRectangleListSum g xpairs)
                (funext
                  (fun xpair =>
                    by
                      by_cases hx :
                          explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                            ρ xpair a
                      · calc
                          rawContribution a xpair = contribution xpair := by
                            exact if_pos (And.intro hx hy)
                          _ = xOnly xpair := by
                            exact (if_pos hx).symm
                      · have hnot :
                            ¬
                              (explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                                  ρ xpair a ∧
                                explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
                                  ρ ypair a) :=
                            fun hboth => hx hboth.1
                        calc
                          rawContribution a xpair = 0 := by
                            exact if_neg hnot
                          _ = xOnly xpair := by
                            exact (if_neg hx).symm))
            have hblock :
                explicitFormulaRectangleListSum xOnly xpairs =
                  explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
                      ((ypair.y₀, ypair.y₁),
                        (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re) -
                    explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
                      ((ypair.y₀, ypair.y₁),
                        (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re) :=
              explicitFormulaRectangleXAdjacentEndpointPairSubspanRawHole_verticalScanSub_eq_rawSides
                f F hρ ha ypair
            calc
              explicitFormulaRectangleListSum
                  (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                    rawContribution a xpair)
                  xpairs =
                  explicitFormulaRectangleListSum xOnly xpairs := by
                exact hreduce
              _ =
                  explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
                      ((ypair.y₀, ypair.y₁),
                        (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re) -
                    explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
                      ((ypair.y₀, ypair.y₁),
                        (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re) := by
                exact hblock
              _ =
                  (if _hspan :
                      explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
                    explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
                        ((ypair.y₀, ypair.y₁),
                          (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re) -
                      explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
                        ((ypair.y₀, ypair.y₁),
                          (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
                  else
                    0) := by
                exact (if_pos hy).symm
          · have hzero :
                explicitFormulaRectangleListSum
                    (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                      rawContribution a xpair)
                    xpairs =
                  0 := by
              have hfun :
                  (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                      rawContribution a xpair) =
                    (fun _xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                      (0 : ℂ)) := by
                exact funext
                  (fun xpair =>
                    by
                      have hnot :
                          ¬
                            (explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                                ρ xpair a ∧
                              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
                                ρ ypair a) :=
                          fun hboth => hy hboth.2
                      exact if_neg hnot)
              exact Eq.trans
                (congrArg
                  (fun g : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → ℂ =>
                    explicitFormulaRectangleListSum g xpairs)
                  hfun)
                (explicitFormulaRectangleListSum_zero xpairs)
            calc
              explicitFormulaRectangleListSum
                  (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                    rawContribution a xpair)
                  xpairs = 0 := by
                exact hzero
              _ =
                  (if _hspan :
                      explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
                    explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
                        ((ypair.y₀, ypair.y₁),
                          (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re) -
                      explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
                        ((ypair.y₀, ypair.y₁),
                          (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
                  else
                    0) := by
                exact (if_neg hy).symm)
  have hsplit :
      (∑ a in S,
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re) -
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
          else
            0) =
        (∑ a in S,
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
              ((ypair.y₀, ypair.y₁),
                (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
          else
            0) -
          (∑ a in S,
            if _hspan :
                explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
            else
              0) := by
    have hpoint :
        ∀ a : ℂ,
          (if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re) -
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
          else
            0) =
            (if _hspan :
                explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
              explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
            else
              0) -
              (if _hspan :
                  explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
                explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
                  ((ypair.y₀, ypair.y₁),
                    (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
              else
                0) := by
      intro a
      by_cases hy :
          explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a
      · rfl
      · exact (sub_zero (0 : ℂ)).symm
    calc
      (∑ a in S,
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re) -
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
          else
            0) =
          ∑ a in S,
            ((if _hspan :
                explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
              explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
            else
              0) -
              (if _hspan :
                  explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
                explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
                  ((ypair.y₀, ypair.y₁),
                    (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
              else
                0)) := by
        exact Finset.sum_congr rfl (fun a _ha => hpoint a)
      _ =
        (∑ a in S,
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
              ((ypair.y₀, ypair.y₁),
                (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
          else
            0) -
          (∑ a in S,
            if _hspan :
                explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
            else
              0) := by
        exact Finset.sum_sub_distrib
  calc
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          if _homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            0
          else
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
                f ((ypair.y₀, ypair.y₁), xpair.x₁) -
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
                f ((ypair.y₀, ypair.y₁), xpair.x₀))
        xpairs =
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            ∑ a in S, rawContribution a xpair)
          xpairs := by
      exact hclassified
    _ =
        ∑ a in S,
          explicitFormulaRectangleListSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              rawContribution a xpair)
            xpairs := by
      exact hcommute
    _ =
        ∑ a in S,
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re) -
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
          else
            0 := by
      exact hraw
    _ =
        (∑ a in S,
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
              ((ypair.y₀, ypair.y₁),
                (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
          else
            0) -
          (∑ a in S,
            if _hspan :
                explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
            else
              0) := by
      exact hsplit

/-- Fixed-column paired vertical scan partition.  On a fixed vertical adjacent span, the
selected right-minus-left vertical scans are the full outer right-minus-left scan with
exactly the raw-hole right-minus-left scans removed. -/
theorem explicitFormulaRectangleSelectedEndpointDataVerticalColumnScanSub_eq_outerSub_sub_holeSub
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
    (explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          if homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
              ({ x₀ := xpair.x₀
                x₁ := xpair.x₁
                y₀ := ypair.y₀
                y₁ := ypair.y₁
                hx₀ := xpair.hx₀
                hx₁ := xpair.hx₁
                hy₀ := ypair.hy₀
                hy₁ := ypair.hy₁
                hx_order := xpair.hx_order
                hy_order := ypair.hy_order
                hx_adj := xpair.hx_adj
                hy_adj := ypair.hy_adj
                homit := homit } :
                  ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ)
          else
            0)
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)) -
      (explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          if homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f
              ({ x₀ := xpair.x₀
                x₁ := xpair.x₁
                y₀ := ypair.y₀
                y₁ := ypair.y₁
                hx₀ := xpair.hx₀
                hx₁ := xpair.hx₁
                hy₀ := ypair.hy₀
                hy₁ := ypair.hy₁
                hx_order := xpair.hx_order
                hy_order := ypair.hy_order
                hx_adj := xpair.hx_adj
                hy_adj := ypair.hy_adj
                homit := homit } :
                  ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ)
          else
            0)
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)) =
      (explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
          f ((ypair.y₀, ypair.y₁), F.c) -
        explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
          f ((ypair.y₀, ypair.y₁), 1 - F.c)) -
        ((∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
              ((ypair.y₀, ypair.y₁),
                (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
          else
            0) -
          (∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
            explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
              ((ypair.y₀, ypair.y₁),
                (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
          else
            0)) := by
  let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
    explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
  let P : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → Prop :=
    fun xpair => explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair
  let rightCoord : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → ℂ :=
    fun xpair =>
      explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
        f ((ypair.y₀, ypair.y₁), xpair.x₁)
  let leftCoord : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → ℂ :=
    fun xpair =>
      explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
        f ((ypair.y₀, ypair.y₁), xpair.x₀)
  have hcell_right :
      explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            if homit :
                explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
              explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
                ({ x₀ := xpair.x₀
                  x₁ := xpair.x₁
                  y₀ := ypair.y₀
                  y₁ := ypair.y₁
                  hx₀ := xpair.hx₀
                  hx₁ := xpair.hx₁
                  hy₀ := ypair.hy₀
                  hy₁ := ypair.hy₁
                  hx_order := xpair.hx_order
                  hy_order := ypair.hy_order
                  hx_adj := xpair.hx_adj
                  hy_adj := ypair.hy_adj
                  homit := homit } :
                    ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ)
            else
              0)
          xpairs =
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            if _homit : P xpair then rightCoord xpair else 0)
          xpairs := by
    calc
      explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            if homit :
                explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
              explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
                ({ x₀ := xpair.x₀
                  x₁ := xpair.x₁
                  y₀ := ypair.y₀
                  y₁ := ypair.y₁
                  hx₀ := xpair.hx₀
                  hx₁ := xpair.hx₁
                  hy₀ := ypair.hy₀
                  hy₁ := ypair.hy₁
                  hx_order := xpair.hx_order
                  hy_order := ypair.hy_order
                  hx_adj := xpair.hx_adj
                  hy_adj := ypair.hy_adj
                  homit := homit } :
                    ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ)
            else
              0)
          xpairs =
          explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegralSum f
            (explicitFormulaRectangleSelectedRightEdgeCoordinatesOfFixedY xpairs ypair) := by
        exact explicitFormulaRectangleSelectedFixedY_rightScan_eq_coordinateIntegralSum
          f xpairs ypair
      _ =
          explicitFormulaRectangleListSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              if _homit : P xpair then rightCoord xpair else 0)
            xpairs := by
        exact explicitFormulaRectangleSelectedRightEdgeCoordinatesOfFixedY_integralSum_eq_listSum
          f ypair xpairs
  have hcell_left :
      explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            if homit :
                explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
              explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f
                ({ x₀ := xpair.x₀
                  x₁ := xpair.x₁
                  y₀ := ypair.y₀
                  y₁ := ypair.y₁
                  hx₀ := xpair.hx₀
                  hx₁ := xpair.hx₁
                  hy₀ := ypair.hy₀
                  hy₁ := ypair.hy₁
                  hx_order := xpair.hx_order
                  hy_order := ypair.hy_order
                  hx_adj := xpair.hx_adj
                  hy_adj := ypair.hy_adj
                  homit := homit } :
                    ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ)
            else
              0)
          xpairs =
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            if _homit : P xpair then leftCoord xpair else 0)
          xpairs := by
    calc
      explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            if homit :
                explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
              explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f
                ({ x₀ := xpair.x₀
                  x₁ := xpair.x₁
                  y₀ := ypair.y₀
                  y₁ := ypair.y₁
                  hx₀ := xpair.hx₀
                  hx₁ := xpair.hx₁
                  hy₀ := ypair.hy₀
                  hy₁ := ypair.hy₁
                  hx_order := xpair.hx_order
                  hy_order := ypair.hy_order
                  hx_adj := xpair.hx_adj
                  hy_adj := ypair.hy_adj
                  homit := homit } :
                    ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ)
            else
              0)
          xpairs =
          explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegralSum f
            (explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfFixedY xpairs ypair) := by
        exact explicitFormulaRectangleSelectedFixedY_leftScan_eq_coordinateIntegralSum
          f xpairs ypair
      _ =
          explicitFormulaRectangleListSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              if _homit : P xpair then leftCoord xpair else 0)
            xpairs := by
        exact explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfFixedY_integralSum_eq_listSum
          f ypair xpairs
  have hselected :
      explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            if _homit : P xpair then rightCoord xpair else 0)
          xpairs -
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            if _homit : P xpair then leftCoord xpair else 0)
          xpairs =
        (explicitFormulaRectangleListSum rightCoord xpairs -
          explicitFormulaRectangleListSum leftCoord xpairs) -
          (explicitFormulaRectangleListSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              if _homit : P xpair then 0 else rightCoord xpair)
            xpairs -
            explicitFormulaRectangleListSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                if _homit : P xpair then 0 else leftCoord xpair)
              xpairs) :=
    explicitFormulaRectangleListSum_selectSub_eq_totalSub_sub_rejectSub
      P rightCoord leftCoord xpairs
  have htotal :
      explicitFormulaRectangleListSum rightCoord xpairs -
          explicitFormulaRectangleListSum leftCoord xpairs =
        explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
            f ((ypair.y₀, ypair.y₁), F.c) -
          explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
            f ((ypair.y₀, ypair.y₁), 1 - F.c) :=
    explicitFormulaRectangleXAdjacentEndpointPair_totalVerticalScanSub_eq_outerSub
      f F hρ hclosed ypair
  have hrejected :
      explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            if _homit : P xpair then 0 else rightCoord xpair)
          xpairs -
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            if _homit : P xpair then 0 else leftCoord xpair)
          xpairs =
        (∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
              ((ypair.y₀, ypair.y₁),
                (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
          else
            0) -
          (∑ a in explicitFormulaRectangleRawSingularCoordinates T,
            if _hspan :
                explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
            else
              0) := by
    have hcombine :
        explicitFormulaRectangleListSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              if _homit : P xpair then 0 else rightCoord xpair)
            xpairs -
          explicitFormulaRectangleListSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              if _homit : P xpair then 0 else leftCoord xpair)
            xpairs =
          explicitFormulaRectangleListSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              if _homit : P xpair then 0 else rightCoord xpair - leftCoord xpair)
            xpairs := by
      let rejectRight : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → ℂ :=
        fun xpair => if _homit : P xpair then 0 else rightCoord xpair
      let rejectLeft : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → ℂ :=
        fun xpair => if _homit : P xpair then 0 else leftCoord xpair
      have hsub :
          explicitFormulaRectangleListSum rejectRight xpairs -
              explicitFormulaRectangleListSum rejectLeft xpairs =
            explicitFormulaRectangleListSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                rejectRight xpair - rejectLeft xpair)
              xpairs :=
        (explicitFormulaRectangleListSum_sub rejectRight rejectLeft xpairs).symm
      have hpoint :
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              rejectRight xpair - rejectLeft xpair) =
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              if _homit : P xpair then 0 else rightCoord xpair - leftCoord xpair) := by
        exact funext
          (fun xpair =>
            by
              by_cases homit : P xpair
              · rfl
              · rfl)
      exact Eq.trans hsub
        (congrArg
          (fun g : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → ℂ =>
            explicitFormulaRectangleListSum g xpairs)
          hpoint)
    calc
      explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            if _homit : P xpair then 0 else rightCoord xpair)
          xpairs -
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            if _homit : P xpair then 0 else leftCoord xpair)
          xpairs =
          explicitFormulaRectangleListSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              if _homit : P xpair then 0 else rightCoord xpair - leftCoord xpair)
            xpairs := by
        exact hcombine
      _ =
          (∑ a in explicitFormulaRectangleRawSingularCoordinates T,
            if _hspan :
                explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
              explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
            else
              0) -
            (∑ a in explicitFormulaRectangleRawSingularCoordinates T,
              if _hspan :
                  explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
                explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
                  ((ypair.y₀, ypair.y₁),
                    (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
              else
                0) := by
        exact explicitFormulaRectangleRejectedEndpointDataVerticalColumnScanSub_eq_holeSub
          f F hρ hsep ypair
  calc
    (explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          if homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
              ({ x₀ := xpair.x₀
                x₁ := xpair.x₁
                y₀ := ypair.y₀
                y₁ := ypair.y₁
                hx₀ := xpair.hx₀
                hx₁ := xpair.hx₁
                hy₀ := ypair.hy₀
                hy₁ := ypair.hy₁
                hx_order := xpair.hx_order
                hy_order := ypair.hy_order
                hx_adj := xpair.hx_adj
                hy_adj := ypair.hy_adj
                homit := homit } :
                  ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ)
          else
            0)
        xpairs) -
      (explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          if homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f
              ({ x₀ := xpair.x₀
                x₁ := xpair.x₁
                y₀ := ypair.y₀
                y₁ := ypair.y₁
                hx₀ := xpair.hx₀
                hx₁ := xpair.hx₁
                hy₀ := ypair.hy₀
                hy₁ := ypair.hy₁
                hx_order := xpair.hx_order
                hy_order := ypair.hy_order
                hx_adj := xpair.hx_adj
                hy_adj := ypair.hy_adj
                homit := homit } :
                  ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ)
          else
            0)
        xpairs) =
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            if _homit : P xpair then rightCoord xpair else 0)
          xpairs -
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            if _homit : P xpair then leftCoord xpair else 0)
          xpairs := by
      exact congrArg₂ HSub.hSub hcell_right hcell_left
    _ =
        (explicitFormulaRectangleListSum rightCoord xpairs -
          explicitFormulaRectangleListSum leftCoord xpairs) -
          (explicitFormulaRectangleListSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              if _homit : P xpair then 0 else rightCoord xpair)
            xpairs -
            explicitFormulaRectangleListSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                if _homit : P xpair then 0 else leftCoord xpair)
              xpairs) := by
      exact hselected
    _ =
        (explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
            f ((ypair.y₀, ypair.y₁), F.c) -
          explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
            f ((ypair.y₀, ypair.y₁), 1 - F.c)) -
        (explicitFormulaRectangleListSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              if _homit : P xpair then 0 else rightCoord xpair)
            xpairs -
          explicitFormulaRectangleListSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              if _homit : P xpair then 0 else leftCoord xpair)
            xpairs) := by
      exact congrArg
        (fun z : ℂ =>
          z -
            (explicitFormulaRectangleListSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                if _homit : P xpair then 0 else rightCoord xpair)
              xpairs -
              explicitFormulaRectangleListSum
                (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                  if _homit : P xpair then 0 else leftCoord xpair)
                xpairs))
        htotal
    _ =
      (explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
          f ((ypair.y₀, ypair.y₁), F.c) -
        explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
          f ((ypair.y₀, ypair.y₁), 1 - F.c)) -
        ((∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
              ((ypair.y₀, ypair.y₁),
                (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
          else
            0) -
          (∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
            explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
              ((ypair.y₀, ypair.y₁),
                (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
          else
            0)) := by
      exact congrArg
        (fun z : ℂ =>
          (explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
              f ((ypair.y₀, ypair.y₁), F.c) -
            explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
              f ((ypair.y₀, ypair.y₁), 1 - F.c)) - z)
        hrejected

/-- Fixed-column vertical coordinate-omission partition.  For one vertical adjacent
slice, the selected right-minus-left scan over horizontal adjacent pairs is the full
outer right-minus-left slice with exactly the raw square-hole subspans removed. -/
theorem explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution_eq_outerSlice_sub_holeSlice_of_coordinateOmissionPartition
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
    explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
        f
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)
        ypair =
      explicitFormulaRectangleVerticalOuterSliceContribution f F T ypair -
        explicitFormulaRectangleVerticalHoleSliceContribution f T ρ ypair := by
  let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
    explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
  let outerRight : ℂ :=
    explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
      f ((ypair.y₀, ypair.y₁), F.c)
  let outerLeft : ℂ :=
    explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
      f ((ypair.y₀, ypair.y₁), 1 - F.c)
  let holeRight : ℂ :=
    ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
      if _hspan :
          explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
        explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
          ((ypair.y₀, ypair.y₁),
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
      else
        0
  let holeLeft : ℂ :=
    ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
      if _hspan :
          explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
        explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
          ((ypair.y₀, ypair.y₁),
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
      else
        0
  let rightScan : ℂ :=
    explicitFormulaRectangleListSum
      (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
        if homit :
            explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
          explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
            ({ x₀ := xpair.x₀
              x₁ := xpair.x₁
              y₀ := ypair.y₀
              y₁ := ypair.y₁
              hx₀ := xpair.hx₀
              hx₁ := xpair.hx₁
              hy₀ := ypair.hy₀
              hy₁ := ypair.hy₁
              hx_order := xpair.hx_order
              hy_order := ypair.hy_order
              hx_adj := xpair.hx_adj
              hy_adj := ypair.hy_adj
              homit := homit } :
                ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ)
        else
          0)
      xpairs
  let leftScan : ℂ :=
    explicitFormulaRectangleListSum
      (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
        if homit :
            explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
          explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f
            ({ x₀ := xpair.x₀
              x₁ := xpair.x₁
              y₀ := ypair.y₀
              y₁ := ypair.y₁
              hx₀ := xpair.hx₀
              hx₁ := xpair.hx₁
              hy₀ := ypair.hy₀
              hy₁ := ypair.hy₁
              hx_order := xpair.hx_order
              hy_order := ypair.hy_order
              hx_adj := xpair.hx_adj
              hy_adj := ypair.hy_adj
              homit := homit } :
                ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ)
        else
          0)
      xpairs
  have hcolumn :
      explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
          f xpairs ypair =
        rightScan - leftScan :=
    explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution_eq_rightScan_sub_leftScan
      f F ypair
  have hscan :
      rightScan - leftScan =
        (outerRight - outerLeft) - (holeRight - holeLeft) :=
    explicitFormulaRectangleSelectedEndpointDataVerticalColumnScanSub_eq_outerSub_sub_holeSub
      f F hT_nonneg hρ hclosed hsep ypair
  have houter :
      explicitFormulaRectangleVerticalOuterSliceContribution f F T ypair =
        outerRight - outerLeft := by
    rfl
  have hhole :
      explicitFormulaRectangleVerticalHoleSliceContribution f T ρ ypair =
        holeRight - holeLeft :=
    explicitFormulaRectangleVerticalHoleSliceContribution_eq_right_sub_left f T ρ ypair
  calc
    explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
        f xpairs ypair =
        rightScan - leftScan := by
      exact hcolumn
    _ = (outerRight - outerLeft) - (holeRight - holeLeft) := by
      exact hscan
    _ =
        explicitFormulaRectangleVerticalOuterSliceContribution f F T ypair -
          (holeRight - holeLeft) := by
      exact congrArg (fun z : ℂ => z - (holeRight - holeLeft)) houter.symm
    _ =
        explicitFormulaRectangleVerticalOuterSliceContribution f F T ypair -
          explicitFormulaRectangleVerticalHoleSliceContribution f T ρ ypair := by
      exact congrArg
        (fun z : ℂ =>
          explicitFormulaRectangleVerticalOuterSliceContribution f F T ypair - z)
        hhole.symm

/-- Fixed-column vertical selected contribution collapses to the local outer vertical
slice minus the local square-hole vertical slices. -/
theorem explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution_eq_outerSlice_sub_holeSlice
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
    explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
        f
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)
        ypair =
      explicitFormulaRectangleVerticalOuterSliceContribution f F T ypair -
        explicitFormulaRectangleVerticalHoleSliceContribution f T ρ ypair := by
  exact
    explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution_eq_outerSlice_sub_holeSlice_of_coordinateOmissionPartition
      f F hT_nonneg hρ hclosed hsep ypair

/-- Coordinate-label version of the fixed-column vertical exposure statement.  The
selected vertical labels in one horizontal slice telescope as a pair: selected right
minus selected left equals the outer right-minus-left slice with the raw hole
right-minus-left slices removed. -/

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
