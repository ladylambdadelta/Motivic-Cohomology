import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part20Parts.Part20_15

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
## Part20 16: HorizontalRejectedAndSelectedScan
-/

theorem explicitFormulaRectangleRejectedEndpointDataHorizontalRowScanSub_eq_holeSub
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hρ : 0 < ρ)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ρ + ρ < dist a b)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :
    explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          if _homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            0
          else
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                f ((xpair.x₀, xpair.x₁), ypair.y₀) -
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                f ((xpair.x₀, xpair.x₁), ypair.y₁))
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      (∑ a in explicitFormulaRectangleRawSingularCoordinates T,
        if _hspan :
            explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a then
          explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
            ((xpair.x₀, xpair.x₁),
              (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
        else
          0) -
        (∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          if _hspan :
              explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a then
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
              ((xpair.x₀, xpair.x₁),
                (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
          else
            0) := by
  let S : Finset ℂ := explicitFormulaRectangleRawSingularCoordinates T
  let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
    explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
  let contribution : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ → ℂ :=
    fun ypair =>
      explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
          f ((xpair.x₀, xpair.x₁), ypair.y₀) -
        explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
          f ((xpair.x₀, xpair.x₁), ypair.y₁)
  let rawContribution : ℂ → ExplicitFormulaRectangleYAdjacentEndpointPair T ρ → ℂ :=
    fun a ypair =>
      if _hspan :
          explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a ∧
            explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
        contribution ypair
      else
        0
  have hclassified :
      explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            if _homit :
                explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
              0
            else
              contribution ypair)
          ypairs =
        explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            ∑ a in S, rawContribution a ypair)
          ypairs := by
    exact congrArg
      (fun g : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ → ℂ =>
        explicitFormulaRectangleListSum g ypairs)
      (funext
        (fun ypair =>
          explicitFormulaRectangleRejectedCoordinateOmission_pairContribution_eq_rawHoleSubspanFinsetSum
            hρ hsep xpair ypair
            (explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
              f ((xpair.x₀, xpair.x₁), ypair.y₀))
            (explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
              f ((xpair.x₀, xpair.x₁), ypair.y₁))))
  have hcommute :
      explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            ∑ a in S, rawContribution a ypair)
          ypairs =
        ∑ a in S,
          explicitFormulaRectangleListSum
            (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
              rawContribution a ypair)
            ypairs :=
    explicitFormulaRectangleListSum_finset_sum
      S
      (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
        fun a : ℂ => rawContribution a ypair)
      ypairs
  have hraw :
      (∑ a in S,
          explicitFormulaRectangleListSum
            (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
              rawContribution a ypair)
            ypairs) =
        ∑ a in S,
          if _hspan :
              explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a then
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
                ((xpair.x₀, xpair.x₁),
                  (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im) -
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
                ((xpair.x₀, xpair.x₁),
                  (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
          else
            0 := by
    exact Finset.sum_congr rfl
      (fun a ha =>
        by
          by_cases hx :
              explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a
          · let yOnly : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ → ℂ :=
              fun ypair =>
                if _hy :
                    explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a then
                  contribution ypair
                else
                  0
            have hreduce :
                explicitFormulaRectangleListSum
                    (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                      rawContribution a ypair)
                    ypairs =
                  explicitFormulaRectangleListSum yOnly ypairs := by
              exact congrArg
                (fun g : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ → ℂ =>
                  explicitFormulaRectangleListSum g ypairs)
                (funext
                  (fun ypair =>
                    by
                      by_cases hy :
                          explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
                            ρ ypair a
                      · calc
                          rawContribution a ypair = contribution ypair := by
                            exact if_pos (And.intro hx hy)
                          _ = yOnly ypair := by
                            exact (if_pos hy).symm
                      · have hnot :
                            ¬
                              (explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                                  ρ xpair a ∧
                                explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
                                  ρ ypair a) :=
                            fun hboth => hy hboth.2
                        calc
                          rawContribution a ypair = 0 := by
                            exact if_neg hnot
                          _ = yOnly ypair := by
                            exact (if_neg hy).symm))
            have hblock :
                explicitFormulaRectangleListSum yOnly ypairs =
                  explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
                      ((xpair.x₀, xpair.x₁),
                        (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im) -
                    explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
                      ((xpair.x₀, xpair.x₁),
                        (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im) :=
              explicitFormulaRectangleYAdjacentEndpointPairSubspanRawHole_horizontalScanSub_eq_rawSides
                f hρ ha xpair
            calc
              explicitFormulaRectangleListSum
                  (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                    rawContribution a ypair)
                  ypairs =
                  explicitFormulaRectangleListSum yOnly ypairs := by
                exact hreduce
              _ =
                  explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
                      ((xpair.x₀, xpair.x₁),
                        (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im) -
                    explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
                      ((xpair.x₀, xpair.x₁),
                        (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im) := by
                exact hblock
              _ =
                  (if _hspan :
                      explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a then
                    explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
                        ((xpair.x₀, xpair.x₁),
                          (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im) -
                      explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
                        ((xpair.x₀, xpair.x₁),
                          (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
                  else
                    0) := by
                exact (if_pos hx).symm
          · have hzero :
                explicitFormulaRectangleListSum
                    (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                      rawContribution a ypair)
                    ypairs =
                  0 := by
              have hfun :
                  (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                      rawContribution a ypair) =
                    (fun _ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                      (0 : ℂ)) := by
                exact funext
                  (fun ypair =>
                    by
                      have hnot :
                          ¬
                            (explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                                ρ xpair a ∧
                              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
                                ρ ypair a) :=
                          fun hboth => hx hboth.1
                      exact if_neg hnot)
              exact Eq.trans
                (congrArg
                  (fun g : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ → ℂ =>
                    explicitFormulaRectangleListSum g ypairs)
                  hfun)
                (explicitFormulaRectangleListSum_zero ypairs)
            calc
              explicitFormulaRectangleListSum
                  (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                    rawContribution a ypair)
                  ypairs = 0 := by
                exact hzero
              _ =
                  (if _hspan :
                      explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a then
                    explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
                        ((xpair.x₀, xpair.x₁),
                          (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im) -
                      explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
                        ((xpair.x₀, xpair.x₁),
                          (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
                  else
                    0) := by
                exact (if_neg hx).symm)
  have hsplit :
      (∑ a in S,
          if _hspan :
              explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a then
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
                ((xpair.x₀, xpair.x₁),
                  (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im) -
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
                ((xpair.x₀, xpair.x₁),
                  (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
          else
            0) =
        (∑ a in S,
          if _hspan :
              explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a then
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
              ((xpair.x₀, xpair.x₁),
                (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
          else
            0) -
          (∑ a in S,
            if _hspan :
                explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a then
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
                ((xpair.x₀, xpair.x₁),
                  (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
            else
              0) := by
    have hpoint :
        ∀ a : ℂ,
          (if _hspan :
              explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a then
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
                ((xpair.x₀, xpair.x₁),
                  (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im) -
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
                ((xpair.x₀, xpair.x₁),
                  (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
          else
            0) =
            (if _hspan :
                explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a then
              explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
                ((xpair.x₀, xpair.x₁),
                  (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
            else
              0) -
              (if _hspan :
                  explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a then
                explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
                  ((xpair.x₀, xpair.x₁),
                    (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
              else
                0) := by
      intro a
      by_cases hx :
          explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a
      · rfl
      · exact (sub_zero (0 : ℂ)).symm
    calc
      (∑ a in S,
          if _hspan :
              explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a then
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
                ((xpair.x₀, xpair.x₁),
                  (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im) -
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
                ((xpair.x₀, xpair.x₁),
                  (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
          else
            0) =
          ∑ a in S,
            ((if _hspan :
                explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a then
              explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
                ((xpair.x₀, xpair.x₁),
                  (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
            else
              0) -
              (if _hspan :
                  explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a then
                explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
                  ((xpair.x₀, xpair.x₁),
                    (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
              else
                0)) := by
        exact Finset.sum_congr rfl (fun a _ha => hpoint a)
      _ =
        (∑ a in S,
          if _hspan :
              explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a then
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
              ((xpair.x₀, xpair.x₁),
                (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
          else
            0) -
          (∑ a in S,
            if _hspan :
                explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a then
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
                ((xpair.x₀, xpair.x₁),
                  (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
            else
              0) := by
        exact Finset.sum_sub_distrib
  calc
    explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          if _homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            0
          else
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                f ((xpair.x₀, xpair.x₁), ypair.y₀) -
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                f ((xpair.x₀, xpair.x₁), ypair.y₁))
        ypairs =
        explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            ∑ a in S, rawContribution a ypair)
          ypairs := by
      exact hclassified
    _ =
        ∑ a in S,
          explicitFormulaRectangleListSum
            (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
              rawContribution a ypair)
            ypairs := by
      exact hcommute
    _ =
        ∑ a in S,
          if _hspan :
              explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a then
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
                ((xpair.x₀, xpair.x₁),
                  (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im) -
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
                ((xpair.x₀, xpair.x₁),
                  (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
          else
            0 := by
      exact hraw
    _ =
        (∑ a in S,
          if _hspan :
              explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a then
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
              ((xpair.x₀, xpair.x₁),
                (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
          else
            0) -
          (∑ a in S,
            if _hspan :
                explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a then
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
                ((xpair.x₀, xpair.x₁),
                  (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
            else
              0) := by
      exact hsplit

/-- Fixed-row paired horizontal scan partition.  On a fixed horizontal adjacent span, the
selected bottom-minus-top horizontal scans are the full outer bottom-minus-top scan with
exactly the raw-hole bottom-minus-top scans removed. -/
theorem explicitFormulaRectangleSelectedEndpointDataHorizontalRowScanSub_eq_outerSub_sub_holeSub
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
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :
    (explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          if homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
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
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ)) -
      (explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          if homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
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
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ)) =
      (explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
          f ((xpair.x₀, xpair.x₁), -T) -
        explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
          f ((xpair.x₀, xpair.x₁), T)) -
        ((∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          if _hspan :
              explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a then
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
              ((xpair.x₀, xpair.x₁),
                (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
          else
            0) -
          (∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          if _hspan :
              explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a then
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
              ((xpair.x₀, xpair.x₁),
                (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
          else
            0)) := by
  let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
    explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
  let P : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ → Prop :=
    fun ypair => explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair
  let bottomCoord : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ → ℂ :=
    fun ypair =>
      explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
        f ((xpair.x₀, xpair.x₁), ypair.y₀)
  let topCoord : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ → ℂ :=
    fun ypair =>
      explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
        f ((xpair.x₀, xpair.x₁), ypair.y₁)
  have hcell_bottom :
      explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            if homit :
                explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
              explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
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
          ypairs =
        explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            if _homit : P ypair then bottomCoord ypair else 0)
          ypairs := by
    calc
      explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            if homit :
                explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
              explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
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
          ypairs =
          explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
            (explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX xpair ypairs) := by
        exact explicitFormulaRectangleSelectedFixedX_bottomScan_eq_coordinateIntegralSum
          f xpair ypairs
      _ =
          explicitFormulaRectangleListSum
            (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
              if _homit : P ypair then bottomCoord ypair else 0)
            ypairs := by
        exact explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX_integralSum_eq_listSum
          f xpair ypairs
  have hcell_top :
      explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            if homit :
                explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
              explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
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
          ypairs =
        explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            if _homit : P ypair then topCoord ypair else 0)
          ypairs := by
    calc
      explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            if homit :
                explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
              explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
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
          ypairs =
          explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
            (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair ypairs) := by
        exact explicitFormulaRectangleSelectedFixedX_topScan_eq_coordinateIntegralSum
          f xpair ypairs
      _ =
          explicitFormulaRectangleListSum
            (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
              if _homit : P ypair then topCoord ypair else 0)
            ypairs := by
        exact explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX_integralSum_eq_listSum
          f xpair ypairs
  have hselected :
      explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            if _homit : P ypair then bottomCoord ypair else 0)
          ypairs -
        explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            if _homit : P ypair then topCoord ypair else 0)
          ypairs =
        (explicitFormulaRectangleListSum bottomCoord ypairs -
          explicitFormulaRectangleListSum topCoord ypairs) -
          (explicitFormulaRectangleListSum
            (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
              if _homit : P ypair then 0 else bottomCoord ypair)
            ypairs -
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                if _homit : P ypair then 0 else topCoord ypair)
              ypairs) :=
    explicitFormulaRectangleListSum_selectSub_eq_totalSub_sub_rejectSub
      P bottomCoord topCoord ypairs
  have htotal :
      explicitFormulaRectangleListSum bottomCoord ypairs -
          explicitFormulaRectangleListSum topCoord ypairs =
        explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
            f ((xpair.x₀, xpair.x₁), -T) -
          explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
            f ((xpair.x₀, xpair.x₁), T) :=
    explicitFormulaRectangleYAdjacentEndpointPair_totalHorizontalScanSub_eq_outerSub
      f F hT_nonneg hρ hclosed xpair
  have hrejected :
      explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            if _homit : P ypair then 0 else bottomCoord ypair)
          ypairs -
        explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            if _homit : P ypair then 0 else topCoord ypair)
          ypairs =
        (∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          if _hspan :
              explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a then
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
              ((xpair.x₀, xpair.x₁),
                (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
          else
            0) -
          (∑ a in explicitFormulaRectangleRawSingularCoordinates T,
            if _hspan :
                explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a then
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
                ((xpair.x₀, xpair.x₁),
                  (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
            else
              0) := by
    have hcombine :
        explicitFormulaRectangleListSum
            (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
              if _homit : P ypair then 0 else bottomCoord ypair)
            ypairs -
          explicitFormulaRectangleListSum
            (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
              if _homit : P ypair then 0 else topCoord ypair)
            ypairs =
          explicitFormulaRectangleListSum
            (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
              if _homit : P ypair then 0 else bottomCoord ypair - topCoord ypair)
            ypairs := by
      let rejectBottom : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ → ℂ :=
        fun ypair => if _homit : P ypair then 0 else bottomCoord ypair
      let rejectTop : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ → ℂ :=
        fun ypair => if _homit : P ypair then 0 else topCoord ypair
      have hsub :
          explicitFormulaRectangleListSum rejectBottom ypairs -
              explicitFormulaRectangleListSum rejectTop ypairs =
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                rejectBottom ypair - rejectTop ypair)
              ypairs :=
        (explicitFormulaRectangleListSum_sub rejectBottom rejectTop ypairs).symm
      have hpoint :
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
              rejectBottom ypair - rejectTop ypair) =
            (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
              if _homit : P ypair then 0 else bottomCoord ypair - topCoord ypair) := by
        exact funext
          (fun ypair =>
            by
              by_cases homit : P ypair
              · rfl
              · rfl)
      exact Eq.trans hsub
        (congrArg
          (fun g : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ → ℂ =>
            explicitFormulaRectangleListSum g ypairs)
          hpoint)
    calc
      explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            if _homit : P ypair then 0 else bottomCoord ypair)
          ypairs -
        explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            if _homit : P ypair then 0 else topCoord ypair)
          ypairs =
          explicitFormulaRectangleListSum
            (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
              if _homit : P ypair then 0 else bottomCoord ypair - topCoord ypair)
            ypairs := by
        exact hcombine
      _ =
          (∑ a in explicitFormulaRectangleRawSingularCoordinates T,
            if _hspan :
                explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a then
              explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
                ((xpair.x₀, xpair.x₁),
                  (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
            else
              0) -
            (∑ a in explicitFormulaRectangleRawSingularCoordinates T,
              if _hspan :
                  explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a then
                explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
                  ((xpair.x₀, xpair.x₁),
                    (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
              else
                0) := by
        exact explicitFormulaRectangleRejectedEndpointDataHorizontalRowScanSub_eq_holeSub
          f F hρ hsep xpair
  calc
    (explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          if homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
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
        ypairs) -
      (explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          if homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
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
        ypairs) =
        explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            if _homit : P ypair then bottomCoord ypair else 0)
          ypairs -
        explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            if _homit : P ypair then topCoord ypair else 0)
          ypairs := by
      exact congrArg₂ HSub.hSub hcell_bottom hcell_top
    _ =
        (explicitFormulaRectangleListSum bottomCoord ypairs -
          explicitFormulaRectangleListSum topCoord ypairs) -
          (explicitFormulaRectangleListSum
            (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
              if _homit : P ypair then 0 else bottomCoord ypair)
            ypairs -
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                if _homit : P ypair then 0 else topCoord ypair)
              ypairs) := by
      exact hselected
    _ =
        (explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
            f ((xpair.x₀, xpair.x₁), -T) -
          explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
            f ((xpair.x₀, xpair.x₁), T)) -
          (explicitFormulaRectangleListSum
            (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
              if _homit : P ypair then 0 else bottomCoord ypair)
            ypairs -
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                if _homit : P ypair then 0 else topCoord ypair)
              ypairs) := by
      exact congrArg
        (fun z : ℂ =>
          z -
            (explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                if _homit : P ypair then 0 else bottomCoord ypair)
              ypairs -
              explicitFormulaRectangleListSum
                (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                  if _homit : P ypair then 0 else topCoord ypair)
                ypairs))
        htotal
    _ =
        (explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
            f ((xpair.x₀, xpair.x₁), -T) -
          explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
            f ((xpair.x₀, xpair.x₁), T)) -
          ((∑ a in explicitFormulaRectangleRawSingularCoordinates T,
            if _hspan :
                explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a then
              explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
                ((xpair.x₀, xpair.x₁),
                  (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
            else
              0) -
            (∑ a in explicitFormulaRectangleRawSingularCoordinates T,
              if _hspan :
                  explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a then
                explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
                  ((xpair.x₀, xpair.x₁),
                    (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
              else
                0)) := by
      exact congrArg
        (fun z : ℂ =>
          (explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
              f ((xpair.x₀, xpair.x₁), -T) -
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
              f ((xpair.x₀, xpair.x₁), T)) - z)
        hrejected

/-- Fixed-row horizontal coordinate-omission partition.  For one horizontal adjacent
slice, the selected bottom-minus-top scan over vertical adjacent pairs is the full
outer bottom-minus-top slice with exactly the raw square-hole subspans removed. -/
theorem explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution_eq_outerSlice_sub_holeSlice_of_coordinateOmissionPartition
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
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :
    explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
        f xpair
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      explicitFormulaRectangleHorizontalOuterSliceContribution f F T xpair -
        explicitFormulaRectangleHorizontalHoleSliceContribution f T ρ xpair := by
  let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
    explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
  let outerBottom : ℂ :=
    explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
      f ((xpair.x₀, xpair.x₁), -T)
  let outerTop : ℂ :=
    explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
      f ((xpair.x₀, xpair.x₁), T)
  let holeBottom : ℂ :=
    ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
      if _hspan :
          explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a then
        explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
          ((xpair.x₀, xpair.x₁),
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
      else
        0
  let holeTop : ℂ :=
    ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
      if _hspan :
          explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a then
        explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
          ((xpair.x₀, xpair.x₁),
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
      else
        0
  let bottomScan : ℂ :=
    explicitFormulaRectangleListSum
      (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
        if homit :
            explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
          explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
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
      ypairs
  let topScan : ℂ :=
    explicitFormulaRectangleListSum
      (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
        if homit :
            explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
          explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
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
      ypairs
  have hrow :
      explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
          f xpair ypairs =
        bottomScan - topScan :=
    by
      let bottomFn : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ → ℂ :=
        fun ypair =>
          if homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
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
      let topFn : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ → ℂ :=
        fun ypair =>
          if homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
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
      have hlist :
          explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
              f xpair ypairs =
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                explicitFormulaRectangleSelectedEndpointDataHorizontalCellContribution
                  f xpair ypair)
              ypairs :=
        explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution_eq_listSum
          f xpair ypairs
      have hpoint :
          ∀ ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ,
            explicitFormulaRectangleSelectedEndpointDataHorizontalCellContribution
                f xpair ypair =
              bottomFn ypair - topFn ypair := by
        intro ypair
        by_cases homit :
            explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair
        · rfl
        · exact (sub_zero (0 : ℂ)).symm
      have hreplace :
          explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                explicitFormulaRectangleSelectedEndpointDataHorizontalCellContribution
                  f xpair ypair)
              ypairs =
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                bottomFn ypair - topFn ypair)
              ypairs := by
        exact congrArg
          (fun g : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ → ℂ =>
            explicitFormulaRectangleListSum g ypairs)
          (funext hpoint)
      calc
        explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
            f xpair ypairs =
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                explicitFormulaRectangleSelectedEndpointDataHorizontalCellContribution
                  f xpair ypair)
              ypairs := by
          exact hlist
        _ =
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                bottomFn ypair - topFn ypair)
              ypairs := by
          exact hreplace
        _ =
            explicitFormulaRectangleListSum bottomFn ypairs -
              explicitFormulaRectangleListSum topFn ypairs := by
          exact explicitFormulaRectangleListSum_sub bottomFn topFn ypairs
  have hscan :
      bottomScan - topScan =
        (outerBottom - outerTop) - (holeBottom - holeTop) :=
    explicitFormulaRectangleSelectedEndpointDataHorizontalRowScanSub_eq_outerSub_sub_holeSub
      f F hT_nonneg hρ hclosed hsep xpair
  have houter :
      explicitFormulaRectangleHorizontalOuterSliceContribution f F T xpair =
        outerBottom - outerTop := by
    rfl
  have hhole :
      explicitFormulaRectangleHorizontalHoleSliceContribution f T ρ xpair =
        holeBottom - holeTop :=
    explicitFormulaRectangleHorizontalHoleSliceContribution_eq_bottom_sub_top f T ρ xpair
  calc
    explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
        f xpair ypairs =
        bottomScan - topScan := by
      exact hrow
    _ = (outerBottom - outerTop) - (holeBottom - holeTop) := by
      exact hscan
    _ =
        explicitFormulaRectangleHorizontalOuterSliceContribution f F T xpair -
          (holeBottom - holeTop) := by
      exact congrArg (fun z : ℂ => z - (holeBottom - holeTop)) houter.symm
    _ =
        explicitFormulaRectangleHorizontalOuterSliceContribution f F T xpair -
          explicitFormulaRectangleHorizontalHoleSliceContribution f T ρ xpair := by
      exact congrArg
        (fun z : ℂ =>
          explicitFormulaRectangleHorizontalOuterSliceContribution f F T xpair - z)
        hhole.symm

/-- Fixed-row horizontal selected contribution collapses to the local outer horizontal
slice minus the local square-hole horizontal slices.

This is the owner-level horizontal exposure sink; coordinate-label and scan statements
below are wrappers around this endpoint-data row contribution. -/
theorem explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution_eq_outerSlice_sub_holeSlice_core
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
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :
    explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
        f xpair
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      explicitFormulaRectangleHorizontalOuterSliceContribution f F T xpair -
        explicitFormulaRectangleHorizontalHoleSliceContribution f T ρ xpair := by
  exact
    explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution_eq_outerSlice_sub_holeSlice_of_coordinateOmissionPartition
      f F hT_nonneg hρ hclosed hsep xpair

/-- Coordinate-label selected fixed-row horizontal sums equal the endpoint-data row
contribution.  This is separated from the outer-minus-hole exposure so the geometric
classification sink is owned by the row contribution theorem. -/
theorem explicitFormulaRectangleSelectedHorizontalEdgeCoordinatesOfFixedX_integralSum_eq_rowContribution_core
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :
    explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
        (explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX
          xpair
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ)) -
      explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
        (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX
          xpair
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ)) =
      explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
        f xpair
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) := by
  let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
    explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
  let bottomScan : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ → ℂ :=
    fun ypair =>
      if homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
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
  let topScan : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ → ℂ :=
    fun ypair =>
      if homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
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
  have hbottom :
      bottomScan =
        explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX xpair ypairs) :=
    explicitFormulaRectangleSelectedFixedX_bottomScan_eq_coordinateIntegralSum
      f xpair ypairs
  have htop :
      topScan =
        explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
          (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair ypairs) :=
    explicitFormulaRectangleSelectedFixedX_topScan_eq_coordinateIntegralSum
      f xpair ypairs
  have hrowList :
      explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
          f xpair ypairs =
        explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            explicitFormulaRectangleSelectedEndpointDataHorizontalCellContribution
              f xpair ypair)
          ypairs :=
    explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution_eq_listSum
      f xpair ypairs
  have hpoint :
      ∀ ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ,
        explicitFormulaRectangleSelectedEndpointDataHorizontalCellContribution
            f xpair ypair =
          bottomScan ypair - topScan ypair := by
    intro ypair
    by_cases homit :
        explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair
    · rfl
    · exact (sub_zero (0 : ℂ)).symm
  have hreplace :
      explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            explicitFormulaRectangleSelectedEndpointDataHorizontalCellContribution
              f xpair ypair)
          ypairs =
        explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            bottomScan ypair - topScan ypair)
          ypairs := by
    exact congrArg
      (fun g : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ → ℂ =>
        explicitFormulaRectangleListSum g ypairs)
      (funext hpoint)
  have hrow :
      explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
          f xpair ypairs =
        explicitFormulaRectangleListSum bottomScan ypairs -
          explicitFormulaRectangleListSum topScan ypairs := by
    calc
      explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
          f xpair ypairs =
          explicitFormulaRectangleListSum
            (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
              explicitFormulaRectangleSelectedEndpointDataHorizontalCellContribution
                f xpair ypair)
            ypairs := by
        exact hrowList
      _ =
          explicitFormulaRectangleListSum
            (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
              bottomScan ypair - topScan ypair)
            ypairs := by
        exact hreplace
      _ =
          explicitFormulaRectangleListSum bottomScan ypairs -
            explicitFormulaRectangleListSum topScan ypairs := by
        exact explicitFormulaRectangleListSum_sub bottomScan topScan ypairs
  calc
    explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
        (explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX xpair ypairs) -
      explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
        (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair ypairs) =
        explicitFormulaRectangleListSum bottomScan ypairs -
          explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
            (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair ypairs) := by
      exact congrArg
        (fun z : ℂ =>
          z -
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
              (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair ypairs))
        hbottom.symm
    _ =
        explicitFormulaRectangleListSum bottomScan ypairs -
          explicitFormulaRectangleListSum topScan ypairs := by
      exact congrArg
        (fun z : ℂ => explicitFormulaRectangleListSum bottomScan ypairs - z)
        htop.symm
    _ =
        explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
          f xpair ypairs := by
      exact hrow.symm

/-- Coordinate-label version of the fixed-row horizontal exposure statement.  The
selected horizontal labels in one vertical slice telescope as a pair: selected bottom
minus selected top equals the outer bottom-minus-top slice with the raw hole
bottom-minus-top slices removed. -/
theorem explicitFormulaRectangleSelectedHorizontalEdgeCoordinatesOfFixedX_integralSum_eq_outerSlice_sub_holeSlice
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
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :
    explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
        (explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX
          xpair
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ)) -
      explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
        (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX
          xpair
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ)) =
      explicitFormulaRectangleHorizontalOuterSliceContribution f F T xpair -
        explicitFormulaRectangleHorizontalHoleSliceContribution f T ρ xpair := by
  have hcoords :
      explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX
            xpair
            (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ)) -
        explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
          (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX
            xpair
            (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ)) =
        explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
          f xpair
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) :=
    explicitFormulaRectangleSelectedHorizontalEdgeCoordinatesOfFixedX_integralSum_eq_rowContribution_core
      f F xpair
  have hrow :
      explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
          f xpair
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
        explicitFormulaRectangleHorizontalOuterSliceContribution f F T xpair -
          explicitFormulaRectangleHorizontalHoleSliceContribution f T ρ xpair :=
    explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution_eq_outerSlice_sub_holeSlice_core
      f F hT_nonneg hρ hclosed hsep xpair
  exact Eq.trans hcoords hrow

/-- Fixed-row selected horizontal scan collapses, as a paired bottom-minus-top scan, to
the local outer horizontal slice minus the local square-hole horizontal slices. -/

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
