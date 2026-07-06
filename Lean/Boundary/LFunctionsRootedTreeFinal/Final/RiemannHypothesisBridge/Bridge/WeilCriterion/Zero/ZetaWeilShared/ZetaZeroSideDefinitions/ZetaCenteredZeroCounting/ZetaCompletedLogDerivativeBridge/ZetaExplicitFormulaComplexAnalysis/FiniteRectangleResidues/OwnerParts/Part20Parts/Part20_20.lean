import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part20Parts.Part20_19

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
## Part20 20: SelectedEndpointGlobalCores
-/

/-- Endpoint data owned by a raw-hole-selected adjacent-pair cell.  The selection
predicate is raw-hole omission; positive radius converts that omission to the
coordinate omission stored by endpoint data. -/
noncomputable def explicitFormulaRectangleRawHoleSelectedAdjacentEndpointData
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ} (hρ : 0 < ρ)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ)
    (homit : explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair) :
    ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ :=
  explicitFormulaRectangleSelectedAdjacentEndpointData
    xpair ypair
    (explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission.centerOmission hρ homit)

/-- Raw-hole-selected endpoint data over one fixed horizontal adjacent endpoint pair. -/
noncomputable def explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ} (hρ : 0 < ρ)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :
    List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) →
      List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ)
  | [] => []
  | ypair :: rest =>
      if homit :
          explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
        explicitFormulaRectangleRawHoleSelectedAdjacentEndpointData hρ xpair ypair homit ::
          explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX hρ xpair rest
      else
        explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX hρ xpair rest

/-- Raw-hole-selected endpoint data over crossed horizontal and vertical adjacent-pair
lists. -/
noncomputable def explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ} (hρ : 0 < ρ) :
    List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) →
      List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) →
        List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ)
  | [], _ypairs => []
  | xpair :: rest, ypairs =>
      explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX hρ xpair ypairs ++
        explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists hρ rest ypairs

/-- Canonical raw-hole-selected endpoint data over the sorted adjacent-pair grid. -/
noncomputable def explicitFormulaRectangleRawHoleSelectedEndpointData
    (F : ExplicitFormulaContourFamily) (T ρ : ℝ) (hρ : 0 < ρ) :
    List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
  explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists hρ
    (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)
    (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ)

theorem explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX_bottom_sum
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ} (hρ : 0 < ρ)
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :
    ∀ ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ),
      explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
          (explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX hρ xpair ypairs) =
        explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            if _homit :
                explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
              explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                f ((xpair.x₀, xpair.x₁), ypair.y₀)
            else
              0)
          ypairs
  | [] => by
      exact Eq.refl _
  | ypair :: rest => by
      have htail :
          explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
              (explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX hρ xpair rest) =
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                if _homit :
                    explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                  explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                    f ((xpair.x₀, xpair.x₁), ypair.y₀)
                else
                  0)
              rest :=
        explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX_bottom_sum
          hρ f xpair rest
      match inferInstanceAs
          (Decidable (explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair)) with
      | isTrue homit =>
          have hcell :
              explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
                (explicitFormulaRectangleRawHoleSelectedAdjacentEndpointData
                  hρ xpair ypair homit) =
              explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                f ((xpair.x₀, xpair.x₁), ypair.y₀) :=
            explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge_eq_coordinateIntegral
              f
              (explicitFormulaRectangleRawHoleSelectedAdjacentEndpointData
                hρ xpair ypair homit)
          have hhead :
              (if _homit :
                  explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                  f ((xpair.x₀, xpair.x₁), ypair.y₀)
              else
                0) =
              explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                f ((xpair.x₀, xpair.x₁), ypair.y₀) :=
            dif_pos homit
          calc
            explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
                (explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX hρ xpair
                  (ypair :: rest)) =
                explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
                  (explicitFormulaRectangleRawHoleSelectedAdjacentEndpointData
                      hρ xpair ypair homit ::
                    explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX
                      hρ xpair rest) := by
              exact congrArg
                (fun data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) =>
                  explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data)
                (dif_pos homit)
            _ =
                explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
                    (explicitFormulaRectangleRawHoleSelectedAdjacentEndpointData
                      hρ xpair ypair homit) +
                  explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
                    (explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX hρ xpair rest) := by
              exact Eq.refl _
            _ =
                explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                    f ((xpair.x₀, xpair.x₁), ypair.y₀) +
                  explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
                    (explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX hρ xpair rest) := by
              exact congrArg
                (fun z : ℂ =>
                  z +
                    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
                      (explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX hρ xpair rest))
                hcell
            _ =
                explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                    f ((xpair.x₀, xpair.x₁), ypair.y₀) +
                  explicitFormulaRectangleListSum
                    (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                      if _homit :
                          explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                        explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                          f ((xpair.x₀, xpair.x₁), ypair.y₀)
                      else
                        0)
                    rest := by
              exact congrArg
                (fun z : ℂ =>
                  explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                      f ((xpair.x₀, xpair.x₁), ypair.y₀) + z)
                htail
            _ =
                (if _homit :
                    explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                  explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                    f ((xpair.x₀, xpair.x₁), ypair.y₀)
                else
                  0) +
                  explicitFormulaRectangleListSum
                    (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                      if _homit :
                          explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                        explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                          f ((xpair.x₀, xpair.x₁), ypair.y₀)
                      else
                        0)
                    rest := by
              exact congrArg
                (fun z : ℂ =>
                  z +
                    explicitFormulaRectangleListSum
                      (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                        if _homit :
                            explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                          explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                            f ((xpair.x₀, xpair.x₁), ypair.y₀)
                        else
                          0)
                      rest)
                hhead.symm
            _ =
                explicitFormulaRectangleListSum
                  (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                    if _homit :
                        explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                      explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                        f ((xpair.x₀, xpair.x₁), ypair.y₀)
                    else
                      0)
                  (ypair :: rest) := by
              exact Eq.refl _
      | isFalse hnot =>
          have hhead :
              (if _homit :
                  explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                  f ((xpair.x₀, xpair.x₁), ypair.y₀)
              else
                0) =
              0 :=
            dif_neg hnot
          calc
            explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
                (explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX hρ xpair
                  (ypair :: rest)) =
                explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
                  (explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX hρ xpair rest) := by
              exact congrArg
                (fun data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) =>
                  explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data)
                (dif_neg hnot)
            _ =
                explicitFormulaRectangleListSum
                  (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                    if _homit :
                        explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                      explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                        f ((xpair.x₀, xpair.x₁), ypair.y₀)
                    else
                      0)
                  rest := by
              exact htail
            _ =
                0 +
                  explicitFormulaRectangleListSum
                  (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                    if _homit :
                        explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                      explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                        f ((xpair.x₀, xpair.x₁), ypair.y₀)
                    else
                      0)
                  rest := by
              exact (zero_add _).symm
            _ =
                (if _homit :
                    explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                  explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                    f ((xpair.x₀, xpair.x₁), ypair.y₀)
                else
                  0) +
                  explicitFormulaRectangleListSum
                    (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                      if _homit :
                          explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                        explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                          f ((xpair.x₀, xpair.x₁), ypair.y₀)
                      else
                        0)
                    rest := by
              exact congrArg
                (fun z : ℂ =>
                  z +
                    explicitFormulaRectangleListSum
                      (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                        if _homit :
                            explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                          explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                            f ((xpair.x₀, xpair.x₁), ypair.y₀)
                        else
                          0)
                      rest)
                hhead.symm
            _ =
                explicitFormulaRectangleListSum
                  (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                    if _homit :
                        explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                      explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                        f ((xpair.x₀, xpair.x₁), ypair.y₀)
                    else
                      0)
                  (ypair :: rest) := by
              exact Eq.refl _

theorem explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX_top_sum
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ} (hρ : 0 < ρ)
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :
    ∀ ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ),
      explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
          (explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX hρ xpair ypairs) =
        explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            if _homit :
                explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                f ((xpair.x₀, xpair.x₁), ypair.y₁)
            else
              0)
          ypairs
  | [] => by
      exact Eq.refl _
  | ypair :: rest => by
      have htail :
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
              (explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX hρ xpair rest) =
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                if _homit :
                    explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                  explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                    f ((xpair.x₀, xpair.x₁), ypair.y₁)
                else
                  0)
              rest :=
        explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX_top_sum
          hρ f xpair rest
      match inferInstanceAs
          (Decidable (explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair)) with
      | isTrue homit =>
          have hcell :
              explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
                (explicitFormulaRectangleRawHoleSelectedAdjacentEndpointData
                  hρ xpair ypair homit) =
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                f ((xpair.x₀, xpair.x₁), ypair.y₁) :=
            explicitFormulaRectangleRegularGridCellEndpointDataTopEdge_eq_coordinateIntegral
              f
              (explicitFormulaRectangleRawHoleSelectedAdjacentEndpointData
                hρ xpair ypair homit)
          have hhead :
              (if _homit :
                  explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                  f ((xpair.x₀, xpair.x₁), ypair.y₁)
              else
                0) =
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                f ((xpair.x₀, xpair.x₁), ypair.y₁) :=
            dif_pos homit
          calc
            explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
                (explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX hρ xpair
                  (ypair :: rest)) =
                explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
                  (explicitFormulaRectangleRawHoleSelectedAdjacentEndpointData
                      hρ xpair ypair homit ::
                    explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX
                      hρ xpair rest) := by
              exact congrArg
                (fun data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) =>
                  explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data)
                (dif_pos homit)
            _ =
                explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
                    (explicitFormulaRectangleRawHoleSelectedAdjacentEndpointData
                      hρ xpair ypair homit) +
                  explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
                    (explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX hρ xpair rest) := by
              exact Eq.refl _
            _ =
                explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                    f ((xpair.x₀, xpair.x₁), ypair.y₁) +
                  explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
                    (explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX hρ xpair rest) := by
              exact congrArg
                (fun z : ℂ =>
                  z +
                    explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
                      (explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX hρ xpair rest))
                hcell
            _ =
                explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                    f ((xpair.x₀, xpair.x₁), ypair.y₁) +
                  explicitFormulaRectangleListSum
                    (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                      if _homit :
                          explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                        explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                          f ((xpair.x₀, xpair.x₁), ypair.y₁)
                      else
                        0)
                    rest := by
              exact congrArg
                (fun z : ℂ =>
                  explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                      f ((xpair.x₀, xpair.x₁), ypair.y₁) + z)
                htail
            _ =
                (if _homit :
                    explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                  explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                    f ((xpair.x₀, xpair.x₁), ypair.y₁)
                else
                  0) +
                  explicitFormulaRectangleListSum
                    (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                      if _homit :
                          explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                        explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                          f ((xpair.x₀, xpair.x₁), ypair.y₁)
                      else
                        0)
                    rest := by
              exact congrArg
                (fun z : ℂ =>
                  z +
                    explicitFormulaRectangleListSum
                      (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                        if _homit :
                            explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                          explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                            f ((xpair.x₀, xpair.x₁), ypair.y₁)
                        else
                          0)
                      rest)
                hhead.symm
            _ =
                explicitFormulaRectangleListSum
                  (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                    if _homit :
                        explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                      explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                        f ((xpair.x₀, xpair.x₁), ypair.y₁)
                    else
                      0)
                  (ypair :: rest) := by
              exact Eq.refl _
      | isFalse hnot =>
          have hhead :
              (if _homit :
                  explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                  f ((xpair.x₀, xpair.x₁), ypair.y₁)
              else
                0) =
              0 :=
            dif_neg hnot
          calc
            explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
                (explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX hρ xpair
                  (ypair :: rest)) =
                explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
                  (explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX hρ xpair rest) := by
              exact congrArg
                (fun data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) =>
                  explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data)
                (dif_neg hnot)
            _ =
                explicitFormulaRectangleListSum
                  (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                    if _homit :
                        explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                      explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                        f ((xpair.x₀, xpair.x₁), ypair.y₁)
                    else
                      0)
                  rest := by
              exact htail
            _ =
                0 +
                  explicitFormulaRectangleListSum
                    (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                      if _homit :
                          explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                        explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                          f ((xpair.x₀, xpair.x₁), ypair.y₁)
                      else
                        0)
                    rest := by
              exact (zero_add _).symm
            _ =
                (if _homit :
                    explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                  explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                    f ((xpair.x₀, xpair.x₁), ypair.y₁)
                else
                  0) +
                  explicitFormulaRectangleListSum
                    (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                      if _homit :
                          explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                        explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                          f ((xpair.x₀, xpair.x₁), ypair.y₁)
                      else
                        0)
                    rest := by
              exact congrArg
                (fun z : ℂ =>
                  z +
                    explicitFormulaRectangleListSum
                      (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                        if _homit :
                            explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                          explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                            f ((xpair.x₀, xpair.x₁), ypair.y₁)
                        else
                          0)
                      rest)
                hhead.symm
            _ =
                explicitFormulaRectangleListSum
                  (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                    if _homit :
                        explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                      explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                        f ((xpair.x₀, xpair.x₁), ypair.y₁)
                    else
                      0)
                  (ypair :: rest) := by
              exact Eq.refl _

theorem explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists_bottom_sum
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ} (hρ : 0 < ρ)
    (f : ZetaAdmissibleFunction)
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ)) :
    ∀ xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ),
      explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
          (explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists hρ xpairs ypairs) =
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                if _homit :
                    explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                  explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                    f ((xpair.x₀, xpair.x₁), ypair.y₀)
                else
                  0)
              ypairs)
          xpairs
  | [] => by
      exact Eq.refl _
  | xpair :: rest => by
      have hhead :
          explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
              (explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX hρ xpair ypairs) =
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                if _homit :
                    explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                  explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                    f ((xpair.x₀, xpair.x₁), ypair.y₀)
                else
                  0)
              ypairs :=
        explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX_bottom_sum hρ f xpair ypairs
      have htail :
          explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
              (explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists hρ rest ypairs) =
            explicitFormulaRectangleListSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                explicitFormulaRectangleListSum
                  (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                    if _homit :
                        explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                      explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                        f ((xpair.x₀, xpair.x₁), ypair.y₀)
                    else
                      0)
                  ypairs)
              rest :=
        explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists_bottom_sum hρ f ypairs rest
      calc
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
            (explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists hρ (xpair :: rest)
              ypairs) =
            explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
                (explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX hρ xpair ypairs) +
              explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
                (explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists hρ rest ypairs) := by
          exact
            explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum_append
              f
              (explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX hρ xpair ypairs)
              (explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists hρ rest ypairs)
        _ =
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                if _homit :
                    explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                  explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                    f ((xpair.x₀, xpair.x₁), ypair.y₀)
                else
                  0)
              ypairs +
              explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
                (explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists hρ rest ypairs) := by
          exact congrArg
            (fun z : ℂ =>
              z +
                explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
                  (explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists hρ rest ypairs))
            hhead
        _ =
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                if _homit :
                    explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                  explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                    f ((xpair.x₀, xpair.x₁), ypair.y₀)
                else
                  0)
              ypairs +
              explicitFormulaRectangleListSum
                (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                  explicitFormulaRectangleListSum
                    (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                      if _homit :
                          explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                        explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                          f ((xpair.x₀, xpair.x₁), ypair.y₀)
                      else
                        0)
                    ypairs)
                rest := by
          exact congrArg
            (fun z : ℂ =>
              explicitFormulaRectangleListSum
                (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                  if _homit :
                      explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                    explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                      f ((xpair.x₀, xpair.x₁), ypair.y₀)
                  else
                    0)
                ypairs + z)
            htail
        _ =
            explicitFormulaRectangleListSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                explicitFormulaRectangleListSum
                  (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                    if _homit :
                        explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                      explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                        f ((xpair.x₀, xpair.x₁), ypair.y₀)
                    else
                      0)
                  ypairs)
              (xpair :: rest) := by
          exact Eq.refl _

theorem explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists_top_sum
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ} (hρ : 0 < ρ)
    (f : ZetaAdmissibleFunction)
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ)) :
    ∀ xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ),
      explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
          (explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists hρ xpairs ypairs) =
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                if _homit :
                    explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                  explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                    f ((xpair.x₀, xpair.x₁), ypair.y₁)
                else
                  0)
              ypairs)
          xpairs
  | [] => by
      exact Eq.refl _
  | xpair :: rest => by
      have hhead :
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
              (explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX hρ xpair ypairs) =
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                if _homit :
                    explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                  explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                    f ((xpair.x₀, xpair.x₁), ypair.y₁)
                else
                  0)
              ypairs :=
        explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX_top_sum hρ f xpair ypairs
      have htail :
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
              (explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists hρ rest ypairs) =
            explicitFormulaRectangleListSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                explicitFormulaRectangleListSum
                  (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                    if _homit :
                        explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                      explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                        f ((xpair.x₀, xpair.x₁), ypair.y₁)
                    else
                      0)
                  ypairs)
              rest :=
        explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists_top_sum hρ f ypairs rest
      calc
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
            (explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists hρ (xpair :: rest)
              ypairs) =
            explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
                (explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX hρ xpair ypairs) +
              explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
                (explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists hρ rest ypairs) := by
          exact
            explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum_append
              f
              (explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX hρ xpair ypairs)
              (explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists hρ rest ypairs)
        _ =
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                if _homit :
                    explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                  explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                    f ((xpair.x₀, xpair.x₁), ypair.y₁)
                else
                  0)
              ypairs +
              explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
                (explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists hρ rest ypairs) := by
          exact congrArg
            (fun z : ℂ =>
              z +
                explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
                  (explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists hρ rest ypairs))
            hhead
        _ =
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                if _homit :
                    explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                  explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                    f ((xpair.x₀, xpair.x₁), ypair.y₁)
                else
                  0)
              ypairs +
              explicitFormulaRectangleListSum
                (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                  explicitFormulaRectangleListSum
                    (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                      if _homit :
                          explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                        explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                          f ((xpair.x₀, xpair.x₁), ypair.y₁)
                      else
                        0)
                    ypairs)
                rest := by
          exact congrArg
            (fun z : ℂ =>
              explicitFormulaRectangleListSum
                (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                  if _homit :
                      explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                    explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                      f ((xpair.x₀, xpair.x₁), ypair.y₁)
                  else
                    0)
                ypairs + z)
            htail
        _ =
            explicitFormulaRectangleListSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                explicitFormulaRectangleListSum
                  (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                    if _homit :
                        explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                      explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                        f ((xpair.x₀, xpair.x₁), ypair.y₁)
                    else
                      0)
                  ypairs)
              (xpair :: rest) := by
          exact Eq.refl _

theorem explicitFormulaRectangleRawHoleSelectedEndpointData_horizontal_side_sum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hρ : 0 < ρ) :
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
          (explicitFormulaRectangleRawHoleSelectedEndpointData F T ρ hρ) -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
          (explicitFormulaRectangleRawHoleSelectedEndpointData F T ρ hρ) =
      explicitFormulaRectangleRawHoleHorizontalEndpointDataSideSum f F T ρ := by
  let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
    explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
  let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
    explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
  let bottomByX : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → ℂ :=
    fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
      explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          if _homit :
              explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
              f ((xpair.x₀, xpair.x₁), ypair.y₀)
          else
            0)
        ypairs
  let topByX : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → ℂ :=
    fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
      explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          if _homit :
              explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
              f ((xpair.x₀, xpair.x₁), ypair.y₁)
          else
            0)
        ypairs
  have hbottom :
      explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
          (explicitFormulaRectangleRawHoleSelectedEndpointData F T ρ hρ) =
        explicitFormulaRectangleListSum bottomByX xpairs :=
    explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists_bottom_sum
      hρ f ypairs xpairs
  have htop :
      explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
          (explicitFormulaRectangleRawHoleSelectedEndpointData F T ρ hρ) =
        explicitFormulaRectangleListSum topByX xpairs :=
    explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists_top_sum
      hρ f ypairs xpairs
  have hsub :
      explicitFormulaRectangleListSum (fun xpair => bottomByX xpair - topByX xpair) xpairs =
        explicitFormulaRectangleListSum bottomByX xpairs -
          explicitFormulaRectangleListSum topByX xpairs :=
    explicitFormulaRectangleListSum_sub bottomByX topByX xpairs
  calc
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
          (explicitFormulaRectangleRawHoleSelectedEndpointData F T ρ hρ) -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
          (explicitFormulaRectangleRawHoleSelectedEndpointData F T ρ hρ) =
        explicitFormulaRectangleListSum bottomByX xpairs -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
            (explicitFormulaRectangleRawHoleSelectedEndpointData F T ρ hρ) := by
      exact congrArg
        (fun z : ℂ =>
          z -
            explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
              (explicitFormulaRectangleRawHoleSelectedEndpointData F T ρ hρ))
        hbottom
    _ =
        explicitFormulaRectangleListSum bottomByX xpairs -
          explicitFormulaRectangleListSum topByX xpairs := by
      exact congrArg
        (fun z : ℂ => explicitFormulaRectangleListSum bottomByX xpairs - z)
        htop
    _ =
        explicitFormulaRectangleListSum (fun xpair => bottomByX xpair - topByX xpair) xpairs := by
      exact hsub.symm
    _ =
        explicitFormulaRectangleRawHoleHorizontalEndpointDataSideSum f F T ρ := by
      exact Eq.refl _

theorem explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX_listSum
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ} (hρ : 0 < ρ)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ)
    (S : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) → ℂ)
    (edge : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ → ℂ)
    (hnil : S [] = 0)
    (hcons :
      ∀ (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ)
        (homit : explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair)
        (tail : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ)),
        S (explicitFormulaRectangleRawHoleSelectedAdjacentEndpointData hρ xpair ypair homit ::
            tail) =
          edge ypair + S tail) :
    ∀ ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ),
      S (explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX hρ xpair ypairs) =
        explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            if _homit :
                explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
              edge ypair
            else
              0)
          ypairs
  | [] => by
      exact hnil
  | ypair :: rest => by
      have htail :
          S (explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX hρ xpair rest) =
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                if _homit :
                    explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                  edge ypair
                else
                  0)
              rest :=
        explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX_listSum
          hρ xpair S edge hnil hcons rest
      match inferInstanceAs
          (Decidable (explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair)) with
      | isTrue homit =>
          have hhead :
              (if _homit :
                  explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                edge ypair
              else
                0) =
              edge ypair :=
            dif_pos homit
          calc
            S (explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX hρ xpair
                (ypair :: rest)) =
                S
                  (explicitFormulaRectangleRawHoleSelectedAdjacentEndpointData
                      hρ xpair ypair homit ::
                    explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX
                      hρ xpair rest) := by
              exact congrArg S (dif_pos homit)
            _ =
                edge ypair +
                  S (explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX
                    hρ xpair rest) := by
              exact
                hcons ypair homit
                  (explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX
                    hρ xpair rest)
            _ =
                edge ypair +
                  explicitFormulaRectangleListSum
                    (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                      if _homit :
                          explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                        edge ypair
                      else
                        0)
                    rest := by
              exact congrArg (fun z : ℂ => edge ypair + z) htail
            _ =
                explicitFormulaRectangleListSum
                  (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                    if _homit :
                        explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                      edge ypair
                    else
                      0)
                  (ypair :: rest) := by
              exact congrArg
                (fun z : ℂ =>
                  z +
                    explicitFormulaRectangleListSum
                      (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                        if _homit :
                            explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                          edge ypair
                        else
                          0)
                      rest)
                hhead.symm
      | isFalse hnot =>
          have hhead :
              (if _homit :
                  explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                edge ypair
              else
                0) =
              0 :=
            dif_neg hnot
          calc
            S (explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX hρ xpair
                (ypair :: rest)) =
                S (explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX
                  hρ xpair rest) := by
              exact congrArg S (dif_neg hnot)
            _ =
                explicitFormulaRectangleListSum
                  (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                    if _homit :
                        explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                      edge ypair
                    else
                      0)
                  rest := by
              exact htail
            _ =
                0 +
                  explicitFormulaRectangleListSum
                    (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                      if _homit :
                          explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                        edge ypair
                      else
                        0)
                    rest := by
              exact (zero_add _).symm
            _ =
                explicitFormulaRectangleListSum
                  (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                    if _homit :
                        explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                      edge ypair
                    else
                      0)
                  (ypair :: rest) := by
              exact congrArg
                (fun z : ℂ =>
                  z +
                    explicitFormulaRectangleListSum
                      (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                        if _homit :
                            explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                          edge ypair
                        else
                          0)
                      rest)
                hhead.symm

theorem explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX_right_sum
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ} (hρ : 0 < ρ)
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :
    ∀ ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ),
      explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
          (explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX hρ xpair ypairs) =
        explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            if _homit :
                explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
              explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
                f ((ypair.y₀, ypair.y₁), xpair.x₁)
            else
              0)
          ypairs :=
  explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX_listSum
    hρ
    xpair
    (fun data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) =>
      explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data)
    (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
      explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
        f ((ypair.y₀, ypair.y₁), xpair.x₁))
    (Eq.refl _)
    (fun ypair homit tail =>
      have hcell :
          explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
              (explicitFormulaRectangleRawHoleSelectedAdjacentEndpointData
                hρ xpair ypair homit) =
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
              f ((ypair.y₀, ypair.y₁), xpair.x₁) :=
        explicitFormulaRectangleRegularGridCellEndpointDataRightEdge_eq_coordinateIntegral
          f
          (explicitFormulaRectangleRawHoleSelectedAdjacentEndpointData
            hρ xpair ypair homit)
      calc
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
            (explicitFormulaRectangleRawHoleSelectedAdjacentEndpointData
                hρ xpair ypair homit :: tail) =
            explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
                (explicitFormulaRectangleRawHoleSelectedAdjacentEndpointData
                  hρ xpair ypair homit) +
              explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f tail := by
          exact Eq.refl _
        _ =
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
                f ((ypair.y₀, ypair.y₁), xpair.x₁) +
              explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f tail := by
          exact congrArg
            (fun z : ℂ =>
              z + explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f tail)
            hcell)

theorem explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX_left_sum
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ} (hρ : 0 < ρ)
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :
    ∀ ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ),
      explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
          (explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX hρ xpair ypairs) =
        explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            if _homit :
                explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
                f ((ypair.y₀, ypair.y₁), xpair.x₀)
            else
              0)
          ypairs :=
  explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX_listSum
    hρ
    xpair
    (fun data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) =>
      explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data)
    (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
      explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
        f ((ypair.y₀, ypair.y₁), xpair.x₀))
    (Eq.refl _)
    (fun ypair homit tail =>
      have hcell :
          explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f
              (explicitFormulaRectangleRawHoleSelectedAdjacentEndpointData
                hρ xpair ypair homit) =
            explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
              f ((ypair.y₀, ypair.y₁), xpair.x₀) :=
        explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge_eq_coordinateIntegral
          f
          (explicitFormulaRectangleRawHoleSelectedAdjacentEndpointData
            hρ xpair ypair homit)
      calc
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
            (explicitFormulaRectangleRawHoleSelectedAdjacentEndpointData
                hρ xpair ypair homit :: tail) =
            explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f
                (explicitFormulaRectangleRawHoleSelectedAdjacentEndpointData
                  hρ xpair ypair homit) +
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f tail := by
          exact Eq.refl _
        _ =
            explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
                f ((ypair.y₀, ypair.y₁), xpair.x₀) +
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f tail := by
          exact congrArg
            (fun z : ℂ =>
              z + explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f tail)
            hcell)

theorem explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists_listSum
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ} (hρ : 0 < ρ)
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ))
    (S : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) → ℂ)
    (rowValue : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → ℂ)
    (hnil : S [] = 0)
    (happend :
      ∀ left right : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ),
        S (left ++ right) = S left + S right)
    (hfixed :
      ∀ xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ,
        S (explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX hρ xpair ypairs) =
          rowValue xpair) :
    ∀ xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ),
      S (explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists hρ xpairs ypairs) =
        explicitFormulaRectangleListSum rowValue xpairs
  | [] => by
      exact hnil
  | xpair :: rest => by
      have hhead :
          S (explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX hρ xpair ypairs) =
            rowValue xpair :=
        hfixed xpair
      have htail :
          S (explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists hρ rest ypairs) =
            explicitFormulaRectangleListSum rowValue rest :=
        explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists_listSum
          hρ ypairs S rowValue hnil happend hfixed rest
      calc
        S (explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists hρ (xpair :: rest)
            ypairs) =
            S (explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX hρ xpair ypairs) +
              S (explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists hρ rest ypairs) := by
          exact
            happend
              (explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX hρ xpair ypairs)
              (explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists hρ rest ypairs)
        _ =
            rowValue xpair +
              S (explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists hρ rest ypairs) := by
          exact congrArg
            (fun z : ℂ =>
              z +
                S (explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists hρ rest ypairs))
            hhead
        _ =
            rowValue xpair +
              explicitFormulaRectangleListSum rowValue rest := by
          exact congrArg (fun z : ℂ => rowValue xpair + z) htail
        _ =
            explicitFormulaRectangleListSum rowValue (xpair :: rest) := by
          exact Eq.refl _

theorem explicitFormulaRectangleListSum_rows_eq_rowMajor
    {α β : Type} (g : α → β → ℂ) (ys : List β) :
    ∀ xs : List α,
      explicitFormulaRectangleListSum
          (fun x : α => explicitFormulaRectangleListSum (fun y : β => g x y) ys)
          xs =
        explicitFormulaRectangleRowMajorDoubleSum g xs ys
  | [] => by
      exact Eq.refl _
  | x :: rest => by
      have htail :
          explicitFormulaRectangleListSum
              (fun x : α => explicitFormulaRectangleListSum (fun y : β => g x y) ys)
              rest =
            explicitFormulaRectangleRowMajorDoubleSum g rest ys :=
        explicitFormulaRectangleListSum_rows_eq_rowMajor g ys rest
      calc
        explicitFormulaRectangleListSum
            (fun x : α => explicitFormulaRectangleListSum (fun y : β => g x y) ys)
            (x :: rest) =
            explicitFormulaRectangleListSum (fun y : β => g x y) ys +
              explicitFormulaRectangleListSum
                (fun x : α => explicitFormulaRectangleListSum (fun y : β => g x y) ys)
                rest := by
          exact Eq.refl _
        _ =
            explicitFormulaRectangleListSum (fun y : β => g x y) ys +
              explicitFormulaRectangleRowMajorDoubleSum g rest ys := by
          exact congrArg
            (fun z : ℂ => explicitFormulaRectangleListSum (fun y : β => g x y) ys + z)
            htail
        _ =
            explicitFormulaRectangleRowMajorDoubleSum g (x :: rest) ys := by
          exact Eq.refl _

theorem explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists_right_sum
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ} (hρ : 0 < ρ)
    (f : ZetaAdmissibleFunction)
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ)) :
    ∀ xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ),
      explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
          (explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists hρ xpairs ypairs) =
        explicitFormulaRectangleRowMajorDoubleSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
              if _homit :
                  explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
                  f ((ypair.y₀, ypair.y₁), xpair.x₁)
              else
                0)
          xpairs ypairs :=
  fun xpairs => by
    let g :
        ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ →
          ExplicitFormulaRectangleYAdjacentEndpointPair T ρ → ℂ :=
      fun xpair ypair =>
        if _homit :
            explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
          explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
            f ((ypair.y₀, ypair.y₁), xpair.x₁)
        else
          0
    have hlist :
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
            (explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists hρ xpairs ypairs) =
          explicitFormulaRectangleListSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              explicitFormulaRectangleListSum
                (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ => g xpair ypair)
                ypairs)
            xpairs :=
      explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists_listSum
        hρ ypairs
        (fun data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) =>
          explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data)
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          explicitFormulaRectangleListSum
            (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ => g xpair ypair)
            ypairs)
        (Eq.refl _)
        (fun left right =>
          explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum_append f left right)
        (fun xpair =>
          explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX_right_sum hρ f xpair ypairs)
        xpairs
    calc
      explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
          (explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists hρ xpairs ypairs) =
          explicitFormulaRectangleListSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              explicitFormulaRectangleListSum
                (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ => g xpair ypair)
                ypairs)
            xpairs := by
        exact hlist
      _ =
          explicitFormulaRectangleRowMajorDoubleSum g xpairs ypairs := by
        exact explicitFormulaRectangleListSum_rows_eq_rowMajor g ypairs xpairs

theorem explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists_left_sum
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ} (hρ : 0 < ρ)
    (f : ZetaAdmissibleFunction)
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ)) :
    ∀ xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ),
      explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
          (explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists hρ xpairs ypairs) =
        explicitFormulaRectangleRowMajorDoubleSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
              if _homit :
                  explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
                  f ((ypair.y₀, ypair.y₁), xpair.x₀)
              else
                0)
          xpairs ypairs :=
  fun xpairs => by
    let g :
        ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ →
          ExplicitFormulaRectangleYAdjacentEndpointPair T ρ → ℂ :=
      fun xpair ypair =>
        if _homit :
            explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
          explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
            f ((ypair.y₀, ypair.y₁), xpair.x₀)
        else
          0
    have hlist :
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
            (explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists hρ xpairs ypairs) =
          explicitFormulaRectangleListSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              explicitFormulaRectangleListSum
                (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ => g xpair ypair)
                ypairs)
            xpairs :=
      explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists_listSum
        hρ ypairs
        (fun data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) =>
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data)
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          explicitFormulaRectangleListSum
            (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ => g xpair ypair)
            ypairs)
        (Eq.refl _)
        (fun left right =>
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum_append f left right)
        (fun xpair =>
          explicitFormulaRectangleRawHoleSelectedEndpointDataOfFixedX_left_sum hρ f xpair ypairs)
        xpairs
    calc
      explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
          (explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists hρ xpairs ypairs) =
          explicitFormulaRectangleListSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              explicitFormulaRectangleListSum
                (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ => g xpair ypair)
                ypairs)
            xpairs := by
        exact hlist
      _ =
          explicitFormulaRectangleRowMajorDoubleSum g xpairs ypairs := by
        exact explicitFormulaRectangleListSum_rows_eq_rowMajor g ypairs xpairs

theorem explicitFormulaRectangleRawHoleVerticalColumnMajorSub_eq_sideSum_pairLists
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ}
    (right left :
      ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ →
        ExplicitFormulaRectangleYAdjacentEndpointPair T ρ → ℂ)
    (xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ)) :
    ∀ ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ),
    explicitFormulaRectangleColumnMajorDoubleSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            right xpair ypair - left xpair ypair)
        xpairs ypairs =
      explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          explicitFormulaRectangleListSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                right xpair ypair)
              xpairs -
            explicitFormulaRectangleListSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                left xpair ypair)
              xpairs)
        ypairs
  | [] => by
      exact Eq.refl _
  | ypair :: rest => by
      have hcolumn :
          explicitFormulaRectangleListSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                right xpair ypair - left xpair ypair)
              xpairs =
            explicitFormulaRectangleListSum
                (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                  right xpair ypair)
                xpairs -
              explicitFormulaRectangleListSum
                (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                  left xpair ypair)
                xpairs :=
        explicitFormulaRectangleListSum_sub
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ => right xpair ypair)
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ => left xpair ypair)
          xpairs
      have htail :
          explicitFormulaRectangleColumnMajorDoubleSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                  right xpair ypair - left xpair ypair)
              xpairs rest =
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                explicitFormulaRectangleListSum
                    (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                      right xpair ypair)
                    xpairs -
                  explicitFormulaRectangleListSum
                    (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                      left xpair ypair)
                    xpairs)
              rest :=
        explicitFormulaRectangleRawHoleVerticalColumnMajorSub_eq_sideSum_pairLists
          right left xpairs rest
      calc
        explicitFormulaRectangleColumnMajorDoubleSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                right xpair ypair - left xpair ypair)
            xpairs (ypair :: rest) =
            explicitFormulaRectangleListSum
                (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                  right xpair ypair - left xpair ypair)
                xpairs +
              explicitFormulaRectangleColumnMajorDoubleSum
                (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                  fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                    right xpair ypair - left xpair ypair)
                xpairs rest := by
          exact Eq.refl _
        _ =
            (explicitFormulaRectangleListSum
                (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                  right xpair ypair)
                xpairs -
              explicitFormulaRectangleListSum
                (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                  left xpair ypair)
                xpairs) +
              explicitFormulaRectangleColumnMajorDoubleSum
                (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                  fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                    right xpair ypair - left xpair ypair)
                xpairs rest := by
          exact congrArg
            (fun z : ℂ =>
              z +
                explicitFormulaRectangleColumnMajorDoubleSum
                  (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                    fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                      right xpair ypair - left xpair ypair)
                  xpairs rest)
            hcolumn
        _ =
            (explicitFormulaRectangleListSum
                (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                  right xpair ypair)
                xpairs -
              explicitFormulaRectangleListSum
                (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                  left xpair ypair)
                xpairs) +
              explicitFormulaRectangleListSum
                (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                  explicitFormulaRectangleListSum
                      (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                        right xpair ypair)
                      xpairs -
                    explicitFormulaRectangleListSum
                      (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                        left xpair ypair)
                      xpairs)
                rest := by
          exact congrArg
            (fun z : ℂ =>
              (explicitFormulaRectangleListSum
                  (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                    right xpair ypair)
                  xpairs -
                explicitFormulaRectangleListSum
                  (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                    left xpair ypair)
                  xpairs) + z)
            htail
        _ =
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                explicitFormulaRectangleListSum
                    (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                      right xpair ypair)
                    xpairs -
                  explicitFormulaRectangleListSum
                    (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                      left xpair ypair)
                    xpairs)
              (ypair :: rest) := by
          exact Eq.refl _

theorem explicitFormulaRectangleRawHoleVerticalColumnMajorSub_eq_sideSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (T ρ : ℝ) :
    let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
      explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
    let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
      explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
    explicitFormulaRectangleColumnMajorDoubleSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            (if _homit :
                explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
              explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
                f ((ypair.y₀, ypair.y₁), xpair.x₁)
            else
              0) -
            (if _homit :
                explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
                f ((ypair.y₀, ypair.y₁), xpair.x₀)
            else
              0))
        xpairs ypairs =
      explicitFormulaRectangleRawHoleVerticalEndpointDataSideSum f F T ρ := by
  let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
    explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
  let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
    explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
  let right :
      ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ →
        ExplicitFormulaRectangleYAdjacentEndpointPair T ρ → ℂ :=
    fun xpair ypair =>
      if _homit :
          explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
        explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
          f ((ypair.y₀, ypair.y₁), xpair.x₁)
      else
        0
  let left :
      ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ →
        ExplicitFormulaRectangleYAdjacentEndpointPair T ρ → ℂ :=
    fun xpair ypair =>
      if _homit :
          explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
        explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
          f ((ypair.y₀, ypair.y₁), xpair.x₀)
      else
        0
  exact
    explicitFormulaRectangleRawHoleVerticalColumnMajorSub_eq_sideSum_pairLists
      right left xpairs ypairs

theorem explicitFormulaRectangleRawHoleSelectedEndpointData_vertical_side_sum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hρ : 0 < ρ) :
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
          (explicitFormulaRectangleRawHoleSelectedEndpointData F T ρ hρ) -
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
          (explicitFormulaRectangleRawHoleSelectedEndpointData F T ρ hρ) =
      explicitFormulaRectangleRawHoleVerticalEndpointDataSideSum f F T ρ := by
  let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
    explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
  let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
    explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
  let right :
      ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ →
        ExplicitFormulaRectangleYAdjacentEndpointPair T ρ → ℂ :=
    fun xpair ypair =>
      if _homit :
          explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
        explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
          f ((ypair.y₀, ypair.y₁), xpair.x₁)
      else
        0
  let left :
      ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ →
        ExplicitFormulaRectangleYAdjacentEndpointPair T ρ → ℂ :=
    fun xpair ypair =>
      if _homit :
          explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
        explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
          f ((ypair.y₀, ypair.y₁), xpair.x₀)
      else
        0
  have hright :
      explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
          (explicitFormulaRectangleRawHoleSelectedEndpointData F T ρ hρ) =
        explicitFormulaRectangleRowMajorDoubleSum right xpairs ypairs :=
    explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists_right_sum
      hρ f ypairs xpairs
  have hleft :
      explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
          (explicitFormulaRectangleRawHoleSelectedEndpointData F T ρ hρ) =
        explicitFormulaRectangleRowMajorDoubleSum left xpairs ypairs :=
    explicitFormulaRectangleRawHoleSelectedEndpointDataOfPairLists_left_sum
      hρ f ypairs xpairs
  have hrowSub :
      explicitFormulaRectangleRowMajorDoubleSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
              right xpair ypair - left xpair ypair)
          xpairs ypairs =
        explicitFormulaRectangleRowMajorDoubleSum right xpairs ypairs -
          explicitFormulaRectangleRowMajorDoubleSum left xpairs ypairs := by
    induction xpairs with
    | nil =>
        exact (sub_self 0).symm
    | cons xpair rest ih =>
        have hrow :
            explicitFormulaRectangleListSum
                (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                  right xpair ypair - left xpair ypair)
                ypairs =
              explicitFormulaRectangleListSum (fun ypair => right xpair ypair) ypairs -
                explicitFormulaRectangleListSum (fun ypair => left xpair ypair) ypairs :=
          explicitFormulaRectangleListSum_sub
            (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ => right xpair ypair)
            (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ => left xpair ypair)
            ypairs
        calc
          explicitFormulaRectangleRowMajorDoubleSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                  right xpair ypair - left xpair ypair)
              (xpair :: rest) ypairs =
              explicitFormulaRectangleListSum
                  (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                    right xpair ypair - left xpair ypair)
                  ypairs +
                explicitFormulaRectangleRowMajorDoubleSum
                  (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                    fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                      right xpair ypair - left xpair ypair)
                  rest ypairs := by
            exact Eq.refl _
          _ =
              (explicitFormulaRectangleListSum (fun ypair => right xpair ypair) ypairs -
                explicitFormulaRectangleListSum (fun ypair => left xpair ypair) ypairs) +
                explicitFormulaRectangleRowMajorDoubleSum
                  (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                    fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                      right xpair ypair - left xpair ypair)
                  rest ypairs := by
            exact congrArg
              (fun z : ℂ =>
                z +
                  explicitFormulaRectangleRowMajorDoubleSum
                    (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                      fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                        right xpair ypair - left xpair ypair)
                    rest ypairs)
              hrow
          _ =
              (explicitFormulaRectangleListSum (fun ypair => right xpair ypair) ypairs -
                explicitFormulaRectangleListSum (fun ypair => left xpair ypair) ypairs) +
                (explicitFormulaRectangleRowMajorDoubleSum right rest ypairs -
                  explicitFormulaRectangleRowMajorDoubleSum left rest ypairs) := by
            exact congrArg
              (fun z : ℂ =>
                (explicitFormulaRectangleListSum (fun ypair => right xpair ypair) ypairs -
                  explicitFormulaRectangleListSum (fun ypair => left xpair ypair) ypairs) + z)
              ih
          _ =
              explicitFormulaRectangleRowMajorDoubleSum right (xpair :: rest) ypairs -
                explicitFormulaRectangleRowMajorDoubleSum left (xpair :: rest) ypairs := by
            exact
              (explicitFormulaRectangleBoxHorizontalContribution_consAlgebra
                (explicitFormulaRectangleListSum (fun ypair => right xpair ypair) ypairs)
                (explicitFormulaRectangleListSum (fun ypair => left xpair ypair) ypairs)
                (explicitFormulaRectangleRowMajorDoubleSum right rest ypairs)
                (explicitFormulaRectangleRowMajorDoubleSum left rest ypairs)).symm
  have hfubini :
      explicitFormulaRectangleRowMajorDoubleSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
              right xpair ypair - left xpair ypair)
          xpairs ypairs =
        explicitFormulaRectangleColumnMajorDoubleSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
              right xpair ypair - left xpair ypair)
          xpairs ypairs :=
    explicitFormulaRectangleRowMajorDoubleSum_eq_columnMajorDoubleSum
      (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
        fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          right xpair ypair - left xpair ypair)
      (xpairs, ypairs)
  have hcolumn :
      explicitFormulaRectangleColumnMajorDoubleSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
              right xpair ypair - left xpair ypair)
          xpairs ypairs =
        explicitFormulaRectangleRawHoleVerticalEndpointDataSideSum f F T ρ :=
    explicitFormulaRectangleRawHoleVerticalColumnMajorSub_eq_sideSum f F T ρ
  calc
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
          (explicitFormulaRectangleRawHoleSelectedEndpointData F T ρ hρ) -
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
          (explicitFormulaRectangleRawHoleSelectedEndpointData F T ρ hρ) =
        explicitFormulaRectangleRowMajorDoubleSum right xpairs ypairs -
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
            (explicitFormulaRectangleRawHoleSelectedEndpointData F T ρ hρ) := by
      exact congrArg
        (fun z : ℂ =>
          z -
            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
              (explicitFormulaRectangleRawHoleSelectedEndpointData F T ρ hρ))
        hright
    _ =
        explicitFormulaRectangleRowMajorDoubleSum right xpairs ypairs -
          explicitFormulaRectangleRowMajorDoubleSum left xpairs ypairs := by
      exact congrArg
        (fun z : ℂ => explicitFormulaRectangleRowMajorDoubleSum right xpairs ypairs - z)
        hleft
    _ =
        explicitFormulaRectangleRowMajorDoubleSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
              right xpair ypair - left xpair ypair)
          xpairs ypairs := by
      exact hrowSub.symm
    _ =
        explicitFormulaRectangleColumnMajorDoubleSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
              right xpair ypair - left xpair ypair)
          xpairs ypairs := by
      exact hfubini
    _ =
        explicitFormulaRectangleRawHoleVerticalEndpointDataSideSum f F T ρ := by
      exact hcolumn

theorem explicitFormulaRectangleRawHoleSelectedEndpointData_horizontalContribution_sortedRadius_core
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hbottom :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ (-T))
    (htop :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ T)
    (hbottomHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
    (htopHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ρ + ρ < dist a b) :
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
          (explicitFormulaRectangleRawHoleSelectedEndpointData F T ρ hρ) -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
          (explicitFormulaRectangleRawHoleSelectedEndpointData F T ρ hρ) =
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
            f T ρ) := by
  calc
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
          (explicitFormulaRectangleRawHoleSelectedEndpointData F T ρ hρ) -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
          (explicitFormulaRectangleRawHoleSelectedEndpointData F T ρ hρ) =
        explicitFormulaRectangleRawHoleHorizontalEndpointDataSideSum f F T ρ := by
      exact explicitFormulaRectangleRawHoleSelectedEndpointData_horizontal_side_sum f F hρ
    _ =
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
            f T ρ) := by
      exact
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalSortedPairListsContribution_core
          f F hT_nonneg hρ hclosed hbottom htop hbottomHole htopHole hsep

theorem explicitFormulaRectangleRawHoleSelectedEndpointData_verticalContribution_sortedRadius_core
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hright :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ F.c)
    (hleft :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ (1 - F.c))
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
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
          (explicitFormulaRectangleRawHoleSelectedEndpointData F T ρ hρ) -
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
          (explicitFormulaRectangleRawHoleSelectedEndpointData F T ρ hρ) =
      (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
            f T ρ) := by
  calc
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
          (explicitFormulaRectangleRawHoleSelectedEndpointData F T ρ hρ) -
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
          (explicitFormulaRectangleRawHoleSelectedEndpointData F T ρ hρ) =
        explicitFormulaRectangleRawHoleVerticalEndpointDataSideSum f F T ρ := by
      exact explicitFormulaRectangleRawHoleSelectedEndpointData_vertical_side_sum f F hρ
    _ =
      (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
            f T ρ) := by
      exact
        explicitFormulaRectangleSelectedBoxCoordinatesVerticalSortedPairListsContribution_core
          f F hT_nonneg hρ hclosed hright hleft hrightHole hleftHole hsep

theorem explicitFormulaRectangleRawHoleSelectedEndpointData_horizontalContribution_core
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
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ε + ε < dist a b) :
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
          (explicitFormulaRectangleRawHoleSelectedEndpointData F T (ε / 2)
            (finiteRectangle_halfRadius_pos hε)) -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
          (explicitFormulaRectangleRawHoleSelectedEndpointData F T (ε / 2)
            (finiteRectangle_halfRadius_pos hε)) =
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
          f T (ε / 2)) -
        (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
            f T (ε / 2)) := by
  exact
    explicitFormulaRectangleRawHoleSelectedEndpointData_horizontalContribution_sortedRadius_core
      f F
      hT_nonneg
      (finiteRectangle_halfRadius_pos hε)
      (explicitFormulaRectangle_closedRadiusControls_halfRadius F T ε hε hclosed)
      hbottom
      htop
      hbottomHole
      htopHole
      (fun a ha b hb hab =>
        calc
          ε / 2 + ε / 2 = ε := by
            exact add_halves ε
          _ < ε + ε := by
            exact lt_add_of_pos_right ε hε
          _ < dist a b := by
            exact hsep a ha b hb hab)

theorem explicitFormulaRectangleRawHoleSelectedEndpointData_verticalContribution_core
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ε : ℝ} (hT_nonneg : 0 ≤ T) (hε : 0 < ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
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
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
          (explicitFormulaRectangleRawHoleSelectedEndpointData F T (ε / 2)
            (finiteRectangle_halfRadius_pos hε)) -
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
          (explicitFormulaRectangleRawHoleSelectedEndpointData F T (ε / 2)
            (finiteRectangle_halfRadius_pos hε)) =
      (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
          f T (ε / 2)) -
        (zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
            f T (ε / 2)) := by
  exact
    explicitFormulaRectangleRawHoleSelectedEndpointData_verticalContribution_sortedRadius_core
      f F
      hT_nonneg
      (finiteRectangle_halfRadius_pos hε)
      (explicitFormulaRectangle_closedRadiusControls_halfRadius F T ε hε hclosed)
      hright
      hleft
      hrightHole
      hleftHole
      (fun a ha b hb hab =>
        calc
          ε / 2 + ε / 2 = ε := by
            exact add_halves ε
          _ < ε + ε := by
            exact lt_add_of_pos_right ε hε
          _ < dist a b := by
            exact hsep a ha b hb hab)

/-
The coordinate-selected endpoint-data exposed-boundary wrappers that used to
occupy the tail of this file are intentionally disabled.  Their assertions are
too strong after `explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission`
was restored to center-coordinate omission: the exposed raw-hole side sums are
owned by the raw-hole-selected endpoint-data theorems above.

theorem explicitFormulaRectangleSelectedEndpointDataHorizontalSortedPairListsContribution_core
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hbottom :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ (-T))
    (htop :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ T)
    (hbottomHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
    (htopHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ρ + ρ < dist a b) :
    let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
      explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
    let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
      explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
    let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          xpairs ypairs)
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data =
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
            f T ρ) := by
  let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
    explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
  let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
    explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
  let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
        xpairs ypairs)
  have hrow :
      explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data =
        explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum
          f xpairs ypairs :=
    explicitFormulaRectangleSelectedEndpointDataHorizontalContribution_pairLists_eq_rowSum
      f xpairs ypairs
  have hraw :
      explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum
          f xpairs ypairs =
        explicitFormulaRectangleRawHoleHorizontalEndpointDataSideSum f F T ρ := by
    exact
      Eq.trans
        (explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum_eq_listSum
          f ypairs xpairs)
        (Eq.refl _)
  calc
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data =
        explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum
          f xpairs ypairs := by
      exact hrow
    _ =
        explicitFormulaRectangleRawHoleHorizontalEndpointDataSideSum f F T ρ := by
      exact hraw
    _ =
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
            f T ρ) := by
      exact
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalSortedPairListsContribution_core
          f F hT_nonneg hρ hclosed hbottom htop hbottomHole htopHole hsep

/-- Endpoint-data vertical side-collapse for the sorted selected grid after the
recursive column contribution has been erased. -/
theorem explicitFormulaRectangleSelectedEndpointDataVerticalSortedPairListsContribution_core
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hright :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ F.c)
    (hleft :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ (1 - F.c))
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
    let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
      explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
    let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
      explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
    let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          xpairs ypairs)
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data =
      (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
            f T ρ) := by
  let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
    explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
  let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
    explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
  let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
        xpairs ypairs)
  have hrow :
      explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data =
        explicitFormulaRectangleSelectedEndpointDataVerticalRowContributionSum
          f xpairs ypairs :=
    explicitFormulaRectangleSelectedEndpointDataVerticalContribution_pairLists_eq_rowSum
      f xpairs ypairs
  have hraw :
      explicitFormulaRectangleSelectedEndpointDataVerticalRowContributionSum
          f xpairs ypairs =
        explicitFormulaRectangleRawHoleVerticalEndpointDataSideSum f F T ρ := by
    exact Eq.refl _
  calc
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data =
        explicitFormulaRectangleSelectedEndpointDataVerticalRowContributionSum
          f xpairs ypairs := by
      exact hrow
    _ =
        explicitFormulaRectangleRawHoleVerticalEndpointDataSideSum f F T ρ := by
      exact hraw
    _ =
      (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
            f T ρ) := by
      exact
        explicitFormulaRectangleSelectedBoxCoordinatesVerticalSortedPairListsContribution_core
          f F hT_nonneg hρ hclosed hright hleft hrightHole hleftHole hsep

/-- Vertical exposed-boundary accounting for the column-contribution sum over the sorted
horizontal and vertical adjacent-pair lists.  This is the correctly oriented column
telescoping statement: internal vertical sides cancel across adjacent horizontal
intervals, leaving only the outer right/left sides and raw square-hole right/left sides. -/
theorem explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum_sortedPairLists_core
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hright :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ F.c)
    (hleft :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ (1 - F.c))
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
    explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum
        f
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
            f T ρ) := by
  let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
    explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
  let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
    explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
  let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
        xpairs ypairs)
  calc
    explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum
        f xpairs ypairs =
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data := by
      exact
        explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum_eq_sortedPairListsContribution
          f F T ρ
    _ =
      (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
            f T ρ) := by
      exact
        explicitFormulaRectangleSelectedEndpointDataVerticalSortedPairListsContribution_core
          f F hT_nonneg hρ hclosed hright hleft hrightHole hleftHole hsep

/-- Row-contribution-sum horizontal exposed-boundary accounting over the sorted
horizontal and vertical adjacent-pair lists.  This is the remaining purely finite
row-telescoping statement after the selected endpoint-data list has been reduced to a
recursive sum of fixed-row contributions. -/
theorem explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum_sortedPairLists_core
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hbottom :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ (-T))
    (htop :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ T)
    (hbottomHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
    (htopHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ρ + ρ < dist a b) :
    explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum
        f
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
            f T ρ) := by
  let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
    explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
  let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
    explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
  let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
        xpairs ypairs)
  calc
    explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum
        f xpairs ypairs =
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data := by
      exact
        explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum_eq_sortedPairListsContribution
          f F T ρ
    _ =
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
            f T ρ) := by
      exact
        explicitFormulaRectangleSelectedEndpointDataHorizontalSortedPairListsContribution_core
          f F hT_nonneg hρ hclosed hbottom htop hbottomHole htopHole hsep

/-- Row-contribution-sum vertical exposed-boundary accounting over the sorted horizontal
and vertical adjacent-pair lists.  This is the remaining purely finite row/column
telescoping statement after the selected endpoint-data list has been reduced to a
recursive sum of fixed-row contributions. -/
theorem explicitFormulaRectangleSelectedEndpointDataVerticalRowContributionSum_sortedPairLists_core
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hright :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ F.c)
    (hleft :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ (1 - F.c))
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
    explicitFormulaRectangleSelectedEndpointDataVerticalRowContributionSum
        f
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
            f T ρ) := by
  calc
    explicitFormulaRectangleSelectedEndpointDataVerticalRowContributionSum
        f
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
        explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum
          f
          (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) := by
      exact
        explicitFormulaRectangleSelectedEndpointDataVerticalRowContributionSum_eq_columnContributionSum
          f
          (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ)
    _ =
      (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
            f T ρ) := by
      exact
        explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum_sortedPairLists_core
          f F hT_nonneg hρ hclosed hright hleft hrightHole hleftHole hsep

/-- Global horizontal exposed-edge accounting over the sorted horizontal adjacent-pair
list, reduced to row-contribution accounting. -/
theorem explicitFormulaRectangleSelectedEndpointData_horizontalContribution_sortedPairLists_of_rowSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hbottom :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ (-T))
    (htop :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ T)
    (hbottomHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
    (htopHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ρ + ρ < dist a b) :
    let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ))
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data =
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
            f T ρ) := by
  let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
    explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
  let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
    explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
  let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
        xpairs ypairs)
  calc
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data =
        explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum
          f xpairs ypairs := by
      exact
        explicitFormulaRectangleSelectedEndpointDataHorizontalContribution_pairLists_eq_rowSum
          f xpairs ypairs
    _ =
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
            f T ρ) := by
      exact
        explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum_sortedPairLists_core
          f F hT_nonneg hρ hclosed hbottom htop hbottomHole htopHole hsep

/-- Global vertical exposed-edge accounting over the sorted horizontal adjacent-pair list,
reduced to row-contribution accounting. -/
theorem explicitFormulaRectangleSelectedEndpointData_verticalContribution_sortedPairLists_of_rowSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hright :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ F.c)
    (hleft :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ (1 - F.c))
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
    let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ))
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data =
      (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
            f T ρ) := by
  let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
    explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
  let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
    explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
  let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
        xpairs ypairs)
  calc
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data =
        explicitFormulaRectangleSelectedEndpointDataVerticalRowContributionSum
          f xpairs ypairs := by
      exact
        explicitFormulaRectangleSelectedEndpointDataVerticalContribution_pairLists_eq_rowSum
          f xpairs ypairs
    _ =
      (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
            f T ρ) := by
      exact
        explicitFormulaRectangleSelectedEndpointDataVerticalRowContributionSum_sortedPairLists_core
          f F hT_nonneg hρ hclosed hright hleft hrightHole hleftHole hsep

/-- Horizontal contribution collapse for the explicit sorted crossed adjacent-pair list.
This is the concrete row-telescoping theorem: after expanding the selected cells in
sorted `x` rows and sorted `y` intervals, internal horizontal sides cancel and the
remaining horizontal sides are the outer bottom/top sides minus the square-hole
bottom/top sides. -/
theorem explicitFormulaRectangleSelectedEndpointData_horizontalContribution_sortedPairLists_core
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hbottom :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ (-T))
    (htop :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ T)
    (hbottomHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
    (htopHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ρ + ρ < dist a b) :
    let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ))
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data =
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
            f T ρ) := by
  exact
    explicitFormulaRectangleSelectedEndpointData_horizontalContribution_sortedPairLists_of_rowSum
      f F hT_nonneg hρ hclosed hbottom htop hbottomHole htopHole hsep

/-- Vertical contribution collapse for the explicit sorted crossed adjacent-pair list.
This is the concrete column-telescoping theorem: after expanding the selected cells in
sorted `x` rows and sorted `y` intervals, internal vertical sides cancel and the
remaining vertical sides are the outer right/left sides minus the square-hole right/left
sides. -/
theorem explicitFormulaRectangleSelectedEndpointData_verticalContribution_sortedPairLists_core
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hright :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ F.c)
    (hleft :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ (1 - F.c))
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
    let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ))
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data =
      (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
            f T ρ) := by
  exact
    explicitFormulaRectangleSelectedEndpointData_verticalContribution_sortedPairLists_of_rowSum
      f F hT_nonneg hρ hclosed hright hleft hrightHole hleftHole hsep

/-- Horizontal contribution collapse for the canonical selected endpoint data at a fixed
subdivision radius.  This is the row-telescoping finite classification: the selected
regular complement cells expose exactly the bottom/top sides of the outer rectangle and
the bottom/top sides of the raw square holes. -/
theorem explicitFormulaRectangleSelectedEndpointData_horizontalContribution_sortedRadius_core
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hbottom :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ (-T))
    (htop :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ T)
    (hbottomHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
    (htopHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ρ + ρ < dist a b) :
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
          (explicitFormulaRectangleSelectedEndpointData F T ρ) -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
          (explicitFormulaRectangleSelectedEndpointData F T ρ) =
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
            f T ρ) := by
  let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
    explicitFormulaRectangleSelectedEndpointData F T ρ
  let sortedData : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ))
  have hdata : data = sortedData :=
    explicitFormulaRectangleSelectedEndpointData_eq_sortedPairLists F T ρ
  calc
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data =
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f sortedData -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data := by
      exact congrArg
        (fun z : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) =>
          explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f z -
            explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data)
        hdata
    _ =
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f sortedData -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f sortedData := by
      exact congrArg
        (fun z : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) =>
          explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f sortedData -
            explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f z)
        hdata
    _ =
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
            f T ρ) := by
      exact
        explicitFormulaRectangleSelectedEndpointData_horizontalContribution_sortedPairLists_core
          f F hT_nonneg hρ hclosed hbottom htop hbottomHole htopHole hsep

/-- Vertical contribution collapse for the canonical selected endpoint data at a fixed
subdivision radius.  This is the column-telescoping finite classification: the selected
regular complement cells expose exactly the right/left sides of the outer rectangle and
the right/left sides of the raw square holes. -/
theorem explicitFormulaRectangleSelectedEndpointData_verticalContribution_sortedRadius_core
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hright :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ F.c)
    (hleft :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ (1 - F.c))
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
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
          (explicitFormulaRectangleSelectedEndpointData F T ρ) -
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
          (explicitFormulaRectangleSelectedEndpointData F T ρ) =
      (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
            f T ρ) := by
  let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
    explicitFormulaRectangleSelectedEndpointData F T ρ
  let sortedData : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ))
  have hdata : data = sortedData :=
    explicitFormulaRectangleSelectedEndpointData_eq_sortedPairLists F T ρ
  calc
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data =
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f sortedData -
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data := by
      exact congrArg
        (fun z : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) =>
          explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f z -
            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data)
        hdata
    _ =
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f sortedData -
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f sortedData := by
      exact congrArg
        (fun z : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) =>
          explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f sortedData -
            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f z)
        hdata
    _ =
      (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
            f T ρ) := by
      exact
        explicitFormulaRectangleSelectedEndpointData_verticalContribution_sortedPairLists_core
          f F hT_nonneg hρ hclosed hright hleft hrightHole hleftHole hsep

/-- Endpoint-data horizontal contribution collapse for the sorted selected grid. -/
theorem explicitFormulaRectangleSelectedEndpointData_horizontalContribution_core
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
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ε + ε < dist a b) :
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
          (explicitFormulaRectangleSelectedEndpointData F T (ε / 2)) -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
          (explicitFormulaRectangleSelectedEndpointData F T (ε / 2)) =
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
          f T (ε / 2)) -
        (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
            f T (ε / 2)) := by
  exact
    explicitFormulaRectangleSelectedEndpointData_horizontalContribution_sortedRadius_core
      f F
      hT_nonneg
      (finiteRectangle_halfRadius_pos hε)
      (explicitFormulaRectangle_closedRadiusControls_halfRadius F T ε hε hclosed)
      hbottom
      htop
      hbottomHole
      htopHole
      (fun a ha b hb hab =>
        calc
          ε / 2 + ε / 2 = ε := by
            exact add_halves ε
          _ < ε + ε := by
            exact lt_add_of_pos_right ε hε
          _ < dist a b := by
            exact hsep a ha b hb hab)

/-- Endpoint-data vertical contribution collapse for the sorted selected grid. -/
theorem explicitFormulaRectangleSelectedEndpointData_verticalContribution_core
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ε : ℝ} (hT_nonneg : 0 ≤ T) (hε : 0 < ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
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
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
          (explicitFormulaRectangleSelectedEndpointData F T (ε / 2)) -
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
          (explicitFormulaRectangleSelectedEndpointData F T (ε / 2)) =
      (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
          f T (ε / 2)) -
        (zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
            f T (ε / 2)) := by
  exact
    explicitFormulaRectangleSelectedEndpointData_verticalContribution_sortedRadius_core
      f F
      hT_nonneg
      (finiteRectangle_halfRadius_pos hε)
      (explicitFormulaRectangle_closedRadiusControls_halfRadius F T ε hε hclosed)
      hright
      hleft
      hrightHole
      hleftHole
      (fun a ha b hb hab =>
        calc
          ε / 2 + ε / 2 = ε := by
            exact add_halves ε
          _ < ε + ε := by
            exact lt_add_of_pos_right ε hε
          _ < dist a b := by
            exact hsep a ha b hb hab)

/-- Horizontal contribution collapse for selected sorted box labels.  This is the
finite exposed-edge classification statement in the horizontal direction: internal
horizontal edges cancel only in the grouped `bottom - top` contribution. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinates_horizontalContribution_core
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
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ε + ε < dist a b) :
    let boxes : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
      explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T (ε / 2))
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T (ε / 2))
    explicitFormulaRectangleBoxBottomEdgeIntegralSum f boxes -
        explicitFormulaRectangleBoxTopEdgeIntegralSum f boxes =
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
          f T (ε / 2)) -
        (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
            f T (ε / 2)) := by
  let boxes : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
    explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
      (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T (ε / 2))
      (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T (ε / 2))
  calc
    explicitFormulaRectangleBoxBottomEdgeIntegralSum f boxes -
        explicitFormulaRectangleBoxTopEdgeIntegralSum f boxes =
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
            (explicitFormulaRectangleSelectedEndpointData F T (ε / 2)) -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
            (explicitFormulaRectangleSelectedEndpointData F T (ε / 2)) := by
      exact
        explicitFormulaRectangleSelectedBoxEdgeCoordinates_horizontalContribution_eq_selectedEndpointData
          f F T (ε / 2)
    _ =
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
          f T (ε / 2)) -
        (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
            f T (ε / 2)) := by
      exact
        explicitFormulaRectangleSelectedEndpointData_horizontalContribution_core
          f F hT_nonneg hε hclosed hbottom htop hbottomHole htopHole hsep
-/
end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
