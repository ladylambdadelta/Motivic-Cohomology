import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.ClosedHeightSpanAvoidance

/-!
# Sorted vertical span control
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Every defined sorted vertical endpoint remains in the closed outer height span. -/
theorem explicitFormulaRectangleSortedYEndpointAt_mem_vertical_Icc_of_closedRadiusControls
    (F : ExplicitFormulaContourFamily) (T radius : ℝ)
    (hT : 0 ≤ T) (hradius : 0 ≤ radius)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a radius ⊆ explicitFormulaContourFamilyInterior F T)
    (k : ℕ) (hk : k < (explicitFormulaRectangleSortedYEndpoints T radius).length) :
    explicitFormulaRectangleSortedYEndpointAt T radius k ∈ Set.Icc (-T) T := by
  let ys : List ℝ := explicitFormulaRectangleSortedYEndpoints T radius
  let index : Fin ys.length := ⟨k, hk⟩
  have hgetMem : ys.get index ∈ ys :=
    List.get_mem ys index.val index.isLt
  have hcarrier :
      ys.get index ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T radius :=
    (explicitFormulaRectangleSortedYEndpoints_mem_iff T radius (ys.get index)).mp hgetMem
  have hspan : ys.get index ∈ Set.Icc (-T) T :=
    explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints_mem_vertical_Icc_of_closedRadiusControls
      F T radius hT hradius hclosed hcarrier
  have hendpoint : explicitFormulaRectangleSortedYEndpointAt T radius k = ys.get index :=
    explicitFormulaRectangleSortedYEndpointAt_of_lt T radius hk
  exact
    Eq.subst
      (motive := fun value : ℝ => value ∈ Set.Icc (-T) T)
      hendpoint.symm hspan

/-- Every adjacent sorted vertical interval is contained in the closed outer height span. -/
theorem explicitFormulaRectangleSortedYAdjacent_uIcc_subset_vertical_Icc
    (F : ExplicitFormulaContourFamily) (T radius : ℝ)
    (hT : 0 ≤ T) (hradius : 0 ≤ radius)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a radius ⊆ explicitFormulaContourFamilyInterior F T)
    (k : ℕ)
    (hk : k < (explicitFormulaRectangleSortedYEndpoints T radius).length - 1) :
    Set.uIcc
        (explicitFormulaRectangleSortedYEndpointAt T radius k)
        (explicitFormulaRectangleSortedYEndpointAt T radius (k + 1)) ⊆
      Set.Icc (-T) T := by
  have hsuccessor : k + 1 < (explicitFormulaRectangleSortedYEndpoints T radius).length :=
    (Nat.lt_sub_iff_add_lt
      (a := k) (b := 1)
      (c := (explicitFormulaRectangleSortedYEndpoints T radius).length)).mp hk
  have hcurrent : k < (explicitFormulaRectangleSortedYEndpoints T radius).length :=
    lt_trans (Nat.lt_succ_self k) hsuccessor
  have hlower :
      explicitFormulaRectangleSortedYEndpointAt T radius k ∈ Set.Icc (-T) T :=
    explicitFormulaRectangleSortedYEndpointAt_mem_vertical_Icc_of_closedRadiusControls
      F T radius hT hradius hclosed k hcurrent
  have hupper :
      explicitFormulaRectangleSortedYEndpointAt T radius (k + 1) ∈ Set.Icc (-T) T :=
    explicitFormulaRectangleSortedYEndpointAt_mem_vertical_Icc_of_closedRadiusControls
      F T radius hT hradius hclosed (k + 1) hsuccessor
  exact Set.uIcc_subset_Icc hlower hupper

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
