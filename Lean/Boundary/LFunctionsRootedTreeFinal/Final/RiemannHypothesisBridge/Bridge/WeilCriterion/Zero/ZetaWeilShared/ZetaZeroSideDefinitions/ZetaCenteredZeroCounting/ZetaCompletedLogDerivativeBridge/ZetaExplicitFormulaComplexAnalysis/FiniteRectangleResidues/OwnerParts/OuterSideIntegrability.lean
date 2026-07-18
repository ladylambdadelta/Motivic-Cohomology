import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.SquareHoleVerticalIntegrability

/-!
# Scheduled outer-side integrability
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Every defined sorted horizontal endpoint remains in the closed outer horizontal span. -/
theorem explicitFormulaRectangleSortedXEndpointAt_mem_horizontal_uIcc_of_closedRadiusControls
    (F : ExplicitFormulaContourFamily) (T radius : ℝ) (hradius : 0 ≤ radius)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a radius ⊆ explicitFormulaContourFamilyInterior F T)
    (k : ℕ) (hk : k < (explicitFormulaRectangleSortedXEndpoints F T radius).length) :
    explicitFormulaRectangleSortedXEndpointAt F T radius k ∈
      Set.uIcc F.c (1 - F.c) := by
  let xs : List ℝ := explicitFormulaRectangleSortedXEndpoints F T radius
  let index : Fin xs.length := ⟨k, hk⟩
  have hgetMem : xs.get index ∈ xs := List.get_mem xs index
  have hcarrier :
      xs.get index ∈
        explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T radius :=
    (explicitFormulaRectangleSortedXEndpoints_mem_iff F T radius (xs.get index)).mp hgetMem
  have hspan : xs.get index ∈ Set.uIcc F.c (1 - F.c) :=
    explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints_mem_horizontal_uIcc_of_closedRadiusControls
      F T radius hradius hclosed hcarrier
  have hendpoint : explicitFormulaRectangleSortedXEndpointAt F T radius k = xs.get index :=
    explicitFormulaRectangleSortedXEndpointAt_of_lt F T radius hk
  exact
    Eq.subst
      (motive := fun value : ℝ => value ∈ Set.uIcc F.c (1 - F.c))
      hendpoint.symm hspan

/-- Every adjacent sorted horizontal interval lies in the closed outer horizontal span. -/
theorem explicitFormulaRectangleSortedXAdjacent_uIcc_subset_horizontal_uIcc
    (F : ExplicitFormulaContourFamily) (T radius : ℝ) (hradius : 0 ≤ radius)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a radius ⊆ explicitFormulaContourFamilyInterior F T)
    (k : ℕ)
    (hk : k < (explicitFormulaRectangleSortedXEndpoints F T radius).length - 1) :
    Set.uIcc
        (explicitFormulaRectangleSortedXEndpointAt F T radius k)
        (explicitFormulaRectangleSortedXEndpointAt F T radius (k + 1)) ⊆
      Set.uIcc F.c (1 - F.c) := by
  have hsuccessor : k + 1 < (explicitFormulaRectangleSortedXEndpoints F T radius).length :=
    (Nat.lt_sub_iff_add_lt
      (a := k) (b := 1)
      (c := (explicitFormulaRectangleSortedXEndpoints F T radius).length)).mp hk
  have hcurrent : k < (explicitFormulaRectangleSortedXEndpoints F T radius).length :=
    lt_trans (Nat.lt_succ_self k) hsuccessor
  have hlower :=
    explicitFormulaRectangleSortedXEndpointAt_mem_horizontal_uIcc_of_closedRadiusControls
      F T radius hradius hclosed k hcurrent
  have hupper :=
    explicitFormulaRectangleSortedXEndpointAt_mem_horizontal_uIcc_of_closedRadiusControls
      F T radius hradius hclosed (k + 1) hsuccessor
  exact Set.uIcc_subset_uIcc hlower hupper

/-- The scheduled bottom outer side is integrable over every sorted horizontal piece. -/
theorem explicitFormulaRectangleSortedXHorizontalSideIntegrable_bottom_of_scheduledPackage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u radius : ℝ)
    (hradius : 0 ≤ radius)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
          Metric.closedBall a radius ⊆
            explicitFormulaContourFamilyInterior F (h.height_schedule.height u)) :
    explicitFormulaRectangleSortedXHorizontalSideIntegrable
      f F (h.height_schedule.height u) radius (-(h.height_schedule.height u)) := by
  intro k hk
  exact
    explicitFormulaRectangle_horizontalEdgeContourIntegrand_intervalIntegrable_of_scheduledPackage
      f F h u
      (fun x hx =>
        explicitFormulaContourFamilyBoundary_mem_of_im_eq_bottom
          F (h.height_schedule.height u)
          (explicitFormulaRectangleSortedXAdjacent_uIcc_subset_horizontal_uIcc
            F (h.height_schedule.height u) radius hradius hclosed k hk hx)
          (ofReal_add_mul_I_im x (-(h.height_schedule.height u))))

/-- The scheduled top outer side is integrable over every sorted horizontal piece. -/
theorem explicitFormulaRectangleSortedXHorizontalSideIntegrable_top_of_scheduledPackage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u radius : ℝ)
    (hradius : 0 ≤ radius)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
          Metric.closedBall a radius ⊆
            explicitFormulaContourFamilyInterior F (h.height_schedule.height u)) :
    explicitFormulaRectangleSortedXHorizontalSideIntegrable
      f F (h.height_schedule.height u) radius (h.height_schedule.height u) := by
  intro k hk
  exact
    explicitFormulaRectangle_horizontalEdgeContourIntegrand_intervalIntegrable_of_scheduledPackage
      f F h u
      (fun x hx =>
        explicitFormulaContourFamilyBoundary_mem_of_im_eq_top
          F (h.height_schedule.height u)
          (explicitFormulaRectangleSortedXAdjacent_uIcc_subset_horizontal_uIcc
            F (h.height_schedule.height u) radius hradius hclosed k hk hx)
          (ofReal_add_mul_I_im x (h.height_schedule.height u)))

/-- The scheduled right outer side is integrable over every sorted vertical piece. -/
theorem explicitFormulaRectangleSortedYVerticalSideIntegrable_right_of_scheduledPackage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u radius : ℝ)
    (hT : 0 < h.height_schedule.height u) (hradius : 0 ≤ radius)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
          Metric.closedBall a radius ⊆
            explicitFormulaContourFamilyInterior F (h.height_schedule.height u)) :
    explicitFormulaRectangleSortedYVerticalSideIntegrable
      f (h.height_schedule.height u) radius F.c := by
  intro k hk
  exact
    explicitFormulaRectangle_verticalEdgeContourIntegrand_intervalIntegrable_of_scheduledPackage
      f F h u
      (fun y hy =>
        explicitFormulaContourFamilyBoundary_mem_of_re_eq_right
          F (h.height_schedule.height u)
          (ofReal_add_mul_I_re F.c y)
          (explicitFormulaRectangleSortedYAdjacent_uIcc_subset_vertical_Icc
            F (h.height_schedule.height u) radius (le_of_lt hT) hradius hclosed k hk hy))

/-- The scheduled left outer side is integrable over every sorted vertical piece. -/
theorem explicitFormulaRectangleSortedYVerticalSideIntegrable_left_of_scheduledPackage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u radius : ℝ)
    (hT : 0 < h.height_schedule.height u) (hradius : 0 ≤ radius)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
          Metric.closedBall a radius ⊆
            explicitFormulaContourFamilyInterior F (h.height_schedule.height u)) :
    explicitFormulaRectangleSortedYVerticalSideIntegrable
      f (h.height_schedule.height u) radius (1 - F.c) := by
  intro k hk
  exact
    explicitFormulaRectangle_verticalEdgeContourIntegrand_intervalIntegrable_of_scheduledPackage
      f F h u
      (fun y hy =>
        explicitFormulaContourFamilyBoundary_mem_of_re_eq_left
          F (h.height_schedule.height u)
          (ofReal_add_mul_I_re (1 - F.c) y)
          (explicitFormulaRectangleSortedYAdjacent_uIcc_subset_vertical_Icc
            F (h.height_schedule.height u) radius (le_of_lt hT) hradius hclosed k hk hy))

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
