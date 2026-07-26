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
  have hgetMem : xs.get index ∈ xs :=
    List.get_mem xs index.val index.isLt
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

/-- Boundary regularity on one rectangle gives integrability of the sorted bottom
outer side over every horizontal piece. -/
theorem explicitFormulaRectangleSortedXHorizontalSideIntegrable_bottom_of_boundaryRegular
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (T radius : ℝ) (hradius : 0 ≤ radius)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a radius ⊆ explicitFormulaContourFamilyInterior F T) :
    explicitFormulaRectangleSortedXHorizontalSideIntegrable
      f F T radius (-T) := by
  intro k hk
  exact
    explicitFormulaRectangle_horizontalEdgeContourIntegrand_intervalIntegrable_of_boundaryRegular
      f F hboundary
      (fun x hx =>
        have hre :
            ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).re = x :=
          ofReal_add_mul_I_re x (-T)
        have hxPoint :
            ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).re ∈
              Set.uIcc
                (explicitFormulaRectangleSortedXEndpointAt F T radius k)
                (explicitFormulaRectangleSortedXEndpointAt F T radius (k + 1)) :=
          Eq.subst
            (motive := fun value : ℝ =>
              value ∈
                Set.uIcc
                  (explicitFormulaRectangleSortedXEndpointAt F T radius k)
                  (explicitFormulaRectangleSortedXEndpointAt F T radius (k + 1)))
            hre.symm
            hx
        explicitFormulaContourFamilyBoundary_mem_of_im_eq_bottom
          F T
          (explicitFormulaRectangleSortedXAdjacent_uIcc_subset_horizontal_uIcc
            F T radius hradius hclosed k hk hxPoint)
          (ofReal_add_mul_I_im x (-T)))

/-- Boundary regularity on one rectangle gives integrability of the sorted top
outer side over every horizontal piece. -/
theorem explicitFormulaRectangleSortedXHorizontalSideIntegrable_top_of_boundaryRegular
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (T radius : ℝ) (hradius : 0 ≤ radius)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a radius ⊆ explicitFormulaContourFamilyInterior F T) :
    explicitFormulaRectangleSortedXHorizontalSideIntegrable
      f F T radius T := by
  intro k hk
  exact
    explicitFormulaRectangle_horizontalEdgeContourIntegrand_intervalIntegrable_of_boundaryRegular
      f F hboundary
      (fun x hx =>
        have hre :
            ((x : ℂ) + (T : ℂ) * Complex.I).re = x :=
          ofReal_add_mul_I_re x T
        have hxPoint :
            ((x : ℂ) + (T : ℂ) * Complex.I).re ∈
              Set.uIcc
                (explicitFormulaRectangleSortedXEndpointAt F T radius k)
                (explicitFormulaRectangleSortedXEndpointAt F T radius (k + 1)) :=
          Eq.subst
            (motive := fun value : ℝ =>
              value ∈
                Set.uIcc
                  (explicitFormulaRectangleSortedXEndpointAt F T radius k)
                  (explicitFormulaRectangleSortedXEndpointAt F T radius (k + 1)))
            hre.symm
            hx
        explicitFormulaContourFamilyBoundary_mem_of_im_eq_top
          F T
          (explicitFormulaRectangleSortedXAdjacent_uIcc_subset_horizontal_uIcc
            F T radius hradius hclosed k hk hxPoint)
          (ofReal_add_mul_I_im x T))

/-- Boundary regularity on one rectangle gives integrability of the sorted right
outer side over every vertical piece. -/
theorem explicitFormulaRectangleSortedYVerticalSideIntegrable_right_of_boundaryRegular
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (T radius : ℝ) (hT : 0 < T) (hradius : 0 ≤ radius)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a radius ⊆ explicitFormulaContourFamilyInterior F T) :
    explicitFormulaRectangleSortedYVerticalSideIntegrable f T radius F.c := by
  intro k hk
  exact
    explicitFormulaRectangle_verticalEdgeContourIntegrand_intervalIntegrable_of_boundaryRegular
      f F hboundary
      (fun y hy =>
        have him :
            ((F.c : ℂ) + (y : ℂ) * Complex.I).im = y :=
          ofReal_add_mul_I_im F.c y
        have hyPoint :
            ((F.c : ℂ) + (y : ℂ) * Complex.I).im ∈
              Set.uIcc
                (explicitFormulaRectangleSortedYEndpointAt T radius k)
                (explicitFormulaRectangleSortedYEndpointAt T radius (k + 1)) :=
          Eq.subst
            (motive := fun value : ℝ =>
              value ∈
                Set.uIcc
                  (explicitFormulaRectangleSortedYEndpointAt T radius k)
                  (explicitFormulaRectangleSortedYEndpointAt T radius (k + 1)))
            him.symm
            hy
        explicitFormulaContourFamilyBoundary_mem_of_re_eq_right
          F T
          (ofReal_add_mul_I_re F.c y)
          (explicitFormulaRectangleSortedYAdjacent_uIcc_subset_vertical_Icc
            F T radius (le_of_lt hT) hradius hclosed k hk hyPoint))

/-- Boundary regularity on one rectangle gives integrability of the sorted left
outer side over every vertical piece. -/
theorem explicitFormulaRectangleSortedYVerticalSideIntegrable_left_of_boundaryRegular
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (T radius : ℝ) (hT : 0 < T) (hradius : 0 ≤ radius)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a radius ⊆ explicitFormulaContourFamilyInterior F T) :
    explicitFormulaRectangleSortedYVerticalSideIntegrable f T radius (1 - F.c) := by
  intro k hk
  exact
    explicitFormulaRectangle_verticalEdgeContourIntegrand_intervalIntegrable_of_boundaryRegular
      f F hboundary
      (fun y hy =>
        have him :
            (((1 - F.c : ℝ) : ℂ) + (y : ℂ) * Complex.I).im = y :=
          ofReal_add_mul_I_im (1 - F.c) y
        have hyPoint :
            (((1 - F.c : ℝ) : ℂ) + (y : ℂ) * Complex.I).im ∈
              Set.uIcc
                (explicitFormulaRectangleSortedYEndpointAt T radius k)
                (explicitFormulaRectangleSortedYEndpointAt T radius (k + 1)) :=
          Eq.subst
            (motive := fun value : ℝ =>
              value ∈
                Set.uIcc
                  (explicitFormulaRectangleSortedYEndpointAt T radius k)
                  (explicitFormulaRectangleSortedYEndpointAt T radius (k + 1)))
            him.symm
            hy
        explicitFormulaContourFamilyBoundary_mem_of_re_eq_left
          F T
          (ofReal_add_mul_I_re (1 - F.c) y)
          (explicitFormulaRectangleSortedYAdjacent_uIcc_subset_vertical_Icc
            F T radius (le_of_lt hT) hradius hclosed k hk hyPoint))

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
  have hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F (h.height_schedule.height u) →
          ContinuousAt
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z :=
    explicitFormulaRectangleContourIntegrand_boundaryRegular_of_avoidsBoundary
      f F h (h.height_schedule.height u)
      (explicitFormulaScheduledRectangle_avoidsSingularBoundary f F h u)
  exact
    explicitFormulaRectangleSortedXHorizontalSideIntegrable_bottom_of_boundaryRegular
      f F (h.height_schedule.height u) radius hradius hboundary hclosed

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
  have hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F (h.height_schedule.height u) →
          ContinuousAt
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z :=
    explicitFormulaRectangleContourIntegrand_boundaryRegular_of_avoidsBoundary
      f F h (h.height_schedule.height u)
      (explicitFormulaScheduledRectangle_avoidsSingularBoundary f F h u)
  exact
    explicitFormulaRectangleSortedXHorizontalSideIntegrable_top_of_boundaryRegular
      f F (h.height_schedule.height u) radius hradius hboundary hclosed

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
  have hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F (h.height_schedule.height u) →
          ContinuousAt
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z :=
    explicitFormulaRectangleContourIntegrand_boundaryRegular_of_avoidsBoundary
      f F h (h.height_schedule.height u)
      (explicitFormulaScheduledRectangle_avoidsSingularBoundary f F h u)
  exact
    explicitFormulaRectangleSortedYVerticalSideIntegrable_right_of_boundaryRegular
      f F (h.height_schedule.height u) radius hT hradius hboundary hclosed

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
  have hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F (h.height_schedule.height u) →
          ContinuousAt
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z :=
    explicitFormulaRectangleContourIntegrand_boundaryRegular_of_avoidsBoundary
      f F h (h.height_schedule.height u)
      (explicitFormulaScheduledRectangle_avoidsSingularBoundary f F h u)
  exact
    explicitFormulaRectangleSortedYVerticalSideIntegrable_left_of_boundaryRegular
      f F (h.height_schedule.height u) radius hT hradius hboundary hclosed

/- Common outer-side package used by the finite-hole grid.  The four boundary
   integrals are assembled only after each side has been proved from boundary
   regularity and the same closed-radius controls. -/
theorem explicitFormulaRectangleSortedOuterSidesIntegrable_of_scheduledPackage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u radius : ℝ)
    (hT : 0 < h.height_schedule.height u) (hradius : 0 ≤ radius)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates
          (h.height_schedule.height u) →
          Metric.closedBall a radius ⊆
            explicitFormulaContourFamilyInterior F (h.height_schedule.height u)) :
    explicitFormulaRectangleSortedXHorizontalSideIntegrable
        f F (h.height_schedule.height u) radius
          (-(h.height_schedule.height u)) ∧
      explicitFormulaRectangleSortedXHorizontalSideIntegrable
        f F (h.height_schedule.height u) radius
          (h.height_schedule.height u) ∧
      explicitFormulaRectangleSortedYVerticalSideIntegrable
        f (h.height_schedule.height u) radius F.c ∧
      explicitFormulaRectangleSortedYVerticalSideIntegrable
        f (h.height_schedule.height u) radius (1 - F.c) := by
  exact ⟨
    explicitFormulaRectangleSortedXHorizontalSideIntegrable_bottom_of_scheduledPackage
      f F h u radius hradius hclosed,
    explicitFormulaRectangleSortedXHorizontalSideIntegrable_top_of_scheduledPackage
      f F h u radius hradius hclosed,
    explicitFormulaRectangleSortedYVerticalSideIntegrable_right_of_scheduledPackage
      f F h u radius hT hradius hclosed,
    explicitFormulaRectangleSortedYVerticalSideIntegrable_left_of_scheduledPackage
      f F h u hT hradius hclosed⟩

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
