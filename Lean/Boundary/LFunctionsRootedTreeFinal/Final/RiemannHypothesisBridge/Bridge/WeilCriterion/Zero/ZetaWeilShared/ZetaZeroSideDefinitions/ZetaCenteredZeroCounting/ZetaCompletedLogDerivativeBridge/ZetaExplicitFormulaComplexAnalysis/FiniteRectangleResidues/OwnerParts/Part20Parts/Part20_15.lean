import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part20Parts.Part20_14

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
## Part20 15: HorizontalOuterAndHoleSides
-/

theorem explicitFormulaRectangleXAdjacentEndpointPairOuter_bottomIntegralSum_eq_fullBottomEdge_of_integrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hint :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ (-T)) :
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
            f ((xpair.x₀, xpair.x₁), -T))
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
      explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
        f ((1 - F.c, F.c), -T) := by
  let xs : List ℝ := explicitFormulaRectangleSortedXEndpoints F T ρ
  let n : ℕ := xs.length - 1
  let a : ℕ → ℝ := explicitFormulaRectangleSortedXEndpointAt F T ρ
  have hfirst :
      a 0 = 1 - F.c := by
    have h0 : 0 < xs.length :=
      explicitFormulaRectangleSortedXEndpoints_length_pos F T ρ
    calc
      a 0 =
          xs.get ⟨0, h0⟩ := by
        exact explicitFormulaRectangleSortedXEndpointAt_of_lt F T ρ h0
      _ = 1 - F.c := by
        exact explicitFormulaRectangleSortedXEndpoints_first_eq_outerLeft F hρ hclosed
  have hlast :
      a n = F.c := by
    have hlast_lt :
        xs.length - 1 < xs.length :=
      Nat.sub_lt
        (explicitFormulaRectangleSortedXEndpoints_length_pos F T ρ)
        Nat.zero_lt_one
    calc
      a n =
          xs.get ⟨xs.length - 1, hlast_lt⟩ := by
        exact explicitFormulaRectangleSortedXEndpointAt_of_lt F T ρ hlast_lt
      _ = F.c := by
        exact explicitFormulaRectangleSortedXEndpoints_last_eq_outerRight F hρ hclosed
  have htelescope :
      explicitFormulaRectangleListSum
          (fun i : Fin n =>
            ∫ x : ℝ in a i.1..a (i.1 + 1),
              zetaCompletedExplicitFormulaContourIntegrand f
                (x + ((-T : ℝ) : ℂ) * Complex.I))
          (List.ofFn (fun i : Fin n => i)) =
        ∫ x : ℝ in a 0..a n,
          zetaCompletedExplicitFormulaContourIntegrand f
            (x + ((-T : ℝ) : ℂ) * Complex.I) :=
    explicitFormulaRectangleListSum_ofFn_horizontalIntegral_adjacent
      f (-T) a hint
  calc
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
            f ((xpair.x₀, xpair.x₁), -T))
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
        explicitFormulaRectangleListSum
          (fun i : Fin n =>
            ∫ x : ℝ in a i.1..a (i.1 + 1),
              zetaCompletedExplicitFormulaContourIntegrand f
                (x + ((-T : ℝ) : ℂ) * Complex.I))
          (List.ofFn (fun i : Fin n => i)) := by
      rfl
    _ =
        ∫ x : ℝ in a 0..a n,
          zetaCompletedExplicitFormulaContourIntegrand f
            (x + ((-T : ℝ) : ℂ) * Complex.I) := by
      exact htelescope
    _ =
        ∫ x : ℝ in (1 - F.c)..F.c,
          zetaCompletedExplicitFormulaContourIntegrand f
            (x + ((-T : ℝ) : ℂ) * Complex.I) := by
      exact
        congrArg
          (fun endpoints : ℝ × ℝ =>
            ∫ x : ℝ in endpoints.1..endpoints.2,
              zetaCompletedExplicitFormulaContourIntegrand f
                (x + ((-T : ℝ) : ℂ) * Complex.I))
          (Prod.ext hfirst hlast)
    _ =
        explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
          f ((1 - F.c, F.c), -T) := by
      rfl

/-- The sorted horizontal subdivision assembles to a full top endpoint-data edge once
interval-integrability on the sorted adjacent subintervals is supplied. -/
theorem explicitFormulaRectangleXAdjacentEndpointPairOuter_topIntegralSum_eq_fullTopEdge_of_integrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hint :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ T) :
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
            f ((xpair.x₀, xpair.x₁), T))
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
      explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
        f ((1 - F.c, F.c), T) := by
  let xs : List ℝ := explicitFormulaRectangleSortedXEndpoints F T ρ
  let n : ℕ := xs.length - 1
  let a : ℕ → ℝ := explicitFormulaRectangleSortedXEndpointAt F T ρ
  have hfirst :
      a 0 = 1 - F.c := by
    have h0 : 0 < xs.length :=
      explicitFormulaRectangleSortedXEndpoints_length_pos F T ρ
    calc
      a 0 =
          xs.get ⟨0, h0⟩ := by
        exact explicitFormulaRectangleSortedXEndpointAt_of_lt F T ρ h0
      _ = 1 - F.c := by
        exact explicitFormulaRectangleSortedXEndpoints_first_eq_outerLeft F hρ hclosed
  have hlast :
      a n = F.c := by
    have hlast_lt :
        xs.length - 1 < xs.length :=
      Nat.sub_lt
        (explicitFormulaRectangleSortedXEndpoints_length_pos F T ρ)
        Nat.zero_lt_one
    calc
      a n =
          xs.get ⟨xs.length - 1, hlast_lt⟩ := by
        exact explicitFormulaRectangleSortedXEndpointAt_of_lt F T ρ hlast_lt
      _ = F.c := by
        exact explicitFormulaRectangleSortedXEndpoints_last_eq_outerRight F hρ hclosed
  have htelescope :
      explicitFormulaRectangleListSum
          (fun i : Fin n =>
            ∫ x : ℝ in a i.1..a (i.1 + 1),
              zetaCompletedExplicitFormulaContourIntegrand f
                (x + (T : ℂ) * Complex.I))
          (List.ofFn (fun i : Fin n => i)) =
        ∫ x : ℝ in a 0..a n,
          zetaCompletedExplicitFormulaContourIntegrand f
            (x + (T : ℂ) * Complex.I) :=
    explicitFormulaRectangleListSum_ofFn_horizontalIntegral_adjacent
      f T a hint
  calc
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
            f ((xpair.x₀, xpair.x₁), T))
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
        explicitFormulaRectangleListSum
          (fun i : Fin n =>
            ∫ x : ℝ in a i.1..a (i.1 + 1),
              zetaCompletedExplicitFormulaContourIntegrand f
                (x + (T : ℂ) * Complex.I))
          (List.ofFn (fun i : Fin n => i)) := by
      rfl
    _ =
        ∫ x : ℝ in a 0..a n,
          zetaCompletedExplicitFormulaContourIntegrand f
            (x + (T : ℂ) * Complex.I) := by
      exact htelescope
    _ =
        ∫ x : ℝ in (1 - F.c)..F.c,
          zetaCompletedExplicitFormulaContourIntegrand f
            (x + (T : ℂ) * Complex.I) := by
      exact
        congrArg
          (fun endpoints : ℝ × ℝ =>
            ∫ x : ℝ in endpoints.1..endpoints.2,
              zetaCompletedExplicitFormulaContourIntegrand f
                (x + (T : ℂ) * Complex.I))
          (Prod.ext hfirst hlast)
    _ =
        explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
          f ((1 - F.c, F.c), T) := by
      rfl

/-- The sorted horizontal subdivision assembles to the full bottom outer endpoint-data
edge. -/
theorem explicitFormulaRectangleXAdjacentEndpointPairOuter_bottomIntegralSum_eq_fullBottomEdge_core
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hbottom :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ (-T)) :
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
            f ((xpair.x₀, xpair.x₁), -T))
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
      explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
        f ((1 - F.c, F.c), -T) := by
  exact
    explicitFormulaRectangleXAdjacentEndpointPairOuter_bottomIntegralSum_eq_fullBottomEdge_of_integrable
      f F hρ hclosed hbottom

/-- The sorted horizontal subdivision assembles to the full top outer endpoint-data
edge. -/
theorem explicitFormulaRectangleXAdjacentEndpointPairOuter_topIntegralSum_eq_fullTopEdge_core
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (htop :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ T) :
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
            f ((xpair.x₀, xpair.x₁), T))
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
      explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
        f ((1 - F.c, F.c), T) := by
  exact
    explicitFormulaRectangleXAdjacentEndpointPairOuter_topIntegralSum_eq_fullTopEdge_of_integrable
      f F hρ hclosed htop

/-- The sorted horizontal subdivision of the outer rectangle assembles to the two full
horizontal endpoint-data edges before line-integral normalization. -/
theorem explicitFormulaRectangleXAdjacentEndpointPairOuter_horizontalIntegralSums_eq_fullEdges
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hbottom :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ (-T))
    (htop :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ T) :
    (explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
            f ((xpair.x₀, xpair.x₁), -T))
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
      explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
        f ((1 - F.c, F.c), -T)) ∧
    (explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
            f ((xpair.x₀, xpair.x₁), T))
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
      explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
        f ((1 - F.c, F.c), T)) := by
  exact
    And.intro
      (explicitFormulaRectangleXAdjacentEndpointPairOuter_bottomIntegralSum_eq_fullBottomEdge_core
        f F hT_nonneg hρ hclosed hbottom)
      (explicitFormulaRectangleXAdjacentEndpointPairOuter_topIntegralSum_eq_fullTopEdge_core
        f F hT_nonneg hρ hclosed htop)

/-- The sorted horizontal subdivision of the outer rectangle assembles to the full
bottom endpoint-data edge before line-integral normalization. -/
theorem explicitFormulaRectangleXAdjacentEndpointPairOuter_bottomIntegralSum_eq_fullBottomEdge
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hbottom :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ (-T))
    (htop :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ T) :
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
            f ((xpair.x₀, xpair.x₁), -T))
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
      explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
        f ((1 - F.c, F.c), -T) := by
  exact
    (explicitFormulaRectangleXAdjacentEndpointPairOuter_horizontalIntegralSums_eq_fullEdges
      f F hT_nonneg hρ hclosed hbottom htop).1

/-- The sorted horizontal subdivision of the outer rectangle assembles to the full top
endpoint-data edge before line-integral normalization. -/
theorem explicitFormulaRectangleXAdjacentEndpointPairOuter_topIntegralSum_eq_fullTopEdge
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hbottom :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ (-T))
    (htop :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ T) :
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
            f ((xpair.x₀, xpair.x₁), T))
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
      explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
        f ((1 - F.c, F.c), T) := by
  exact
    (explicitFormulaRectangleXAdjacentEndpointPairOuter_horizontalIntegralSums_eq_fullEdges
      f F hT_nonneg hρ hclosed hbottom htop).2

/-- The full horizontal endpoint-data edges have the oriented normalization of the named
horizontal line integrals. -/
theorem explicitFormulaRectangleOuterHorizontalEndpointDataEdgeIntegrals_eq_neg_lineIntegrals
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    (explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
        f ((F.c, 1 - F.c), -T) =
      -(zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T))) ∧
    (explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
        f ((F.c, 1 - F.c), T) =
      -(zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T))) := by
  constructor
  · exact
      explicitFormulaRectangleOuterBottomEndpointDataEdgeIntegral_eq_neg_bottomLineIntegral_core
        f F T
  · exact
      explicitFormulaRectangleOuterTopEndpointDataEdgeIntegral_eq_neg_topLineIntegral_core
        f F T

/-- The full bottom endpoint-data edge has the oriented normalization of the named
bottom line integral. -/
theorem explicitFormulaRectangleOuterBottomEndpointDataEdgeIntegral_eq_neg_bottomLineIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
        f ((F.c, 1 - F.c), -T) =
      -(zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T)) := by
  exact
    (explicitFormulaRectangleOuterHorizontalEndpointDataEdgeIntegrals_eq_neg_lineIntegrals
      f F T).1

/-- The full top endpoint-data edge has the oriented normalization of the named top line
integral. -/
theorem explicitFormulaRectangleOuterTopEndpointDataEdgeIntegral_eq_neg_topLineIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
        f ((F.c, 1 - F.c), T) =
      -(zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T)) := by
  exact
    (explicitFormulaRectangleOuterHorizontalEndpointDataEdgeIntegrals_eq_neg_lineIntegrals
      f F T).2

/-- The sorted horizontal subdivision of the outer rectangle assembles to the oriented
bottom tangent side. -/
theorem explicitFormulaRectangleXAdjacentEndpointPairOuter_bottomIntegralSum_eq_outerBottomSide
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hbottom :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ (-T))
    (htop :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ T) :
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
            f ((xpair.x₀, xpair.x₁), -T))
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
      zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) := by
  calc
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
            f ((xpair.x₀, xpair.x₁), -T))
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
        explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
          f ((1 - F.c, F.c), -T) := by
      exact
        explicitFormulaRectangleXAdjacentEndpointPairOuter_bottomIntegralSum_eq_fullBottomEdge
          f F hT_nonneg hρ hclosed hbottom htop
    _ = zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) := by
      exact
        explicitFormulaRectangleOuterBottomEndpointDataEdgeIntegral_forward_eq_bottomLineIntegral_core
          f F T

/-- The sorted horizontal subdivision of the outer rectangle assembles to the oriented
top tangent side. -/
theorem explicitFormulaRectangleXAdjacentEndpointPairOuter_topIntegralSum_eq_outerTopSide
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hbottom :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ (-T))
    (htop :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ T) :
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
            f ((xpair.x₀, xpair.x₁), T))
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
      zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) := by
  calc
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
            f ((xpair.x₀, xpair.x₁), T))
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
        explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
          f ((1 - F.c, F.c), T) := by
      exact
        explicitFormulaRectangleXAdjacentEndpointPairOuter_topIntegralSum_eq_fullTopEdge
          f F hT_nonneg hρ hclosed hbottom htop
    _ = zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) := by
      exact
        explicitFormulaRectangleOuterTopEndpointDataEdgeIntegral_forward_eq_topLineIntegral_core
          f F T

/-- The bottom outer horizontal endpoint-data slices over the sorted horizontal
subdivision assemble to the forward bottom side of the outer rectangle. -/
theorem explicitFormulaRectangleHorizontalOuterBottomSliceContributionSum_eq_outerBottomSide
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hbottom :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ (-T))
    (htop :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ T) :
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
            f ((xpair.x₀, xpair.x₁), -T))
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
      zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) := by
  exact
    explicitFormulaRectangleXAdjacentEndpointPairOuter_bottomIntegralSum_eq_outerBottomSide
      f F hT_nonneg hρ hclosed hbottom htop

/-- The top outer horizontal endpoint-data slices over the sorted horizontal subdivision
assemble to the forward top side of the outer rectangle. -/
theorem explicitFormulaRectangleHorizontalOuterTopSliceContributionSum_eq_outerTopSide
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hbottom :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ (-T))
    (htop :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ T) :
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
            f ((xpair.x₀, xpair.x₁), T))
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
      zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) := by
  exact
    explicitFormulaRectangleXAdjacentEndpointPairOuter_topIntegralSum_eq_outerTopSide
      f F hT_nonneg hρ hclosed hbottom htop

/-- The bottom raw-hole horizontal slices over the sorted horizontal subdivision assemble
to the grouped bottom sides of the raw square holes. -/
theorem explicitFormulaRectangleHorizontalHoleBottomSliceContributionSum_eq_holeBottomSide
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
              a ≠ b → ρ + ρ < dist a b) :
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
            if _hspan :
                explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                  ρ xpair a then
              explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
                ((xpair.x₀, xpair.x₁),
                  (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
            else
              0)
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
      explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum f T ρ := by
  let S : Finset ℂ := explicitFormulaRectangleRawSingularCoordinates T
  calc
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          ∑ a in S,
            if _hspan :
                explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                  ρ xpair a then
              explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
                ((xpair.x₀, xpair.x₁),
                  (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
            else
              0)
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
        ∑ a in S,
          explicitFormulaRectangleListSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              if _hspan :
                  explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                    ρ xpair a then
                explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
                  ((xpair.x₀, xpair.x₁),
                    (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
              else
                0)
            (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) := by
      exact
        explicitFormulaRectangleHorizontalHoleBottomSliceContributionSum_groupedByRawCoordinate
          f F T ρ
    _ =
        ∑ a in S,
          explicitFormulaRectangleBoxBottomEdgeIntegral f
            (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ρ a) := by
      exact Finset.sum_congr rfl
        (fun a ha =>
          explicitFormulaRectangleXAdjacentEndpointPairSubspanRawHole_bottomIntegralSum_eq_rawBoxBottom
            f F hT_nonneg hρ hclosed hsep ha (hbottomHole a ha))
    _ =
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum f T ρ := by
      rfl

/-- The top raw-hole horizontal slices over the sorted horizontal subdivision assemble
to the grouped top sides of the raw square holes. -/
theorem explicitFormulaRectangleHorizontalHoleTopSliceContributionSum_eq_holeTopSide
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
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
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
            if _hspan :
                explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                  ρ xpair a then
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
                ((xpair.x₀, xpair.x₁),
                  (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
            else
              0)
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
      explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum f T ρ := by
  let S : Finset ℂ := explicitFormulaRectangleRawSingularCoordinates T
  calc
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          ∑ a in S,
            if _hspan :
                explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                  ρ xpair a then
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
                ((xpair.x₀, xpair.x₁),
                  (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
            else
              0)
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
        ∑ a in S,
          explicitFormulaRectangleListSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              if _hspan :
                  explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                    ρ xpair a then
                explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
                  ((xpair.x₀, xpair.x₁),
                    (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
              else
                0)
            (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) := by
      exact
        explicitFormulaRectangleHorizontalHoleTopSliceContributionSum_groupedByRawCoordinate
          f F T ρ
    _ =
        ∑ a in S,
          explicitFormulaRectangleBoxTopEdgeIntegral f
            (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ρ a) := by
      exact Finset.sum_congr rfl
        (fun a ha =>
          explicitFormulaRectangleXAdjacentEndpointPairSubspanRawHole_topIntegralSum_eq_rawBoxTop
            f F hT_nonneg hρ hclosed hsep ha (htopHole a ha))
    _ =
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum f T ρ := by
      rfl

/-- A raw-hole horizontal slice is the bottom raw-hole slice minus the top raw-hole slice
at the same sorted horizontal span. -/
theorem explicitFormulaRectangleHorizontalHoleSliceContribution_eq_bottom_sub_top
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ρ : ℝ)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :
    explicitFormulaRectangleHorizontalHoleSliceContribution f T ρ xpair =
      (∑ a in explicitFormulaRectangleRawSingularCoordinates T,
        if _hspan :
            explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
              ρ xpair a then
          explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
            ((xpair.x₀, xpair.x₁),
              (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
        else
          0) -
        (∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          if _hspan :
              explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                ρ xpair a then
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
              ((xpair.x₀, xpair.x₁),
                (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
          else
            0) := by
  have hpoint :
      ∀ a : ℂ,
        (if _hspan :
            explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
              ρ xpair a then
          explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
              ((xpair.x₀, xpair.x₁),
                (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im) -
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
              ((xpair.x₀, xpair.x₁),
                (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
        else
          0) =
          (if _hspan :
              explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                ρ xpair a then
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
              ((xpair.x₀, xpair.x₁),
                (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
          else
            0) -
            (if _hspan :
                explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                  ρ xpair a then
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
                ((xpair.x₀, xpair.x₁),
                  (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
            else
              0) := by
    intro a
    by_cases hspan :
        explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a
    · rfl
    · exact (sub_zero (0 : ℂ)).symm
  calc
    explicitFormulaRectangleHorizontalHoleSliceContribution f T ρ xpair =
        ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          ((if _hspan :
              explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                ρ xpair a then
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
                ((xpair.x₀, xpair.x₁),
                  (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
          else
            0) -
            (if _hspan :
                explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                  ρ xpair a then
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
                ((xpair.x₀, xpair.x₁),
                  (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
            else
              0)) := by
      exact Finset.sum_congr rfl (fun a _ha => hpoint a)
    _ =
        (∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          if _hspan :
              explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                ρ xpair a then
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
              ((xpair.x₀, xpair.x₁),
                (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
          else
            0) -
          (∑ a in explicitFormulaRectangleRawSingularCoordinates T,
            if _hspan :
                explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
                  ρ xpair a then
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
                ((xpair.x₀, xpair.x₁),
                  (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
            else
              0) := by
      exact Finset.sum_sub_distrib

/-- Fixed-row rejected horizontal scan grouping.  The non-selected bottom-minus-top
vertical adjacent-pair scan is exactly the sum of raw-hole bottom-minus-top slices whose
horizontal span contains the fixed `xpair`. -/

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
