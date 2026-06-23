import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part20Parts.Part20_09

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
## Part20 10: VerticalOuterAndHoleSides
-/

theorem explicitFormulaRectangleYAdjacentEndpointPairOuter_rightIntegralSum_eq_fullRightEdge_of_integrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ}
    (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hint :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ F.c) :
    explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
            f ((ypair.y₀, ypair.y₁), F.c))
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
        f ((-T, T), F.c) := by
  let ys : List ℝ := explicitFormulaRectangleSortedYEndpoints T ρ
  let n : ℕ := ys.length - 1
  let a : ℕ → ℝ := explicitFormulaRectangleSortedYEndpointAt T ρ
  have hfirst :
      a 0 = -T := by
    have h0 : 0 < ys.length :=
      explicitFormulaRectangleSortedYEndpoints_length_pos T ρ
    calc
      a 0 =
          ys.get ⟨0, h0⟩ := by
        exact explicitFormulaRectangleSortedYEndpointAt_of_lt T ρ h0
      _ = -T := by
        exact
          explicitFormulaRectangleSortedYEndpoints_first_eq_outerLower
            F hT_nonneg hρ hclosed
  have hlast :
      a n = T := by
    have hlast_lt :
        ys.length - 1 < ys.length :=
      Nat.sub_lt
        (explicitFormulaRectangleSortedYEndpoints_length_pos T ρ)
        Nat.zero_lt_one
    calc
      a n =
          ys.get ⟨ys.length - 1, hlast_lt⟩ := by
        exact explicitFormulaRectangleSortedYEndpointAt_of_lt T ρ hlast_lt
      _ = T := by
        exact
          explicitFormulaRectangleSortedYEndpoints_last_eq_outerUpper
            F hT_nonneg hρ hclosed
  have htelescope :
      explicitFormulaRectangleListSum
          (fun i : Fin n =>
            Complex.I •
              ∫ y : ℝ in a i.1..a (i.1 + 1),
                zetaCompletedExplicitFormulaContourIntegrand f
                  ((F.c : ℂ) + y * Complex.I))
          (List.ofFn (fun i : Fin n => i)) =
        Complex.I •
          ∫ y : ℝ in a 0..a n,
            zetaCompletedExplicitFormulaContourIntegrand f
              ((F.c : ℂ) + y * Complex.I) :=
    explicitFormulaRectangleListSum_ofFn_verticalIntegral_adjacent
      f F.c a hint
  calc
    explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
            f ((ypair.y₀, ypair.y₁), F.c))
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
        explicitFormulaRectangleListSum
          (fun i : Fin n =>
            Complex.I •
              ∫ y : ℝ in a i.1..a (i.1 + 1),
                zetaCompletedExplicitFormulaContourIntegrand f
                  ((F.c : ℂ) + y * Complex.I))
          (List.ofFn (fun i : Fin n => i)) := by
      rfl
    _ =
        Complex.I •
          ∫ y : ℝ in a 0..a n,
            zetaCompletedExplicitFormulaContourIntegrand f
              ((F.c : ℂ) + y * Complex.I) := by
      exact htelescope
    _ =
        Complex.I •
          ∫ y : ℝ in (-T)..T,
            zetaCompletedExplicitFormulaContourIntegrand f
              ((F.c : ℂ) + y * Complex.I) := by
      exact
        congrArg
          (fun endpoints : ℝ × ℝ =>
            Complex.I •
              ∫ y : ℝ in endpoints.1..endpoints.2,
                zetaCompletedExplicitFormulaContourIntegrand f
                  ((F.c : ℂ) + y * Complex.I))
          (Prod.ext hfirst hlast)
    _ =
        explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
          f ((-T, T), F.c) := by
      rfl

/-- The sorted vertical subdivision assembles to a full left vertical endpoint-data edge
once interval-integrability on the sorted adjacent subintervals is supplied. -/
theorem explicitFormulaRectangleYAdjacentEndpointPairOuter_leftIntegralSum_eq_fullLeftEdge_of_integrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ}
    (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hint :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ (1 - F.c)) :
    explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
            f ((ypair.y₀, ypair.y₁), 1 - F.c))
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
        f ((-T, T), 1 - F.c) := by
  let ys : List ℝ := explicitFormulaRectangleSortedYEndpoints T ρ
  let n : ℕ := ys.length - 1
  let a : ℕ → ℝ := explicitFormulaRectangleSortedYEndpointAt T ρ
  have hfirst :
      a 0 = -T := by
    have h0 : 0 < ys.length :=
      explicitFormulaRectangleSortedYEndpoints_length_pos T ρ
    calc
      a 0 =
          ys.get ⟨0, h0⟩ := by
        exact explicitFormulaRectangleSortedYEndpointAt_of_lt T ρ h0
      _ = -T := by
        exact
          explicitFormulaRectangleSortedYEndpoints_first_eq_outerLower
            F hT_nonneg hρ hclosed
  have hlast :
      a n = T := by
    have hlast_lt :
        ys.length - 1 < ys.length :=
      Nat.sub_lt
        (explicitFormulaRectangleSortedYEndpoints_length_pos T ρ)
        Nat.zero_lt_one
    calc
      a n =
          ys.get ⟨ys.length - 1, hlast_lt⟩ := by
        exact explicitFormulaRectangleSortedYEndpointAt_of_lt T ρ hlast_lt
      _ = T := by
        exact
          explicitFormulaRectangleSortedYEndpoints_last_eq_outerUpper
            F hT_nonneg hρ hclosed
  have htelescope :
      explicitFormulaRectangleListSum
          (fun i : Fin n =>
            Complex.I •
              ∫ y : ℝ in a i.1..a (i.1 + 1),
                zetaCompletedExplicitFormulaContourIntegrand f
                  (((1 - F.c : ℝ) : ℂ) + y * Complex.I))
          (List.ofFn (fun i : Fin n => i)) =
        Complex.I •
          ∫ y : ℝ in a 0..a n,
            zetaCompletedExplicitFormulaContourIntegrand f
              (((1 - F.c : ℝ) : ℂ) + y * Complex.I) :=
    explicitFormulaRectangleListSum_ofFn_verticalIntegral_adjacent
      f (1 - F.c) a hint
  calc
    explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
            f ((ypair.y₀, ypair.y₁), 1 - F.c))
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
        explicitFormulaRectangleListSum
          (fun i : Fin n =>
            Complex.I •
              ∫ y : ℝ in a i.1..a (i.1 + 1),
                zetaCompletedExplicitFormulaContourIntegrand f
                  (((1 - F.c : ℝ) : ℂ) + y * Complex.I))
          (List.ofFn (fun i : Fin n => i)) := by
      rfl
    _ =
        Complex.I •
          ∫ y : ℝ in a 0..a n,
            zetaCompletedExplicitFormulaContourIntegrand f
              (((1 - F.c : ℝ) : ℂ) + y * Complex.I) := by
      exact htelescope
    _ =
        Complex.I •
          ∫ y : ℝ in (-T)..T,
            zetaCompletedExplicitFormulaContourIntegrand f
              (((1 - F.c : ℝ) : ℂ) + y * Complex.I) := by
      exact
        congrArg
          (fun endpoints : ℝ × ℝ =>
            Complex.I •
              ∫ y : ℝ in endpoints.1..endpoints.2,
                zetaCompletedExplicitFormulaContourIntegrand f
                  (((1 - F.c : ℝ) : ℂ) + y * Complex.I))
          (Prod.ext hfirst hlast)
    _ =
        explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
          f ((-T, T), 1 - F.c) := by
      rfl

/-- The sorted vertical subdivision assembles to the full right outer endpoint-data
edge. -/
theorem explicitFormulaRectangleYAdjacentEndpointPairOuter_rightIntegralSum_eq_fullRightEdge_core
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hint :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ F.c) :
    explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
            f ((ypair.y₀, ypair.y₁), F.c))
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
        f ((-T, T), F.c) := by
  exact
    explicitFormulaRectangleYAdjacentEndpointPairOuter_rightIntegralSum_eq_fullRightEdge_of_integrable
      f F hT_nonneg hρ hclosed hint

/-- The sorted vertical subdivision assembles to the full left outer endpoint-data
edge. -/
theorem explicitFormulaRectangleYAdjacentEndpointPairOuter_leftIntegralSum_eq_fullLeftEdge_core
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hint :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ (1 - F.c)) :
    explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
            f ((ypair.y₀, ypair.y₁), 1 - F.c))
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
        f ((-T, T), 1 - F.c) := by
  exact
    explicitFormulaRectangleYAdjacentEndpointPairOuter_leftIntegralSum_eq_fullLeftEdge_of_integrable
      f F hT_nonneg hρ hclosed hint

/-- The sorted vertical subdivision of the outer rectangle assembles to the two full
vertical endpoint-data edges before line-integral normalization. -/
theorem explicitFormulaRectangleYAdjacentEndpointPairOuter_verticalIntegralSums_eq_fullEdges
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hright :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ F.c)
    (hleft :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ (1 - F.c)) :
    (explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
            f ((ypair.y₀, ypair.y₁), F.c))
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
        f ((-T, T), F.c)) ∧
    (explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
            f ((ypair.y₀, ypair.y₁), 1 - F.c))
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
        f ((-T, T), 1 - F.c)) := by
  exact
    And.intro
      (explicitFormulaRectangleYAdjacentEndpointPairOuter_rightIntegralSum_eq_fullRightEdge_core
        f F hT_nonneg hρ hclosed hright)
      (explicitFormulaRectangleYAdjacentEndpointPairOuter_leftIntegralSum_eq_fullLeftEdge_core
        f F hT_nonneg hρ hclosed hleft)

/-- The sorted vertical subdivision of the outer rectangle assembles to the full
right endpoint-data edge before line-integral normalization. -/
theorem explicitFormulaRectangleYAdjacentEndpointPairOuter_rightIntegralSum_eq_fullRightEdge
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
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
          explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
            f ((ypair.y₀, ypair.y₁), F.c))
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
        f ((-T, T), F.c) := by
  exact
    (explicitFormulaRectangleYAdjacentEndpointPairOuter_verticalIntegralSums_eq_fullEdges
      f F hT_nonneg hρ hclosed hright hleft).1

/-- The sorted vertical subdivision of the outer rectangle assembles to the full
left endpoint-data edge before line-integral normalization. -/
theorem explicitFormulaRectangleYAdjacentEndpointPairOuter_leftIntegralSum_eq_fullLeftEdge
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
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
          explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
            f ((ypair.y₀, ypair.y₁), 1 - F.c))
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
        f ((-T, T), 1 - F.c) := by
  exact
    (explicitFormulaRectangleYAdjacentEndpointPairOuter_verticalIntegralSums_eq_fullEdges
      f F hT_nonneg hρ hclosed hright hleft).2

/-- The full vertical endpoint-data edges have the same normalization as the named
vertical line integrals. -/
theorem explicitFormulaRectangleOuterVerticalEndpointDataEdgeIntegrals_eq_lineIntegrals_mul_I
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) {T : ℝ}
    (hT_nonneg : 0 ≤ T) :
    (explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
        f ((-T, T), F.c) =
      zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I) ∧
    (explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
        f ((-T, T), 1 - F.c) =
      zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I) := by
  constructor
  · calc
      explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
          f ((-T, T), F.c) =
          Complex.I • zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) := by
        exact
          explicitFormulaRectangleOuterRightEndpointDataEdgeIntegral_eq_rightLineIntegral_smul
            f F hT_nonneg
      _ =
          zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I := by
        exact
          explicitFormulaRectangle_complexI_smul_eq_mul_right
            (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T))
  · calc
      explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
          f ((-T, T), 1 - F.c) =
          Complex.I • zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) := by
        exact
          explicitFormulaRectangleOuterLeftEndpointDataEdgeIntegral_eq_leftLineIntegral_smul
            f F hT_nonneg
      _ =
          zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I := by
        exact
          explicitFormulaRectangle_complexI_smul_eq_mul_right
            (zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T))

/-- The full right endpoint-data edge has the same normalization as the named right
line integral. -/
theorem explicitFormulaRectangleOuterRightEndpointDataEdgeIntegral_eq_rightLineIntegral_mul_I
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) {T : ℝ}
    (hT_nonneg : 0 ≤ T) :
    explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
        f ((-T, T), F.c) =
      zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I := by
  exact
    (explicitFormulaRectangleOuterVerticalEndpointDataEdgeIntegrals_eq_lineIntegrals_mul_I
      f F hT_nonneg).1

/-- The full left endpoint-data edge has the same normalization as the named left line
integral. -/
theorem explicitFormulaRectangleOuterLeftEndpointDataEdgeIntegral_eq_leftLineIntegral_mul_I
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) {T : ℝ}
    (hT_nonneg : 0 ≤ T) :
    explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
        f ((-T, T), 1 - F.c) =
      zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I := by
  exact
    (explicitFormulaRectangleOuterVerticalEndpointDataEdgeIntegrals_eq_lineIntegrals_mul_I
      f F hT_nonneg).2

/-- The sorted vertical subdivision of the outer rectangle assembles to the right
tangent side. -/
theorem explicitFormulaRectangleYAdjacentEndpointPairOuter_rightIntegralSum_eq_outerRightSide
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
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
          explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
            f ((ypair.y₀, ypair.y₁), F.c))
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I := by
  calc
    explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
            f ((ypair.y₀, ypair.y₁), F.c))
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
        explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
          f ((-T, T), F.c) := by
      exact
        explicitFormulaRectangleYAdjacentEndpointPairOuter_rightIntegralSum_eq_fullRightEdge
          f F hT_nonneg hρ hclosed hright hleft
    _ = zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I := by
      exact
        explicitFormulaRectangleOuterRightEndpointDataEdgeIntegral_eq_rightLineIntegral_mul_I
          f F hT_nonneg

/-- The sorted vertical subdivision of the outer rectangle assembles to the left
tangent side. -/
theorem explicitFormulaRectangleYAdjacentEndpointPairOuter_leftIntegralSum_eq_outerLeftSide
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
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
          explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
            f ((ypair.y₀, ypair.y₁), 1 - F.c))
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I := by
  calc
    explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
            f ((ypair.y₀, ypair.y₁), 1 - F.c))
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
        explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
          f ((-T, T), 1 - F.c) := by
      exact
        explicitFormulaRectangleYAdjacentEndpointPairOuter_leftIntegralSum_eq_fullLeftEdge
          f F hT_nonneg hρ hclosed hright hleft
    _ = zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I := by
      exact
        explicitFormulaRectangleOuterLeftEndpointDataEdgeIntegral_eq_leftLineIntegral_mul_I
          f F hT_nonneg

/-- The right outer vertical endpoint-data slices over the sorted vertical subdivision
assemble to the right side of the outer rectangle with the tangent factor. -/
theorem explicitFormulaRectangleVerticalOuterRightSliceContributionSum_eq_outerRightSide
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
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
          explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
            f ((ypair.y₀, ypair.y₁), F.c))
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I := by
  exact
    explicitFormulaRectangleYAdjacentEndpointPairOuter_rightIntegralSum_eq_outerRightSide
      f F hT_nonneg hρ hclosed hright hleft

/-- The left outer vertical endpoint-data slices over the sorted vertical subdivision
assemble to the left side of the outer rectangle with the tangent factor. -/
theorem explicitFormulaRectangleVerticalOuterLeftSliceContributionSum_eq_outerLeftSide
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
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
          explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
            f ((ypair.y₀, ypair.y₁), 1 - F.c))
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I := by
  exact
    explicitFormulaRectangleYAdjacentEndpointPairOuter_leftIntegralSum_eq_outerLeftSide
      f F hT_nonneg hρ hclosed hright hleft

/-- The right raw-hole vertical slices over the sorted vertical subdivision assemble to
the grouped right sides of the raw square holes. -/
theorem explicitFormulaRectangleVerticalHoleRightSliceContributionSum_eq_holeRightSide
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
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ρ + ρ < dist a b) :
    explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
            if _hspan :
                explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
                  ρ ypair a then
              explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
            else
              0)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum f T ρ := by
  let S : Finset ℂ := explicitFormulaRectangleRawSingularCoordinates T
  calc
    explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          ∑ a in S,
            if _hspan :
                explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
                  ρ ypair a then
              explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
            else
              0)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
        ∑ a in S,
          explicitFormulaRectangleListSum
            (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
              if _hspan :
                  explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
                    ρ ypair a then
                explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
                  ((ypair.y₀, ypair.y₁),
                    (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
              else
                0)
            (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) := by
      exact
        explicitFormulaRectangleVerticalHoleRightSliceContributionSum_groupedByRawCoordinate
          f T ρ
    _ =
        ∑ a in S,
          explicitFormulaRectangleBoxRightEdgeIntegral f
            (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ρ a) := by
      exact Finset.sum_congr rfl
        (fun a ha =>
          explicitFormulaRectangleYAdjacentEndpointPairSubspanRawHole_rightIntegralSum_eq_rawBoxRight
            f F hT_nonneg hρ hclosed hsep ha (hrightHole a ha))
    _ =
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum f T ρ := by
      rfl

/-- The left raw-hole vertical slices over the sorted vertical subdivision assemble to
the grouped left sides of the raw square holes. -/
theorem explicitFormulaRectangleVerticalHoleLeftSliceContributionSum_eq_holeLeftSide
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
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
          ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
            if _hspan :
                explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
                  ρ ypair a then
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
            else
              0)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum f T ρ := by
  let S : Finset ℂ := explicitFormulaRectangleRawSingularCoordinates T
  calc
    explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          ∑ a in S,
            if _hspan :
                explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
                  ρ ypair a then
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
            else
              0)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
        ∑ a in S,
          explicitFormulaRectangleListSum
            (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
              if _hspan :
                  explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
                    ρ ypair a then
                explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
                  ((ypair.y₀, ypair.y₁),
                    (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
              else
                0)
            (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) := by
      exact
        explicitFormulaRectangleVerticalHoleLeftSliceContributionSum_groupedByRawCoordinate
          f T ρ
    _ =
        ∑ a in S,
          explicitFormulaRectangleBoxLeftEdgeIntegral f
            (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ρ a) := by
      exact Finset.sum_congr rfl
        (fun a ha =>
          explicitFormulaRectangleYAdjacentEndpointPairSubspanRawHole_leftIntegralSum_eq_rawBoxLeft
            f F hT_nonneg hρ hclosed hsep ha (hleftHole a ha))
    _ =
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum f T ρ := by
      rfl

/-- A raw-hole vertical slice is the right raw-hole slice minus the left raw-hole slice
at the same sorted vertical span. -/
theorem explicitFormulaRectangleVerticalHoleSliceContribution_eq_right_sub_left
    (f : ZetaAdmissibleFunction) (T ρ : ℝ)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :
    explicitFormulaRectangleVerticalHoleSliceContribution f T ρ ypair =
      (∑ a in explicitFormulaRectangleRawSingularCoordinates T,
        if _hspan :
            explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
              ρ ypair a then
          explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
            ((ypair.y₀, ypair.y₁),
              (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
        else
          0) -
        (∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
                ρ ypair a then
            explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
              ((ypair.y₀, ypair.y₁),
                (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
          else
            0) := by
  have hpoint :
      ∀ a : ℂ,
        (if _hspan :
            explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
              ρ ypair a then
          explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
              ((ypair.y₀, ypair.y₁),
                (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re) -
            explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
              ((ypair.y₀, ypair.y₁),
                (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
        else
          0) =
          (if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
                ρ ypair a then
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
              ((ypair.y₀, ypair.y₁),
                (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
          else
            0) -
            (if _hspan :
                explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
                  ρ ypair a then
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
            else
              0) := by
    intro a
    by_cases hspan :
        explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole ρ ypair a
    · rfl
    · exact (sub_zero (0 : ℂ)).symm
  calc
    explicitFormulaRectangleVerticalHoleSliceContribution f T ρ ypair =
        ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          ((if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
                ρ ypair a then
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
          else
            0) -
            (if _hspan :
                explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
                  ρ ypair a then
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
            else
              0)) := by
      exact Finset.sum_congr rfl (fun a _ha => hpoint a)
    _ =
        (∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          if _hspan :
              explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
                ρ ypair a then
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
              ((ypair.y₀, ypair.y₁),
                (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
          else
            0) -
          (∑ a in explicitFormulaRectangleRawSingularCoordinates T,
            if _hspan :
                explicitFormulaRectangleYAdjacentEndpointPairSubspanOfRawHole
                  ρ ypair a then
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
                ((ypair.y₀, ypair.y₁),
                  (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
            else
              0) := by
      exact Finset.sum_sub_distrib

/-- A fixed-column selected vertical contribution is its selected right-edge scan minus
its selected left-edge scan. -/

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
