import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part20Parts.Part20_12

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

set_option maxHeartbeats 800000

theorem explicitFormulaRectangle_horizontalGuardedSub_eq_guarded_sub
    {P : Prop} [Decidable P] (lower upper : ℂ) :
    (if _h : P then lower - upper else 0) =
      (if _h : P then lower else 0) - (if _h : P then upper else 0) := by
  match inferInstanceAs (Decidable P) with
  | isTrue h =>
      exact Eq.trans (if_pos h)
        (congrArg₂ HSub.hSub (if_pos h).symm (if_pos h).symm)
  | isFalse h =>
      exact Eq.trans (if_neg h)
        (Eq.trans (sub_zero (0 : ℂ)).symm
          (congrArg₂ HSub.hSub (if_neg h).symm (if_neg h).symm))

theorem explicitFormulaRectangleXAdjacentEndpointPair_totalBottomHorizontalListSum_eq_ofFn
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (y : ℝ) :
    let n : ℕ := (explicitFormulaRectangleSortedXEndpoints F T ρ).length - 1
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
            f ((xpair.x₀, xpair.x₁), y))
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
      explicitFormulaRectangleListSum
        (fun i : Fin n =>
          explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
            ((explicitFormulaRectangleSortedXEndpointAt F T ρ i.1,
              explicitFormulaRectangleSortedXEndpointAt F T ρ (i.1 + 1)), y))
        (List.ofFn (fun i : Fin n => i)) := by
  let n : ℕ := (explicitFormulaRectangleSortedXEndpoints F T ρ).length - 1
  have hlist :
      explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
              f ((xpair.x₀, xpair.x₁), y))
          (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
        explicitFormulaRectangleListSum
          (fun i : Fin n =>
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
              (((explicitFormulaRectangleXAdjacentEndpointPairAt F T ρ i).x₀,
                (explicitFormulaRectangleXAdjacentEndpointPairAt F T ρ i).x₁), y))
          (List.ofFn (fun i : Fin n => i)) :=
    Eq.trans
      (congrArg
        (fun xs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) =>
          explicitFormulaRectangleListSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                f ((xpair.x₀, xpair.x₁), y))
            xs)
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints_eq_ofFn_pairAt
          F T ρ))
      (explicitFormulaRectangleListSum_ofFn_comp
        (fun i : Fin n => explicitFormulaRectangleXAdjacentEndpointPairAt F T ρ i)
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
            f ((xpair.x₀, xpair.x₁), y)))
  have hcoords :
      explicitFormulaRectangleListSum
          (fun i : Fin n =>
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
              (((explicitFormulaRectangleXAdjacentEndpointPairAt F T ρ i).x₀,
                (explicitFormulaRectangleXAdjacentEndpointPairAt F T ρ i).x₁), y))
          (List.ofFn (fun i : Fin n => i)) =
        explicitFormulaRectangleListSum
          (fun i : Fin n =>
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
              ((explicitFormulaRectangleSortedXEndpointAt F T ρ i.1,
                explicitFormulaRectangleSortedXEndpointAt F T ρ (i.1 + 1)), y))
          (List.ofFn (fun i : Fin n => i)) :=
    congrArg
      (fun g : Fin n → ℂ =>
        explicitFormulaRectangleListSum g (List.ofFn (fun i : Fin n => i)))
      (funext
        (fun i =>
          congrArg
            (fun endpoints : ℝ × ℝ =>
              explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
                (endpoints, y))
            (Prod.ext
              (explicitFormulaRectangleXAdjacentEndpointPairAt_x₀ F T ρ i)
              (explicitFormulaRectangleXAdjacentEndpointPairAt_x₁ F T ρ i))))
  exact Eq.trans hlist hcoords

theorem explicitFormulaRectangleXAdjacentEndpointPair_totalTopHorizontalListSum_eq_ofFn
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (y : ℝ) :
    let n : ℕ := (explicitFormulaRectangleSortedXEndpoints F T ρ).length - 1
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
            f ((xpair.x₀, xpair.x₁), y))
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
      explicitFormulaRectangleListSum
        (fun i : Fin n =>
          explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
            ((explicitFormulaRectangleSortedXEndpointAt F T ρ i.1,
              explicitFormulaRectangleSortedXEndpointAt F T ρ (i.1 + 1)), y))
        (List.ofFn (fun i : Fin n => i)) := by
  let n : ℕ := (explicitFormulaRectangleSortedXEndpoints F T ρ).length - 1
  have hlist :
      explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
              f ((xpair.x₀, xpair.x₁), y))
          (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
        explicitFormulaRectangleListSum
          (fun i : Fin n =>
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
              (((explicitFormulaRectangleXAdjacentEndpointPairAt F T ρ i).x₀,
                (explicitFormulaRectangleXAdjacentEndpointPairAt F T ρ i).x₁), y))
          (List.ofFn (fun i : Fin n => i)) :=
    Eq.trans
      (congrArg
        (fun xs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) =>
          explicitFormulaRectangleListSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                f ((xpair.x₀, xpair.x₁), y))
            xs)
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints_eq_ofFn_pairAt
          F T ρ))
      (explicitFormulaRectangleListSum_ofFn_comp
        (fun i : Fin n => explicitFormulaRectangleXAdjacentEndpointPairAt F T ρ i)
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
            f ((xpair.x₀, xpair.x₁), y)))
  have hcoords :
      explicitFormulaRectangleListSum
          (fun i : Fin n =>
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
              (((explicitFormulaRectangleXAdjacentEndpointPairAt F T ρ i).x₀,
                (explicitFormulaRectangleXAdjacentEndpointPairAt F T ρ i).x₁), y))
          (List.ofFn (fun i : Fin n => i)) =
        explicitFormulaRectangleListSum
          (fun i : Fin n =>
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
              ((explicitFormulaRectangleSortedXEndpointAt F T ρ i.1,
                explicitFormulaRectangleSortedXEndpointAt F T ρ (i.1 + 1)), y))
          (List.ofFn (fun i : Fin n => i)) :=
    congrArg
      (fun g : Fin n → ℂ =>
        explicitFormulaRectangleListSum g (List.ofFn (fun i : Fin n => i)))
      (funext
        (fun i =>
          congrArg
            (fun endpoints : ℝ × ℝ =>
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
                (endpoints, y))
            (Prod.ext
              (explicitFormulaRectangleXAdjacentEndpointPairAt_x₀ F T ρ i)
              (explicitFormulaRectangleXAdjacentEndpointPairAt_x₁ F T ρ i))))
  exact Eq.trans hlist hcoords

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
            ∫ x : ℝ in (a i.1)..(a (i.1 + 1)),
              zetaCompletedExplicitFormulaContourIntegrand f
                (x + ((-T : ℝ) : ℂ) * Complex.I))
          (List.ofFn (fun i : Fin n => i)) =
        ∫ x : ℝ in (a 0)..(a n),
          zetaCompletedExplicitFormulaContourIntegrand f
            (x + ((-T : ℝ) : ℂ) * Complex.I) :=
    explicitFormulaRectangleListSum_ofFn_horizontalIntegral_adjacent
      f (-T) a hint
  have hleftEndpoint :
      (∫ x : ℝ in (a 0)..(a n),
          zetaCompletedExplicitFormulaContourIntegrand f
            (x + ((-T : ℝ) : ℂ) * Complex.I)) =
        ∫ x : ℝ in (1 - F.c)..(a n),
          zetaCompletedExplicitFormulaContourIntegrand f
            (x + ((-T : ℝ) : ℂ) * Complex.I) :=
    congrArg
      (fun x0 : ℝ =>
        ∫ x : ℝ in x0..(a n),
          zetaCompletedExplicitFormulaContourIntegrand f
            (x + ((-T : ℝ) : ℂ) * Complex.I))
      hfirst
  have hrightEndpoint :
      (∫ x : ℝ in (1 - F.c)..(a n),
          zetaCompletedExplicitFormulaContourIntegrand f
            (x + ((-T : ℝ) : ℂ) * Complex.I)) =
        ∫ x : ℝ in (1 - F.c)..F.c,
          zetaCompletedExplicitFormulaContourIntegrand f
            (x + ((-T : ℝ) : ℂ) * Complex.I) :=
    congrArg
      (fun x1 : ℝ =>
        ∫ x : ℝ in (1 - F.c)..x1,
          zetaCompletedExplicitFormulaContourIntegrand f
            (x + ((-T : ℝ) : ℂ) * Complex.I))
      hlast
  calc
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
            f ((xpair.x₀, xpair.x₁), -T))
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
        explicitFormulaRectangleListSum
          (fun i : Fin n =>
            ∫ x : ℝ in (a i.1)..(a (i.1 + 1)),
              zetaCompletedExplicitFormulaContourIntegrand f
                (x + ((-T : ℝ) : ℂ) * Complex.I))
          (List.ofFn (fun i : Fin n => i)) := by
      exact
        explicitFormulaRectangleXAdjacentEndpointPair_totalBottomHorizontalListSum_eq_ofFn
          f F (-T)
    _ =
        ∫ x : ℝ in (a 0)..(a n),
          zetaCompletedExplicitFormulaContourIntegrand f
            (x + ((-T : ℝ) : ℂ) * Complex.I) := by
      exact htelescope
    _ =
        ∫ x : ℝ in (1 - F.c)..F.c,
          zetaCompletedExplicitFormulaContourIntegrand f
            (x + ((-T : ℝ) : ℂ) * Complex.I) := by
      exact Eq.trans hleftEndpoint hrightEndpoint
    _ =
        explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
          f ((1 - F.c, F.c), -T) := by
      exact Eq.refl _

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
            ∫ x : ℝ in (a i.1)..(a (i.1 + 1)),
              zetaCompletedExplicitFormulaContourIntegrand f
                (x + (T : ℂ) * Complex.I))
          (List.ofFn (fun i : Fin n => i)) =
        ∫ x : ℝ in (a 0)..(a n),
          zetaCompletedExplicitFormulaContourIntegrand f
            (x + (T : ℂ) * Complex.I) :=
    explicitFormulaRectangleListSum_ofFn_horizontalIntegral_adjacent
      f T a hint
  have hleftEndpoint :
      (∫ x : ℝ in (a 0)..(a n),
          zetaCompletedExplicitFormulaContourIntegrand f
            (x + (T : ℂ) * Complex.I)) =
        ∫ x : ℝ in (1 - F.c)..(a n),
          zetaCompletedExplicitFormulaContourIntegrand f
            (x + (T : ℂ) * Complex.I) :=
    congrArg
      (fun x0 : ℝ =>
        ∫ x : ℝ in x0..(a n),
          zetaCompletedExplicitFormulaContourIntegrand f
            (x + (T : ℂ) * Complex.I))
      hfirst
  have hrightEndpoint :
      (∫ x : ℝ in (1 - F.c)..(a n),
          zetaCompletedExplicitFormulaContourIntegrand f
            (x + (T : ℂ) * Complex.I)) =
        ∫ x : ℝ in (1 - F.c)..F.c,
          zetaCompletedExplicitFormulaContourIntegrand f
            (x + (T : ℂ) * Complex.I) :=
    congrArg
      (fun x1 : ℝ =>
        ∫ x : ℝ in (1 - F.c)..x1,
          zetaCompletedExplicitFormulaContourIntegrand f
            (x + (T : ℂ) * Complex.I))
      hlast
  calc
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
            f ((xpair.x₀, xpair.x₁), T))
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
        explicitFormulaRectangleListSum
          (fun i : Fin n =>
            ∫ x : ℝ in (a i.1)..(a (i.1 + 1)),
              zetaCompletedExplicitFormulaContourIntegrand f
                (x + (T : ℂ) * Complex.I))
          (List.ofFn (fun i : Fin n => i)) := by
      exact
        explicitFormulaRectangleXAdjacentEndpointPair_totalTopHorizontalListSum_eq_ofFn
          f F T
    _ =
        ∫ x : ℝ in (a 0)..(a n),
          zetaCompletedExplicitFormulaContourIntegrand f
            (x + (T : ℂ) * Complex.I) := by
      exact htelescope
    _ =
        ∫ x : ℝ in (1 - F.c)..F.c,
          zetaCompletedExplicitFormulaContourIntegrand f
            (x + (T : ℂ) * Complex.I) := by
      exact Eq.trans hleftEndpoint hrightEndpoint
    _ =
        explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
          f ((1 - F.c, F.c), T) := by
      exact Eq.refl _

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
    (hbottomHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ρ + ρ < dist a b) :
    ∑ z in (explicitFormulaRectangleRawSingularCoordinates T).attach,
        explicitFormulaRectangleRawHoleXBlockBottomContribution f F hρ z.1 z.2 =
      explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum f T ρ := by
  let S : Finset ℂ := explicitFormulaRectangleRawSingularCoordinates T
  calc
    ∑ z in S.attach,
        explicitFormulaRectangleRawHoleXBlockBottomContribution f F hρ z.1 z.2 =
        ∑ z in S.attach,
          explicitFormulaRectangleBoxBottomEdgeIntegral f
            (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ρ z.1) := by
      exact Finset.sum_congr (Eq.refl S.attach)
        (fun z _hz =>
          explicitFormulaRectangleRawHoleXBlockBottomContribution_eq_rawBoxBottom_of_integrable
            f F hρ z.2 (hbottomHole z.1 z.2))
    _ =
        ∑ a in S,
          explicitFormulaRectangleBoxBottomEdgeIntegral f
            (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ρ a) := by
      exact Finset.sum_attach S
        (fun a => explicitFormulaRectangleBoxBottomEdgeIntegral f
          (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ρ a))
    _ =
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum f T ρ := by
      exact Eq.refl _

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
    ∑ z in (explicitFormulaRectangleRawSingularCoordinates T).attach,
        explicitFormulaRectangleRawHoleXBlockTopContribution f F hρ z.1 z.2 =
      explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum f T ρ := by
  let S : Finset ℂ := explicitFormulaRectangleRawSingularCoordinates T
  calc
    ∑ z in S.attach,
        explicitFormulaRectangleRawHoleXBlockTopContribution f F hρ z.1 z.2 =
        ∑ z in S.attach,
          explicitFormulaRectangleBoxTopEdgeIntegral f
            (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ρ z.1) := by
      exact Finset.sum_congr (Eq.refl S.attach)
        (fun z _hz =>
          explicitFormulaRectangleRawHoleXBlockTopContribution_eq_rawBoxTop_of_integrable
            f F hρ z.2 (htopHole z.1 z.2))
    _ =
        ∑ a in S,
          explicitFormulaRectangleBoxTopEdgeIntegral f
            (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ρ a) := by
      exact Finset.sum_attach S
        (fun a => explicitFormulaRectangleBoxTopEdgeIntegral f
          (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ρ a))
    _ =
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum f T ρ := by
      exact Eq.refl _

/-- The filtered bottom raw-hole horizontal slices over the sorted horizontal subdivision
assemble to the grouped bottom sides of the raw square holes. -/
theorem explicitFormulaRectangleHorizontalHoleBottomFilteredSliceContributionSum_eq_holeBottomSide
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hbottomHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
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
  let filteredByRaw : ℂ → ℂ :=
    fun a =>
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
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)
  have hgroup :
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
        ∑ a in S, filteredByRaw a :=
    explicitFormulaRectangleHorizontalHoleBottomSliceContributionSum_groupedByRawCoordinate
      f F T ρ
  have hpoint :
      (∑ a in S, filteredByRaw a) =
        ∑ a in S,
          explicitFormulaRectangleBoxBottomEdgeIntegral f
            (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ρ a) := by
    exact Finset.sum_congr (Eq.refl S)
      (fun a ha =>
        let hspan :=
          explicitFormulaRectangleXAdjacentEndpointPairSubspanRawHole_listSum_eq_subrange
            (F := F) (T := T) (ρ := ρ) (a := a) hρ ha
            (fun edge : ExplicitFormulaRectangleHorizontalEndpointDataEdge =>
              explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f edge)
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im
        let hblock :
            explicitFormulaRectangleListSum
              (fun i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a) =>
                explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
                  ((explicitFormulaRectangleSortedXEndpointAt F T ρ
                      (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a + i.1),
                    explicitFormulaRectangleSortedXEndpointAt F T ρ
                      (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a + (i.1 + 1))),
                    (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im))
              (List.ofFn
                (fun i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a) => i)) =
              explicitFormulaRectangleRawHoleXBlockBottomContribution f F hρ a ha :=
          (explicitFormulaRectangleRawHoleXBlockBottomContribution_eq_generatedEndpointListSum
            f F hρ ha).symm
        let hraw :
            explicitFormulaRectangleRawHoleXBlockBottomContribution f F hρ a ha =
              explicitFormulaRectangleBoxBottomEdgeIntegral f
                (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ρ a) :=
          explicitFormulaRectangleRawHoleXBlockBottomContribution_eq_rawBoxBottom_of_integrable
            f F hρ ha (hbottomHole a ha)
        Eq.trans hspan (Eq.trans hblock hraw))
  calc
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
        ∑ a in S, filteredByRaw a := by
      exact hgroup
    _ =
        ∑ a in S,
          explicitFormulaRectangleBoxBottomEdgeIntegral f
            (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ρ a) := by
      exact hpoint
    _ =
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum f T ρ := by
      exact Eq.refl _

/-- The filtered top raw-hole horizontal slices over the sorted horizontal subdivision
assemble to the grouped top sides of the raw square holes. -/
theorem explicitFormulaRectangleHorizontalHoleTopFilteredSliceContributionSum_eq_holeTopSide
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
  let filteredByRaw : ℂ → ℂ :=
    fun a =>
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
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)
  have hgroup :
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
        ∑ a in S, filteredByRaw a :=
    explicitFormulaRectangleHorizontalHoleTopSliceContributionSum_groupedByRawCoordinate
      f F T ρ
  have hpoint :
      (∑ a in S, filteredByRaw a) =
        ∑ a in S,
          explicitFormulaRectangleBoxTopEdgeIntegral f
            (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ρ a) := by
    exact Finset.sum_congr (Eq.refl S)
      (fun a ha =>
        let hspan :=
          explicitFormulaRectangleXAdjacentEndpointPairSubspanRawHole_listSum_eq_subrange
            (F := F) (T := T) (ρ := ρ) (a := a) hρ ha
            (fun edge : ExplicitFormulaRectangleHorizontalEndpointDataEdge =>
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f edge)
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im
        let hblock :
            explicitFormulaRectangleListSum
              (fun i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a) =>
                explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
                  ((explicitFormulaRectangleSortedXEndpointAt F T ρ
                      (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a + i.1),
                    explicitFormulaRectangleSortedXEndpointAt F T ρ
                      (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a + (i.1 + 1))),
                    (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im))
              (List.ofFn
                (fun i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a) => i)) =
              explicitFormulaRectangleRawHoleXBlockTopContribution f F hρ a ha :=
          (explicitFormulaRectangleRawHoleXBlockTopContribution_eq_generatedEndpointListSum
            f F hρ ha).symm
        let hraw :
            explicitFormulaRectangleRawHoleXBlockTopContribution f F hρ a ha =
              explicitFormulaRectangleBoxTopEdgeIntegral f
                (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ρ a) :=
          explicitFormulaRectangleRawHoleXBlockTopContribution_eq_rawBoxTop_of_integrable
            f F hρ ha (htopHole a ha)
        Eq.trans hspan (Eq.trans hblock hraw))
  calc
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
        ∑ a in S, filteredByRaw a := by
      exact hgroup
    _ =
        ∑ a in S,
          explicitFormulaRectangleBoxTopEdgeIntegral f
            (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ρ a) := by
      exact hpoint
    _ =
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum f T ρ := by
      exact Eq.refl _

/-- A generated raw-hole horizontal slice is the bottom raw-hole slice minus the top
raw-hole slice at the same generated horizontal span. -/
theorem explicitFormulaRectangleRawHoleXBlockSliceContribution_eq_bottom_sub_top
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hρ : 0 < ρ)
    (a : ℂ) (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a)) :
    explicitFormulaRectangleRawHoleXBlockSliceContribution f F hρ a ha i =
      explicitFormulaRectangleRawHoleXBlockBottomSliceContribution f F hρ a ha i -
        explicitFormulaRectangleRawHoleXBlockTopSliceContribution f F hρ a ha i := by
  exact Eq.refl _

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
  let S : Finset ℂ := explicitFormulaRectangleRawSingularCoordinates T
  let bottom : ℂ → ℂ :=
    fun a =>
      if _hspan :
          explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a then
        explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
          ((xpair.x₀, xpair.x₁),
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
      else
        0
  let top : ℂ → ℂ :=
    fun a =>
      if _hspan :
          explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a then
        explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
          ((xpair.x₀, xpair.x₁),
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
      else
        0
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
          0) = bottom a - top a := by
    intro a
    exact
      explicitFormulaRectangle_horizontalGuardedSub_eq_guarded_sub
        (P := explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole ρ xpair a)
        (explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
          ((xpair.x₀, xpair.x₁),
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im))
        (explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
          ((xpair.x₀, xpair.x₁),
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im))
  calc
    explicitFormulaRectangleHorizontalHoleSliceContribution f T ρ xpair =
        ∑ a in S, (bottom a - top a) := by
      exact Finset.sum_congr (Eq.refl S) (fun a _ha => hpoint a)
    _ = (∑ a in S, bottom a) - ∑ a in S, top a := by
      exact Finset.sum_sub_distrib

/-- A generated raw-hole horizontal block contribution is the generated bottom block
minus the generated top block. -/
theorem explicitFormulaRectangleRawHoleXBlockContribution_eq_bottom_sub_top
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hρ : 0 < ρ)
    (a : ℂ) (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    explicitFormulaRectangleRawHoleXBlockContribution f F hρ a ha =
      explicitFormulaRectangleRawHoleXBlockBottomContribution f F hρ a ha -
        explicitFormulaRectangleRawHoleXBlockTopContribution f F hρ a ha := by
  let span : ℕ := explicitFormulaRectangleRawHoleXSpanLength F T ρ a
  let bottom : Fin span → ℂ :=
    fun i => explicitFormulaRectangleRawHoleXBlockBottomSliceContribution f F hρ a ha i
  let top : Fin span → ℂ :=
    fun i => explicitFormulaRectangleRawHoleXBlockTopSliceContribution f F hρ a ha i
  have hleft :
      explicitFormulaRectangleRawHoleXBlockContribution f F hρ a ha =
        explicitFormulaRectangleListSum
          (fun i : Fin span => bottom i - top i)
          (List.ofFn (fun i : Fin span => i)) := by
    exact Eq.refl _
  have hsplit :
      explicitFormulaRectangleListSum
          (fun i : Fin span => bottom i - top i)
          (List.ofFn (fun i : Fin span => i)) =
        explicitFormulaRectangleListSum bottom (List.ofFn (fun i : Fin span => i)) -
          explicitFormulaRectangleListSum top (List.ofFn (fun i : Fin span => i)) :=
    explicitFormulaRectangleListSum_sub bottom top (List.ofFn (fun i : Fin span => i))
  exact Eq.trans hleft hsplit

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
