import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part20Parts.Part20_05

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
## Part20 06: SelectedContributionScans
-/

attribute [local instance] Classical.propDecidable

/-- Endpoint data owned by a selected adjacent-pair cell. -/
noncomputable def explicitFormulaRectangleSelectedAdjacentEndpointData
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε)
    (homit : explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair) :
    ExplicitFormulaRectangleRegularGridCellEndpointData F T ε :=
  (({ xpair := xpair
      ypair := ypair
      homit := homit } :
      ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε).toEndpointData)

/-- Horizontal grouped side contribution is additive across appended box lists. -/
theorem explicitFormulaRectangleBoxHorizontalContribution_append
    (f : ZetaAdmissibleFunction)
    (left right : List ExplicitFormulaRectangleEndpointDataBoxEdge) :
    (explicitFormulaRectangleBoxBottomEdgeIntegralSum f (left ++ right) -
        explicitFormulaRectangleBoxTopEdgeIntegralSum f (left ++ right)) =
      (explicitFormulaRectangleBoxBottomEdgeIntegralSum f left -
          explicitFormulaRectangleBoxTopEdgeIntegralSum f left) +
        (explicitFormulaRectangleBoxBottomEdgeIntegralSum f right -
          explicitFormulaRectangleBoxTopEdgeIntegralSum f right) := by
  let bl : ℂ := explicitFormulaRectangleBoxBottomEdgeIntegralSum f left
  let br : ℂ := explicitFormulaRectangleBoxBottomEdgeIntegralSum f right
  let tl : ℂ := explicitFormulaRectangleBoxTopEdgeIntegralSum f left
  let tr : ℂ := explicitFormulaRectangleBoxTopEdgeIntegralSum f right
  have hbottom :
      explicitFormulaRectangleBoxBottomEdgeIntegralSum f (left ++ right) = bl + br :=
    explicitFormulaRectangleBoxBottomEdgeIntegralSum_append f left right
  have htop :
      explicitFormulaRectangleBoxTopEdgeIntegralSum f (left ++ right) = tl + tr :=
    explicitFormulaRectangleBoxTopEdgeIntegralSum_append f left right
  calc
    explicitFormulaRectangleBoxBottomEdgeIntegralSum f (left ++ right) -
        explicitFormulaRectangleBoxTopEdgeIntegralSum f (left ++ right) =
        (bl + br) -
          explicitFormulaRectangleBoxTopEdgeIntegralSum f (left ++ right) := by
      exact congrArg
        (fun z : ℂ =>
          z - explicitFormulaRectangleBoxTopEdgeIntegralSum f (left ++ right))
        hbottom
    _ = (bl + br) - (tl + tr) := by
      exact congrArg (fun z : ℂ => (bl + br) - z) htop
    _ = (bl - tl) + (br - tr) := by
      calc
        (bl + br) - (tl + tr) =
            (bl + br) + -(tl + tr) := by
          exact sub_eq_add_neg (bl + br) (tl + tr)
        _ = (bl + br) + (-tl + -tr) := by
          exact congrArg (fun z : ℂ => (bl + br) + z) (neg_add tl tr)
        _ = bl + (br + (-tl + -tr)) := by
          exact add_assoc bl br (-tl + -tr)
        _ = bl + ((br + -tl) + -tr) := by
          exact congrArg (fun z : ℂ => bl + z) (add_assoc br (-tl) (-tr)).symm
        _ = bl + ((-tl + br) + -tr) := by
          exact congrArg (fun z : ℂ => bl + (z + -tr)) (add_comm br (-tl))
        _ = bl + (-tl + (br + -tr)) := by
          exact congrArg (fun z : ℂ => bl + z) (add_assoc (-tl) br (-tr))
        _ = (bl + -tl) + (br + -tr) := by
          exact (add_assoc bl (-tl) (br + -tr)).symm
        _ = (bl - tl) + (br + -tr) := by
          exact congrArg (fun z : ℂ => z + (br + -tr)) (sub_eq_add_neg bl tl).symm
        _ = (bl - tl) + (br - tr) := by
          exact congrArg (fun z : ℂ => (bl - tl) + z) (sub_eq_add_neg br tr).symm

/-- Vertical grouped side contribution is additive across appended box lists. -/
theorem explicitFormulaRectangleBoxVerticalContribution_append
    (f : ZetaAdmissibleFunction)
    (left right : List ExplicitFormulaRectangleEndpointDataBoxEdge) :
    (explicitFormulaRectangleBoxRightEdgeIntegralSum f (left ++ right) -
        explicitFormulaRectangleBoxLeftEdgeIntegralSum f (left ++ right)) =
      (explicitFormulaRectangleBoxRightEdgeIntegralSum f left -
          explicitFormulaRectangleBoxLeftEdgeIntegralSum f left) +
        (explicitFormulaRectangleBoxRightEdgeIntegralSum f right -
          explicitFormulaRectangleBoxLeftEdgeIntegralSum f right) := by
  let rl : ℂ := explicitFormulaRectangleBoxRightEdgeIntegralSum f left
  let rr : ℂ := explicitFormulaRectangleBoxRightEdgeIntegralSum f right
  let ll : ℂ := explicitFormulaRectangleBoxLeftEdgeIntegralSum f left
  let lr : ℂ := explicitFormulaRectangleBoxLeftEdgeIntegralSum f right
  have hright :
      explicitFormulaRectangleBoxRightEdgeIntegralSum f (left ++ right) = rl + rr :=
    explicitFormulaRectangleBoxRightEdgeIntegralSum_append f left right
  have hleft :
      explicitFormulaRectangleBoxLeftEdgeIntegralSum f (left ++ right) = ll + lr :=
    explicitFormulaRectangleBoxLeftEdgeIntegralSum_append f left right
  calc
    explicitFormulaRectangleBoxRightEdgeIntegralSum f (left ++ right) -
        explicitFormulaRectangleBoxLeftEdgeIntegralSum f (left ++ right) =
        (rl + rr) -
          explicitFormulaRectangleBoxLeftEdgeIntegralSum f (left ++ right) := by
      exact congrArg
        (fun z : ℂ =>
          z - explicitFormulaRectangleBoxLeftEdgeIntegralSum f (left ++ right))
        hright
    _ = (rl + rr) - (ll + lr) := by
      exact congrArg (fun z : ℂ => (rl + rr) - z) hleft
    _ = (rl - ll) + (rr - lr) := by
      calc
        (rl + rr) - (ll + lr) =
            (rl + rr) + -(ll + lr) := by
          exact sub_eq_add_neg (rl + rr) (ll + lr)
        _ = (rl + rr) + (-ll + -lr) := by
          exact congrArg (fun z : ℂ => (rl + rr) + z) (neg_add ll lr)
        _ = rl + (rr + (-ll + -lr)) := by
          exact add_assoc rl rr (-ll + -lr)
        _ = rl + ((rr + -ll) + -lr) := by
          exact congrArg (fun z : ℂ => rl + z) (add_assoc rr (-ll) (-lr)).symm
        _ = rl + ((-ll + rr) + -lr) := by
          exact congrArg (fun z : ℂ => rl + (z + -lr)) (add_comm rr (-ll))
        _ = rl + (-ll + (rr + -lr)) := by
          exact congrArg (fun z : ℂ => rl + z) (add_assoc (-ll) rr (-lr))
        _ = (rl + -ll) + (rr + -lr) := by
          exact (add_assoc rl (-ll) (rr + -lr)).symm
        _ = (rl - ll) + (rr + -lr) := by
          exact congrArg (fun z : ℂ => z + (rr + -lr)) (sub_eq_add_neg rl ll).symm
        _ = (rl - ll) + (rr - lr) := by
          exact congrArg (fun z : ℂ => (rl - ll) + z) (sub_eq_add_neg rr lr).symm

/-- Algebra for splitting a horizontal grouped contribution into a head box and tail. -/
theorem explicitFormulaRectangleBoxHorizontalContribution_consAlgebra
    (bottom top tailBottom tailTop : ℂ) :
    (bottom + tailBottom) - (top + tailTop) =
      (bottom - top) + (tailBottom - tailTop) := by
  calc
    (bottom + tailBottom) - (top + tailTop) =
        (bottom + tailBottom) + -(top + tailTop) := by
      exact sub_eq_add_neg (bottom + tailBottom) (top + tailTop)
    _ = (bottom + tailBottom) + (-top + -tailTop) := by
      exact congrArg (fun z : ℂ => (bottom + tailBottom) + z) (neg_add top tailTop)
    _ = bottom + (tailBottom + (-top + -tailTop)) := by
      exact add_assoc bottom tailBottom (-top + -tailTop)
    _ = bottom + ((tailBottom + -top) + -tailTop) := by
      exact congrArg
        (fun z : ℂ => bottom + z)
        (add_assoc tailBottom (-top) (-tailTop)).symm
    _ = bottom + ((-top + tailBottom) + -tailTop) := by
      exact congrArg (fun z : ℂ => bottom + (z + -tailTop)) (add_comm tailBottom (-top))
    _ = bottom + (-top + (tailBottom + -tailTop)) := by
      exact congrArg (fun z : ℂ => bottom + z) (add_assoc (-top) tailBottom (-tailTop))
    _ = (bottom + -top) + (tailBottom + -tailTop) := by
      exact (add_assoc bottom (-top) (tailBottom + -tailTop)).symm
    _ = (bottom - top) + (tailBottom + -tailTop) := by
      exact congrArg
        (fun z : ℂ => z + (tailBottom + -tailTop))
        (sub_eq_add_neg bottom top).symm
    _ = (bottom - top) + (tailBottom - tailTop) := by
      exact congrArg
        (fun z : ℂ => (bottom - top) + z)
        (sub_eq_add_neg tailBottom tailTop).symm

/-- Horizontal coordinate-label contribution is additive across appended bottom and top
edge lists. -/
theorem explicitFormulaRectangleHorizontalEndpointDataContribution_append
    (f : ZetaAdmissibleFunction)
    (bottomLeft bottomRight topLeft topRight :
      List ExplicitFormulaRectangleHorizontalEndpointDataEdge) :
    explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
          (bottomLeft ++ bottomRight) -
        explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
          (topLeft ++ topRight) =
      (explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f bottomLeft -
          explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f topLeft) +
        (explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f bottomRight -
          explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f topRight) := by
  let bl : ℂ :=
    explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f bottomLeft
  let br : ℂ :=
    explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f bottomRight
  let tl : ℂ :=
    explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f topLeft
  let tr : ℂ :=
    explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f topRight
  have hbottom :
      explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
          (bottomLeft ++ bottomRight) =
        bl + br :=
    explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum_append
      f bottomLeft bottomRight
  have htop :
      explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
          (topLeft ++ topRight) =
        tl + tr :=
    explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum_append
      f topLeft topRight
  calc
    explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
          (bottomLeft ++ bottomRight) -
        explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
          (topLeft ++ topRight) =
        (bl + br) -
          explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
            (topLeft ++ topRight) := by
      exact congrArg
        (fun z : ℂ =>
          z -
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
              (topLeft ++ topRight))
        hbottom
    _ = (bl + br) - (tl + tr) := by
      exact congrArg (fun z : ℂ => (bl + br) - z) htop
    _ = (bl - tl) + (br - tr) := by
      exact explicitFormulaRectangleBoxHorizontalContribution_consAlgebra bl tl br tr

/-- Horizontal coordinate-label contribution for one selected fixed row follows the
coordinate-omission filter at the head vertical adjacent pair. -/
theorem explicitFormulaRectangleSelectedHorizontalEndpointDataContribution_fixedX_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε)
    (rest : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX
            xpair (ypair :: rest)) -
        explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
          (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX
            xpair (ypair :: rest)) =
      if _homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        (explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
            ((xpair.x₀, xpair.x₁), ypair.y₀) -
          explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
            ((xpair.x₀, xpair.x₁), ypair.y₁)) +
          (explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX xpair rest) -
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
              (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair rest))
      else
        explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
            (explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX xpair rest) -
          explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
            (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair rest) := by
  if homit :
      explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
    have hbranch :
        explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX
                xpair (ypair :: rest)) -
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
              (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX
                xpair (ypair :: rest)) =
          (explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
              ((xpair.x₀, xpair.x₁), ypair.y₀) -
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
              ((xpair.x₀, xpair.x₁), ypair.y₁)) +
            (explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
                (explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX xpair rest) -
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
                (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair rest)) := by
      have hbottomList :
          explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX xpair (ypair :: rest) =
            ((xpair.x₀, xpair.x₁), ypair.y₀) ::
              explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX xpair rest :=
        dif_pos homit
      have htopList :
          explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair (ypair :: rest) =
            ((xpair.x₀, xpair.x₁), ypair.y₁) ::
              explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair rest :=
        dif_pos homit
      calc
        explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX
                xpair (ypair :: rest)) -
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
              (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX
                xpair (ypair :: rest)) =
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
                (((xpair.x₀, xpair.x₁), ypair.y₀) ::
                  explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX xpair rest) -
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
                (((xpair.x₀, xpair.x₁), ypair.y₁) ::
                  explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair rest) := by
          exact congrArg₂ Sub.sub
            (congrArg
              (fun edges : List ExplicitFormulaRectangleHorizontalEndpointDataEdge =>
                explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f edges)
              hbottomList)
            (congrArg
              (fun edges : List ExplicitFormulaRectangleHorizontalEndpointDataEdge =>
                explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f edges)
              htopList)
        _ =
            (explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
                ((xpair.x₀, xpair.x₁), ypair.y₀) -
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
                ((xpair.x₀, xpair.x₁), ypair.y₁)) +
              (explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
                  (explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX xpair rest) -
                explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
                  (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair rest)) :=
          explicitFormulaRectangleBoxHorizontalContribution_consAlgebra
            (explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
              ((xpair.x₀, xpair.x₁), ypair.y₀))
            (explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
              ((xpair.x₀, xpair.x₁), ypair.y₁))
            (explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX xpair rest))
            (explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
              (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair rest))
    calc
      explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
            (explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX
              xpair (ypair :: rest)) -
          explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
            (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX
              xpair (ypair :: rest)) =
          (explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
              ((xpair.x₀, xpair.x₁), ypair.y₀) -
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
              ((xpair.x₀, xpair.x₁), ypair.y₁)) +
            (explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
                (explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX xpair rest) -
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
                (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair rest)) := hbranch
      _ =
          if _homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            (explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
                ((xpair.x₀, xpair.x₁), ypair.y₀) -
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
                ((xpair.x₀, xpair.x₁), ypair.y₁)) +
              (explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
                  (explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX xpair rest) -
                explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
                  (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair rest))
          else
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
                (explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX xpair rest) -
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
                (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair rest) := by
        exact (if_pos homit).symm
  else
    have hbranch :
        explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX
                xpair (ypair :: rest)) -
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
              (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX
                xpair (ypair :: rest)) =
          explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX xpair rest) -
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
              (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair rest) := by
      have hbottomList :
          explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX xpair (ypair :: rest) =
            explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX xpair rest :=
        dif_neg homit
      have htopList :
          explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair (ypair :: rest) =
            explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair rest :=
        dif_neg homit
      exact congrArg₂ Sub.sub
        (congrArg
          (fun edges : List ExplicitFormulaRectangleHorizontalEndpointDataEdge =>
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f edges)
          hbottomList)
        (congrArg
          (fun edges : List ExplicitFormulaRectangleHorizontalEndpointDataEdge =>
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f edges)
          htopList)
    calc
      explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
            (explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX
              xpair (ypair :: rest)) -
          explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
            (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX
              xpair (ypair :: rest)) =
          explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX xpair rest) -
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
              (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair rest) := hbranch
      _ =
          if _homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            (explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
                ((xpair.x₀, xpair.x₁), ypair.y₀) -
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
                ((xpair.x₀, xpair.x₁), ypair.y₁)) +
              (explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
                  (explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX xpair rest) -
                explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
                  (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair rest))
          else
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
                (explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX xpair rest) -
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
                (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair rest) := by
        exact (if_neg homit).symm

/-- Horizontal coordinate-label contribution for one selected fixed row is zero over an
empty vertical-pair source list. -/
theorem explicitFormulaRectangleSelectedHorizontalEndpointDataContribution_fixedX_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX
            xpair ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))) -
      explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
          (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX
            xpair ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))) =
      0 := by
  calc
    explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX
            xpair ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))) -
        explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
          (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX
            xpair ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))) =
        0 - 0 := by
      rfl
    _ = 0 := by
      exact sub_self 0

/-- The explicit fixed-row bottom-edge scan is the bottom-edge sum of the selected
fixed-row endpoint-data list. -/
theorem explicitFormulaRectangleSelectedFixedX_bottomScan_eq_endpointDataBottomEdgeSum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    ∀ ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε),
      explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
            if homit :
                explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
              explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
              (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit)
            else
              0)
          ypairs =
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
              xpair ypairs))
  | [] =>
      rfl
  | ypair :: rest =>
      if homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        calc
          explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                if homit :
                    explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                  explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
              (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit)
                else
                  0)
              (ypair :: rest) =
            explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
              (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit) +
              explicitFormulaRectangleListSum
                (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                  if homit :
                      explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                    explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
              (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit)
                  else
                    0)
                rest := by
            calc
              explicitFormulaRectangleListSum
                  (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                    if homit :
                        explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                      explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
                (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit)
                    else
                      0)
                  (ypair :: rest) =
                (if h :
                    explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                  explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
                    (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair h)
                else
                  0) +
                  explicitFormulaRectangleListSum
                    (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                      if homit :
                          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                        explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
                  (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit)
                      else
                        0)
                    rest := by
                rfl
              _ =
                explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
                  (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit) +
                  explicitFormulaRectangleListSum
                    (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                      if homit :
                          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                        explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
                  (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit)
                      else
                        0)
                    rest := by
                exact congrArg
                  (fun z : ℂ =>
                    z +
                      explicitFormulaRectangleListSum
                        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                          if homit :
                              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                            explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
                      (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit)
                          else
                            0)
                        rest)
                  (dif_pos homit)
          _ =
            explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
              (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit) +
              explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
                (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                  (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                    xpair rest)) := by
            exact congrArg
              (fun z : ℂ =>
                explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
              (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit) + z)
              (explicitFormulaRectangleSelectedFixedX_bottomScan_eq_endpointDataBottomEdgeSum
                f xpair rest)
          _ =
            explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
              (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                  xpair (ypair :: rest))) := by
            have hcons :=
              explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum_selectedFixedX_cons
                f xpair ypair rest
            have hbranch :
                (if h :
                    explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                  explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
                    (({ xpair := xpair
                        ypair := ypair
                        homit := h } :
                        ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε).toEndpointData) +
                    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
                      (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                          xpair rest))
                else
                  explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
                    (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                        xpair rest))) =
                  explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
                    (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit) +
                    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
                      (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                          xpair rest)) := by
              exact dif_pos homit
            exact (Eq.trans hcons hbranch).symm
      else
        calc
          explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                if homit :
                    explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                  explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
              (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit)
                else
                  0)
              (ypair :: rest) =
            0 +
              explicitFormulaRectangleListSum
                (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                  if homit :
                      explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                    explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
              (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit)
                  else
                    0)
                rest := by
            calc
              explicitFormulaRectangleListSum
                  (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                    if homit :
                        explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                      explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
                (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit)
                    else
                      0)
                  (ypair :: rest) =
                (if h :
                    explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                  explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
                    (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair h)
                else
                  0) +
                  explicitFormulaRectangleListSum
                    (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                      if homit :
                          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                        explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
                  (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit)
                      else
                        0)
                    rest := by
                rfl
              _ =
                0 +
                  explicitFormulaRectangleListSum
                    (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                      if homit :
                          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                        explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
                  (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit)
                      else
                        0)
                    rest := by
                exact congrArg
                  (fun z : ℂ =>
                    z +
                      explicitFormulaRectangleListSum
                        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                          if homit :
                              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                            explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
                      (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit)
                          else
                            0)
                        rest)
                  (dif_neg homit)
          _ =
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                if homit :
                    explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                  explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
              (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit)
                else
                  0)
              rest := by
            exact zero_add _
          _ =
            explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
              (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                  xpair rest)) := by
            exact explicitFormulaRectangleSelectedFixedX_bottomScan_eq_endpointDataBottomEdgeSum
              f xpair rest
          _ =
            explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
              (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                  xpair (ypair :: rest))) := by
            have hcons :=
              explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum_selectedFixedX_cons
                f xpair ypair rest
            have hbranch :
                (if h :
                    explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                  explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
                    (({ xpair := xpair
                        ypair := ypair
                        homit := h } :
                        ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε).toEndpointData) +
                    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
                      (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                          xpair rest))
                else
                  explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
                    (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                        xpair rest))) =
                  explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
                    (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                        xpair rest)) := by
              exact dif_neg homit
            exact (Eq.trans hcons hbranch).symm

/-- The explicit fixed-row top-edge scan is the top-edge sum of the selected fixed-row
endpoint-data list. -/
theorem explicitFormulaRectangleSelectedFixedX_topScan_eq_endpointDataTopEdgeSum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    ∀ ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε),
      explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
            if homit :
                explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
              explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
              (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit)
            else
              0)
          ypairs =
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
              xpair ypairs))
  | [] =>
      rfl
  | ypair :: rest =>
      if homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        calc
          explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                if homit :
                    explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                  explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
              (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit)
                else
                  0)
              (ypair :: rest) =
            explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
              (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit) +
              explicitFormulaRectangleListSum
                (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                  if homit :
                      explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                    explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
              (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit)
                  else
                    0)
                rest := by
            calc
              explicitFormulaRectangleListSum
                  (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                    if homit :
                        explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                      explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
                (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit)
                    else
                      0)
                  (ypair :: rest) =
                (if h :
                    explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                  explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
                    (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair h)
                else
                  0) +
                  explicitFormulaRectangleListSum
                    (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                      if homit :
                          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                        explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
                  (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit)
                      else
                        0)
                    rest := by
                rfl
              _ =
                explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
                  (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit) +
                  explicitFormulaRectangleListSum
                    (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                      if homit :
                          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                        explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
                  (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit)
                      else
                        0)
                    rest := by
                exact congrArg
                  (fun z : ℂ =>
                    z +
                      explicitFormulaRectangleListSum
                        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                          if homit :
                              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                            explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
                      (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit)
                          else
                            0)
                        rest)
                  (dif_pos homit)
          _ =
            explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
              (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit) +
              explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
                (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                  (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                    xpair rest)) := by
            exact congrArg
              (fun z : ℂ =>
                explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
              (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit) + z)
              (explicitFormulaRectangleSelectedFixedX_topScan_eq_endpointDataTopEdgeSum
                f xpair rest)
          _ =
            explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
              (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                  xpair (ypair :: rest))) := by
            have hcons :=
              explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum_selectedFixedX_cons
                f xpair ypair rest
            have hbranch :
                (if h :
                    explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                  explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
                    (({ xpair := xpair
                        ypair := ypair
                        homit := h } :
                        ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε).toEndpointData) +
                    explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
                      (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                          xpair rest))
                else
                  explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
                    (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                        xpair rest))) =
                  explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
                    (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit) +
                    explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
                      (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                          xpair rest)) := by
              exact dif_pos homit
            exact (Eq.trans hcons hbranch).symm
      else
        calc
          explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                if homit :
                    explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                  explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
              (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit)
                else
                  0)
              (ypair :: rest) =
            0 +
              explicitFormulaRectangleListSum
                (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                  if homit :
                      explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                    explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
              (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit)
                  else
                    0)
                rest := by
            calc
              explicitFormulaRectangleListSum
                  (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                    if homit :
                        explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                      explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
                (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit)
                    else
                      0)
                  (ypair :: rest) =
                (if h :
                    explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                  explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
                    (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair h)
                else
                  0) +
                  explicitFormulaRectangleListSum
                    (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                      if homit :
                          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                        explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
                  (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit)
                      else
                        0)
                    rest := by
                rfl
              _ =
                0 +
                  explicitFormulaRectangleListSum
                    (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                      if homit :
                          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                        explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
                  (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit)
                      else
                        0)
                    rest := by
                exact congrArg
                  (fun z : ℂ =>
                    z +
                      explicitFormulaRectangleListSum
                        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                          if homit :
                              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                            explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
                      (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit)
                          else
                            0)
                        rest)
                  (dif_neg homit)
          _ =
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                if homit :
                    explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                  explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
              (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit)
                else
                  0)
              rest := by
            exact zero_add _
          _ =
            explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
              (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                  xpair rest)) := by
            exact explicitFormulaRectangleSelectedFixedX_topScan_eq_endpointDataTopEdgeSum
              f xpair rest
          _ =
            explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
              (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                  xpair (ypair :: rest))) := by
            have hcons :=
              explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum_selectedFixedX_cons
                f xpair ypair rest
            have hbranch :
                (if h :
                    explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                  explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
                    (({ xpair := xpair
                        ypair := ypair
                        homit := h } :
                        ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε).toEndpointData) +
                    explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
                      (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                          xpair rest))
                else
                  explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
                    (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                        xpair rest))) =
                  explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
                    (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                        xpair rest)) := by
              exact dif_neg homit
            exact (Eq.trans hcons hbranch).symm

/-- The explicit fixed-row bottom-edge scan is the selected bottom coordinate-label
integral sum. -/
theorem explicitFormulaRectangleSelectedFixedX_bottomScan_eq_coordinateIntegralSum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
          if homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
              (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit)
          else
            0)
        ypairs =
      explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
        (explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX xpair ypairs) := by
  let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
        xpair ypairs)
  have hscan :
      explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
            if homit :
                explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
              explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
              (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit)
            else
              0)
          ypairs =
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data :=
    explicitFormulaRectangleSelectedFixedX_bottomScan_eq_endpointDataBottomEdgeSum
      f xpair ypairs
  have hsum :
      explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data =
        explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
          (data.map
            (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
              d.bottomEdgeCoordinates)) :=
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum_eq_bottomHorizontalEdgeIntegralSum
      f data
  have hcoords :
      data.map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d.bottomEdgeCoordinates) =
        explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX xpair ypairs :=
    explicitFormulaRectangleSelectedEndpointDataFixedX_bottomEdgeCoordinates xpair ypairs
  exact Eq.trans hscan
    (Eq.trans hsum
      (congrArg
        (fun edges : List ExplicitFormulaRectangleHorizontalEndpointDataEdge =>
          explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f edges)
        hcoords))

/-- The explicit fixed-row top-edge scan is the selected top coordinate-label integral
sum. -/
theorem explicitFormulaRectangleSelectedFixedX_topScan_eq_coordinateIntegralSum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
          if homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
              (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit)
          else
            0)
        ypairs =
      explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
        (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair ypairs) := by
  let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
        xpair ypairs)
  have hscan :
      explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
            if homit :
                explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
              explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
              (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit)
            else
              0)
          ypairs =
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data :=
    explicitFormulaRectangleSelectedFixedX_topScan_eq_endpointDataTopEdgeSum
      f xpair ypairs
  have hsum :
      explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data =
        explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
          (data.map
            (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
              d.topEdgeCoordinates)) :=
    explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum_eq_topHorizontalEdgeIntegralSum
      f data
  have hcoords :
      data.map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d.topEdgeCoordinates) =
        explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair ypairs :=
    explicitFormulaRectangleSelectedEndpointDataFixedX_topEdgeCoordinates xpair ypairs
  exact Eq.trans hscan
    (Eq.trans hsum
      (congrArg
        (fun edges : List ExplicitFormulaRectangleHorizontalEndpointDataEdge =>
          explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f edges)
        hcoords))

/-- Algebra for splitting a vertical grouped contribution into a head box and tail. -/
theorem explicitFormulaRectangleBoxVerticalContribution_consAlgebra
    (right left tailRight tailLeft : ℂ) :
    (right + tailRight) - (left + tailLeft) =
      (right - left) + (tailRight - tailLeft) :=
  explicitFormulaRectangleBoxHorizontalContribution_consAlgebra right left tailRight tailLeft

/-- Regroup head and tail horizontal/vertical boundary contributions. -/
theorem explicitFormulaRectangleBoxBoundaryContribution_consAlgebra
    (headHorizontal headVertical tailHorizontal tailVertical : ℂ) :
    (headHorizontal + headVertical) + (tailHorizontal + tailVertical) =
      (headHorizontal + tailHorizontal) + (headVertical + tailVertical) := by
  calc
    (headHorizontal + headVertical) + (tailHorizontal + tailVertical) =
        headHorizontal + (headVertical + (tailHorizontal + tailVertical)) := by
      exact add_assoc headHorizontal headVertical (tailHorizontal + tailVertical)
    _ = headHorizontal + ((headVertical + tailHorizontal) + tailVertical) := by
      exact congrArg
        (fun z : ℂ => headHorizontal + z)
        (add_assoc headVertical tailHorizontal tailVertical).symm
    _ = headHorizontal + ((tailHorizontal + headVertical) + tailVertical) := by
      exact congrArg
        (fun z : ℂ => headHorizontal + (z + tailVertical))
        (add_comm headVertical tailHorizontal)
    _ = headHorizontal + (tailHorizontal + (headVertical + tailVertical)) := by
      exact congrArg
        (fun z : ℂ => headHorizontal + z)
        (add_assoc tailHorizontal headVertical tailVertical)
    _ = (headHorizontal + tailHorizontal) + (headVertical + tailVertical) := by
      exact (add_assoc headHorizontal tailHorizontal (headVertical + tailVertical)).symm

/-- Full endpoint-data box boundary sums decompose into their four oriented side sums. -/
theorem explicitFormulaRectangleEndpointDataBoxBoundarySum_eq_edgeSums
    (f : ZetaAdmissibleFunction) :
    ∀ edges : List ExplicitFormulaRectangleEndpointDataBoxEdge,
      explicitFormulaRectangleEndpointDataBoxBoundarySum f edges =
        explicitFormulaRectangleBoxBottomEdgeIntegralSum f edges -
          explicitFormulaRectangleBoxTopEdgeIntegralSum f edges +
            (explicitFormulaRectangleBoxRightEdgeIntegralSum f edges -
              explicitFormulaRectangleBoxLeftEdgeIntegralSum f edges)
  | [] =>
      calc
        explicitFormulaRectangleEndpointDataBoxBoundarySum f
            ([] : List ExplicitFormulaRectangleEndpointDataBoxEdge) =
            0 := by
          rfl
        _ = 0 + 0 := by
          exact (add_zero 0).symm
        _ = (0 - 0) + 0 := by
          exact congrArg (fun z : ℂ => z + 0) (sub_self 0).symm
        _ = (0 - 0) + (0 - 0) := by
          exact congrArg (fun z : ℂ => (0 - 0) + z) (sub_self 0).symm
        _ =
            explicitFormulaRectangleBoxBottomEdgeIntegralSum f
                ([] : List ExplicitFormulaRectangleEndpointDataBoxEdge) -
              explicitFormulaRectangleBoxTopEdgeIntegralSum f
                ([] : List ExplicitFormulaRectangleEndpointDataBoxEdge) +
                (explicitFormulaRectangleBoxRightEdgeIntegralSum f
                    ([] : List ExplicitFormulaRectangleEndpointDataBoxEdge) -
                  explicitFormulaRectangleBoxLeftEdgeIntegralSum f
                    ([] : List ExplicitFormulaRectangleEndpointDataBoxEdge)) := by
          rfl
  | edge :: rest =>
      let headHorizontal : ℂ :=
        explicitFormulaRectangleBoxBottomEdgeIntegral f edge -
          explicitFormulaRectangleBoxTopEdgeIntegral f edge
      let headVertical : ℂ :=
        explicitFormulaRectangleBoxRightEdgeIntegral f edge -
          explicitFormulaRectangleBoxLeftEdgeIntegral f edge
      let tailHorizontal : ℂ :=
        explicitFormulaRectangleBoxBottomEdgeIntegralSum f rest -
          explicitFormulaRectangleBoxTopEdgeIntegralSum f rest
      let tailVertical : ℂ :=
        explicitFormulaRectangleBoxRightEdgeIntegralSum f rest -
          explicitFormulaRectangleBoxLeftEdgeIntegralSum f rest
      have hcell :
          finiteRectangleSubdivisionCellBoundaryIntegral
              (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
              (explicitFormulaRectangleEndpointDataBoxLowerCorner edge)
              (explicitFormulaRectangleEndpointDataBoxUpperCorner edge) =
            headHorizontal + headVertical :=
        (explicitFormulaRectangleEndpointDataBoxBoundary_eq_cellBoundary f edge).symm
      have htail :
          explicitFormulaRectangleEndpointDataBoxBoundarySum f rest =
            tailHorizontal + tailVertical :=
        explicitFormulaRectangleEndpointDataBoxBoundarySum_eq_edgeSums f rest
      have hhorizontal :
          explicitFormulaRectangleBoxBottomEdgeIntegralSum f (edge :: rest) -
              explicitFormulaRectangleBoxTopEdgeIntegralSum f (edge :: rest) =
            headHorizontal + tailHorizontal := by
        exact explicitFormulaRectangleBoxHorizontalContribution_consAlgebra
          (explicitFormulaRectangleBoxBottomEdgeIntegral f edge)
          (explicitFormulaRectangleBoxTopEdgeIntegral f edge)
          (explicitFormulaRectangleBoxBottomEdgeIntegralSum f rest)
          (explicitFormulaRectangleBoxTopEdgeIntegralSum f rest)
      have hvertical :
          explicitFormulaRectangleBoxRightEdgeIntegralSum f (edge :: rest) -
              explicitFormulaRectangleBoxLeftEdgeIntegralSum f (edge :: rest) =
            headVertical + tailVertical := by
        exact explicitFormulaRectangleBoxVerticalContribution_consAlgebra
          (explicitFormulaRectangleBoxRightEdgeIntegral f edge)
          (explicitFormulaRectangleBoxLeftEdgeIntegral f edge)
          (explicitFormulaRectangleBoxRightEdgeIntegralSum f rest)
          (explicitFormulaRectangleBoxLeftEdgeIntegralSum f rest)
      calc
        explicitFormulaRectangleEndpointDataBoxBoundarySum f (edge :: rest) =
            finiteRectangleSubdivisionCellBoundaryIntegral
                (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
                (explicitFormulaRectangleEndpointDataBoxLowerCorner edge)
                (explicitFormulaRectangleEndpointDataBoxUpperCorner edge) +
              explicitFormulaRectangleEndpointDataBoxBoundarySum f rest := by
          rfl
        _ = (headHorizontal + headVertical) +
              explicitFormulaRectangleEndpointDataBoxBoundarySum f rest := by
          exact congrArg
            (fun z : ℂ => z + explicitFormulaRectangleEndpointDataBoxBoundarySum f rest)
            hcell
        _ = (headHorizontal + headVertical) + (tailHorizontal + tailVertical) := by
          exact congrArg (fun z : ℂ => (headHorizontal + headVertical) + z) htail
        _ = (headHorizontal + tailHorizontal) + (headVertical + tailVertical) := by
          exact explicitFormulaRectangleBoxBoundaryContribution_consAlgebra
            headHorizontal headVertical tailHorizontal tailVertical
        _ =
            (explicitFormulaRectangleBoxBottomEdgeIntegralSum f (edge :: rest) -
              explicitFormulaRectangleBoxTopEdgeIntegralSum f (edge :: rest)) +
              (explicitFormulaRectangleBoxRightEdgeIntegralSum f (edge :: rest) -
                explicitFormulaRectangleBoxLeftEdgeIntegralSum f (edge :: rest)) := by
          exact congrArg₂ Add.add hhorizontal.symm hvertical.symm

/-- Horizontal grouped contribution over selected crossed adjacent-pair lists splits
into the selected fixed row plus the remaining rows. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinatesHorizontalContribution_pairLists_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (rest : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    let firstRow : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
      explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair ypairs
    let remaining : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
      explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists rest ypairs
    explicitFormulaRectangleBoxBottomEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
            (xpair :: rest) ypairs) -
        explicitFormulaRectangleBoxTopEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
            (xpair :: rest) ypairs) =
      (explicitFormulaRectangleBoxBottomEdgeIntegralSum f firstRow -
          explicitFormulaRectangleBoxTopEdgeIntegralSum f firstRow) +
        (explicitFormulaRectangleBoxBottomEdgeIntegralSum f remaining -
          explicitFormulaRectangleBoxTopEdgeIntegralSum f remaining) := by
  exact
    explicitFormulaRectangleBoxHorizontalContribution_append
      f
      (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair ypairs)
      (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists rest ypairs)

/-- Vertical grouped contribution over selected crossed adjacent-pair lists splits into
the selected fixed row plus the remaining rows. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinatesVerticalContribution_pairLists_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (rest : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    let firstRow : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
      explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair ypairs
    let remaining : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
      explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists rest ypairs
    explicitFormulaRectangleBoxRightEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
            (xpair :: rest) ypairs) -
        explicitFormulaRectangleBoxLeftEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
            (xpair :: rest) ypairs) =
      (explicitFormulaRectangleBoxRightEdgeIntegralSum f firstRow -
          explicitFormulaRectangleBoxLeftEdgeIntegralSum f firstRow) +
        (explicitFormulaRectangleBoxRightEdgeIntegralSum f remaining -
          explicitFormulaRectangleBoxLeftEdgeIntegralSum f remaining) := by
  exact
    explicitFormulaRectangleBoxVerticalContribution_append
      f
      (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair ypairs)
      (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists rest ypairs)

/-- Horizontal grouped contribution for one selected fixed row follows the
coordinate-omission filter at the head vertical adjacent pair. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinatesHorizontalContribution_fixedX_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε)
    (rest : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    explicitFormulaRectangleBoxBottomEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair (ypair :: rest)) -
        explicitFormulaRectangleBoxTopEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair (ypair :: rest)) =
      if _homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        (explicitFormulaRectangleBoxBottomEdgeIntegral f
            (((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) :
              ExplicitFormulaRectangleEndpointDataBoxEdge) -
          explicitFormulaRectangleBoxTopEdgeIntegral f
            (((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) :
              ExplicitFormulaRectangleEndpointDataBoxEdge)) +
          (explicitFormulaRectangleBoxBottomEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest) -
            explicitFormulaRectangleBoxTopEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest))
      else
        explicitFormulaRectangleBoxBottomEdgeIntegralSum f
            (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest) -
          explicitFormulaRectangleBoxTopEdgeIntegralSum f
            (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest) := by
  if homit :
      explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
    let head : ExplicitFormulaRectangleEndpointDataBoxEdge :=
      ((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁))
    let tail : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
      explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest
    have hbranch :
        explicitFormulaRectangleBoxBottomEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair (ypair :: rest)) -
            explicitFormulaRectangleBoxTopEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair (ypair :: rest)) =
            (explicitFormulaRectangleBoxBottomEdgeIntegral f head -
            explicitFormulaRectangleBoxTopEdgeIntegral f head) +
            (explicitFormulaRectangleBoxBottomEdgeIntegralSum f tail -
              explicitFormulaRectangleBoxTopEdgeIntegralSum f tail) := by
      have hselected :
          explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair (ypair :: rest) =
            head :: tail :=
        explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX_cons_of_omission
          xpair ypair rest homit
      calc
        explicitFormulaRectangleBoxBottomEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair (ypair :: rest)) -
            explicitFormulaRectangleBoxTopEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair (ypair :: rest)) =
            explicitFormulaRectangleBoxBottomEdgeIntegralSum f (head :: tail) -
              explicitFormulaRectangleBoxTopEdgeIntegralSum f (head :: tail) := by
          exact congrArg₂ Sub.sub
            (congrArg
              (fun edges : List ExplicitFormulaRectangleEndpointDataBoxEdge =>
                explicitFormulaRectangleBoxBottomEdgeIntegralSum f edges)
              hselected)
            (congrArg
              (fun edges : List ExplicitFormulaRectangleEndpointDataBoxEdge =>
                explicitFormulaRectangleBoxTopEdgeIntegralSum f edges)
              hselected)
        _ =
            (explicitFormulaRectangleBoxBottomEdgeIntegral f head -
              explicitFormulaRectangleBoxTopEdgeIntegral f head) +
              (explicitFormulaRectangleBoxBottomEdgeIntegralSum f tail -
                explicitFormulaRectangleBoxTopEdgeIntegralSum f tail) :=
          explicitFormulaRectangleBoxHorizontalContribution_consAlgebra
            (explicitFormulaRectangleBoxBottomEdgeIntegral f head)
            (explicitFormulaRectangleBoxTopEdgeIntegral f head)
            (explicitFormulaRectangleBoxBottomEdgeIntegralSum f tail)
            (explicitFormulaRectangleBoxTopEdgeIntegralSum f tail)
    calc
      explicitFormulaRectangleBoxBottomEdgeIntegralSum f
            (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair (ypair :: rest)) -
          explicitFormulaRectangleBoxTopEdgeIntegralSum f
            (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair (ypair :: rest)) =
          (explicitFormulaRectangleBoxBottomEdgeIntegral f head -
            explicitFormulaRectangleBoxTopEdgeIntegral f head) +
            (explicitFormulaRectangleBoxBottomEdgeIntegralSum f tail -
              explicitFormulaRectangleBoxTopEdgeIntegralSum f tail) := hbranch
      _ =
          if _homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            (explicitFormulaRectangleBoxBottomEdgeIntegral f
                (((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) :
                  ExplicitFormulaRectangleEndpointDataBoxEdge) -
              explicitFormulaRectangleBoxTopEdgeIntegral f
                (((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) :
                  ExplicitFormulaRectangleEndpointDataBoxEdge)) +
              (explicitFormulaRectangleBoxBottomEdgeIntegralSum f
                  (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest) -
                explicitFormulaRectangleBoxTopEdgeIntegralSum f
                  (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest))
          else
            explicitFormulaRectangleBoxBottomEdgeIntegralSum f
                (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest) -
              explicitFormulaRectangleBoxTopEdgeIntegralSum f
                (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest) := by
        exact (if_pos homit).symm
  else
    have hbranch :
        explicitFormulaRectangleBoxBottomEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair (ypair :: rest)) -
            explicitFormulaRectangleBoxTopEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair (ypair :: rest)) =
            explicitFormulaRectangleBoxBottomEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest) -
            explicitFormulaRectangleBoxTopEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest) := by
      have hselected :
          explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair (ypair :: rest) =
            explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest :=
        explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX_skip_of_not_omission
          xpair ypair rest homit
      exact congrArg₂ Sub.sub
        (congrArg
          (fun edges : List ExplicitFormulaRectangleEndpointDataBoxEdge =>
            explicitFormulaRectangleBoxBottomEdgeIntegralSum f edges)
          hselected)
        (congrArg
          (fun edges : List ExplicitFormulaRectangleEndpointDataBoxEdge =>
            explicitFormulaRectangleBoxTopEdgeIntegralSum f edges)
          hselected)
    calc
      explicitFormulaRectangleBoxBottomEdgeIntegralSum f
            (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair (ypair :: rest)) -
          explicitFormulaRectangleBoxTopEdgeIntegralSum f
            (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair (ypair :: rest)) =
          explicitFormulaRectangleBoxBottomEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest) -
            explicitFormulaRectangleBoxTopEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest) := hbranch
      _ =
          if _homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            (explicitFormulaRectangleBoxBottomEdgeIntegral f
                (((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) :
                  ExplicitFormulaRectangleEndpointDataBoxEdge) -
              explicitFormulaRectangleBoxTopEdgeIntegral f
                (((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) :
                  ExplicitFormulaRectangleEndpointDataBoxEdge)) +
              (explicitFormulaRectangleBoxBottomEdgeIntegralSum f
                  (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest) -
                explicitFormulaRectangleBoxTopEdgeIntegralSum f
                  (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest))
          else
            explicitFormulaRectangleBoxBottomEdgeIntegralSum f
                (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest) -
              explicitFormulaRectangleBoxTopEdgeIntegralSum f
                (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest) := by
        exact (if_neg homit).symm

/-- Vertical grouped contribution for one selected fixed row follows the
coordinate-omission filter at the head vertical adjacent pair. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinatesVerticalContribution_fixedX_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε)
    (rest : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    explicitFormulaRectangleBoxRightEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair (ypair :: rest)) -
        explicitFormulaRectangleBoxLeftEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair (ypair :: rest)) =
      if _homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        (explicitFormulaRectangleBoxRightEdgeIntegral f
            (((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) :
              ExplicitFormulaRectangleEndpointDataBoxEdge) -
          explicitFormulaRectangleBoxLeftEdgeIntegral f
            (((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) :
              ExplicitFormulaRectangleEndpointDataBoxEdge)) +
          (explicitFormulaRectangleBoxRightEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest) -
            explicitFormulaRectangleBoxLeftEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest))
      else
        explicitFormulaRectangleBoxRightEdgeIntegralSum f
            (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest) -
          explicitFormulaRectangleBoxLeftEdgeIntegralSum f
            (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest) := by
  if homit :
      explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
    let head : ExplicitFormulaRectangleEndpointDataBoxEdge :=
      ((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁))
    let tail : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
      explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest
    have hbranch :
        explicitFormulaRectangleBoxRightEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair (ypair :: rest)) -
            explicitFormulaRectangleBoxLeftEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair (ypair :: rest)) =
            (explicitFormulaRectangleBoxRightEdgeIntegral f head -
            explicitFormulaRectangleBoxLeftEdgeIntegral f head) +
            (explicitFormulaRectangleBoxRightEdgeIntegralSum f tail -
              explicitFormulaRectangleBoxLeftEdgeIntegralSum f tail) := by
      have hselected :
          explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair (ypair :: rest) =
            head :: tail :=
        explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX_cons_of_omission
          xpair ypair rest homit
      calc
        explicitFormulaRectangleBoxRightEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair (ypair :: rest)) -
            explicitFormulaRectangleBoxLeftEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair (ypair :: rest)) =
            explicitFormulaRectangleBoxRightEdgeIntegralSum f (head :: tail) -
              explicitFormulaRectangleBoxLeftEdgeIntegralSum f (head :: tail) := by
          exact congrArg₂ Sub.sub
            (congrArg
              (fun edges : List ExplicitFormulaRectangleEndpointDataBoxEdge =>
                explicitFormulaRectangleBoxRightEdgeIntegralSum f edges)
              hselected)
            (congrArg
              (fun edges : List ExplicitFormulaRectangleEndpointDataBoxEdge =>
                explicitFormulaRectangleBoxLeftEdgeIntegralSum f edges)
              hselected)
        _ =
            (explicitFormulaRectangleBoxRightEdgeIntegral f head -
              explicitFormulaRectangleBoxLeftEdgeIntegral f head) +
              (explicitFormulaRectangleBoxRightEdgeIntegralSum f tail -
                explicitFormulaRectangleBoxLeftEdgeIntegralSum f tail) :=
          explicitFormulaRectangleBoxVerticalContribution_consAlgebra
            (explicitFormulaRectangleBoxRightEdgeIntegral f head)
            (explicitFormulaRectangleBoxLeftEdgeIntegral f head)
            (explicitFormulaRectangleBoxRightEdgeIntegralSum f tail)
            (explicitFormulaRectangleBoxLeftEdgeIntegralSum f tail)
    calc
      explicitFormulaRectangleBoxRightEdgeIntegralSum f
            (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair (ypair :: rest)) -
          explicitFormulaRectangleBoxLeftEdgeIntegralSum f
            (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair (ypair :: rest)) =
          (explicitFormulaRectangleBoxRightEdgeIntegral f head -
            explicitFormulaRectangleBoxLeftEdgeIntegral f head) +
            (explicitFormulaRectangleBoxRightEdgeIntegralSum f tail -
              explicitFormulaRectangleBoxLeftEdgeIntegralSum f tail) := hbranch
      _ =
          if _homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            (explicitFormulaRectangleBoxRightEdgeIntegral f
                (((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) :
                  ExplicitFormulaRectangleEndpointDataBoxEdge) -
              explicitFormulaRectangleBoxLeftEdgeIntegral f
                (((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) :
                  ExplicitFormulaRectangleEndpointDataBoxEdge)) +
              (explicitFormulaRectangleBoxRightEdgeIntegralSum f
                  (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest) -
                explicitFormulaRectangleBoxLeftEdgeIntegralSum f
                  (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest))
          else
            explicitFormulaRectangleBoxRightEdgeIntegralSum f
                (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest) -
              explicitFormulaRectangleBoxLeftEdgeIntegralSum f
                (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest) := by
        exact (if_pos homit).symm
  else
    have hbranch :
        explicitFormulaRectangleBoxRightEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair (ypair :: rest)) -
            explicitFormulaRectangleBoxLeftEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair (ypair :: rest)) =
            explicitFormulaRectangleBoxRightEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest) -
            explicitFormulaRectangleBoxLeftEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest) := by
      have hselected :
          explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair (ypair :: rest) =
            explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest :=
        explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX_skip_of_not_omission
          xpair ypair rest homit
      exact congrArg₂ Sub.sub
        (congrArg
          (fun edges : List ExplicitFormulaRectangleEndpointDataBoxEdge =>
            explicitFormulaRectangleBoxRightEdgeIntegralSum f edges)
          hselected)
        (congrArg
          (fun edges : List ExplicitFormulaRectangleEndpointDataBoxEdge =>
            explicitFormulaRectangleBoxLeftEdgeIntegralSum f edges)
          hselected)
    calc
      explicitFormulaRectangleBoxRightEdgeIntegralSum f
            (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair (ypair :: rest)) -
          explicitFormulaRectangleBoxLeftEdgeIntegralSum f
            (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair (ypair :: rest)) =
          explicitFormulaRectangleBoxRightEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest) -
            explicitFormulaRectangleBoxLeftEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest) := hbranch
      _ =
          if _homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            (explicitFormulaRectangleBoxRightEdgeIntegral f
                (((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) :
                  ExplicitFormulaRectangleEndpointDataBoxEdge) -
              explicitFormulaRectangleBoxLeftEdgeIntegral f
                (((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) :
                  ExplicitFormulaRectangleEndpointDataBoxEdge)) +
              (explicitFormulaRectangleBoxRightEdgeIntegralSum f
                  (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest) -
                explicitFormulaRectangleBoxLeftEdgeIntegralSum f
                  (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest))
          else
            explicitFormulaRectangleBoxRightEdgeIntegralSum f
                (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest) -
              explicitFormulaRectangleBoxLeftEdgeIntegralSum f
                (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest) := by
        exact (if_neg homit).symm

/-- Horizontal grouped contribution for a selected fixed row is zero over an empty
vertical-pair source list. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinatesHorizontalContribution_fixedX_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    explicitFormulaRectangleBoxBottomEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX
            xpair ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))) -
    explicitFormulaRectangleBoxTopEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX
            xpair ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))) =
      0 := by
  calc
    explicitFormulaRectangleBoxBottomEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX
            xpair ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))) -
        explicitFormulaRectangleBoxTopEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX
            xpair ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))) =
        0 - 0 := by
      rfl
    _ = 0 := by
      exact sub_self 0

/-- Vertical grouped contribution for a selected fixed row is zero over an empty
vertical-pair source list. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinatesVerticalContribution_fixedX_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    explicitFormulaRectangleBoxRightEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX
            xpair ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))) -
    explicitFormulaRectangleBoxLeftEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX
            xpair ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))) =
      0 := by
  calc
    explicitFormulaRectangleBoxRightEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX
            xpair ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))) -
        explicitFormulaRectangleBoxLeftEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX
            xpair ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))) =
        0 - 0 := by
      rfl
    _ = 0 := by
      exact sub_self 0

/-- Horizontal grouped contribution over an empty horizontal adjacent-pair list is zero. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinatesHorizontalContribution_pairLists_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    explicitFormulaRectangleBoxBottomEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
            ([] : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)) ypairs) -
    explicitFormulaRectangleBoxTopEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
            ([] : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)) ypairs) =
      0 := by
  calc
    explicitFormulaRectangleBoxBottomEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
            ([] : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)) ypairs) -
        explicitFormulaRectangleBoxTopEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
            ([] : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)) ypairs) =
        0 - 0 := by
      rfl
    _ = 0 := by
      exact sub_self 0

/-- Vertical grouped contribution over an empty horizontal adjacent-pair list is zero. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinatesVerticalContribution_pairLists_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    explicitFormulaRectangleBoxRightEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
            ([] : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)) ypairs) -
    explicitFormulaRectangleBoxLeftEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
            ([] : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)) ypairs) =
      0 := by
  calc
    explicitFormulaRectangleBoxRightEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
            ([] : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)) ypairs) -
        explicitFormulaRectangleBoxLeftEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
            ([] : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)) ypairs) =
        0 - 0 := by
      rfl
    _ = 0 := by
      exact sub_self 0

/-- Vertical grouped contribution over sorted selected full-box rows splits at the head
horizontal adjacent pair. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinatesVerticalContribution_sortedPairLists_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (rest : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)) :
    let firstRow : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
      explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX
        xpair
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)
    let remaining : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
      explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
        rest
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)
    explicitFormulaRectangleBoxRightEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
            (xpair :: rest)
            (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)) -
        explicitFormulaRectangleBoxLeftEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
            (xpair :: rest)
            (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)) =
      (explicitFormulaRectangleBoxRightEdgeIntegralSum f firstRow -
          explicitFormulaRectangleBoxLeftEdgeIntegralSum f firstRow) +
        (explicitFormulaRectangleBoxRightEdgeIntegralSum f remaining -
          explicitFormulaRectangleBoxLeftEdgeIntegralSum f remaining) :=
  explicitFormulaRectangleSelectedBoxEdgeCoordinatesVerticalContribution_pairLists_cons
    f xpair rest (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)

/-- Vertical grouped contribution over an empty sorted horizontal row list is zero. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinatesVerticalContribution_sortedPairLists_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction) :
    explicitFormulaRectangleBoxRightEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
            ([] : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
            (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)) -
        explicitFormulaRectangleBoxLeftEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
            ([] : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
            (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)) =
      0 :=
  explicitFormulaRectangleSelectedBoxEdgeCoordinatesVerticalContribution_pairLists_nil
    f (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)

/-- Half-radius vertical grouped contribution over sorted selected rows splits at the
head horizontal adjacent pair. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinatesVerticalContribution_halfRadius_sortedPairLists_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T (ε / 2))
    (rest : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T (ε / 2))) :
    let firstRow : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
      explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX
        xpair
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T (ε / 2))
    let remaining : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
      explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
        rest
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T (ε / 2))
    explicitFormulaRectangleBoxRightEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
            (xpair :: rest)
            (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T (ε / 2))) -
        explicitFormulaRectangleBoxLeftEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
            (xpair :: rest)
            (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T (ε / 2))) =
      (explicitFormulaRectangleBoxRightEdgeIntegralSum f firstRow -
          explicitFormulaRectangleBoxLeftEdgeIntegralSum f firstRow) +
        (explicitFormulaRectangleBoxRightEdgeIntegralSum f remaining -
          explicitFormulaRectangleBoxLeftEdgeIntegralSum f remaining) :=
  explicitFormulaRectangleSelectedBoxEdgeCoordinatesVerticalContribution_sortedPairLists_cons
    f xpair rest

/-- Half-radius vertical grouped contribution over an empty sorted horizontal row list is
zero. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinatesVerticalContribution_halfRadius_sortedPairLists_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction) :
    explicitFormulaRectangleBoxRightEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
            ([] : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T (ε / 2)))
            (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T (ε / 2))) -
        explicitFormulaRectangleBoxLeftEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
            ([] : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T (ε / 2)))
            (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T (ε / 2))) =
      0 :=
  explicitFormulaRectangleSelectedBoxEdgeCoordinatesVerticalContribution_sortedPairLists_nil
    f

/-- Sorted selected full-box boundary sum splits at the head horizontal adjacent-pair.
This is the concrete recursive reduction used by the exposed-boundary collapse. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinatesBoundarySum_sortedPairLists_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (rest : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)) :
    explicitFormulaRectangleEndpointDataBoxBoundarySum f
        (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
          (xpair :: rest)
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)) =
      explicitFormulaRectangleEndpointDataBoxBoundarySum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX
            xpair
            (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)) +
        explicitFormulaRectangleEndpointDataBoxBoundarySum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
            rest
            (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)) :=
  explicitFormulaRectangleSelectedBoxEdgeCoordinatesBoundarySum_pairLists_cons
    f xpair rest (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)

/-- The sorted selected full-box boundary sum is zero when the sorted horizontal
adjacent-pair list has no rows. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinatesBoundarySum_sortedPairLists_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction) :
    explicitFormulaRectangleEndpointDataBoxBoundarySum f
        (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
          ([] : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)) =
      0 :=
  explicitFormulaRectangleSelectedBoxEdgeCoordinatesBoundarySum_pairLists_nil
    f (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)

/-- The sorted selected full-box boundary sum decomposes into its four oriented
box-side sums.  This is the edge-sum normal form for the exposed-boundary collapse. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinatesBoundarySum_sortedPairLists_eq_edgeSums
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    explicitFormulaRectangleEndpointDataBoxBoundarySum f
        (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
          (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε)
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)) =
      explicitFormulaRectangleBoxBottomEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
            (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε)
            (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)) -
        explicitFormulaRectangleBoxTopEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
            (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε)
            (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)) +
          (explicitFormulaRectangleBoxRightEdgeIntegralSum f
            (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
              (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε)
              (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)) -
            explicitFormulaRectangleBoxLeftEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
                (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε)
                (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε))) := by
  exact
    explicitFormulaRectangleEndpointDataBoxBoundarySum_eq_edgeSums
      f
      (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε))

/-- Half-radius sorted selected full-box boundary sum splits at the head horizontal
adjacent-pair. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinatesBoundarySum_halfRadius_sortedPairLists_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T (ε / 2))
    (rest : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T (ε / 2))) :
    explicitFormulaRectangleEndpointDataBoxBoundarySum f
        (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
          (xpair :: rest)
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T (ε / 2))) =
      explicitFormulaRectangleEndpointDataBoxBoundarySum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX
            xpair
            (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T (ε / 2))) +
        explicitFormulaRectangleEndpointDataBoxBoundarySum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
            rest
            (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T (ε / 2))) :=
  explicitFormulaRectangleSelectedBoxEdgeCoordinatesBoundarySum_sortedPairLists_cons
    f xpair rest

/-- Half-radius sorted selected full-box boundary sum is zero over an empty horizontal
row list. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinatesBoundarySum_halfRadius_sortedPairLists_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction) :
    explicitFormulaRectangleEndpointDataBoxBoundarySum f
        (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
          ([] : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T (ε / 2)))
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T (ε / 2))) =
      0 :=
  explicitFormulaRectangleSelectedBoxEdgeCoordinatesBoundarySum_sortedPairLists_nil
    f

/-- Half-radius selected full-box boundary sum in four-side normal form. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinatesBoundarySum_halfRadius_sortedPairLists_eq_edgeSums
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    explicitFormulaRectangleEndpointDataBoxBoundarySum f
        (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
          (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T (ε / 2))
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T (ε / 2))) =
      explicitFormulaRectangleBoxBottomEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
            (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T (ε / 2))
            (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T (ε / 2))) -
        explicitFormulaRectangleBoxTopEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
            (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T (ε / 2))
            (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T (ε / 2))) +
          (explicitFormulaRectangleBoxRightEdgeIntegralSum f
            (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
              (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T (ε / 2))
              (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T (ε / 2))) -
            explicitFormulaRectangleBoxLeftEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
                (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T (ε / 2))
                (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T (ε / 2)))) := by
  exact
    explicitFormulaRectangleSelectedBoxEdgeCoordinatesBoundarySum_sortedPairLists_eq_edgeSums
      f F T (ε / 2)

/-- Closed-radius interior control at radius `ε` restricts to the half-radius closed
balls used by the selected inscribed-square grid. -/
theorem explicitFormulaRectangle_closedRadiusControls_halfRadius
    (F : ExplicitFormulaContourFamily) (T ε : ℝ) (hε : 0 < ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) :
    ∀ a : ℂ,
      a ∈ explicitFormulaRectangleRawSingularCoordinates T →
        Metric.closedBall a (ε / 2) ⊆
          explicitFormulaContourFamilyInterior F T := by
  intro a ha
  exact Set.Subset.trans
    (finiteRectangle_closedBall_subset_of_radius_le
      (finiteRectangle_halfRadius_le_self hε))
    (hclosed a ha)

/-- The strict separation hypothesis at radius `ε` gives disjoint half-radius closed
balls for distinct raw singular coordinates. -/
theorem explicitFormulaRectangle_rawSingularCoordinates_halfRadius_closedBalls_disjoint
    (T ε : ℝ) (hε : 0 < ε)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ε + ε < dist a b) :
    ∀ a : ℂ,
      a ∈ explicitFormulaRectangleRawSingularCoordinates T →
        ∀ b : ℂ,
          b ∈ explicitFormulaRectangleRawSingularCoordinates T →
            a ≠ b →
              Disjoint (Metric.closedBall a (ε / 2)) (Metric.closedBall b (ε / 2)) := by
  intro a ha b hb hab
  have hhalf_sum :
      ε / 2 + ε / 2 < dist a b := by
    calc
      ε / 2 + ε / 2 = ε := by
        exact add_halves ε
      _ < ε + ε := by
        exact lt_add_of_pos_right ε hε
      _ < dist a b := by
        exact hsep a ha b hb hab
  exact Metric.closedBall_disjoint_closedBall hhalf_sum

/-- Distinct raw inscribed-square closed cells at half radius are disjoint under the
closed-radius separation controls used by the selected complement grid. -/
theorem explicitFormulaRectangleRawInscribedSquareClosedCell_halfRadius_pairwiseDisjoint
    (T ε : ℝ) (hε : 0 < ε)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ε + ε < dist a b)
    (a : ℂ) (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (b : ℂ) (hb : b ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (hab : a ≠ b) :
    Disjoint
      (explicitFormulaRectangleRawInscribedSquareClosedCell (ε / 2) a)
      (explicitFormulaRectangleRawInscribedSquareClosedCell (ε / 2) b) := by
  exact
    explicitFormulaRectangleRawInscribedSquareClosedCell_pairwiseDisjoint_of_closedRadiusControls
      T (ε / 2) (le_of_lt (finiteRectangle_halfRadius_pos hε))
      (explicitFormulaRectangle_rawSingularCoordinates_halfRadius_closedBalls_disjoint
        T ε hε hsep)
      a ha b hb hab

/-- Horizontal endpoints in the half-radius inscribed-square subdivision lie in the
closed horizontal span of the outer rectangle. -/
theorem explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints_mem_horizontal_uIcc_halfRadius
    (F : ExplicitFormulaContourFamily) (T ε : ℝ) (hε : 0 < ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    {x : ℝ}
    (hx : x ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T (ε / 2)) :
    x ∈ Set.uIcc F.c (1 - F.c) :=
  explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints_mem_horizontal_uIcc_of_closedRadiusControls
    F T (ε / 2)
    (le_of_lt (finiteRectangle_halfRadius_pos hε))
    (explicitFormulaRectangle_closedRadiusControls_halfRadius F T ε hε hclosed)
    hx

/-- Vertical endpoints in the half-radius inscribed-square subdivision lie in the closed
height interval of the outer rectangle. -/
theorem explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints_mem_vertical_Icc_halfRadius
    (F : ExplicitFormulaContourFamily) (T ε : ℝ) (hT_nonneg : 0 ≤ T) (hε : 0 < ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    {y : ℝ}
    (hy : y ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T (ε / 2)) :
    y ∈ Set.Icc (-T) T :=
  explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints_mem_vertical_Icc_of_closedRadiusControls
    F T (ε / 2) hT_nonneg
    (le_of_lt (finiteRectangle_halfRadius_pos hε))
    (explicitFormulaRectangle_closedRadiusControls_halfRadius F T ε hε hclosed)
    hy

/-- Negating each oriented edge contribution is the same as negating the grouped
four-edge expression. -/
theorem explicitFormulaRectangleEndpointDataBoxEdgeSums_neg_group
    (bottom top right left : ℂ) :
    (-bottom) - (-top) + ((-right) - (-left)) =
      -(bottom - top + (right - left)) := by
  calc
    (-bottom) - (-top) + ((-right) - (-left)) =
        ((-bottom) + -(-top)) + (((-right) + -(-left))) := by
      exact congrArg₂ Add.add
        (sub_eq_add_neg (-bottom) (-top))
        (sub_eq_add_neg (-right) (-left))
    _ = ((-bottom) + top) + (((-right) + left)) := by
      exact congrArg₂ Add.add
        (congrArg (fun z : ℂ => (-bottom) + z) (neg_neg top))
        (congrArg (fun z : ℂ => (-right) + z) (neg_neg left))
    _ = (top + (-bottom)) + (left + (-right)) := by
      exact congrArg₂ Add.add
        (add_comm (-bottom) top)
        (add_comm (-right) left)
    _ = (top - bottom) + (left - right) := by
      exact congrArg₂ Add.add
        (sub_eq_add_neg top bottom).symm
        (sub_eq_add_neg left right).symm
    _ = -(bottom - top) + (left - right) := by
      exact congrArg
        (fun z : ℂ => z + (left - right))
        (neg_sub bottom top).symm
    _ = -(bottom - top) + -(right - left) := by
      exact congrArg
        (fun z : ℂ => -(bottom - top) + z)
        (neg_sub right left).symm
    _ = -((bottom - top) + (right - left)) := by
      exact (neg_add (bottom - top) (right - left)).symm
    _ = -(bottom - top + (right - left)) := by
      rfl

/-- Side-specific constructor for the raw-edge-sum exposed-boundary collapse.  Once the
selected bottom/top/right/left box-side sums have been identified with their exposed
outer-minus-hole values, the combined four-side identity follows by algebraic
substitution. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinates_edgeSums_tangentBoundary_rawEdgeSums_of_sideSums
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (boxes : List ExplicitFormulaRectangleEndpointDataBoxEdge)
    (outerBottom outerTop outerRight outerLeft : ℂ)
    (houter :
      outerBottom - outerTop + (outerRight - outerLeft) =
        zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T))
    (hbottom :
      explicitFormulaRectangleBoxBottomEdgeIntegralSum f boxes =
        outerBottom -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
            f T ε)
    (htop :
      explicitFormulaRectangleBoxTopEdgeIntegralSum f boxes =
        outerTop -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
            f T ε)
    (hright :
      explicitFormulaRectangleBoxRightEdgeIntegralSum f boxes =
        outerRight -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
            f T ε)
    (hleft :
      explicitFormulaRectangleBoxLeftEdgeIntegralSum f boxes =
        outerLeft -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
            f T ε) :
    explicitFormulaRectangleBoxBottomEdgeIntegralSum f boxes -
        explicitFormulaRectangleBoxTopEdgeIntegralSum f boxes +
          (explicitFormulaRectangleBoxRightEdgeIntegralSum f boxes -
            explicitFormulaRectangleBoxLeftEdgeIntegralSum f boxes) =
      zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
        (explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
            f T ε -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
            f T ε +
            (explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
                f T ε -
              explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
                f T ε)) := by
  let B : ℂ := explicitFormulaRectangleBoxBottomEdgeIntegralSum f boxes
  let U : ℂ := explicitFormulaRectangleBoxTopEdgeIntegralSum f boxes
  let R : ℂ := explicitFormulaRectangleBoxRightEdgeIntegralSum f boxes
  let L : ℂ := explicitFormulaRectangleBoxLeftEdgeIntegralSum f boxes
  let b : ℂ :=
    explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum f T ε
  let u : ℂ :=
    explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum f T ε
  let r : ℂ :=
    explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum f T ε
  let l : ℂ :=
    explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum f T ε
  calc
    B - U + (R - L) =
        (outerBottom - b) - U + (R - L) := by
      exact congrArg (fun z : ℂ => z - U + (R - L)) hbottom
    _ = (outerBottom - b) - (outerTop - u) + (R - L) := by
      exact congrArg (fun z : ℂ => (outerBottom - b) - z + (R - L)) htop
    _ = (outerBottom - b) - (outerTop - u) + ((outerRight - r) - L) := by
      exact congrArg
        (fun z : ℂ => (outerBottom - b) - (outerTop - u) + (z - L))
        hright
    _ = (outerBottom - b) - (outerTop - u) + ((outerRight - r) - (outerLeft - l)) := by
      exact congrArg
        (fun z : ℂ => (outerBottom - b) - (outerTop - u) + ((outerRight - r) - z))
        hleft
    _ =
        (outerBottom - outerTop + (outerRight - outerLeft)) +
          ((-b) - (-u) + ((-r) - (-l))) := by
      exact
        (finiteRectangleSubdivisionEndpointBoundary_consEdgeAlgebra
          outerBottom outerTop outerRight outerLeft (-b) (-u) (-r) (-l)
        ).symm
    _ =
        (outerBottom - outerTop + (outerRight - outerLeft)) +
          -(b - u + (r - l)) := by
      exact congrArg
        (fun z : ℂ => (outerBottom - outerTop + (outerRight - outerLeft)) + z)
        (explicitFormulaRectangleEndpointDataBoxEdgeSums_neg_group b u r l)
    _ =
        (outerBottom - outerTop + (outerRight - outerLeft)) -
          (b - u + (r - l)) := by
      exact
        (sub_eq_add_neg
          (outerBottom - outerTop + (outerRight - outerLeft))
          (b - u + (r - l))).symm
    _ =
        zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
          (b - u + (r - l)) := by
      exact congrArg (fun z : ℂ => z - (b - u + (r - l))) houter

/-- The correctly oriented outer side values assemble to the tangent rectangle contour.
The horizontal values are negated because the selected sorted subdivision sums horizontal
intervals left-to-right, while the tangent contour contribution is top minus bottom. -/
theorem explicitFormulaRectangleTangentContour_eq_orientedOuterSideSums
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    (-(zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T))) -
        (-(zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T))) +
          (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
            zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I) =
      zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) := by
  let R : ℂ := zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I
  let L : ℂ := zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I
  let U : ℂ := zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T)
  let B : ℂ := zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T)
  calc
    (-B) - (-U) + (R - L) =
        ((-B) + -(-U)) + (R - L) := by
      exact congrArg (fun z : ℂ => z + (R - L)) (sub_eq_add_neg (-B) (-U))
    _ = ((-B) + U) + (R - L) := by
      exact congrArg
        (fun z : ℂ => ((-B) + z) + (R - L))
        (neg_neg U)
    _ = (U + (-B)) + (R - L) := by
      exact congrArg (fun z : ℂ => z + (R - L)) (add_comm (-B) U)
    _ = (U - B) + (R - L) := by
      exact congrArg (fun z : ℂ => z + (R - L)) (sub_eq_add_neg U B).symm
    _ = (R - L) + (U - B) := by
      exact add_comm (U - B) (R - L)
    _ = (R - L) + (U + -B) := by
      exact congrArg (fun z : ℂ => (R - L) + z) (sub_eq_add_neg U B)
    _ = ((R - L) + U) + -B := by
      exact (add_assoc (R - L) U (-B)).symm
    _ = (R - L + U) - B := by
      exact (sub_eq_add_neg (R - L + U) B).symm
    _ = R - L + U - B := by
      rfl
    _ = zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) := by
      rfl

/-- Box-coordinate horizontal contribution over the sorted selected grid is the
corresponding endpoint-data horizontal contribution. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinates_horizontalContribution_eq_selectedEndpointData
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    let boxes : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
      explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)
    explicitFormulaRectangleBoxBottomEdgeIntegralSum f boxes -
        explicitFormulaRectangleBoxTopEdgeIntegralSum f boxes =
      explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
          (explicitFormulaRectangleSelectedEndpointData F T ε) -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
          (explicitFormulaRectangleSelectedEndpointData F T ε) := by
  let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
    explicitFormulaRectangleSelectedEndpointData F T ε
  let boxes : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
    explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
      (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε)
      (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)
  have hboxes :
      data.map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d.boxEdgeCoordinates) =
        boxes :=
    explicitFormulaRectangleSelectedEndpointData_boxEdgeCoordinates_eq_sortedPairLists
      F T ε
  have hbottom :
      explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data =
        explicitFormulaRectangleBoxBottomEdgeIntegralSum f
          (data.map
            (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
              d.boxEdgeCoordinates)) :=
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum_eq_boxBottomEdgeIntegralSum
      f data
  have htop :
      explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data =
        explicitFormulaRectangleBoxTopEdgeIntegralSum f
          (data.map
            (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
              d.boxEdgeCoordinates)) :=
    explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum_eq_boxTopEdgeIntegralSum
      f data
  calc
    explicitFormulaRectangleBoxBottomEdgeIntegralSum f boxes -
        explicitFormulaRectangleBoxTopEdgeIntegralSum f boxes =
        explicitFormulaRectangleBoxBottomEdgeIntegralSum f
            (data.map
              (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                d.boxEdgeCoordinates)) -
          explicitFormulaRectangleBoxTopEdgeIntegralSum f boxes := by
      exact congrArg
        (fun z : List ExplicitFormulaRectangleEndpointDataBoxEdge =>
          explicitFormulaRectangleBoxBottomEdgeIntegralSum f z -
            explicitFormulaRectangleBoxTopEdgeIntegralSum f boxes)
        hboxes.symm
    _ =
        explicitFormulaRectangleBoxBottomEdgeIntegralSum f
            (data.map
              (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                d.boxEdgeCoordinates)) -
          explicitFormulaRectangleBoxTopEdgeIntegralSum f
            (data.map
              (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                d.boxEdgeCoordinates)) := by
      exact congrArg
        (fun z : List ExplicitFormulaRectangleEndpointDataBoxEdge =>
          explicitFormulaRectangleBoxBottomEdgeIntegralSum f
              (data.map
                (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  d.boxEdgeCoordinates)) -
            explicitFormulaRectangleBoxTopEdgeIntegralSum f z)
        hboxes.symm
    _ =
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data -
          explicitFormulaRectangleBoxTopEdgeIntegralSum f
            (data.map
              (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                d.boxEdgeCoordinates)) := by
      exact congrArg
        (fun z : ℂ =>
          z -
            explicitFormulaRectangleBoxTopEdgeIntegralSum f
              (data.map
                (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  d.boxEdgeCoordinates)))
        hbottom.symm
    _ =
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data := by
      exact congrArg
        (fun z : ℂ =>
          explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data - z)
        htop.symm

/-- Box-coordinate vertical contribution over the sorted selected grid is the
corresponding endpoint-data vertical contribution. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinates_verticalContribution_eq_selectedEndpointData
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    let boxes : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
      explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)
    explicitFormulaRectangleBoxRightEdgeIntegralSum f boxes -
        explicitFormulaRectangleBoxLeftEdgeIntegralSum f boxes =
      explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
          (explicitFormulaRectangleSelectedEndpointData F T ε) -
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
          (explicitFormulaRectangleSelectedEndpointData F T ε) := by
  let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
    explicitFormulaRectangleSelectedEndpointData F T ε
  let boxes : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
    explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
      (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε)
      (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)
  have hboxes :
      data.map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d.boxEdgeCoordinates) =
        boxes :=
    explicitFormulaRectangleSelectedEndpointData_boxEdgeCoordinates_eq_sortedPairLists
      F T ε
  have hright :
      explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data =
        explicitFormulaRectangleBoxRightEdgeIntegralSum f
          (data.map
            (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
              d.boxEdgeCoordinates)) :=
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum_eq_boxRightEdgeIntegralSum
      f data
  have hleft :
      explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data =
        explicitFormulaRectangleBoxLeftEdgeIntegralSum f
          (data.map
            (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
              d.boxEdgeCoordinates)) :=
    explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum_eq_boxLeftEdgeIntegralSum
      f data
  calc
    explicitFormulaRectangleBoxRightEdgeIntegralSum f boxes -
        explicitFormulaRectangleBoxLeftEdgeIntegralSum f boxes =
        explicitFormulaRectangleBoxRightEdgeIntegralSum f
            (data.map
              (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                d.boxEdgeCoordinates)) -
          explicitFormulaRectangleBoxLeftEdgeIntegralSum f boxes := by
      exact congrArg
        (fun z : List ExplicitFormulaRectangleEndpointDataBoxEdge =>
          explicitFormulaRectangleBoxRightEdgeIntegralSum f z -
            explicitFormulaRectangleBoxLeftEdgeIntegralSum f boxes)
        hboxes.symm
    _ =
        explicitFormulaRectangleBoxRightEdgeIntegralSum f
            (data.map
              (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                d.boxEdgeCoordinates)) -
          explicitFormulaRectangleBoxLeftEdgeIntegralSum f
            (data.map
              (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                d.boxEdgeCoordinates)) := by
      exact congrArg
        (fun z : List ExplicitFormulaRectangleEndpointDataBoxEdge =>
          explicitFormulaRectangleBoxRightEdgeIntegralSum f
              (data.map
                (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  d.boxEdgeCoordinates)) -
            explicitFormulaRectangleBoxLeftEdgeIntegralSum f z)
        hboxes.symm
    _ =
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
          explicitFormulaRectangleBoxLeftEdgeIntegralSum f
            (data.map
              (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                d.boxEdgeCoordinates)) := by
      exact congrArg
        (fun z : ℂ =>
          z -
            explicitFormulaRectangleBoxLeftEdgeIntegralSum f
              (data.map
                (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  d.boxEdgeCoordinates)))
        hright.symm
    _ =
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data := by
      exact congrArg
        (fun z : ℂ =>
          explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data - z)
        hleft.symm

/-- Endpoint-data horizontal grouped contribution over selected crossed adjacent-pair
lists splits into the selected fixed row plus the remaining rows. -/
theorem explicitFormulaRectangleSelectedEndpointDataHorizontalContribution_pairLists_cons
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
    let whole : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          (xpair :: rest) ypairs)
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f whole -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f whole =
      (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f firstRow -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f firstRow) +
        (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f remaining -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f remaining) := by
  let firstRow : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
        xpair ypairs)
  let remaining : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
        rest ypairs)
  let whole : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
        (xpair :: rest) ypairs)
  have hbottom :
      explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f whole =
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f firstRow +
          explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f remaining :=
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum_selectedPairLists_cons
      f xpair rest ypairs
  have htop :
      explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f whole =
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f firstRow +
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f remaining :=
    explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum_selectedPairLists_cons
      f xpair rest ypairs
  calc
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f whole -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f whole =
        (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f firstRow +
            explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f remaining) -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f whole := by
      exact congrArg
        (fun z : ℂ =>
          z - explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f whole)
        hbottom
    _ =
        (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f firstRow +
            explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f remaining) -
          (explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f firstRow +
            explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f remaining) := by
      exact congrArg
        (fun z : ℂ =>
          (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f firstRow +
              explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f remaining) - z)
        htop
    _ =
        (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f firstRow -
            explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f firstRow) +
          (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f remaining -
            explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f remaining) := by
      exact
        explicitFormulaRectangleBoxHorizontalContribution_consAlgebra
          (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f firstRow)
          (explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f firstRow)
          (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f remaining)
          (explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f remaining)

/-- Endpoint-data vertical grouped contribution over selected crossed adjacent-pair
lists splits into the selected fixed row plus the remaining rows. -/
theorem explicitFormulaRectangleSelectedEndpointDataVerticalContribution_pairLists_cons
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
    let whole : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          (xpair :: rest) ypairs)
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f whole -
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f whole =
      (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f firstRow -
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f firstRow) +
        (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f remaining -
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f remaining) := by
  let firstRow : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
        xpair ypairs)
  let remaining : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
        rest ypairs)
  let whole : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
        (xpair :: rest) ypairs)
  have hright :
      explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f whole =
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f firstRow +
          explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f remaining :=
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum_selectedPairLists_cons
      f xpair rest ypairs
  have hleft :
      explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f whole =
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f firstRow +
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f remaining :=
    explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum_selectedPairLists_cons
      f xpair rest ypairs
  calc
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f whole -
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f whole =
        (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f firstRow +
            explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f remaining) -
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f whole := by
      exact congrArg
        (fun z : ℂ =>
          z - explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f whole)
        hright
    _ =
        (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f firstRow +
            explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f remaining) -
          (explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f firstRow +
            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f remaining) := by
      exact congrArg
        (fun z : ℂ =>
          (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f firstRow +
              explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f remaining) - z)
        hleft
    _ =
        (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f firstRow -
            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f firstRow) +
          (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f remaining -
            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f remaining) := by
      exact
        explicitFormulaRectangleBoxVerticalContribution_consAlgebra
          (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f firstRow)
          (explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f firstRow)
          (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f remaining)
          (explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f remaining)

/-- Endpoint-data horizontal grouped contribution over an empty selected crossed
adjacent-pair source list is zero. -/
theorem explicitFormulaRectangleSelectedEndpointDataHorizontalContribution_pairLists_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
              ([] : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)) ypairs)) -
    explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
              ([] : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)) ypairs)) =
      0 := by
  calc
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
              ([] : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)) ypairs)) -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
              ([] : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)) ypairs)) =
        0 - 0 := by
      rfl
    _ = 0 := by
      exact sub_self 0

/-- Endpoint-data vertical grouped contribution over an empty selected crossed
adjacent-pair source list is zero. -/
theorem explicitFormulaRectangleSelectedEndpointDataVerticalContribution_pairLists_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
              ([] : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)) ypairs)) -
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
              ([] : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)) ypairs)) =
      0 := by
  calc
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
              ([] : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)) ypairs)) -
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
              ([] : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)) ypairs)) =
        0 - 0 := by
      rfl
    _ = 0 := by
      exact sub_self 0

/-- Endpoint-data horizontal grouped contribution over sorted selected rows splits at
the head horizontal adjacent pair. -/
theorem explicitFormulaRectangleSelectedEndpointDataHorizontalContribution_sortedPairLists_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (rest : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)) :
    let firstRow : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
          xpair
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε))
    let remaining : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          rest
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε))
    let whole : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          (xpair :: rest)
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε))
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f whole -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f whole =
      (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f firstRow -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f firstRow) +
        (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f remaining -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f remaining) :=
  explicitFormulaRectangleSelectedEndpointDataHorizontalContribution_pairLists_cons
    f xpair rest (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)

/-- Endpoint-data horizontal grouped contribution over an empty sorted horizontal row list
is zero. -/
theorem explicitFormulaRectangleSelectedEndpointDataHorizontalContribution_sortedPairLists_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction) :
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
              ([] : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
              (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε))) -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
              ([] : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
              (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε))) =
      0 :=
  explicitFormulaRectangleSelectedEndpointDataHorizontalContribution_pairLists_nil
    f (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)

/-- Endpoint-data vertical grouped contribution over sorted selected rows splits at the
head horizontal adjacent pair. -/
theorem explicitFormulaRectangleSelectedEndpointDataVerticalContribution_sortedPairLists_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (rest : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)) :
    let firstRow : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
          xpair
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε))
    let remaining : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          rest
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε))
    let whole : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          (xpair :: rest)
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε))
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f whole -
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f whole =
      (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f firstRow -
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f firstRow) +
        (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f remaining -
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f remaining) :=
  explicitFormulaRectangleSelectedEndpointDataVerticalContribution_pairLists_cons
    f xpair rest (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)

/-- Endpoint-data vertical grouped contribution over an empty sorted horizontal row list
is zero. -/
theorem explicitFormulaRectangleSelectedEndpointDataVerticalContribution_sortedPairLists_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction) :
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
              ([] : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
              (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε))) -
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
              ([] : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
              (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε))) =
      0 :=
  explicitFormulaRectangleSelectedEndpointDataVerticalContribution_pairLists_nil
    f (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)

/-- Endpoint-data horizontal grouped contribution for one selected fixed row follows the
coordinate-omission filter at the head vertical adjacent pair. -/
theorem explicitFormulaRectangleSelectedEndpointDataHorizontalContribution_fixedX_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε)
    (rest : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    let row : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
          xpair (ypair :: rest))
    let tail : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
          xpair rest)
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f row -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f row =
      if homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        (explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
              (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit) -
          explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
              (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit)) +
          (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f tail -
            explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f tail)
      else
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f tail -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f tail := by
  if homit :
      explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
    let row : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
          xpair (ypair :: rest))
    let tail : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
          xpair rest)
    let head : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε :=
      explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit
    have hbottom :
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f row =
          explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f head +
            explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f tail :=
      have hcons :=
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum_selectedFixedX_cons
          f xpair ypair rest
      have hbranch :
          (if h :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
              (({ xpair := xpair
                  ypair := ypair
                  homit := h } :
                  ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε).toEndpointData) +
              explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f tail
          else
            explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f tail) =
            explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f head +
              explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f tail := by
        exact dif_pos homit
      Eq.trans hcons hbranch
    have htop :
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f row =
          explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f head +
            explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f tail :=
      have hcons :=
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum_selectedFixedX_cons
          f xpair ypair rest
      have hbranch :
          (if h :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
              (({ xpair := xpair
                  ypair := ypair
                  homit := h } :
                  ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε).toEndpointData) +
              explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f tail
          else
            explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f tail) =
            explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f head +
              explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f tail := by
        exact dif_pos homit
      Eq.trans hcons hbranch
    calc
      explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f row -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f row =
          (explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f head +
              explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f tail) -
            explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f row := by
        exact congrArg
          (fun z : ℂ =>
            z - explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f row)
          hbottom
      _ =
          (explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f head +
              explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f tail) -
            (explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f head +
              explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f tail) := by
        exact congrArg
          (fun z : ℂ =>
            (explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f head +
                explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f tail) - z)
          htop
      _ =
          (explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f head -
            explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f head) +
            (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f tail -
              explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f tail) := by
        exact
          explicitFormulaRectangleBoxHorizontalContribution_consAlgebra
            (explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f head)
            (explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f head)
            (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f tail)
            (explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f tail)
      _ =
          if _homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            (explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
                  (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair _homit) -
              explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
                  (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair _homit)) +
              (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f tail -
                explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f tail)
          else
            explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f tail -
              explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f tail := by
        have hbranch :
            (if _homit :
                explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
              (explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
                    (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair _homit) -
                explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
                    (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair _homit)) +
                (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f tail -
                  explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f tail)
            else
              explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f tail -
                explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f tail) =
              (explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f head -
                explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f head) +
                (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f tail -
                  explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f tail) := by
          exact dif_pos homit
        exact hbranch.symm
  else
    let row : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
          xpair (ypair :: rest))
    let tail : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
          xpair rest)
    have hbottom :
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f row =
          explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f tail :=
      have hcons :=
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum_selectedFixedX_cons
          f xpair ypair rest
      have hbranch :
          (if h :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
              (({ xpair := xpair
                  ypair := ypair
                  homit := h } :
                  ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε).toEndpointData) +
              explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f tail
          else
            explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f tail) =
            explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f tail := by
        exact dif_neg homit
      Eq.trans hcons hbranch
    have htop :
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f row =
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f tail :=
      have hcons :=
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum_selectedFixedX_cons
          f xpair ypair rest
      have hbranch :
          (if h :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
              (({ xpair := xpair
                  ypair := ypair
                  homit := h } :
                  ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε).toEndpointData) +
              explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f tail
          else
            explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f tail) =
            explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f tail := by
        exact dif_neg homit
      Eq.trans hcons hbranch
    calc
      explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f row -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f row =
          explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f tail -
            explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f row := by
        exact congrArg
          (fun z : ℂ =>
            z - explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f row)
          hbottom
      _ =
          explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f tail -
            explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f tail := by
        exact congrArg
          (fun z : ℂ =>
            explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f tail - z)
          htop
      _ =
          if _homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            (explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
                  (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair _homit) -
              explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
                  (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair _homit)) +
              (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f tail -
                explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f tail)
          else
            explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f tail -
              explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f tail := by
        have hbranch :
            (if _homit :
                explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
              (explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
                    (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair _homit) -
                explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
                    (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair _homit)) +
                (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f tail -
                  explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f tail)
            else
              explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f tail -
                explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f tail) =
              explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f tail -
                explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f tail := by
          exact dif_neg homit
        exact hbranch.symm

/-- Endpoint-data vertical grouped contribution for one selected fixed row follows the
coordinate-omission filter at the head vertical adjacent pair. -/
theorem explicitFormulaRectangleSelectedEndpointDataVerticalContribution_fixedX_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε)
    (rest : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    let row : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
          xpair (ypair :: rest))
    let tail : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
          xpair rest)
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f row -
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f row =
      if homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        (explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
              (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit) -
          explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f
              (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit)) +
          (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f tail -
            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f tail)
      else
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f tail -
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f tail := by
  if homit :
      explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
    let row : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
          xpair (ypair :: rest))
    let tail : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
          xpair rest)
    let head : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε :=
      explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair homit
    have hright :
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f row =
          explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f head +
            explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f tail :=
      have hcons :=
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum_selectedFixedX_cons
          f xpair ypair rest
      have hbranch :
          (if h :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
              (({ xpair := xpair
                  ypair := ypair
                  homit := h } :
                  ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε).toEndpointData) +
              explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f tail
          else
            explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f tail) =
            explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f head +
              explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f tail := by
        exact dif_pos homit
      Eq.trans hcons hbranch
    have hleft :
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f row =
          explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f head +
            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f tail :=
      have hcons :=
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum_selectedFixedX_cons
          f xpair ypair rest
      have hbranch :
          (if h :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f
              (({ xpair := xpair
                  ypair := ypair
                  homit := h } :
                  ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε).toEndpointData) +
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f tail
          else
            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f tail) =
            explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f head +
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f tail := by
        exact dif_pos homit
      Eq.trans hcons hbranch
    calc
      explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f row -
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f row =
          (explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f head +
              explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f tail) -
            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f row := by
        exact congrArg
          (fun z : ℂ =>
            z - explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f row)
          hright
      _ =
          (explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f head +
              explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f tail) -
            (explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f head +
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f tail) := by
        exact congrArg
          (fun z : ℂ =>
            (explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f head +
                explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f tail) - z)
          hleft
      _ =
          (explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f head -
            explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f head) +
            (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f tail -
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f tail) := by
        exact
          explicitFormulaRectangleBoxVerticalContribution_consAlgebra
            (explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f head)
            (explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f head)
            (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f tail)
            (explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f tail)
      _ =
          if _homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            (explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
                  (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair _homit) -
              explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f
                  (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair _homit)) +
              (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f tail -
                explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f tail)
          else
            explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f tail -
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f tail := by
        have hbranch :
            (if _homit :
                explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
              (explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
                    (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair _homit) -
                explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f
                    (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair _homit)) +
                (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f tail -
                  explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f tail)
            else
              explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f tail -
                explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f tail) =
              (explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f head -
                explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f head) +
                (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f tail -
                  explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f tail) := by
          exact dif_pos homit
        exact hbranch.symm
  else
    let row : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
          xpair (ypair :: rest))
    let tail : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
          xpair rest)
    have hright :
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f row =
          explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f tail :=
      have hcons :=
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum_selectedFixedX_cons
          f xpair ypair rest
      have hbranch :
          (if h :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
              (({ xpair := xpair
                  ypair := ypair
                  homit := h } :
                  ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε).toEndpointData) +
              explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f tail
          else
            explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f tail) =
            explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f tail := by
        exact dif_neg homit
      Eq.trans hcons hbranch
    have hleft :
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f row =
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f tail :=
      have hcons :=
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum_selectedFixedX_cons
          f xpair ypair rest
      have hbranch :
          (if h :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f
              (({ xpair := xpair
                  ypair := ypair
                  homit := h } :
                  ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε).toEndpointData) +
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f tail
          else
            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f tail) =
            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f tail := by
        exact dif_neg homit
      Eq.trans hcons hbranch
    calc
      explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f row -
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f row =
          explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f tail -
            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f row := by
        exact congrArg
          (fun z : ℂ =>
            z - explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f row)
          hright
      _ =
          explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f tail -
            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f tail := by
        exact congrArg
          (fun z : ℂ =>
            explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f tail - z)
          hleft
      _ =
          if _homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            (explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
                  (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair _homit) -
              explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f
                  (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair _homit)) +
              (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f tail -
                explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f tail)
          else
            explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f tail -
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f tail := by
        have hbranch :
            (if _homit :
                explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
              (explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
                    (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair _homit) -
                explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f
                    (explicitFormulaRectangleSelectedAdjacentEndpointData xpair ypair _homit)) +
                (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f tail -
                  explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f tail)
            else
              explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f tail -
                explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f tail) =
              explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f tail -
                explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f tail := by
          exact dif_neg homit
        exact hbranch.symm

/-- Endpoint-data horizontal grouped contribution for one selected fixed row is zero over
an empty vertical-pair source list. -/
theorem explicitFormulaRectangleSelectedEndpointDataHorizontalContribution_fixedX_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
              xpair ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)))) -
    explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
              xpair ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)))) =
      0 := by
  calc
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
              xpair ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)))) -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
              xpair ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)))) =
        0 - 0 := by
      rfl
    _ = 0 := by
      exact sub_self 0

/-- Endpoint-data vertical grouped contribution for one selected fixed row is zero over
an empty vertical-pair source list. -/
theorem explicitFormulaRectangleSelectedEndpointDataVerticalContribution_fixedX_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
              xpair ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)))) -
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
              xpair ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)))) =
      0 := by
  calc
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
              xpair ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)))) -
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
              xpair ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)))) =
        0 - 0 := by
      rfl
    _ = 0 := by
      exact sub_self 0

/-- Horizontal grouped contribution over selected endpoint data with sorted vertical
adjacent-pair source list splits at the head horizontal adjacent pair. -/
theorem explicitFormulaRectangleSelectedEndpointDataHorizontalContribution_sortedY_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (rest : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)) :
    let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε) :=
      explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε
    let firstRow : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
          xpair ypairs)
    let remaining : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          rest ypairs)
    let whole : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          (xpair :: rest) ypairs)
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f whole -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f whole =
      (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f firstRow -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f firstRow) +
        (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f remaining -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f remaining) :=
  explicitFormulaRectangleSelectedEndpointDataHorizontalContribution_pairLists_cons
    f xpair rest (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)

/-- Vertical grouped contribution over selected endpoint data with sorted vertical
adjacent-pair source list splits at the head horizontal adjacent pair. -/
theorem explicitFormulaRectangleSelectedEndpointDataVerticalContribution_sortedY_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (rest : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)) :
    let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε) :=
      explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε
    let firstRow : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
          xpair ypairs)
    let remaining : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          rest ypairs)
    let whole : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          (xpair :: rest) ypairs)
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f whole -
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f whole =
      (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f firstRow -
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f firstRow) +
        (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f remaining -
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f remaining) :=
  explicitFormulaRectangleSelectedEndpointDataVerticalContribution_pairLists_cons
    f xpair rest (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)

/-- Horizontal grouped contribution over an empty sorted horizontal adjacent-pair source
list is zero. -/
theorem explicitFormulaRectangleSelectedEndpointDataHorizontalContribution_sortedY_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction) :
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
              ([] : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
              (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε))) -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
              ([] : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
              (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε))) =
      0 :=
  explicitFormulaRectangleSelectedEndpointDataHorizontalContribution_pairLists_nil
    f (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)

/-- Vertical grouped contribution over an empty sorted horizontal adjacent-pair source
list is zero. -/
theorem explicitFormulaRectangleSelectedEndpointDataVerticalContribution_sortedY_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction) :
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
              ([] : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
              (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε))) -
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
              ([] : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
              (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε))) =
      0 :=
  explicitFormulaRectangleSelectedEndpointDataVerticalContribution_pairLists_nil
    f (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
