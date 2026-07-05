import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part19

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
## Part20 01: BoxEdgeAlgebra
-/


/-- Finite-sum algebra for rebracketing bottom/top/right/left edge contributions. -/
theorem finiteRectangleSubdivisionEndpointBoundary_finsetEdgeAlgebra
    (S : Finset ℂ) (bottom top right left : ℂ → ℂ) :
    (∑ a in S, (bottom a - top a + (right a - left a))) =
      (∑ a in S, bottom a) - (∑ a in S, top a) +
        ((∑ a in S, right a) - (∑ a in S, left a)) := by
  let B : ℂ := ∑ a in S, bottom a
  let U : ℂ := ∑ a in S, top a
  let R : ℂ := ∑ a in S, right a
  let L : ℂ := ∑ a in S, left a
  have hsplit :
      (∑ a in S, (bottom a - top a + (right a - left a))) =
        (∑ a in S, (bottom a - top a)) +
          (∑ a in S, (right a - left a)) := by
    exact
      Finset.sum_add_distrib
        (s := S)
        (f := fun a : ℂ => bottom a - top a)
        (g := fun a : ℂ => right a - left a)
  have hbottom_top :
      (∑ a in S, (bottom a - top a)) = B - U := by
    calc
      (∑ a in S, (bottom a - top a)) =
          (∑ a in S, (bottom a + -top a)) := by
        exact Finset.sum_congr (Eq.refl _)
          (fun a _ha => sub_eq_add_neg (bottom a) (top a))
      _ =
          (∑ a in S, bottom a) +
            (∑ a in S, -top a) := by
        exact Finset.sum_add_distrib
          (s := S)
          (f := bottom)
          (g := fun a : ℂ => -top a)
      _ =
          (∑ a in S, bottom a) +
            -(∑ a in S, top a) := by
        exact congrArg
          (fun z : ℂ => (∑ a in S, bottom a) + z)
          (Finset.sum_neg_distrib)
      _ = B - U := by
        exact (sub_eq_add_neg B U).symm
  have hright_left :
      (∑ a in S, (right a - left a)) = R - L := by
    calc
      (∑ a in S, (right a - left a)) =
          (∑ a in S, (right a + -left a)) := by
        exact Finset.sum_congr (Eq.refl _)
          (fun a _ha => sub_eq_add_neg (right a) (left a))
      _ =
          (∑ a in S, right a) +
            (∑ a in S, -left a) := by
        exact Finset.sum_add_distrib
          (s := S)
          (f := right)
          (g := fun a : ℂ => -left a)
      _ =
          (∑ a in S, right a) +
            -(∑ a in S, left a) := by
        exact congrArg
          (fun z : ℂ => (∑ a in S, right a) + z)
          (Finset.sum_neg_distrib)
      _ = R - L := by
        exact (sub_eq_add_neg R L).symm
  calc
    (∑ a in S, (bottom a - top a + (right a - left a))) =
        (∑ a in S, (bottom a - top a)) +
          (∑ a in S, (right a - left a)) := by
      exact hsplit
    _ = (B - U) + (∑ a in S, (right a - left a)) := by
      exact congrArg
        (fun z : ℂ => z + (∑ a in S, (right a - left a)))
        hbottom_top
    _ = (B - U) + (R - L) := by
      exact congrArg (fun z : ℂ => (B - U) + z) hright_left
    _ =
      (∑ a in S, bottom a) - (∑ a in S, top a) +
        ((∑ a in S, right a) - (∑ a in S, left a)) := by
      let hB : B = ∑ a in S, bottom a := Eq.refl B
      let hU : U = ∑ a in S, top a := Eq.refl U
      let hR : R = ∑ a in S, right a := Eq.refl R
      let hL : L = ∑ a in S, left a := Eq.refl L
      exact
        congrArg₂ HAdd.hAdd
          (congrArg₂ HSub.hSub hB hU)
          (congrArg₂ HSub.hSub hR hL)
/-- Coordinate box of one endpoint-data cell: horizontal endpoints together with vertical
endpoints.  Unlike a single side label, this keeps enough endpoint data for every side
integral to be definitionally identical to the existing cell-edge definitions. -/
abbrev ExplicitFormulaRectangleEndpointDataBoxEdge : Type :=
  (ℝ × ℝ) × (ℝ × ℝ)

/-- Box label carried by one proof-carrying endpoint-data cell. -/
def ExplicitFormulaRectangleRegularGridCellEndpointData.boxEdgeCoordinates
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :
    ExplicitFormulaRectangleEndpointDataBoxEdge :=
  ((d.x₀, d.x₁), (d.y₀, d.y₁))

/-- Lower-left complex corner of a full endpoint-data box label. -/
def explicitFormulaRectangleEndpointDataBoxLowerCorner
    (edge : ExplicitFormulaRectangleEndpointDataBoxEdge) : ℂ :=
  (edge.1.1 : ℂ) + (edge.2.1 : ℂ) * Complex.I

/-- Upper-right complex corner of a full endpoint-data box label. -/
def explicitFormulaRectangleEndpointDataBoxUpperCorner
    (edge : ExplicitFormulaRectangleEndpointDataBoxEdge) : ℂ :=
  (edge.1.2 : ℂ) + (edge.2.2 : ℂ) * Complex.I

/-- Bottom edge integral read from a full endpoint-data box label. -/
noncomputable def explicitFormulaRectangleBoxBottomEdgeIntegral
    (f : ZetaAdmissibleFunction)
    (edge : ExplicitFormulaRectangleEndpointDataBoxEdge) : ℂ :=
  ∫ x : ℝ in
      ((edge.1.1 : ℂ) + (edge.2.1 : ℂ) * Complex.I).re..
        ((edge.1.2 : ℂ) + (edge.2.2 : ℂ) * Complex.I).re,
    zetaCompletedExplicitFormulaContourIntegrand f
      (x + ((edge.1.1 : ℂ) + (edge.2.1 : ℂ) * Complex.I).im * Complex.I)

/-- Top edge integral read from a full endpoint-data box label. -/
noncomputable def explicitFormulaRectangleBoxTopEdgeIntegral
    (f : ZetaAdmissibleFunction)
    (edge : ExplicitFormulaRectangleEndpointDataBoxEdge) : ℂ :=
  ∫ x : ℝ in
      ((edge.1.1 : ℂ) + (edge.2.1 : ℂ) * Complex.I).re..
        ((edge.1.2 : ℂ) + (edge.2.2 : ℂ) * Complex.I).re,
    zetaCompletedExplicitFormulaContourIntegrand f
      (x + ((edge.1.2 : ℂ) + (edge.2.2 : ℂ) * Complex.I).im * Complex.I)

/-- Right vertical edge integral read from a full endpoint-data box label. -/
noncomputable def explicitFormulaRectangleBoxRightEdgeIntegral
    (f : ZetaAdmissibleFunction)
    (edge : ExplicitFormulaRectangleEndpointDataBoxEdge) : ℂ :=
  Complex.I •
    ∫ y : ℝ in
      ((edge.1.1 : ℂ) + (edge.2.1 : ℂ) * Complex.I).im..
        ((edge.1.2 : ℂ) + (edge.2.2 : ℂ) * Complex.I).im,
      zetaCompletedExplicitFormulaContourIntegrand f
        (((edge.1.2 : ℂ) + (edge.2.2 : ℂ) * Complex.I).re + y * Complex.I)

/-- Left vertical edge integral read from a full endpoint-data box label. -/
noncomputable def explicitFormulaRectangleBoxLeftEdgeIntegral
    (f : ZetaAdmissibleFunction)
    (edge : ExplicitFormulaRectangleEndpointDataBoxEdge) : ℂ :=
  Complex.I •
    ∫ y : ℝ in
      ((edge.1.1 : ℂ) + (edge.2.1 : ℂ) * Complex.I).im..
        ((edge.1.2 : ℂ) + (edge.2.2 : ℂ) * Complex.I).im,
      zetaCompletedExplicitFormulaContourIntegrand f
        (((edge.1.1 : ℂ) + (edge.2.1 : ℂ) * Complex.I).re + y * Complex.I)

/-- A cell bottom edge is the bottom integral of its full box label. -/
theorem explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge_eq_boxIntegral
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :
    explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f d =
      explicitFormulaRectangleBoxBottomEdgeIntegral f d.boxEdgeCoordinates := by
  exact Eq.refl _
/-- A cell top edge is the top integral of its full box label. -/
theorem explicitFormulaRectangleRegularGridCellEndpointDataTopEdge_eq_boxIntegral
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :
    explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f d =
      explicitFormulaRectangleBoxTopEdgeIntegral f d.boxEdgeCoordinates := by
  exact Eq.refl _
/-- A cell right edge is the right integral of its full box label. -/
theorem explicitFormulaRectangleRegularGridCellEndpointDataRightEdge_eq_boxIntegral
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :
    explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f d =
      explicitFormulaRectangleBoxRightEdgeIntegral f d.boxEdgeCoordinates := by
  exact Eq.refl _
/-- A cell left edge is the left integral of its full box label. -/
theorem explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge_eq_boxIntegral
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :
    explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f d =
      explicitFormulaRectangleBoxLeftEdgeIntegral f d.boxEdgeCoordinates := by
  exact Eq.refl _
/-- The four oriented side integrals of a full endpoint-data box reassemble as the
standard finite-rectangle cell boundary integral between its lower-left and upper-right
corners. -/
theorem explicitFormulaRectangleEndpointDataBoxBoundary_eq_cellBoundary
    (f : ZetaAdmissibleFunction)
    (edge : ExplicitFormulaRectangleEndpointDataBoxEdge) :
    explicitFormulaRectangleBoxBottomEdgeIntegral f edge -
        explicitFormulaRectangleBoxTopEdgeIntegral f edge +
          (explicitFormulaRectangleBoxRightEdgeIntegral f edge -
            explicitFormulaRectangleBoxLeftEdgeIntegral f edge) =
      finiteRectangleSubdivisionCellBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
        (explicitFormulaRectangleEndpointDataBoxLowerCorner edge)
        (explicitFormulaRectangleEndpointDataBoxUpperCorner edge) := by
  let A : ℂ := explicitFormulaRectangleBoxBottomEdgeIntegral f edge
  let B : ℂ := explicitFormulaRectangleBoxTopEdgeIntegral f edge
  let C : ℂ := explicitFormulaRectangleBoxRightEdgeIntegral f edge
  let D : ℂ := explicitFormulaRectangleBoxLeftEdgeIntegral f edge
  calc
    explicitFormulaRectangleBoxBottomEdgeIntegral f edge -
        explicitFormulaRectangleBoxTopEdgeIntegral f edge +
          (explicitFormulaRectangleBoxRightEdgeIntegral f edge -
            explicitFormulaRectangleBoxLeftEdgeIntegral f edge) =
        (A - B) + (C + -D) := by
      exact congrArg
        (fun z : ℂ => (A - B) + z)
        (sub_eq_add_neg C D)
    _ = ((A - B) + C) + -D := by
      exact (add_assoc (A - B) C (-D)).symm
    _ = (A - B + C) - D := by
      exact (sub_eq_add_neg (A - B + C) D).symm
    _ =
        finiteRectangleSubdivisionCellBoundaryIntegral
          (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
          (explicitFormulaRectangleEndpointDataBoxLowerCorner edge)
          (explicitFormulaRectangleEndpointDataBoxUpperCorner edge) := by
      exact Eq.refl _
noncomputable def explicitFormulaRectangleHorizontalRealEndpointIntegral
    (f : ZetaAdmissibleFunction) (x₀ x₁ y : ℝ) : ℂ :=
  ∫ x : ℝ in x₀..x₁,
    zetaCompletedExplicitFormulaContourIntegrand f
      (x + (y : ℂ) * Complex.I)

noncomputable def explicitFormulaRectangleVerticalRealEndpointIntegral
    (f : ZetaAdmissibleFunction) (y₀ y₁ x : ℝ) : ℂ :=
  Complex.I •
    ∫ y : ℝ in y₀..y₁,
      zetaCompletedExplicitFormulaContourIntegrand f
        ((x : ℂ) + y * Complex.I)

/-- Integral carried by a bottom-oriented horizontal endpoint-data edge label.  The
definition deliberately matches `...BottomEdge` after taking `bottomEdgeCoordinates`. -/
noncomputable def explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
    (f : ZetaAdmissibleFunction)
    (edge : ExplicitFormulaRectangleHorizontalEndpointDataEdge) : ℂ :=
  explicitFormulaRectangleHorizontalRealEndpointIntegral f edge.1.1 edge.1.2 edge.2

/-- Integral carried by a top-oriented horizontal endpoint-data edge label.  The
definition records the coordinate label; equality with `...TopEdge` additionally uses
the fact that `x + yi` has imaginary coordinate `y`. -/
noncomputable def explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
    (f : ZetaAdmissibleFunction)
    (edge : ExplicitFormulaRectangleHorizontalEndpointDataEdge) : ℂ :=
  explicitFormulaRectangleHorizontalRealEndpointIntegral f edge.1.1 edge.1.2 edge.2

/-- Integral carried by a right-oriented vertical endpoint-data edge label.  The
definition records the coordinate label; equality with `...RightEdge` additionally uses
the fact that `x + yi` has imaginary coordinate `y`. -/
noncomputable def explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
    (f : ZetaAdmissibleFunction)
    (edge : ExplicitFormulaRectangleVerticalEndpointDataEdge) : ℂ :=
  explicitFormulaRectangleVerticalRealEndpointIntegral f edge.1.1 edge.1.2 edge.2

/-- Integral carried by a left-oriented vertical endpoint-data edge label.  The definition
records the coordinate label; equality with `...LeftEdge` additionally uses the fact that
`x + yi` has imaginary coordinate `y`. -/
noncomputable def explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
    (f : ZetaAdmissibleFunction)
    (edge : ExplicitFormulaRectangleVerticalEndpointDataEdge) : ℂ :=
  explicitFormulaRectangleVerticalRealEndpointIntegral f edge.1.1 edge.1.2 edge.2

/-- A cell bottom edge is the bottom-oriented integral of its bottom coordinate label. -/
theorem explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge_eq_coordinateIntegral
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :
    explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f d =
      explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
        f d.bottomEdgeCoordinates := by
  cases d with
  | mk x₀ x₁ y₀ y₁ hx₀mem hx₁mem hy₀mem hy₁mem
      hx_order hy_order hx_adj hy_adj homit =>
  have hx₀ : (((x₀ : ℂ) + (y₀ : ℂ) * Complex.I).re) = x₀ :=
    ofReal_add_mul_I_re x₀ y₀
  have hx₁ : (((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).re) = x₁ :=
    ofReal_add_mul_I_re x₁ y₁
  have hy₀ : (((x₀ : ℂ) + (y₀ : ℂ) * Complex.I).im) = y₀ :=
    ofReal_add_mul_I_im x₀ y₀
  calc
    explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
        ⟨x₀, x₁, y₀, y₁, hx₀mem, hx₁mem, hy₀mem, hy₁mem,
          hx_order, hy_order, hx_adj, hy_adj, homit⟩ =
        explicitFormulaRectangleHorizontalRealEndpointIntegral f
          (((x₀ : ℂ) + (y₀ : ℂ) * Complex.I).re)
          (((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).re)
          (((x₀ : ℂ) + (y₀ : ℂ) * Complex.I).im) := by
      exact Eq.refl _
    _ =
        explicitFormulaRectangleHorizontalRealEndpointIntegral f x₀ x₁ y₀ := by
      calc
        explicitFormulaRectangleHorizontalRealEndpointIntegral f
            (((x₀ : ℂ) + (y₀ : ℂ) * Complex.I).re)
            (((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).re)
            (((x₀ : ℂ) + (y₀ : ℂ) * Complex.I).im) =
            explicitFormulaRectangleHorizontalRealEndpointIntegral f
              x₀
              (((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).re)
              (((x₀ : ℂ) + (y₀ : ℂ) * Complex.I).im) := by
          exact congrArg
            (fun t : ℝ =>
              explicitFormulaRectangleHorizontalRealEndpointIntegral f t
                (((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).re)
                (((x₀ : ℂ) + (y₀ : ℂ) * Complex.I).im))
            hx₀
        _ =
            explicitFormulaRectangleHorizontalRealEndpointIntegral f
              x₀ x₁
              (((x₀ : ℂ) + (y₀ : ℂ) * Complex.I).im) := by
          exact congrArg
            (fun t : ℝ =>
              explicitFormulaRectangleHorizontalRealEndpointIntegral f x₀ t
                (((x₀ : ℂ) + (y₀ : ℂ) * Complex.I).im))
            hx₁
        _ =
            explicitFormulaRectangleHorizontalRealEndpointIntegral f x₀ x₁ y₀ := by
          exact congrArg
            (fun t : ℝ => explicitFormulaRectangleHorizontalRealEndpointIntegral f x₀ x₁ t)
            hy₀
    _ =
        explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
          f ((x₀, x₁), y₀) := by
      exact Eq.refl _
/-- A cell top edge is the top-oriented integral of its top coordinate label. -/
theorem explicitFormulaRectangleRegularGridCellEndpointDataTopEdge_eq_coordinateIntegral
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :
    explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f d =
      explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
        f d.topEdgeCoordinates := by
  cases d with
  | mk x₀ x₁ y₀ y₁ hx₀mem hx₁mem hy₀mem hy₁mem
      hx_order hy_order hx_adj hy_adj homit =>
  have hx₀ : (((x₀ : ℂ) + (y₀ : ℂ) * Complex.I).re) = x₀ :=
    ofReal_add_mul_I_re x₀ y₀
  have hx₁ : (((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).re) = x₁ :=
    ofReal_add_mul_I_re x₁ y₁
  have hy₁ : (((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).im) = y₁ :=
    ofReal_add_mul_I_im x₁ y₁
  calc
    explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
        ⟨x₀, x₁, y₀, y₁, hx₀mem, hx₁mem, hy₀mem, hy₁mem,
          hx_order, hy_order, hx_adj, hy_adj, homit⟩ =
        explicitFormulaRectangleHorizontalRealEndpointIntegral f
          (((x₀ : ℂ) + (y₀ : ℂ) * Complex.I).re)
          (((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).re)
          (((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).im) := by
      exact Eq.refl _
    _ =
        explicitFormulaRectangleHorizontalRealEndpointIntegral f x₀ x₁ y₁ := by
      calc
        explicitFormulaRectangleHorizontalRealEndpointIntegral f
            (((x₀ : ℂ) + (y₀ : ℂ) * Complex.I).re)
            (((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).re)
            (((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).im) =
            explicitFormulaRectangleHorizontalRealEndpointIntegral f
              x₀
              (((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).re)
              (((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).im) := by
          exact congrArg
            (fun t : ℝ =>
              explicitFormulaRectangleHorizontalRealEndpointIntegral f t
                (((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).re)
                (((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).im))
            hx₀
        _ =
            explicitFormulaRectangleHorizontalRealEndpointIntegral f
              x₀ x₁
              (((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).im) := by
          exact congrArg
            (fun t : ℝ =>
              explicitFormulaRectangleHorizontalRealEndpointIntegral f x₀ t
                (((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).im))
            hx₁
        _ =
            explicitFormulaRectangleHorizontalRealEndpointIntegral f x₀ x₁ y₁ := by
          exact congrArg
            (fun t : ℝ => explicitFormulaRectangleHorizontalRealEndpointIntegral f x₀ x₁ t)
            hy₁
    _ =
        explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
          f ((x₀, x₁), y₁) := by
      exact Eq.refl _
/-- A cell right edge is the right-oriented integral of its right coordinate label. -/
theorem explicitFormulaRectangleRegularGridCellEndpointDataRightEdge_eq_coordinateIntegral
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :
    explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f d =
      explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
        f d.rightEdgeCoordinates := by
  cases d with
  | mk x₀ x₁ y₀ y₁ hx₀mem hx₁mem hy₀mem hy₁mem
      hx_order hy_order hx_adj hy_adj homit =>
  have hy₀ : (((x₀ : ℂ) + (y₀ : ℂ) * Complex.I).im) = y₀ :=
    ofReal_add_mul_I_im x₀ y₀
  have hy₁ : (((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).im) = y₁ :=
    ofReal_add_mul_I_im x₁ y₁
  have hx₁ : (((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).re) = x₁ :=
    ofReal_add_mul_I_re x₁ y₁
  calc
    explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
        ⟨x₀, x₁, y₀, y₁, hx₀mem, hx₁mem, hy₀mem, hy₁mem,
          hx_order, hy_order, hx_adj, hy_adj, homit⟩ =
        explicitFormulaRectangleVerticalRealEndpointIntegral f
          (((x₀ : ℂ) + (y₀ : ℂ) * Complex.I).im)
          (((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).im)
          (((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).re) := by
      exact Eq.refl _
    _ =
        explicitFormulaRectangleVerticalRealEndpointIntegral f y₀ y₁ x₁ := by
      calc
        explicitFormulaRectangleVerticalRealEndpointIntegral f
            (((x₀ : ℂ) + (y₀ : ℂ) * Complex.I).im)
            (((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).im)
            (((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).re) =
            explicitFormulaRectangleVerticalRealEndpointIntegral f
              y₀
              (((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).im)
              (((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).re) := by
          exact congrArg
            (fun t : ℝ =>
              explicitFormulaRectangleVerticalRealEndpointIntegral f t
                (((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).im)
                (((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).re))
            hy₀
        _ =
            explicitFormulaRectangleVerticalRealEndpointIntegral f
              y₀ y₁
              (((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).re) := by
          exact congrArg
            (fun t : ℝ =>
              explicitFormulaRectangleVerticalRealEndpointIntegral f y₀ t
                (((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).re))
            hy₁
        _ =
            explicitFormulaRectangleVerticalRealEndpointIntegral f y₀ y₁ x₁ := by
          exact congrArg
            (fun t : ℝ => explicitFormulaRectangleVerticalRealEndpointIntegral f y₀ y₁ t)
            hx₁
    _ =
        explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
          f ((y₀, y₁), x₁) := by
      exact Eq.refl _
/-- A cell left edge is the left-oriented integral of its left coordinate label. -/
theorem explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge_eq_coordinateIntegral
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :
    explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f d =
      explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
        f d.leftEdgeCoordinates := by
  cases d with
  | mk x₀ x₁ y₀ y₁ hx₀mem hx₁mem hy₀mem hy₁mem
      hx_order hy_order hx_adj hy_adj homit =>
  have hy₀ : (((x₀ : ℂ) + (y₀ : ℂ) * Complex.I).im) = y₀ :=
    ofReal_add_mul_I_im x₀ y₀
  have hy₁ : (((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).im) = y₁ :=
    ofReal_add_mul_I_im x₁ y₁
  have hx₀ : (((x₀ : ℂ) + (y₀ : ℂ) * Complex.I).re) = x₀ :=
    ofReal_add_mul_I_re x₀ y₀
  calc
    explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f
        ⟨x₀, x₁, y₀, y₁, hx₀mem, hx₁mem, hy₀mem, hy₁mem,
          hx_order, hy_order, hx_adj, hy_adj, homit⟩ =
        explicitFormulaRectangleVerticalRealEndpointIntegral f
          (((x₀ : ℂ) + (y₀ : ℂ) * Complex.I).im)
          (((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).im)
          (((x₀ : ℂ) + (y₀ : ℂ) * Complex.I).re) := by
      exact Eq.refl _
    _ =
        explicitFormulaRectangleVerticalRealEndpointIntegral f y₀ y₁ x₀ := by
      calc
        explicitFormulaRectangleVerticalRealEndpointIntegral f
            (((x₀ : ℂ) + (y₀ : ℂ) * Complex.I).im)
            (((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).im)
            (((x₀ : ℂ) + (y₀ : ℂ) * Complex.I).re) =
            explicitFormulaRectangleVerticalRealEndpointIntegral f
              y₀
              (((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).im)
              (((x₀ : ℂ) + (y₀ : ℂ) * Complex.I).re) := by
          exact congrArg
            (fun t : ℝ =>
              explicitFormulaRectangleVerticalRealEndpointIntegral f t
                (((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).im)
                (((x₀ : ℂ) + (y₀ : ℂ) * Complex.I).re))
            hy₀
        _ =
            explicitFormulaRectangleVerticalRealEndpointIntegral f
              y₀ y₁
              (((x₀ : ℂ) + (y₀ : ℂ) * Complex.I).re) := by
          exact congrArg
            (fun t : ℝ =>
              explicitFormulaRectangleVerticalRealEndpointIntegral f y₀ t
                (((x₀ : ℂ) + (y₀ : ℂ) * Complex.I).re))
            hy₁
        _ =
            explicitFormulaRectangleVerticalRealEndpointIntegral f y₀ y₁ x₀ := by
          exact congrArg
            (fun t : ℝ => explicitFormulaRectangleVerticalRealEndpointIntegral f y₀ y₁ t)
            hx₀
    _ =
        explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
          f ((y₀, y₁), x₀) := by
      exact Eq.refl _
/-- Right and left vertical coordinate labels at the same vertical line carry the same
coordinate integral. -/
theorem explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral_eq_left_sameCoordinate
    (f : ZetaAdmissibleFunction) (y₀ y₁ x : ℝ) :
    explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f ((y₀, y₁), x) =
      explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f ((y₀, y₁), x) := by
  exact Eq.refl _
/-- Bottom and top horizontal coordinate labels at the same horizontal line carry the
same coordinate integral. -/
theorem explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral_eq_top_sameCoordinate
    (f : ZetaAdmissibleFunction) (x₀ x₁ y : ℝ) :
    explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f ((x₀, x₁), y) =
      explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f ((x₀, x₁), y) := by
  exact Eq.refl _
/-- Sum of bottom-oriented horizontal endpoint-data edge-label integrals. -/
noncomputable def explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum
    (f : ZetaAdmissibleFunction) :
    List ExplicitFormulaRectangleHorizontalEndpointDataEdge → ℂ
  | [] => 0
  | edge :: rest =>
      explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f edge +
        explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f rest

/-- Sum of top-oriented horizontal endpoint-data coordinate-label integrals. -/
noncomputable def explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum
    (f : ZetaAdmissibleFunction) :
    List ExplicitFormulaRectangleHorizontalEndpointDataEdge → ℂ
  | [] => 0
  | edge :: rest =>
      explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f edge +
        explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f rest

/-- Sum of right-oriented vertical endpoint-data coordinate-label integrals. -/
noncomputable def explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegralSum
    (f : ZetaAdmissibleFunction) :
    List ExplicitFormulaRectangleVerticalEndpointDataEdge → ℂ
  | [] => 0
  | edge :: rest =>
      explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f edge +
        explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegralSum f rest

/-- Sum of left-oriented vertical endpoint-data coordinate-label integrals. -/
noncomputable def explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegralSum
    (f : ZetaAdmissibleFunction) :
    List ExplicitFormulaRectangleVerticalEndpointDataEdge → ℂ
  | [] => 0
  | edge :: rest =>
      explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f edge +
        explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegralSum f rest

/-- Sum of bottom-oriented endpoint-data box-label integrals. -/
noncomputable def explicitFormulaRectangleBoxBottomEdgeIntegralSum
    (f : ZetaAdmissibleFunction) :
    List ExplicitFormulaRectangleEndpointDataBoxEdge → ℂ
  | [] => 0
  | edge :: rest =>
      explicitFormulaRectangleBoxBottomEdgeIntegral f edge +
        explicitFormulaRectangleBoxBottomEdgeIntegralSum f rest

/-- Sum of top-oriented endpoint-data box-label integrals.  The box label is retained
because the existing top-edge definition uses both diagonal endpoint records in its
interval bounds. -/
noncomputable def explicitFormulaRectangleBoxTopEdgeIntegralSum
    (f : ZetaAdmissibleFunction) :
    List ExplicitFormulaRectangleEndpointDataBoxEdge → ℂ
  | [] => 0
  | edge :: rest =>
      explicitFormulaRectangleBoxTopEdgeIntegral f edge +
        explicitFormulaRectangleBoxTopEdgeIntegralSum f rest

/-- Sum of right-oriented endpoint-data box-label integrals. -/
noncomputable def explicitFormulaRectangleBoxRightEdgeIntegralSum
    (f : ZetaAdmissibleFunction) :
    List ExplicitFormulaRectangleEndpointDataBoxEdge → ℂ
  | [] => 0
  | edge :: rest =>
      explicitFormulaRectangleBoxRightEdgeIntegral f edge +
        explicitFormulaRectangleBoxRightEdgeIntegralSum f rest

/-- Sum of left-oriented endpoint-data box-label integrals. -/
noncomputable def explicitFormulaRectangleBoxLeftEdgeIntegralSum
    (f : ZetaAdmissibleFunction) :
    List ExplicitFormulaRectangleEndpointDataBoxEdge → ℂ
  | [] => 0
  | edge :: rest =>
      explicitFormulaRectangleBoxLeftEdgeIntegral f edge +
        explicitFormulaRectangleBoxLeftEdgeIntegralSum f rest

/-- Sum of full endpoint-data box cell-boundary integrals. -/
noncomputable def explicitFormulaRectangleEndpointDataBoxBoundarySum
    (f : ZetaAdmissibleFunction) :
    List ExplicitFormulaRectangleEndpointDataBoxEdge → ℂ
  | [] => 0
  | edge :: rest =>
      finiteRectangleSubdivisionCellBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
        (explicitFormulaRectangleEndpointDataBoxLowerCorner edge)
        (explicitFormulaRectangleEndpointDataBoxUpperCorner edge) +
        explicitFormulaRectangleEndpointDataBoxBoundarySum f rest

/-- Full endpoint-data box boundary sums split across list append. -/
theorem explicitFormulaRectangleEndpointDataBoxBoundarySum_append
    (f : ZetaAdmissibleFunction)
    (xs ys : List ExplicitFormulaRectangleEndpointDataBoxEdge) :
    explicitFormulaRectangleEndpointDataBoxBoundarySum f (xs ++ ys) =
      explicitFormulaRectangleEndpointDataBoxBoundarySum f xs +
        explicitFormulaRectangleEndpointDataBoxBoundarySum f ys := by
  induction xs with
  | nil =>
      exact (zero_add
        (explicitFormulaRectangleEndpointDataBoxBoundarySum f ys)).symm
  | cons edge rest ih =>
      calc
        explicitFormulaRectangleEndpointDataBoxBoundarySum f ((edge :: rest) ++ ys) =
          finiteRectangleSubdivisionCellBoundaryIntegral
              (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
              (explicitFormulaRectangleEndpointDataBoxLowerCorner edge)
              (explicitFormulaRectangleEndpointDataBoxUpperCorner edge) +
            explicitFormulaRectangleEndpointDataBoxBoundarySum f (rest ++ ys) := by
          exact Eq.refl _
        _ =
          finiteRectangleSubdivisionCellBoundaryIntegral
              (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
              (explicitFormulaRectangleEndpointDataBoxLowerCorner edge)
              (explicitFormulaRectangleEndpointDataBoxUpperCorner edge) +
            (explicitFormulaRectangleEndpointDataBoxBoundarySum f rest +
              explicitFormulaRectangleEndpointDataBoxBoundarySum f ys) := by
          exact congrArg
            (fun z : ℂ =>
              finiteRectangleSubdivisionCellBoundaryIntegral
                  (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w)
                  (explicitFormulaRectangleEndpointDataBoxLowerCorner edge)
                  (explicitFormulaRectangleEndpointDataBoxUpperCorner edge) + z)
            ih
        _ =
          (finiteRectangleSubdivisionCellBoundaryIntegral
              (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
              (explicitFormulaRectangleEndpointDataBoxLowerCorner edge)
              (explicitFormulaRectangleEndpointDataBoxUpperCorner edge) +
            explicitFormulaRectangleEndpointDataBoxBoundarySum f rest) +
              explicitFormulaRectangleEndpointDataBoxBoundarySum f ys := by
          exact
            (add_assoc
              (finiteRectangleSubdivisionCellBoundaryIntegral
                (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
                (explicitFormulaRectangleEndpointDataBoxLowerCorner edge)
                (explicitFormulaRectangleEndpointDataBoxUpperCorner edge))
              (explicitFormulaRectangleEndpointDataBoxBoundarySum f rest)
              (explicitFormulaRectangleEndpointDataBoxBoundarySum f ys)).symm

/-- Bottom coordinate-label sums split across list append. -/
theorem explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum_append
    (f : ZetaAdmissibleFunction)
    (xs ys : List ExplicitFormulaRectangleHorizontalEndpointDataEdge) :
    explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f (xs ++ ys) =
      explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f xs +
        explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f ys := by
  induction xs with
  | nil =>
      exact (zero_add
        (explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f ys)).symm
  | cons edge rest ih =>
      calc
        explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
            ((edge :: rest) ++ ys) =
          explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f edge +
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
              (rest ++ ys) := by
          exact Eq.refl _
        _ =
          explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f edge +
            (explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f rest +
              explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f ys) := by
          exact congrArg
            (fun z : ℂ =>
              explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f edge + z)
            ih
        _ =
          (explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f edge +
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f rest) +
              explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f ys := by
          exact
            (add_assoc
              (explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f edge)
              (explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f rest)
              (explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f ys)).symm

/-- Top coordinate-label sums split across list append. -/
theorem explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum_append
    (f : ZetaAdmissibleFunction)
    (xs ys : List ExplicitFormulaRectangleHorizontalEndpointDataEdge) :
    explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f (xs ++ ys) =
      explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f xs +
        explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f ys := by
  induction xs with
  | nil =>
      exact (zero_add
        (explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f ys)).symm
  | cons edge rest ih =>
      calc
        explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
            ((edge :: rest) ++ ys) =
          explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f edge +
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
              (rest ++ ys) := by
          exact Eq.refl _
        _ =
          explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f edge +
            (explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f rest +
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f ys) := by
          exact congrArg
            (fun z : ℂ =>
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f edge + z)
            ih
        _ =
          (explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f edge +
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f rest) +
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f ys := by
          exact
            (add_assoc
              (explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f edge)
              (explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f rest)
              (explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f ys)).symm

/-- Right coordinate-label sums split across list append. -/
theorem explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegralSum_append
    (f : ZetaAdmissibleFunction)
    (xs ys : List ExplicitFormulaRectangleVerticalEndpointDataEdge) :
    explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegralSum f (xs ++ ys) =
      explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegralSum f xs +
        explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegralSum f ys := by
  induction xs with
  | nil =>
      exact (zero_add
        (explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegralSum f ys)).symm
  | cons edge rest ih =>
      calc
        explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegralSum f
            ((edge :: rest) ++ ys) =
          explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f edge +
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegralSum f
              (rest ++ ys) := by
          exact Eq.refl _
        _ =
          explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f edge +
            (explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegralSum f rest +
              explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegralSum f ys) := by
          exact congrArg
            (fun z : ℂ =>
              explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f edge + z)
            ih
        _ =
          (explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f edge +
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegralSum f rest) +
              explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegralSum f ys := by
          exact
            (add_assoc
              (explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f edge)
              (explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegralSum f rest)
              (explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegralSum f ys)).symm

/-- Left coordinate-label sums split across list append. -/
theorem explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegralSum_append
    (f : ZetaAdmissibleFunction)
    (xs ys : List ExplicitFormulaRectangleVerticalEndpointDataEdge) :
    explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegralSum f (xs ++ ys) =
      explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegralSum f xs +
        explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegralSum f ys := by
  induction xs with
  | nil =>
      exact (zero_add
        (explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegralSum f ys)).symm
  | cons edge rest ih =>
      calc
        explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegralSum f
            ((edge :: rest) ++ ys) =
          explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f edge +
            explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegralSum f
              (rest ++ ys) := by
          exact Eq.refl _
        _ =
          explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f edge +
            (explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegralSum f rest +
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegralSum f ys) := by
          exact congrArg
            (fun z : ℂ =>
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f edge + z)
            ih
        _ =
          (explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f edge +
            explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegralSum f rest) +
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegralSum f ys := by
          exact
            (add_assoc
              (explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f edge)
              (explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegralSum f rest)
              (explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegralSum f ys)).symm

/-- Bottom box-label sums split across list append. -/
theorem explicitFormulaRectangleBoxBottomEdgeIntegralSum_append
    (f : ZetaAdmissibleFunction)
    (xs ys : List ExplicitFormulaRectangleEndpointDataBoxEdge) :
    explicitFormulaRectangleBoxBottomEdgeIntegralSum f (xs ++ ys) =
      explicitFormulaRectangleBoxBottomEdgeIntegralSum f xs +
        explicitFormulaRectangleBoxBottomEdgeIntegralSum f ys := by
  induction xs with
  | nil =>
      exact (zero_add
        (explicitFormulaRectangleBoxBottomEdgeIntegralSum f ys)).symm
  | cons edge rest ih =>
      calc
        explicitFormulaRectangleBoxBottomEdgeIntegralSum f ((edge :: rest) ++ ys) =
          explicitFormulaRectangleBoxBottomEdgeIntegral f edge +
            explicitFormulaRectangleBoxBottomEdgeIntegralSum f (rest ++ ys) := by
          exact Eq.refl _
        _ =
          explicitFormulaRectangleBoxBottomEdgeIntegral f edge +
            (explicitFormulaRectangleBoxBottomEdgeIntegralSum f rest +
              explicitFormulaRectangleBoxBottomEdgeIntegralSum f ys) := by
          exact congrArg
            (fun z : ℂ => explicitFormulaRectangleBoxBottomEdgeIntegral f edge + z)
            ih
        _ =
          (explicitFormulaRectangleBoxBottomEdgeIntegral f edge +
            explicitFormulaRectangleBoxBottomEdgeIntegralSum f rest) +
              explicitFormulaRectangleBoxBottomEdgeIntegralSum f ys := by
          exact
            (add_assoc
              (explicitFormulaRectangleBoxBottomEdgeIntegral f edge)
              (explicitFormulaRectangleBoxBottomEdgeIntegralSum f rest)
              (explicitFormulaRectangleBoxBottomEdgeIntegralSum f ys)).symm

/-- Top box-label sums split across list append. -/
theorem explicitFormulaRectangleBoxTopEdgeIntegralSum_append
    (f : ZetaAdmissibleFunction)
    (xs ys : List ExplicitFormulaRectangleEndpointDataBoxEdge) :
    explicitFormulaRectangleBoxTopEdgeIntegralSum f (xs ++ ys) =
      explicitFormulaRectangleBoxTopEdgeIntegralSum f xs +
        explicitFormulaRectangleBoxTopEdgeIntegralSum f ys := by
  induction xs with
  | nil =>
      exact (zero_add
        (explicitFormulaRectangleBoxTopEdgeIntegralSum f ys)).symm
  | cons edge rest ih =>
      calc
        explicitFormulaRectangleBoxTopEdgeIntegralSum f ((edge :: rest) ++ ys) =
          explicitFormulaRectangleBoxTopEdgeIntegral f edge +
            explicitFormulaRectangleBoxTopEdgeIntegralSum f (rest ++ ys) := by
          exact Eq.refl _
        _ =
          explicitFormulaRectangleBoxTopEdgeIntegral f edge +
            (explicitFormulaRectangleBoxTopEdgeIntegralSum f rest +
              explicitFormulaRectangleBoxTopEdgeIntegralSum f ys) := by
          exact congrArg
            (fun z : ℂ => explicitFormulaRectangleBoxTopEdgeIntegral f edge + z)
            ih
        _ =
          (explicitFormulaRectangleBoxTopEdgeIntegral f edge +
            explicitFormulaRectangleBoxTopEdgeIntegralSum f rest) +
              explicitFormulaRectangleBoxTopEdgeIntegralSum f ys := by
          exact
            (add_assoc
              (explicitFormulaRectangleBoxTopEdgeIntegral f edge)
              (explicitFormulaRectangleBoxTopEdgeIntegralSum f rest)
              (explicitFormulaRectangleBoxTopEdgeIntegralSum f ys)).symm

/-- Right box-label sums split across list append. -/
theorem explicitFormulaRectangleBoxRightEdgeIntegralSum_append
    (f : ZetaAdmissibleFunction)
    (xs ys : List ExplicitFormulaRectangleEndpointDataBoxEdge) :
    explicitFormulaRectangleBoxRightEdgeIntegralSum f (xs ++ ys) =
      explicitFormulaRectangleBoxRightEdgeIntegralSum f xs +
        explicitFormulaRectangleBoxRightEdgeIntegralSum f ys := by
  induction xs with
  | nil =>
      exact (zero_add
        (explicitFormulaRectangleBoxRightEdgeIntegralSum f ys)).symm
  | cons edge rest ih =>
      calc
        explicitFormulaRectangleBoxRightEdgeIntegralSum f ((edge :: rest) ++ ys) =
          explicitFormulaRectangleBoxRightEdgeIntegral f edge +
            explicitFormulaRectangleBoxRightEdgeIntegralSum f (rest ++ ys) := by
          exact Eq.refl _
        _ =
          explicitFormulaRectangleBoxRightEdgeIntegral f edge +
            (explicitFormulaRectangleBoxRightEdgeIntegralSum f rest +
              explicitFormulaRectangleBoxRightEdgeIntegralSum f ys) := by
          exact congrArg
            (fun z : ℂ => explicitFormulaRectangleBoxRightEdgeIntegral f edge + z)
            ih
        _ =
          (explicitFormulaRectangleBoxRightEdgeIntegral f edge +
            explicitFormulaRectangleBoxRightEdgeIntegralSum f rest) +
              explicitFormulaRectangleBoxRightEdgeIntegralSum f ys := by
          exact
            (add_assoc
              (explicitFormulaRectangleBoxRightEdgeIntegral f edge)
              (explicitFormulaRectangleBoxRightEdgeIntegralSum f rest)
              (explicitFormulaRectangleBoxRightEdgeIntegralSum f ys)).symm

/-- Left box-label sums split across list append. -/
theorem explicitFormulaRectangleBoxLeftEdgeIntegralSum_append
    (f : ZetaAdmissibleFunction)
    (xs ys : List ExplicitFormulaRectangleEndpointDataBoxEdge) :
    explicitFormulaRectangleBoxLeftEdgeIntegralSum f (xs ++ ys) =
      explicitFormulaRectangleBoxLeftEdgeIntegralSum f xs +
        explicitFormulaRectangleBoxLeftEdgeIntegralSum f ys := by
  induction xs with
  | nil =>
      exact (zero_add
        (explicitFormulaRectangleBoxLeftEdgeIntegralSum f ys)).symm
  | cons edge rest ih =>
      calc
        explicitFormulaRectangleBoxLeftEdgeIntegralSum f ((edge :: rest) ++ ys) =
          explicitFormulaRectangleBoxLeftEdgeIntegral f edge +
            explicitFormulaRectangleBoxLeftEdgeIntegralSum f (rest ++ ys) := by
          exact Eq.refl _
        _ =
          explicitFormulaRectangleBoxLeftEdgeIntegral f edge +
            (explicitFormulaRectangleBoxLeftEdgeIntegralSum f rest +
              explicitFormulaRectangleBoxLeftEdgeIntegralSum f ys) := by
          exact congrArg
            (fun z : ℂ => explicitFormulaRectangleBoxLeftEdgeIntegral f edge + z)
            ih
        _ =
          (explicitFormulaRectangleBoxLeftEdgeIntegral f edge +
            explicitFormulaRectangleBoxLeftEdgeIntegralSum f rest) +
              explicitFormulaRectangleBoxLeftEdgeIntegralSum f ys := by
          exact
            (add_assoc
              (explicitFormulaRectangleBoxLeftEdgeIntegral f edge)
              (explicitFormulaRectangleBoxLeftEdgeIntegralSum f rest)
              (explicitFormulaRectangleBoxLeftEdgeIntegralSum f ys)).symm

/-- The bottom-edge sum over endpoint data is exactly the sum over the corresponding
bottom horizontal coordinate labels. -/
theorem explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum_eq_bottomHorizontalEdgeIntegralSum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction) :
    ∀ data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε),
      explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data =
        explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
          (data.map
            (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
              d.bottomEdgeCoordinates))
  | [] => Eq.refl _
  | d :: rest =>
      calc
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f (d :: rest) =
            explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f d +
              explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f rest := by
          exact Eq.refl _
        _ =
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                f d.bottomEdgeCoordinates +
              explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f rest := by
          exact
            congrArg
              (fun z : ℂ =>
                z + explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f rest)
              (explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge_eq_coordinateIntegral
                f d)
        _ =
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                f d.bottomEdgeCoordinates +
              explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
                (rest.map
                  (fun e : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                    e.bottomEdgeCoordinates)) := by
          exact
            congrArg
              (fun z : ℂ =>
                explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                    f d.bottomEdgeCoordinates + z)
              (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum_eq_bottomHorizontalEdgeIntegralSum
                f rest)
        _ =
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
              ((d :: rest).map
                (fun e : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  e.bottomEdgeCoordinates)) := by
          exact Eq.refl _
/-- The top-edge sum over endpoint data is exactly the sum over the corresponding
top horizontal coordinate labels. -/
theorem explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum_eq_topHorizontalEdgeIntegralSum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction) :
    ∀ data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε),
      explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data =
        explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
          (data.map
            (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
              d.topEdgeCoordinates))
  | [] => Eq.refl _
  | d :: rest =>
      calc
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f (d :: rest) =
            explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f d +
              explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f rest := by
          exact Eq.refl _
        _ =
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                f d.topEdgeCoordinates +
              explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f rest := by
          exact
            congrArg
              (fun z : ℂ =>
                z + explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f rest)
              (explicitFormulaRectangleRegularGridCellEndpointDataTopEdge_eq_coordinateIntegral
                f d)
        _ =
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                f d.topEdgeCoordinates +
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
                (rest.map
                  (fun e : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                    e.topEdgeCoordinates)) := by
          exact
            congrArg
              (fun z : ℂ =>
                explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                    f d.topEdgeCoordinates + z)
              (explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum_eq_topHorizontalEdgeIntegralSum
                f rest)
        _ =
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
              ((d :: rest).map
                (fun e : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  e.topEdgeCoordinates)) := by
          exact Eq.refl _
/-- The right-edge sum over endpoint data is exactly the sum over the corresponding
right vertical coordinate labels. -/
theorem explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum_eq_rightVerticalEdgeIntegralSum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction) :
    ∀ data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε),
      explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data =
        explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegralSum f
          (data.map
            (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
              d.rightEdgeCoordinates))
  | [] => Eq.refl _
  | d :: rest =>
      calc
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f (d :: rest) =
            explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f d +
              explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f rest := by
          exact Eq.refl _
        _ =
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
                f d.rightEdgeCoordinates +
              explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f rest := by
          exact
            congrArg
              (fun z : ℂ =>
                z + explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f rest)
              (explicitFormulaRectangleRegularGridCellEndpointDataRightEdge_eq_coordinateIntegral
                f d)
        _ =
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
                f d.rightEdgeCoordinates +
              explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegralSum f
                (rest.map
                  (fun e : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                    e.rightEdgeCoordinates)) := by
          exact
            congrArg
              (fun z : ℂ =>
                explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
                    f d.rightEdgeCoordinates + z)
              (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum_eq_rightVerticalEdgeIntegralSum
                f rest)
        _ =
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegralSum f
              ((d :: rest).map
                (fun e : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  e.rightEdgeCoordinates)) := by
          exact Eq.refl _
/-- The left-edge sum over endpoint data is exactly the sum over the corresponding
left vertical coordinate labels. -/
theorem explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum_eq_leftVerticalEdgeIntegralSum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction) :
    ∀ data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε),
      explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data =
        explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegralSum f
          (data.map
            (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
              d.leftEdgeCoordinates))
  | [] => Eq.refl _
  | d :: rest =>
      calc
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f (d :: rest) =
            explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f d +
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f rest := by
          exact Eq.refl _
        _ =
            explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
                f d.leftEdgeCoordinates +
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f rest := by
          exact
            congrArg
              (fun z : ℂ =>
                z + explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f rest)
              (explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge_eq_coordinateIntegral
                f d)
        _ =
            explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
                f d.leftEdgeCoordinates +
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegralSum f
                (rest.map
                  (fun e : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                    e.leftEdgeCoordinates)) := by
          exact
            congrArg
              (fun z : ℂ =>
                explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
                    f d.leftEdgeCoordinates + z)
              (explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum_eq_leftVerticalEdgeIntegralSum
                f rest)
        _ =
            explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegralSum f
              ((d :: rest).map
                (fun e : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  e.leftEdgeCoordinates)) := by
          exact Eq.refl _
/-- The bottom-edge sum over endpoint data is exactly the sum over the corresponding
endpoint-data box labels. -/
theorem explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum_eq_boxBottomEdgeIntegralSum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction) :
    ∀ data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε),
      explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data =
        explicitFormulaRectangleBoxBottomEdgeIntegralSum f
          (data.map
            (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
              d.boxEdgeCoordinates))
  | [] => Eq.refl _
  | d :: rest =>
      calc
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f (d :: rest) =
            explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f d +
              explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f rest := by
          exact Eq.refl _
        _ =
            explicitFormulaRectangleBoxBottomEdgeIntegral f d.boxEdgeCoordinates +
              explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f rest := by
          exact
            congrArg
              (fun z : ℂ =>
                z + explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f rest)
              (explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge_eq_boxIntegral
                f d)
        _ =
            explicitFormulaRectangleBoxBottomEdgeIntegral f d.boxEdgeCoordinates +
              explicitFormulaRectangleBoxBottomEdgeIntegralSum f
                (rest.map
                  (fun e : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                    e.boxEdgeCoordinates)) := by
          exact
            congrArg
              (fun z : ℂ =>
                explicitFormulaRectangleBoxBottomEdgeIntegral f d.boxEdgeCoordinates + z)
              (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum_eq_boxBottomEdgeIntegralSum
                f rest)
        _ =
            explicitFormulaRectangleBoxBottomEdgeIntegralSum f
              ((d :: rest).map
                (fun e : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  e.boxEdgeCoordinates)) := by
          exact Eq.refl _
/-- The top-edge sum over endpoint data is exactly the sum over the corresponding
endpoint-data box labels. -/
theorem explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum_eq_boxTopEdgeIntegralSum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction) :
    ∀ data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε),
      explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data =
        explicitFormulaRectangleBoxTopEdgeIntegralSum f
          (data.map
            (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
              d.boxEdgeCoordinates))
  | [] => Eq.refl _
  | d :: rest =>
      calc
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f (d :: rest) =
            explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f d +
              explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f rest := by
          exact Eq.refl _
        _ =
            explicitFormulaRectangleBoxTopEdgeIntegral f d.boxEdgeCoordinates +
              explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f rest := by
          exact
            congrArg
              (fun z : ℂ =>
                z + explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f rest)
              (explicitFormulaRectangleRegularGridCellEndpointDataTopEdge_eq_boxIntegral
                f d)
        _ =
            explicitFormulaRectangleBoxTopEdgeIntegral f d.boxEdgeCoordinates +
              explicitFormulaRectangleBoxTopEdgeIntegralSum f
                (rest.map
                  (fun e : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                    e.boxEdgeCoordinates)) := by
          exact
            congrArg
              (fun z : ℂ =>
                explicitFormulaRectangleBoxTopEdgeIntegral f d.boxEdgeCoordinates + z)
              (explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum_eq_boxTopEdgeIntegralSum
                f rest)
        _ =
            explicitFormulaRectangleBoxTopEdgeIntegralSum f
              ((d :: rest).map
                (fun e : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  e.boxEdgeCoordinates)) := by
          exact Eq.refl _
/-- The right-edge sum over endpoint data is exactly the sum over the corresponding
endpoint-data box labels. -/
theorem explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum_eq_boxRightEdgeIntegralSum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction) :
    ∀ data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε),
      explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data =
        explicitFormulaRectangleBoxRightEdgeIntegralSum f
          (data.map
            (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
              d.boxEdgeCoordinates))
  | [] => Eq.refl _
  | d :: rest =>
      calc
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f (d :: rest) =
            explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f d +
              explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f rest := by
          exact Eq.refl _
        _ =
            explicitFormulaRectangleBoxRightEdgeIntegral f d.boxEdgeCoordinates +
              explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f rest := by
          exact
            congrArg
              (fun z : ℂ =>
                z + explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f rest)
              (explicitFormulaRectangleRegularGridCellEndpointDataRightEdge_eq_boxIntegral
                f d)
        _ =
            explicitFormulaRectangleBoxRightEdgeIntegral f d.boxEdgeCoordinates +
              explicitFormulaRectangleBoxRightEdgeIntegralSum f
                (rest.map
                  (fun e : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                    e.boxEdgeCoordinates)) := by
          exact
            congrArg
              (fun z : ℂ =>
                explicitFormulaRectangleBoxRightEdgeIntegral f d.boxEdgeCoordinates + z)
              (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum_eq_boxRightEdgeIntegralSum
                f rest)
        _ =
            explicitFormulaRectangleBoxRightEdgeIntegralSum f
              ((d :: rest).map
                (fun e : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  e.boxEdgeCoordinates)) := by
          exact Eq.refl _
/-- The left-edge sum over endpoint data is exactly the sum over the corresponding
endpoint-data box labels. -/
theorem explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum_eq_boxLeftEdgeIntegralSum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction) :
    ∀ data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε),
      explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data =
        explicitFormulaRectangleBoxLeftEdgeIntegralSum f
          (data.map
            (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
              d.boxEdgeCoordinates))
  | [] => Eq.refl _
  | d :: rest =>
      calc
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f (d :: rest) =
            explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f d +
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f rest := by
          exact Eq.refl _
        _ =
            explicitFormulaRectangleBoxLeftEdgeIntegral f d.boxEdgeCoordinates +
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f rest := by
          exact
            congrArg
              (fun z : ℂ =>
                z + explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f rest)
              (explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge_eq_boxIntegral
                f d)
        _ =
            explicitFormulaRectangleBoxLeftEdgeIntegral f d.boxEdgeCoordinates +
              explicitFormulaRectangleBoxLeftEdgeIntegralSum f
                (rest.map
                  (fun e : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                    e.boxEdgeCoordinates)) := by
          exact
            congrArg
              (fun z : ℂ =>
                explicitFormulaRectangleBoxLeftEdgeIntegral f d.boxEdgeCoordinates + z)
              (explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum_eq_boxLeftEdgeIntegralSum
                f rest)
        _ =
            explicitFormulaRectangleBoxLeftEdgeIntegralSum f
              ((d :: rest).map
                (fun e : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  e.boxEdgeCoordinates)) := by
          exact Eq.refl _
/-- Endpoint-data boundary sums are box-boundary sums over the mapped full-box labels. -/
theorem explicitFormulaRectangleRegularGridEndpointDataBoundarySum_eq_boxBoundarySum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction) :
    ∀ data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε),
      explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data =
        explicitFormulaRectangleEndpointDataBoxBoundarySum f
          (data.map
            (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
              d.boxEdgeCoordinates))
  | [] => Eq.refl _
  | d :: rest =>
      calc
        explicitFormulaRectangleRegularGridEndpointDataBoundarySum f (d :: rest) =
            explicitFormulaRectangleRegularGridCellEndpointDataBoundary f d +
              explicitFormulaRectangleRegularGridEndpointDataBoundarySum f rest := by
          exact Eq.refl _
        _ =
            finiteRectangleSubdivisionCellBoundaryIntegral
                (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
                (explicitFormulaRectangleEndpointDataBoxLowerCorner d.boxEdgeCoordinates)
                (explicitFormulaRectangleEndpointDataBoxUpperCorner d.boxEdgeCoordinates) +
              explicitFormulaRectangleRegularGridEndpointDataBoundarySum f rest := by
          have hcell :
              explicitFormulaRectangleRegularGridCellEndpointDataBoundary f d =
                finiteRectangleSubdivisionCellBoundaryIntegral
                  (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
                  (explicitFormulaRectangleEndpointDataBoxLowerCorner d.boxEdgeCoordinates)
                  (explicitFormulaRectangleEndpointDataBoxUpperCorner d.boxEdgeCoordinates) := by
            exact Eq.refl _
          exact congrArg
            (fun z : ℂ => z + explicitFormulaRectangleRegularGridEndpointDataBoundarySum f rest)
            hcell
        _ =
            finiteRectangleSubdivisionCellBoundaryIntegral
                (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
                (explicitFormulaRectangleEndpointDataBoxLowerCorner d.boxEdgeCoordinates)
                (explicitFormulaRectangleEndpointDataBoxUpperCorner d.boxEdgeCoordinates) +
              explicitFormulaRectangleEndpointDataBoxBoundarySum f
                (rest.map
                  (fun e : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                    e.boxEdgeCoordinates)) := by
          exact congrArg
            (fun z : ℂ =>
              finiteRectangleSubdivisionCellBoundaryIntegral
                  (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w)
                  (explicitFormulaRectangleEndpointDataBoxLowerCorner d.boxEdgeCoordinates)
                  (explicitFormulaRectangleEndpointDataBoxUpperCorner d.boxEdgeCoordinates) + z)
            (explicitFormulaRectangleRegularGridEndpointDataBoundarySum_eq_boxBoundarySum
              f rest)
        _ =
            explicitFormulaRectangleEndpointDataBoxBoundarySum f
              ((d :: rest).map
                (fun e : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  e.boxEdgeCoordinates)) := by
          exact Eq.refl _
end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
