import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaVerticalBoundaryLimits

/-!
# Side assembly for the finite-height Abel-Plana contour

This file owns the algebraic reconstruction from vertical boundary faces and
principal-value residue accounting to the finite-height named side expression
plus horizontal-edge error.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open Filter
open MeasureTheory

/-- Pointwise finite-height bridge from the normalized principal-value
rectangle side to the two normalized boundary faces and the horizontal edge
error. -/
def Complex.FiniteHeightPVRectangleBoundaryBridge
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) : Prop :=
  (fun ρ : ℝ =>
      Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ) =ᶠ[
    𝓝[>] (0 : ℝ)]
    (fun ρ : ℝ =>
      (Complex.finiteAbelPlanaLogLeftBoundaryFacePVNormalized N w T ρ +
        Complex.finiteAbelPlanaLogRightBoundaryFacePVNormalized N w T ρ) +
        Complex.finiteAbelPlanaLogHorizontalEdgeError N w T)

/-- Target-side finite-height bridge identifying the limiting normalized
boundary-face sum, after adding the horizontal edge error, with the named
finite-height side. -/
def Complex.FiniteHeightPVBoundaryTargetBridge
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) : Prop :=
  (((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
          Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
      (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
    ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
          Complex.I *
            Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
      (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) +
    Complex.finiteAbelPlanaLogHorizontalEdgeError N w T =
      Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T +
        Complex.finiteAbelPlanaLogHorizontalEdgeError N w T

/-- Eventual finite-height bridge package used by the finite contour wrappers. -/
def Complex.FiniteHeightPVBridgePackageAt
    (N : ℕ)
    (w : ℂ) : Prop :=
  ∀ᶠ T : ℝ in atTop,
    0 < T ∧
      Complex.FiniteHeightPVRectangleBoundaryBridge N w T ∧
      Complex.FiniteHeightPVBoundaryTargetBridge N w T

/-- Eventual finite-height bridge package used by the finite contour wrappers. -/
def Complex.FiniteHeightPVBridgePackage
    (w : ℂ) : Prop :=
  ∀ N : ℕ, Complex.FiniteHeightPVBridgePackageAt N w

/-- Algebraic collection of finite-height side terms into vertical and
horizontal contributions. -/
theorem Complex.finiteAbelPlana_sideExpression_collect_horizontal
    (lowerConstant bottom upperConstant top rawVertical : ℂ) :
    (lowerConstant + bottom) - (upperConstant + top) + rawVertical =
      (lowerConstant - upperConstant + rawVertical) + (bottom - top) := by
  calc
    (lowerConstant + bottom) - (upperConstant + top) + rawVertical
        =
      (lowerConstant - upperConstant + (bottom - top)) + rawVertical := by
      exact congrArg (fun z : ℂ => z + rawVertical)
        (add_sub_add_comm lowerConstant bottom upperConstant top)
    _ =
      (lowerConstant - upperConstant + rawVertical) + (bottom - top) := by
      exact add_right_comm
        (lowerConstant - upperConstant) (bottom - top) rawVertical

/-- The named two-face boundary sum unfolds to the real endpoint side plus the
named vertical side. -/
theorem Complex.finiteAbelPlana_log_namedBoundaryFaceSum_unfold
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T =
      Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N w +
        Complex.finiteAbelPlanaLogFiniteHeightNamedVerticalSideExpression N w T := by
  rfl

/-- The finite-height rectangle side is the lower side minus the upper side
plus the raw vertical contribution. -/
theorem Complex.finiteAbelPlana_log_rectangleSideExpression_eq_horizontal_add_rawVertical
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpression N w T =
      Complex.finiteAbelPlanaLogFiniteHeightLowerSide N w T -
        Complex.finiteAbelPlanaLogFiniteHeightUpperSide N w T +
          Complex.finiteAbelPlanaLogFiniteHeightRawVerticalSideExpression N w T := by
  have hrectangle :
      Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpression N w T =
        Complex.finiteAbelPlanaLogFiniteHeightLowerSide N w T -
          Complex.finiteAbelPlanaLogFiniteHeightUpperSide N w T +
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSide N w T -
              Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSide w T :=
    Complex.finiteAbelPlana_log_finiteHeightRectangleSideExpression_unfold
      N w T
  have hraw :
      Complex.finiteAbelPlanaLogFiniteHeightRawVerticalSideExpression N w T =
        Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSide N w T -
          Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSide w T :=
    Complex.finiteAbelPlana_log_finiteHeightRawVerticalSideExpression_unfold
      N w T
  let A : ℂ :=
    Complex.finiteAbelPlanaLogFiniteHeightLowerSide N w T -
      Complex.finiteAbelPlanaLogFiniteHeightUpperSide N w T
  let R : ℂ := Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSide N w T
  let L : ℂ := Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSide w T
  have hgroup :
      A + R - L = A + (R - L) := by
    calc
      A + R - L = (A + R) + -L := by
        exact sub_eq_add_neg (A + R) L
      _ = A + (R + -L) := by
        exact add_assoc A R (-L)
      _ = A + (R - L) := by
        exact congrArg (fun z : ℂ => A + z) (sub_eq_add_neg R L).symm
  exact hrectangle.trans
    (Eq.trans hgroup
      (congrArg
        (fun z : ℂ =>
          Complex.finiteAbelPlanaLogFiniteHeightLowerSide N w T -
            Complex.finiteAbelPlanaLogFiniteHeightUpperSide N w T + z)
        hraw.symm))

/-- Replacing the lower and upper horizontal sides by their constant and
exponential pieces collects the rectangle side into the named vertical block
plus the horizontal error block. -/
theorem Complex.finiteAbelPlana_sideExpression_collect_after_horizontal_splits
    (lower upper lowerConstant bottom upperConstant top rawVertical : ℂ)
    (hlower : lower = lowerConstant + bottom)
    (hupper : upper = upperConstant + top) :
    lower - upper + rawVertical =
      (lowerConstant - upperConstant + rawVertical) + (bottom - top) := by
  exact hlower ▸ hupper ▸
    Complex.finiteAbelPlana_sideExpression_collect_horizontal
      lowerConstant bottom upperConstant top rawVertical

/-- Normalized boundary-face algebra after the constant and exponential
vertical pieces have already been identified with the named vertical
integrals. -/
theorem Complex.finiteAbelPlana_log_boundaryFaces_normalized_limitTarget_eq_realEndpoint_vertical_add_horizontal
    (N : ℕ)
    (w : ℂ)
    (T : ℝ)
    (hside :
      Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T =
        Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N w +
          Complex.finiteAbelPlanaLogFiniteHeightNamedVerticalSideExpression N w T) :
    (((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
            Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
        (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
      ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
            Complex.I *
              Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
        (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) =
      (Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N w +
        Complex.finiteAbelPlanaLogFiniteHeightNamedVerticalSideExpression N w T) +
        Complex.finiteAbelPlanaLogHorizontalEdgeError N w T →
    (((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
            Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
        (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
      ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
            Complex.I *
              Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
        (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) =
      Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T +
        Complex.finiteAbelPlanaLogHorizontalEdgeError N w T := by
  intro hboundary
  have hnamed :
      Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T +
          Complex.finiteAbelPlanaLogHorizontalEdgeError N w T =
        (Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N w +
            Complex.finiteAbelPlanaLogFiniteHeightNamedVerticalSideExpression N w T) +
          Complex.finiteAbelPlanaLogHorizontalEdgeError N w T := by
    exact congrArg
      (fun z : ℂ => z + Complex.finiteAbelPlanaLogHorizontalEdgeError N w T)
      hside
  exact hboundary.trans hnamed.symm

/-- Normalized rectangle-side algebra reducing the finite rectangle split to
the boundary-face limit target. -/
theorem Complex.finiteAbelPlana_log_normalized_rectangle_sideExpression_eq_boundaryFaces_limitTarget_algebra
    (N : ℕ)
    (w : ℂ)
    (T : ℝ)
    (hraw :
      Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpression N w T =
        (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T -
          Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T +
            Complex.finiteAbelPlanaLogFiniteHeightRawVerticalSideExpression N w T) +
          (Complex.finiteAbelPlanaLogBottomHorizontalEdge N w T -
            Complex.finiteAbelPlanaLogTopHorizontalEdge N w T))
    (hvertical :
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ((Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T -
          Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T +
            Complex.finiteAbelPlanaLogFiniteHeightRawVerticalSideExpression N w T) +
          (Complex.finiteAbelPlanaLogBottomHorizontalEdge N w T -
            Complex.finiteAbelPlanaLogTopHorizontalEdge N w T)) =
        Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T +
          Complex.finiteAbelPlanaLogHorizontalEdgeError N w T) :
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
      Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpression N w T =
      Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T +
        Complex.finiteAbelPlanaLogHorizontalEdgeError N w T := by
  have hscaled :
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpression N w T =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ((Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T -
          Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T +
            Complex.finiteAbelPlanaLogFiniteHeightRawVerticalSideExpression N w T) +
          (Complex.finiteAbelPlanaLogBottomHorizontalEdge N w T -
            Complex.finiteAbelPlanaLogTopHorizontalEdge N w T)) := by
    exact congrArg
      (fun z : ℂ => ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ * z)
      hraw
  exact hscaled.trans hvertical

/-- The normalized boundary-face limit target is the finite named side plus
the normalized horizontal edge error. -/
theorem Complex.finiteAbelPlana_log_boundaryFaces_normalized_limitTarget_eq_namedSide_add_horizontalError
    (N : ℕ)
    (w : ℂ)
    (T : ℝ)
    (hboundary :
      (((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
            (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
              Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
          (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
        ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
            (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
              Complex.I *
                Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
          (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) =
        (Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N w +
          Complex.finiteAbelPlanaLogFiniteHeightNamedVerticalSideExpression N w T) +
          Complex.finiteAbelPlanaLogHorizontalEdgeError N w T) :
    (((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
            Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
        (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
      ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
            Complex.I *
              Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
        (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) =
      Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T +
        Complex.finiteAbelPlanaLogHorizontalEdgeError N w T := by
  have hnamed :
      Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T =
        Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N w +
          Complex.finiteAbelPlanaLogFiniteHeightNamedVerticalSideExpression N w T :=
    Complex.finiteAbelPlana_log_finiteHeightNamedSideExpression_eq_realEndpoint_add_vertical
      N w T
  exact
    Complex.finiteAbelPlana_log_boundaryFaces_normalized_limitTarget_eq_realEndpoint_vertical_add_horizontal
      N w T hnamed hboundary

/-- Transport from the raw finite rectangle side split to the normalized
boundary-face limit target. -/
theorem Complex.finiteAbelPlana_log_normalized_rectangle_sideExpression_eq_boundaryFaces_limitTarget
    (N : ℕ)
    (w : ℂ)
    (T : ℝ)
    (hraw :
      Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpression N w T =
        (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T -
          Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T +
            Complex.finiteAbelPlanaLogFiniteHeightRawVerticalSideExpression N w T) +
          (Complex.finiteAbelPlanaLogBottomHorizontalEdge N w T -
            Complex.finiteAbelPlanaLogTopHorizontalEdge N w T))
    (hvertical :
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ((Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T -
          Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T +
            Complex.finiteAbelPlanaLogFiniteHeightRawVerticalSideExpression N w T) +
          (Complex.finiteAbelPlanaLogBottomHorizontalEdge N w T -
            Complex.finiteAbelPlanaLogTopHorizontalEdge N w T)) =
        Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T +
          Complex.finiteAbelPlanaLogHorizontalEdgeError N w T) :
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
      Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpression N w T =
      Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T +
        Complex.finiteAbelPlanaLogHorizontalEdgeError N w T := by
  exact
    Complex.finiteAbelPlana_log_normalized_rectangle_sideExpression_eq_boundaryFaces_limitTarget_algebra
      N w T hraw hvertical

/-- The constant horizontal cotangent pieces and raw vertical sides normalize
to the real-axis endpoint contribution plus the named Abel-Plana vertical
jump expression, after applying the residue normalization used by the
principal-value rectangle. -/
theorem Complex.finiteAbelPlana_log_constantHorizontal_rawVertical_normalized_eq_namedSide_add_horizontalError
    (N : ℕ)
    (w : ℂ)
    (T : ℝ)
    (hboundary :
      (((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
            (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
              Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
          (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
        ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
            (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
              Complex.I *
                Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
          (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) =
        (Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N w +
          Complex.finiteAbelPlanaLogFiniteHeightNamedVerticalSideExpression N w T) +
          Complex.finiteAbelPlanaLogHorizontalEdgeError N w T) :
    (((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
            Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
        (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
      ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
            Complex.I *
              Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
        (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) =
      Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T +
        Complex.finiteAbelPlanaLogHorizontalEdgeError N w T := by
  exact
    Complex.finiteAbelPlana_log_boundaryFaces_normalized_limitTarget_eq_namedSide_add_horizontalError
      N w T hboundary

/-- Constructor for the target side of the finite-height PV bridge package. -/
theorem Complex.finiteAbelPlana_log_finiteHeightPVBoundaryTargetBridge_of_boundaryFaces
    (N : ℕ)
    (w : ℂ)
    (T : ℝ)
    (hboundary :
      (((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
            (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
              Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
          (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
        ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
            (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
              Complex.I *
                Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
          (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) =
        Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T) :
    Complex.FiniteHeightPVBoundaryTargetBridge N w T := by
  unfold Complex.FiniteHeightPVBoundaryTargetBridge
  exact congrArg
    (fun z : ℂ => z + Complex.finiteAbelPlanaLogHorizontalEdgeError N w T)
    hboundary

/-- Eventual constructor for the target side of the finite-height PV bridge
package. -/
theorem Complex.finiteAbelPlana_log_finiteHeightPVBoundaryTargetBridge_eventually_of_boundaryFaces
    (N : ℕ)
    (w : ℂ)
    (hboundary :
      ∀ᶠ T : ℝ in atTop,
        (((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
              (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
                Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
            (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
          ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
              (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
                Complex.I *
                  Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
            (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) =
          Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T) :
    ∀ᶠ T : ℝ in atTop,
      Complex.FiniteHeightPVBoundaryTargetBridge N w T := by
  filter_upwards [hboundary] with T hT
  exact
    Complex.finiteAbelPlana_log_finiteHeightPVBoundaryTargetBridge_of_boundaryFaces
      N w T hT

/-- Lower/upper cotangent half-plane algebra for the full finite-height side
expression.

This is the exact side-normalization statement after the horizontal
constant-kernel pieces, the endpoint principal-value indentations, and the two
vertical jump integrals are collected. -/
theorem Complex.finiteAbelPlana_log_finiteHeightSideAlgebra_eq_realEndpoint_vertical_sub_horizontal
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (T : ℝ)
    (hT : 0 < T)
    (hnormalized :
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ((Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T -
          Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T +
            Complex.finiteAbelPlanaLogFiniteHeightRawVerticalSideExpression N w T) +
          (Complex.finiteAbelPlanaLogBottomHorizontalEdge N w T -
            Complex.finiteAbelPlanaLogTopHorizontalEdge N w T)) =
        Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T +
          Complex.finiteAbelPlanaLogHorizontalEdgeError N w T) :
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
      Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpression N w T =
      (Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N w +
        Complex.finiteAbelPlanaLogFiniteHeightNamedVerticalSideExpression N w T) +
        Complex.finiteAbelPlanaLogHorizontalEdgeError N w T := by
  have hlower :
      Complex.finiteAbelPlanaLogFiniteHeightLowerSide N w T =
        Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
          Complex.finiteAbelPlanaLogBottomHorizontalEdge N w T :=
    Complex.finiteAbelPlana_log_lowerHorizontalSide_eq_constant_add_bottomEdge
      N w T hw hT
  have hupper :
      Complex.finiteAbelPlanaLogFiniteHeightUpperSide N w T =
        Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T +
          Complex.finiteAbelPlanaLogTopHorizontalEdge N w T :=
    Complex.finiteAbelPlana_log_upperHorizontalSide_eq_constant_add_topEdge
      N w T hw hT
  have hraw :
      Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpression N w T =
        (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T -
          Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T +
            Complex.finiteAbelPlanaLogFiniteHeightRawVerticalSideExpression N w T) +
          (Complex.finiteAbelPlanaLogBottomHorizontalEdge N w T -
            Complex.finiteAbelPlanaLogTopHorizontalEdge N w T) := by
    calc
      Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpression N w T =
          Complex.finiteAbelPlanaLogFiniteHeightLowerSide N w T -
            Complex.finiteAbelPlanaLogFiniteHeightUpperSide N w T +
              Complex.finiteAbelPlanaLogFiniteHeightRawVerticalSideExpression N w T :=
        Complex.finiteAbelPlana_log_rectangleSideExpression_eq_horizontal_add_rawVertical
          N w T
      _ =
          (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T -
            Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T +
              Complex.finiteAbelPlanaLogFiniteHeightRawVerticalSideExpression N w T) +
            (Complex.finiteAbelPlanaLogBottomHorizontalEdge N w T -
              Complex.finiteAbelPlanaLogTopHorizontalEdge N w T) := by
        exact
          Complex.finiteAbelPlana_sideExpression_collect_after_horizontal_splits
            (Complex.finiteAbelPlanaLogFiniteHeightLowerSide N w T)
            (Complex.finiteAbelPlanaLogFiniteHeightUpperSide N w T)
            (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T)
            (Complex.finiteAbelPlanaLogBottomHorizontalEdge N w T)
            (Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T)
            (Complex.finiteAbelPlanaLogTopHorizontalEdge N w T)
            (Complex.finiteAbelPlanaLogFiniteHeightRawVerticalSideExpression N w T)
            hlower hupper
  exact
    Complex.finiteAbelPlana_log_normalized_rectangle_sideExpression_eq_boundaryFaces_limitTarget
      N w T hraw hnormalized

/-- Raw side decomposition of the finite Abel-Plana rectangle after applying
the cotangent half-plane expansions. -/
theorem Complex.finiteAbelPlana_log_finiteHeightCotangentSideRewrite
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (T : ℝ)
    (hT : 0 < T)
    (hnormalized :
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ((Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T -
          Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T +
            Complex.finiteAbelPlanaLogFiniteHeightRawVerticalSideExpression N w T) +
          (Complex.finiteAbelPlanaLogBottomHorizontalEdge N w T -
            Complex.finiteAbelPlanaLogTopHorizontalEdge N w T)) =
        Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T +
          Complex.finiteAbelPlanaLogHorizontalEdgeError N w T) :
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
      Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpression N w T =
      Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T +
        Complex.finiteAbelPlanaLogHorizontalEdgeError N w T := by
  have hside :
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpression N w T =
        Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T +
          Complex.finiteAbelPlanaLogHorizontalEdgeError N w T :=
    Complex.finiteAbelPlana_log_finiteHeightSideAlgebra_eq_realEndpoint_vertical_sub_horizontal
      N hw T hT hnormalized
  exact hside

/-- Side decomposition of the finite Abel-Plana rectangle. -/
theorem Complex.finiteAbelPlana_log_finiteHeightRectangle_sideDecomposition
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (T : ℝ)
    (hT : 0 < T)
    (hnormalized :
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ((Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T -
          Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T +
            Complex.finiteAbelPlanaLogFiniteHeightRawVerticalSideExpression N w T) +
          (Complex.finiteAbelPlanaLogBottomHorizontalEdge N w T -
            Complex.finiteAbelPlanaLogTopHorizontalEdge N w T)) =
        Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T +
          Complex.finiteAbelPlanaLogHorizontalEdgeError N w T) :
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
      Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpression N w T =
      Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T +
        Complex.finiteAbelPlanaLogHorizontalEdgeError N w T := by
  exact
    Complex.finiteAbelPlana_log_finiteHeightCotangentSideRewrite
      N hw T hT hnormalized

/-- The named two-face boundary target is the same finite-height named side
expression used by the side assembly theorem. -/
theorem Complex.finiteAbelPlana_log_namedBoundaryFaceSum_eq_finiteHeightNamedSideExpression
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T =
      Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T := by
  have hside :
      Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T =
        Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N w +
          Complex.finiteAbelPlanaLogFiniteHeightNamedVerticalSideExpression N w T :=
    Complex.finiteAbelPlana_log_finiteHeightNamedSideExpression_eq_realEndpoint_add_vertical
      N w T
  have hboundary :
      Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T =
        Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N w +
          Complex.finiteAbelPlanaLogFiniteHeightNamedVerticalSideExpression N w T := by
    rfl
  exact hboundary.trans hside.symm

/-- The collapsed finite-height normalized boundary target is the named
finite-height Abel-Plana side. -/
theorem Complex.finiteAbelPlana_log_boundaryFaces_normalized_target_eq_namedSide
    (N : ℕ)
    (w : ℂ)
    (T : ℝ)
    (hboundary :
      (((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
            (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
              Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
          (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
        ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
            (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
              Complex.I *
                Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
          (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) =
        Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T) :
    (((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
            Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
        (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
      ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
            Complex.I *
              Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
        (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) =
      Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T := by
  exact hboundary.trans
    (Complex.finiteAbelPlana_log_namedBoundaryFaceSum_eq_finiteHeightNamedSideExpression
      N w T)

/-- Owner constructor for the target side of the finite-height PV bridge from
the collapsed normalized boundary-face equality. -/
theorem Complex.finiteAbelPlana_log_finiteHeightPVBoundaryTargetBridge_of_normalizedTarget
    (N : ℕ)
    (w : ℂ)
    (T : ℝ)
    (hboundary :
      (((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
            (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
              Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
          (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
        ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
            (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
              Complex.I *
                Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
          (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) =
        Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T) :
    Complex.FiniteHeightPVBoundaryTargetBridge N w T := by
  exact
    Complex.finiteAbelPlana_log_finiteHeightPVBoundaryTargetBridge_of_boundaryFaces
      N w T
      (Complex.finiteAbelPlana_log_boundaryFaces_normalized_target_eq_namedSide
        N w T hboundary)

/-- Finite-height residue accounting identifies the contour error with the
two horizontal edges.

This is the classical punctured-rectangle calculation: apply
`Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable` to
`finiteAbelPlanaLogRectangleIntegrand w`, remove small circles around integer
poles, let the circle radii tend to zero using the local unit-residue theorem,
rewrite the vertical sides by the cotangent exponential identities, and collect
the remaining side contribution as the horizontal pair. -/
theorem Complex.finiteAbelPlana_log_rectangleSideExpressionPV_tendsto_integerResidues
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    ∀ T : ℝ,
      0 < T →
      Tendsto
        (fun ρ : ℝ =>
          Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ)
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w)) := by
  intro T hT
  exact
    Complex.finiteAbelPlana_log_finiteHeightRectangle_principalValueResidueTheorem
      hw N T hT

/-- Pointwise decomposition of the PV-normalized rectangle side expression
into the two PV-normalized boundary faces and the horizontal edge error. -/
theorem Complex.finiteAbelPlana_log_rectangleSideExpressionPVNormalized_boundaryFaces_algebra
    (N : ℕ)
    (w : ℂ)
    (T ε : ℝ)
    (hbridge :
      Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ε =
        (Complex.finiteAbelPlanaLogLeftBoundaryFacePVNormalized N w T ε +
          Complex.finiteAbelPlanaLogRightBoundaryFacePVNormalized N w T ε) +
          Complex.finiteAbelPlanaLogHorizontalEdgeError N w T) :
    Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ε =
      (Complex.finiteAbelPlanaLogLeftBoundaryFacePVNormalized N w T ε +
        Complex.finiteAbelPlanaLogRightBoundaryFacePVNormalized N w T ε) +
        Complex.finiteAbelPlanaLogHorizontalEdgeError N w T := by
  exact hbridge

/-- Pointwise decomposition of the PV-normalized rectangle side expression
into the two PV-normalized boundary faces and the horizontal edge error. -/
theorem Complex.finiteAbelPlana_log_rectangleSideExpressionPVNormalized_eq_boundaryFaces_add_horizontalError
    (N : ℕ)
    (w : ℂ)
    (T ε : ℝ)
    (hbridge :
      Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ε =
        (Complex.finiteAbelPlanaLogLeftBoundaryFacePVNormalized N w T ε +
          Complex.finiteAbelPlanaLogRightBoundaryFacePVNormalized N w T ε) +
          Complex.finiteAbelPlanaLogHorizontalEdgeError N w T) :
    Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ε =
      (Complex.finiteAbelPlanaLogLeftBoundaryFacePVNormalized N w T ε +
        Complex.finiteAbelPlanaLogRightBoundaryFacePVNormalized N w T ε) +
        Complex.finiteAbelPlanaLogHorizontalEdgeError N w T :=
  Complex.finiteAbelPlana_log_rectangleSideExpressionPVNormalized_boundaryFaces_algebra
    N w T ε hbridge

/-- Oriented normalization for the left vertical PV exponential remainder.

This is the exact conversion needed to pass from the raw left vertical side
split to the normalized left boundary face. -/
noncomputable def Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSidePVRawNormalized
    (w : ℂ)
    (T ε : ℝ) : ℂ :=
  ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
    (-Complex.I *
      Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSidePV w T ε)

/-- Oriented normalization for the left vertical PV exponential remainder.

This is the exact conversion needed to pass from the raw left vertical side
split to the normalized left boundary face. -/
def Complex.LeftPVNormalizedRemainderOrientation
    (w : ℂ)
    (T ε : ℝ) : Prop :=
  Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSidePVRawNormalized w T ε =
    Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSidePVNormalized w T ε

/-- Oriented normalization for the right vertical PV exponential remainder.

This is the exact conversion needed to pass from the raw right vertical side
split to the normalized right boundary face. -/
noncomputable def Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSidePVRawNormalized
    (N : ℕ)
    (w : ℂ)
    (T ε : ℝ) : ℂ :=
  ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
    (Complex.I *
      Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSidePV N w T ε)

/-- Oriented normalization for the right vertical PV exponential remainder.

This is the exact conversion needed to pass from the raw right vertical side
split to the normalized right boundary face. -/
def Complex.RightPVNormalizedRemainderOrientation
    (N : ℕ)
    (w : ℂ)
    (T ε : ℝ) : Prop :=
  Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSidePVRawNormalized N w T ε =
    Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSidePVNormalized N w T ε

/-- Constructor for the left raw-to-normalized PV remainder orientation. -/
theorem Complex.leftPVNormalizedRemainderOrientation_of_rawNormalized_eq
    (w : ℂ)
    (T ε : ℝ)
    (h :
      Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSidePVRawNormalized w T ε =
        Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSidePVNormalized w T ε) :
    Complex.LeftPVNormalizedRemainderOrientation w T ε :=
  h

/-- Constructor for the right raw-to-normalized PV remainder orientation. -/
theorem Complex.rightPVNormalizedRemainderOrientation_of_rawNormalized_eq
    (N : ℕ)
    (w : ℂ)
    (T ε : ℝ)
    (h :
      Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSidePVRawNormalized N w T ε =
        Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSidePVNormalized N w T ε) :
    Complex.RightPVNormalizedRemainderOrientation N w T ε :=
  h

/-- The left raw normalized remainder is the residue-normalized sum of the
changed lower half-line and the upper half-line remainders. -/
theorem Complex.finiteAbelPlana_log_leftRemainderPVRawNormalized_eq_changedIntervalSum
    (w : ℂ)
    (T ε : ℝ)
    (hε : 0 < ε)
    (hεT : ε < T) :
    Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSidePVRawNormalized w T ε =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (((-Complex.I) *
          (∫ t : ℝ in ε..T,
            Complex.finiteAbelPlanaLogSummand w (-(Complex.I * (t : ℂ))) *
              (Complex.finiteAbelPlanaCotangentKernel (-(Complex.I * (t : ℂ))) -
                (Real.pi : ℂ) * Complex.I))) +
        ((-Complex.I) *
          (∫ t : ℝ in ε..T,
            Complex.finiteAbelPlanaLogSummand w (Complex.I * (t : ℂ)) *
              (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (t : ℂ)) +
                (Real.pi : ℂ) * Complex.I)))) := by
  unfold Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSidePVRawNormalized
    Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSidePV
  have hchange :
      (-Complex.I) *
        (∫ y : ℝ in (-T)..(-ε),
          Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
            (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (y : ℂ)) -
              (Real.pi : ℂ) * Complex.I)) =
      (-Complex.I) *
        (∫ t : ℝ in ε..T,
          Complex.finiteAbelPlanaLogSummand w (-(Complex.I * (t : ℂ))) *
            (Complex.finiteAbelPlanaCotangentKernel (-(Complex.I * (t : ℂ))) -
              (Real.pi : ℂ) * Complex.I)) :=
    Complex.finiteAbelPlana_log_leftVerticalRemainderPV_negativeHalf_changeVariables
      w T ε hε hεT
  calc
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (-Complex.I *
          ((∫ y : ℝ in (-T)..(-ε),
              Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
                (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (y : ℂ)) -
                  (Real.pi : ℂ) * Complex.I)) +
            ∫ y : ℝ in ε..T,
              Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
                (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (y : ℂ)) +
                  (Real.pi : ℂ) * Complex.I))) =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (((-Complex.I) *
          (∫ y : ℝ in (-T)..(-ε),
            Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
              (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (y : ℂ)) -
                (Real.pi : ℂ) * Complex.I))) +
        ((-Complex.I) *
          (∫ t : ℝ in ε..T,
            Complex.finiteAbelPlanaLogSummand w (Complex.I * (t : ℂ)) *
              (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (t : ℂ)) +
                (Real.pi : ℂ) * Complex.I)))) := by
      exact congrArg
        (fun z : ℂ => ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ * z)
        (mul_add (-Complex.I)
          (∫ y : ℝ in (-T)..(-ε),
            Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
              (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (y : ℂ)) -
                (Real.pi : ℂ) * Complex.I))
          (∫ t : ℝ in ε..T,
            Complex.finiteAbelPlanaLogSummand w (Complex.I * (t : ℂ)) *
              (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (t : ℂ)) +
                (Real.pi : ℂ) * Complex.I)))
    _ =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (((-Complex.I) *
          (∫ t : ℝ in ε..T,
            Complex.finiteAbelPlanaLogSummand w (-(Complex.I * (t : ℂ))) *
              (Complex.finiteAbelPlanaCotangentKernel (-(Complex.I * (t : ℂ))) -
                (Real.pi : ℂ) * Complex.I))) +
        ((-Complex.I) *
          (∫ t : ℝ in ε..T,
            Complex.finiteAbelPlanaLogSummand w (Complex.I * (t : ℂ)) *
              (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (t : ℂ)) +
                (Real.pi : ℂ) * Complex.I)))) := by
      exact congrArg
        (fun z : ℂ =>
          ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
            (z +
              ((-Complex.I) *
                (∫ t : ℝ in ε..T,
                  Complex.finiteAbelPlanaLogSummand w (Complex.I * (t : ℂ)) *
                    (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (t : ℂ)) +
                      (Real.pi : ℂ) * Complex.I)))))
        hchange

/-- The right raw normalized remainder is the residue-normalized sum of the
changed lower half-line and the upper half-line remainders. -/
theorem Complex.finiteAbelPlana_log_rightRemainderPVRawNormalized_eq_changedIntervalSum
    (N : ℕ)
    (w : ℂ)
    (T ε : ℝ)
    (hε : 0 < ε)
    (hεT : ε < T) :
    let M : ℕ := N + 1
    Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSidePVRawNormalized N w T ε =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ((Complex.I *
          (∫ t : ℝ in ε..T,
            Complex.finiteAbelPlanaLogSummand w ((M : ℂ) - Complex.I * (t : ℂ)) *
              (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) - Complex.I * (t : ℂ)) -
                (Real.pi : ℂ) * Complex.I))) +
        (Complex.I *
          (∫ t : ℝ in ε..T,
            Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (t : ℂ)) *
              (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) + Complex.I * (t : ℂ)) +
                (Real.pi : ℂ) * Complex.I)))) := by
  let M : ℕ := N + 1
  unfold Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSidePVRawNormalized
    Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSidePV
  have hchange :
      Complex.I *
        (∫ y : ℝ in (-T)..(-ε),
          Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (y : ℂ)) *
            (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) + Complex.I * (y : ℂ)) -
              (Real.pi : ℂ) * Complex.I)) =
      Complex.I *
        (∫ t : ℝ in ε..T,
          Complex.finiteAbelPlanaLogSummand w ((M : ℂ) - Complex.I * (t : ℂ)) *
            (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) - Complex.I * (t : ℂ)) -
              (Real.pi : ℂ) * Complex.I)) :=
    Complex.finiteAbelPlana_log_rightVerticalRemainderPV_negativeHalf_changeVariables
      N w T ε hε hεT
  calc
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (Complex.I *
          ((∫ y : ℝ in (-T)..(-ε),
              Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (y : ℂ)) *
                (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) + Complex.I * (y : ℂ)) -
                  (Real.pi : ℂ) * Complex.I)) +
            ∫ y : ℝ in ε..T,
              Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (y : ℂ)) *
                (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) + Complex.I * (y : ℂ)) +
                  (Real.pi : ℂ) * Complex.I))) =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ((Complex.I *
          (∫ y : ℝ in (-T)..(-ε),
            Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (y : ℂ)) *
              (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) + Complex.I * (y : ℂ)) -
                (Real.pi : ℂ) * Complex.I))) +
        (Complex.I *
          (∫ t : ℝ in ε..T,
            Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (t : ℂ)) *
              (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) + Complex.I * (t : ℂ)) +
                (Real.pi : ℂ) * Complex.I)))) := by
      exact congrArg
        (fun z : ℂ => ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ * z)
        (mul_add Complex.I
          (∫ y : ℝ in (-T)..(-ε),
            Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (y : ℂ)) *
              (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) + Complex.I * (y : ℂ)) -
                (Real.pi : ℂ) * Complex.I))
          (∫ t : ℝ in ε..T,
            Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (t : ℂ)) *
              (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) + Complex.I * (t : ℂ)) +
                (Real.pi : ℂ) * Complex.I)))
    _ =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ((Complex.I *
          (∫ t : ℝ in ε..T,
            Complex.finiteAbelPlanaLogSummand w ((M : ℂ) - Complex.I * (t : ℂ)) *
              (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) - Complex.I * (t : ℂ)) -
                (Real.pi : ℂ) * Complex.I))) +
        (Complex.I *
          (∫ t : ℝ in ε..T,
            Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (t : ℂ)) *
              (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) + Complex.I * (t : ℂ)) +
                (Real.pi : ℂ) * Complex.I)))) := by
      exact congrArg
        (fun z : ℂ =>
          ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
            (z +
              (Complex.I *
                (∫ t : ℝ in ε..T,
                  Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (t : ℂ)) *
                    (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) + Complex.I * (t : ℂ)) +
                      (Real.pi : ℂ) * Complex.I)))))
        hchange

/-- Changed lower-half left endpoint exponential-remainder integrand on a
positive finite window. -/
noncomputable def Complex.leftChangedLowerRemainderIntegrand
    (w : ℂ) : ℝ → ℂ :=
  fun t : ℝ =>
    (-Complex.I) *
      (Complex.finiteAbelPlanaLogSummand w (-(Complex.I * (t : ℂ))) *
        (Complex.finiteAbelPlanaCotangentKernel (-(Complex.I * (t : ℂ))) -
          (Real.pi : ℂ) * Complex.I))

/-- Upper-half left endpoint exponential-remainder integrand on a positive
finite window. -/
noncomputable def Complex.leftUpperRemainderIntegrand
    (w : ℂ) : ℝ → ℂ :=
  fun t : ℝ =>
    (-Complex.I) *
      (Complex.finiteAbelPlanaLogSummand w (Complex.I * (t : ℂ)) *
        (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (t : ℂ)) +
          (Real.pi : ℂ) * Complex.I))

/-- Changed lower-half right endpoint exponential-remainder integrand on a
positive finite window. -/
noncomputable def Complex.rightChangedLowerRemainderIntegrand
    (N : ℕ)
    (w : ℂ) : ℝ → ℂ :=
  fun t : ℝ =>
    Complex.I *
      (Complex.finiteAbelPlanaLogSummand w
          (((N + 1 : ℕ) : ℂ) - Complex.I * (t : ℂ)) *
        (Complex.finiteAbelPlanaCotangentKernel
            (((N + 1 : ℕ) : ℂ) - Complex.I * (t : ℂ)) -
          (Real.pi : ℂ) * Complex.I))

/-- Upper-half right endpoint exponential-remainder integrand on a positive
finite window. -/
noncomputable def Complex.rightUpperRemainderIntegrand
    (N : ℕ)
    (w : ℂ) : ℝ → ℂ :=
  fun t : ℝ =>
    Complex.I *
      (Complex.finiteAbelPlanaLogSummand w
          (((N + 1 : ℕ) : ℂ) + Complex.I * (t : ℂ)) *
        (Complex.finiteAbelPlanaCotangentKernel
            (((N + 1 : ℕ) : ℂ) + Complex.I * (t : ℂ)) +
          (Real.pi : ℂ) * Complex.I))

/-- The remaining finite-interval linearity step for the left normalized PV
remainder after the lower half-line has been changed by `y = -t`. -/
theorem Complex.finiteAbelPlana_log_leftChangedIntervalSum_eq_remainderPVNormalized
    (w : ℂ)
    (T ε : ℝ)
    (hεT : ε ≤ T)
    (hlower :
      IntervalIntegrable (Complex.leftChangedLowerRemainderIntegrand w)
        volume ε T)
    (hupper :
      IntervalIntegrable (Complex.leftUpperRemainderIntegrand w)
        volume ε T) :
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (((-Complex.I) *
          (∫ t : ℝ in ε..T,
            Complex.finiteAbelPlanaLogSummand w (-(Complex.I * (t : ℂ))) *
              (Complex.finiteAbelPlanaCotangentKernel (-(Complex.I * (t : ℂ))) -
                (Real.pi : ℂ) * Complex.I))) +
        ((-Complex.I) *
          (∫ t : ℝ in ε..T,
            Complex.finiteAbelPlanaLogSummand w (Complex.I * (t : ℂ)) *
              (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (t : ℂ)) +
                (Real.pi : ℂ) * Complex.I)))) =
      Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSidePVNormalized w T ε := by
  let q : ℂ := ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹
  let L : ℝ → ℂ := Complex.leftChangedLowerRemainderIntegrand w
  let U : ℝ → ℂ := Complex.leftUpperRemainderIntegrand w
  have hsum :
      ∫ t : ℝ in ε..T, L t + U t =
        (∫ t : ℝ in ε..T, L t) + ∫ t : ℝ in ε..T, U t :=
    intervalIntegral.integral_add
      (μ := MeasureTheory.volume)
      hlower hupper
  have hscale :
      ∫ t : ℝ in ε..T, q * (L t + U t) =
        q * ∫ t : ℝ in ε..T, L t + U t :=
    intervalIntegral.integral_const_mul q (fun t : ℝ => L t + U t)
  have htoSet :
      ∫ t : ℝ in ε..T, q * (L t + U t) =
        ∫ t : ℝ in Set.Ioc ε T, q * (L t + U t) :=
    intervalIntegral.integral_of_le hεT
  have hL :
      ∫ t : ℝ in ε..T, L t =
        (-Complex.I) *
          (∫ t : ℝ in ε..T,
            Complex.finiteAbelPlanaLogSummand w (-(Complex.I * (t : ℂ))) *
              (Complex.finiteAbelPlanaCotangentKernel (-(Complex.I * (t : ℂ))) -
                (Real.pi : ℂ) * Complex.I)) :=
    intervalIntegral.integral_const_mul
      (-Complex.I)
      (fun t : ℝ =>
        Complex.finiteAbelPlanaLogSummand w (-(Complex.I * (t : ℂ))) *
          (Complex.finiteAbelPlanaCotangentKernel (-(Complex.I * (t : ℂ))) -
            (Real.pi : ℂ) * Complex.I))
  have hU :
      ∫ t : ℝ in ε..T, U t =
        (-Complex.I) *
          (∫ t : ℝ in ε..T,
            Complex.finiteAbelPlanaLogSummand w (Complex.I * (t : ℂ)) *
              (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (t : ℂ)) +
                (Real.pi : ℂ) * Complex.I)) :=
    intervalIntegral.integral_const_mul
      (-Complex.I)
      (fun t : ℝ =>
        Complex.finiteAbelPlanaLogSummand w (Complex.I * (t : ℂ)) *
          (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (t : ℂ)) +
            (Real.pi : ℂ) * Complex.I))
  unfold Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSidePVNormalized
  calc
    q *
        (((-Complex.I) *
          (∫ t : ℝ in ε..T,
            Complex.finiteAbelPlanaLogSummand w (-(Complex.I * (t : ℂ))) *
              (Complex.finiteAbelPlanaCotangentKernel (-(Complex.I * (t : ℂ))) -
                (Real.pi : ℂ) * Complex.I))) +
        ((-Complex.I) *
          (∫ t : ℝ in ε..T,
            Complex.finiteAbelPlanaLogSummand w (Complex.I * (t : ℂ)) *
              (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (t : ℂ)) +
                (Real.pi : ℂ) * Complex.I)))) =
      q * ((∫ t : ℝ in ε..T, L t) + ∫ t : ℝ in ε..T, U t) := by
      exact congrArg (fun z : ℂ => q * z)
        (congrArg₂ HAdd.hAdd hL.symm hU.symm)
    _ = q * ∫ t : ℝ in ε..T, L t + U t := by
      exact congrArg (fun z : ℂ => q * z) hsum.symm
    _ = ∫ t : ℝ in ε..T, q * (L t + U t) := by
      exact hscale.symm
    _ = ∫ t : ℝ in Set.Ioc ε T, q * (L t + U t) := htoSet

/-- The remaining finite-interval linearity step for the right normalized PV
remainder after the lower half-line has been changed by `y = -t`. -/
theorem Complex.finiteAbelPlana_log_rightChangedIntervalSum_eq_remainderPVNormalized
    (N : ℕ)
    (w : ℂ)
    (T ε : ℝ)
    (hεT : ε ≤ T)
    (hlower :
      IntervalIntegrable (Complex.rightChangedLowerRemainderIntegrand N w)
        volume ε T)
    (hupper :
      IntervalIntegrable (Complex.rightUpperRemainderIntegrand N w)
        volume ε T) :
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ((Complex.I *
          (∫ t : ℝ in ε..T,
            Complex.finiteAbelPlanaLogSummand w
              (((N + 1 : ℕ) : ℂ) - Complex.I * (t : ℂ)) *
              (Complex.finiteAbelPlanaCotangentKernel
                (((N + 1 : ℕ) : ℂ) - Complex.I * (t : ℂ)) -
                (Real.pi : ℂ) * Complex.I))) +
        (Complex.I *
          (∫ t : ℝ in ε..T,
            Complex.finiteAbelPlanaLogSummand w
              (((N + 1 : ℕ) : ℂ) + Complex.I * (t : ℂ)) *
              (Complex.finiteAbelPlanaCotangentKernel
                (((N + 1 : ℕ) : ℂ) + Complex.I * (t : ℂ)) +
                (Real.pi : ℂ) * Complex.I)))) =
      Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSidePVNormalized N w T ε := by
  let M : ℕ := N + 1
  let q : ℂ := ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹
  let L : ℝ → ℂ := Complex.rightChangedLowerRemainderIntegrand N w
  let U : ℝ → ℂ := Complex.rightUpperRemainderIntegrand N w
  have hsum :
      ∫ t : ℝ in ε..T, L t + U t =
        (∫ t : ℝ in ε..T, L t) + ∫ t : ℝ in ε..T, U t :=
    intervalIntegral.integral_add
      (μ := MeasureTheory.volume)
      hlower hupper
  have hscale :
      ∫ t : ℝ in ε..T, q * (L t + U t) =
        q * ∫ t : ℝ in ε..T, L t + U t :=
    intervalIntegral.integral_const_mul q (fun t : ℝ => L t + U t)
  have htoSet :
      ∫ t : ℝ in ε..T, q * (L t + U t) =
        ∫ t : ℝ in Set.Ioc ε T, q * (L t + U t) :=
    intervalIntegral.integral_of_le hεT
  have hL :
      ∫ t : ℝ in ε..T, L t =
        Complex.I *
          (∫ t : ℝ in ε..T,
            Complex.finiteAbelPlanaLogSummand w ((M : ℂ) - Complex.I * (t : ℂ)) *
              (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) - Complex.I * (t : ℂ)) -
                (Real.pi : ℂ) * Complex.I)) :=
    intervalIntegral.integral_const_mul
      Complex.I
      (fun t : ℝ =>
        Complex.finiteAbelPlanaLogSummand w ((M : ℂ) - Complex.I * (t : ℂ)) *
          (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) - Complex.I * (t : ℂ)) -
            (Real.pi : ℂ) * Complex.I))
  have hU :
      ∫ t : ℝ in ε..T, U t =
        Complex.I *
          (∫ t : ℝ in ε..T,
            Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (t : ℂ)) *
              (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) + Complex.I * (t : ℂ)) +
                (Real.pi : ℂ) * Complex.I)) :=
    intervalIntegral.integral_const_mul
      Complex.I
      (fun t : ℝ =>
        Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (t : ℂ)) *
          (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) + Complex.I * (t : ℂ)) +
            (Real.pi : ℂ) * Complex.I))
  unfold Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSidePVNormalized
  calc
    q *
        ((Complex.I *
          (∫ t : ℝ in ε..T,
            Complex.finiteAbelPlanaLogSummand w ((M : ℂ) - Complex.I * (t : ℂ)) *
              (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) - Complex.I * (t : ℂ)) -
                (Real.pi : ℂ) * Complex.I))) +
        (Complex.I *
          (∫ t : ℝ in ε..T,
            Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (t : ℂ)) *
              (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) + Complex.I * (t : ℂ)) +
                (Real.pi : ℂ) * Complex.I)))) =
      q * ((∫ t : ℝ in ε..T, L t) + ∫ t : ℝ in ε..T, U t) := by
      exact congrArg (fun z : ℂ => q * z)
        (congrArg₂ HAdd.hAdd hL.symm hU.symm)
    _ = q * ∫ t : ℝ in ε..T, L t + U t := by
      exact congrArg (fun z : ℂ => q * z) hsum.symm
    _ = ∫ t : ℝ in ε..T, q * (L t + U t) := by
      exact hscale.symm
    _ = ∫ t : ℝ in Set.Ioc ε T, q * (L t + U t) := htoSet

/-- Continuity of the changed lower-half left endpoint logarithmic summand. -/
theorem Complex.continuous_leftChangedLowerVerticalSummand
    {w : ℂ}
    (hw : 0 < w.re) :
    Continuous
      (fun t : ℝ =>
        Complex.finiteAbelPlanaLogSummand w (-(Complex.I * (t : ℂ)))) := by
  have hlog_base :
      Continuous
        (fun y : ℝ =>
          Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ))) :=
    Complex.continuous_finiteAbelPlana_log_leftVerticalSummand hw
  exact
    (hlog_base.comp continuous_neg).congr
      (fun t =>
        congrArg
          (fun z : ℂ => Complex.finiteAbelPlanaLogSummand w z)
          (Complex.I_mul_neg_real_eq_neg_I_mul t))

/-- Cotangent-kernel continuity on the changed lower-half left endpoint
positive window. -/
theorem Complex.continuousOn_leftChangedLowerCotangentKernel
    (T ε : ℝ)
    (hε : 0 < ε)
    (hεT : ε < T) :
    ContinuousOn
      (fun t : ℝ =>
        Complex.finiteAbelPlanaCotangentKernel (-(Complex.I * (t : ℂ))))
      (Set.uIcc ε T) := by
  have horder : ε ≤ T := hεT.le
  have hpath :
      Continuous (fun t : ℝ => -(Complex.I * (t : ℂ))) :=
    (continuous_const.mul Complex.continuous_ofReal).neg
  intro t ht
  have htIcc : t ∈ Set.Icc ε T :=
    (Set.uIcc_of_le horder).symm ▸ ht
  have ht_pos : 0 < t :=
    lt_of_lt_of_le hε htIcc.1
  have him :
      (-(Complex.I * (t : ℂ))).im = -t := by
    calc
      (-(Complex.I * (t : ℂ))).im = -((Complex.I * (t : ℂ)).im) :=
        Complex.neg_im (Complex.I * (t : ℂ))
      _ = -t := by
        exact congrArg Neg.neg
          (Eq.trans (Complex.I_mul_im (t : ℂ)) (Complex.ofReal_re t))
  have hne : (-(Complex.I * (t : ℂ))).im ≠ 0 :=
    him.symm ▸ ne_of_lt (neg_neg_of_pos ht_pos)
  exact
    (ContinuousAt.comp'
      (g := Complex.finiteAbelPlanaCotangentKernel)
      (f := fun t : ℝ => -(Complex.I * (t : ℂ)))
      (Complex.differentiableAt_finiteAbelPlanaCotangentKernel
        (Complex.sin_pi_mul_ne_zero_of_im_ne_zero hne)).continuousAt
      hpath.continuousAt).continuousWithinAt

/-- Cotangent-kernel continuity on the upper-half left endpoint positive
window. -/
theorem Complex.continuousOn_leftUpperCotangentKernel
    (T ε : ℝ)
    (hε : 0 < ε)
    (hεT : ε < T) :
    ContinuousOn
      (fun t : ℝ =>
        Complex.finiteAbelPlanaCotangentKernel (Complex.I * (t : ℂ)))
      (Set.uIcc ε T) := by
  have horder : ε ≤ T := hεT.le
  have hpath :
      Continuous (fun t : ℝ => Complex.I * (t : ℂ)) :=
    continuous_const.mul Complex.continuous_ofReal
  intro t ht
  have htIcc : t ∈ Set.Icc ε T :=
    (Set.uIcc_of_le horder).symm ▸ ht
  have ht_pos : 0 < t :=
    lt_of_lt_of_le hε htIcc.1
  have him : (Complex.I * (t : ℂ)).im = t :=
    Eq.trans (Complex.I_mul_im (t : ℂ)) (Complex.ofReal_re t)
  have hne : (Complex.I * (t : ℂ)).im ≠ 0 :=
    him.symm ▸ ne_of_gt ht_pos
  exact
    (ContinuousAt.comp'
      (g := Complex.finiteAbelPlanaCotangentKernel)
      (f := fun t : ℝ => Complex.I * (t : ℂ))
      (Complex.differentiableAt_finiteAbelPlanaCotangentKernel
        (Complex.sin_pi_mul_ne_zero_of_im_ne_zero hne)).continuousAt
      hpath.continuousAt).continuousWithinAt

/-- Continuity of the changed lower-half right endpoint logarithmic summand. -/
theorem Complex.continuous_rightChangedLowerVerticalSummand
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re) :
    Continuous
      (fun t : ℝ =>
        Complex.finiteAbelPlanaLogSummand w
          (((N + 1 : ℕ) : ℂ) - Complex.I * (t : ℂ))) := by
  let M : ℕ := N + 1
  have hlog_base :
      Continuous
        (fun y : ℝ =>
          Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (y : ℂ))) :=
    Complex.continuous_finiteAbelPlana_log_rightVerticalSummand N hw
  exact
    (hlog_base.comp continuous_neg).congr
      (fun t =>
        congrArg
          (fun z : ℂ => Complex.finiteAbelPlanaLogSummand w z)
          (Complex.rightVertical_add_I_mul_neg_real_eq_sub_I_mul M t))

/-- Cotangent-kernel continuity on the changed lower-half right endpoint
positive window. -/
theorem Complex.continuousOn_rightChangedLowerCotangentKernel
    (N : ℕ)
    (T ε : ℝ)
    (hε : 0 < ε)
    (hεT : ε < T) :
    ContinuousOn
      (fun t : ℝ =>
        Complex.finiteAbelPlanaCotangentKernel
          (((N + 1 : ℕ) : ℂ) - Complex.I * (t : ℂ)))
      (Set.uIcc ε T) := by
  let M : ℕ := N + 1
  have horder : ε ≤ T := hεT.le
  have hpath :
      Continuous (fun t : ℝ => (M : ℂ) - Complex.I * (t : ℂ)) :=
    continuous_const.sub (continuous_const.mul Complex.continuous_ofReal)
  intro t ht
  have htIcc : t ∈ Set.Icc ε T :=
    (Set.uIcc_of_le horder).symm ▸ ht
  have ht_pos : 0 < t :=
    lt_of_lt_of_le hε htIcc.1
  have hM_im : ((M : ℂ)).im = 0 :=
    Complex.ofReal_im (M : ℝ)
  have hI_im : (Complex.I * (t : ℂ)).im = t :=
    Eq.trans (Complex.I_mul_im (t : ℂ)) (Complex.ofReal_re t)
  have him :
      ((M : ℂ) - Complex.I * (t : ℂ)).im = -t := by
    calc
      ((M : ℂ) - Complex.I * (t : ℂ)).im =
          ((M : ℂ)).im - (Complex.I * (t : ℂ)).im :=
        Complex.sub_im (M : ℂ) (Complex.I * (t : ℂ))
      _ = 0 - (Complex.I * (t : ℂ)).im := by
        exact congrArg (fun r : ℝ => r - (Complex.I * (t : ℂ)).im) hM_im
      _ = 0 - t := by
        exact congrArg (fun r : ℝ => 0 - r) hI_im
      _ = -t := by
        exact zero_sub t
  have hne : ((M : ℂ) - Complex.I * (t : ℂ)).im ≠ 0 :=
    him.symm ▸ ne_of_lt (neg_neg_of_pos ht_pos)
  exact
    (ContinuousAt.comp'
      (g := Complex.finiteAbelPlanaCotangentKernel)
      (f := fun t : ℝ => (M : ℂ) - Complex.I * (t : ℂ))
      (Complex.differentiableAt_finiteAbelPlanaCotangentKernel
        (Complex.sin_pi_mul_ne_zero_of_im_ne_zero hne)).continuousAt
      hpath.continuousAt).continuousWithinAt

/-- Cotangent-kernel continuity on the upper-half right endpoint positive
window. -/
theorem Complex.continuousOn_rightUpperCotangentKernel
    (N : ℕ)
    (T ε : ℝ)
    (hε : 0 < ε)
    (hεT : ε < T) :
    ContinuousOn
      (fun t : ℝ =>
        Complex.finiteAbelPlanaCotangentKernel
          (((N + 1 : ℕ) : ℂ) + Complex.I * (t : ℂ)))
      (Set.uIcc ε T) := by
  let M : ℕ := N + 1
  have horder : ε ≤ T := hεT.le
  have hpath :
      Continuous (fun t : ℝ => (M : ℂ) + Complex.I * (t : ℂ)) :=
    continuous_const.add (continuous_const.mul Complex.continuous_ofReal)
  intro t ht
  have htIcc : t ∈ Set.Icc ε T :=
    (Set.uIcc_of_le horder).symm ▸ ht
  have ht_pos : 0 < t :=
    lt_of_lt_of_le hε htIcc.1
  have hM_im : ((M : ℂ)).im = 0 :=
    Complex.ofReal_im (M : ℝ)
  have hI_im : (Complex.I * (t : ℂ)).im = t :=
    Eq.trans (Complex.I_mul_im (t : ℂ)) (Complex.ofReal_re t)
  have him :
      ((M : ℂ) + Complex.I * (t : ℂ)).im = t := by
    calc
      ((M : ℂ) + Complex.I * (t : ℂ)).im =
          ((M : ℂ)).im + (Complex.I * (t : ℂ)).im :=
        Complex.add_im (M : ℂ) (Complex.I * (t : ℂ))
      _ = 0 + (Complex.I * (t : ℂ)).im := by
        exact congrArg (fun r : ℝ => r + (Complex.I * (t : ℂ)).im) hM_im
      _ = 0 + t := by
        exact congrArg (fun r : ℝ => 0 + r) hI_im
      _ = t := by
        exact zero_add t
  have hne : ((M : ℂ) + Complex.I * (t : ℂ)).im ≠ 0 :=
    him.symm ▸ ne_of_gt ht_pos
  exact
    (ContinuousAt.comp'
      (g := Complex.finiteAbelPlanaCotangentKernel)
      (f := fun t : ℝ => (M : ℂ) + Complex.I * (t : ℂ))
      (Complex.differentiableAt_finiteAbelPlanaCotangentKernel
        (Complex.sin_pi_mul_ne_zero_of_im_ne_zero hne)).continuousAt
      hpath.continuousAt).continuousWithinAt

/-- Interval integrability of the changed lower-half left vertical
exponential-remainder integrand on a positive finite window. -/
theorem Complex.intervalIntegrable_leftChangedLowerRemainderIntegrand
    {w : ℂ}
    (hw : 0 < w.re)
    (T ε : ℝ)
    (hε : 0 < ε)
    (hεT : ε < T) :
    IntervalIntegrable (Complex.leftChangedLowerRemainderIntegrand w)
      volume ε T := by
  have hlog :
      Continuous
        (fun t : ℝ =>
          Complex.finiteAbelPlanaLogSummand w (-(Complex.I * (t : ℂ)))) :=
    Complex.continuous_leftChangedLowerVerticalSummand hw
  have hcot :
      ContinuousOn
        (fun t : ℝ =>
          Complex.finiteAbelPlanaCotangentKernel (-(Complex.I * (t : ℂ))))
        (Set.uIcc ε T) :=
    Complex.continuousOn_leftChangedLowerCotangentKernel T ε hε hεT
  exact
    (continuousOn_const.mul
      (hlog.continuousOn.mul (hcot.sub continuousOn_const))).intervalIntegrable

/-- Interval integrability of the upper-half left vertical
exponential-remainder integrand on a positive finite window. -/
theorem Complex.intervalIntegrable_leftUpperRemainderIntegrand
    {w : ℂ}
    (hw : 0 < w.re)
    (T ε : ℝ)
    (hε : 0 < ε)
    (hεT : ε < T) :
    IntervalIntegrable (Complex.leftUpperRemainderIntegrand w)
      volume ε T := by
  have hlog :
      Continuous
        (fun t : ℝ =>
          Complex.finiteAbelPlanaLogSummand w (Complex.I * (t : ℂ))) :=
    Complex.continuous_finiteAbelPlana_log_leftVerticalSummand hw
  have hcot :
      ContinuousOn
        (fun t : ℝ =>
          Complex.finiteAbelPlanaCotangentKernel (Complex.I * (t : ℂ)))
        (Set.uIcc ε T) :=
    Complex.continuousOn_leftUpperCotangentKernel T ε hε hεT
  exact
    (continuousOn_const.mul
      (hlog.continuousOn.mul (hcot.add continuousOn_const))).intervalIntegrable

/-- Interval integrability of the changed lower-half right endpoint vertical
exponential-remainder integrand on a positive finite window. -/
theorem Complex.intervalIntegrable_rightChangedLowerRemainderIntegrand
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (T ε : ℝ)
    (hε : 0 < ε)
    (hεT : ε < T) :
    IntervalIntegrable (Complex.rightChangedLowerRemainderIntegrand N w)
      volume ε T := by
  let M : ℕ := N + 1
  have hlog :
      Continuous
        (fun t : ℝ =>
          Complex.finiteAbelPlanaLogSummand w ((M : ℂ) - Complex.I * (t : ℂ))) :=
    Complex.continuous_rightChangedLowerVerticalSummand N hw
  have hcot :
      ContinuousOn
        (fun t : ℝ =>
          Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) - Complex.I * (t : ℂ)))
        (Set.uIcc ε T) :=
    Complex.continuousOn_rightChangedLowerCotangentKernel N T ε hε hεT
  exact
    (continuousOn_const.mul
      (hlog.continuousOn.mul (hcot.sub continuousOn_const))).intervalIntegrable

/-- Interval integrability of the upper-half right endpoint vertical
exponential-remainder integrand on a positive finite window. -/
theorem Complex.intervalIntegrable_rightUpperRemainderIntegrand
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (T ε : ℝ)
    (hε : 0 < ε)
    (hεT : ε < T) :
    IntervalIntegrable (Complex.rightUpperRemainderIntegrand N w)
      volume ε T := by
  let M : ℕ := N + 1
  have hlog :
      Continuous
        (fun t : ℝ =>
          Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (t : ℂ))) :=
    Complex.continuous_finiteAbelPlana_log_rightVerticalSummand N hw
  have hcot :
      ContinuousOn
        (fun t : ℝ =>
          Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) + Complex.I * (t : ℂ)))
        (Set.uIcc ε T) :=
    Complex.continuousOn_rightUpperCotangentKernel N T ε hε hεT
  exact
    (continuousOn_const.mul
      (hlog.continuousOn.mul (hcot.add continuousOn_const))).intervalIntegrable

/-- Left raw-to-normalized PV remainder orientation from the finite interval
integrability of the two changed half-line remainder integrands. -/
theorem Complex.leftPVNormalizedRemainderOrientation_of_changedIntervalIntegrable
    (w : ℂ)
    (T ε : ℝ)
    (hε : 0 < ε)
    (hεT : ε < T)
    (hlower :
      IntervalIntegrable (Complex.leftChangedLowerRemainderIntegrand w)
        volume ε T)
    (hupper :
      IntervalIntegrable (Complex.leftUpperRemainderIntegrand w)
        volume ε T) :
    Complex.LeftPVNormalizedRemainderOrientation w T ε := by
  exact
    Complex.leftPVNormalizedRemainderOrientation_of_rawNormalized_eq
      w T ε
      ((Complex.finiteAbelPlana_log_leftRemainderPVRawNormalized_eq_changedIntervalSum
          w T ε hε hεT).trans
        (Complex.finiteAbelPlana_log_leftChangedIntervalSum_eq_remainderPVNormalized
          w T ε hεT.le hlower hupper))

/-- Right raw-to-normalized PV remainder orientation from the finite interval
integrability of the two changed half-line remainder integrands. -/
theorem Complex.rightPVNormalizedRemainderOrientation_of_changedIntervalIntegrable
    (N : ℕ)
    (w : ℂ)
    (T ε : ℝ)
    (hε : 0 < ε)
    (hεT : ε < T)
    (hlower :
      IntervalIntegrable (Complex.rightChangedLowerRemainderIntegrand N w)
        volume ε T)
    (hupper :
      IntervalIntegrable (Complex.rightUpperRemainderIntegrand N w)
        volume ε T) :
    Complex.RightPVNormalizedRemainderOrientation N w T ε := by
  exact
    Complex.rightPVNormalizedRemainderOrientation_of_rawNormalized_eq
      N w T ε
      ((Complex.finiteAbelPlana_log_rightRemainderPVRawNormalized_eq_changedIntervalSum
          N w T ε hε hεT).trans
        (Complex.finiteAbelPlana_log_rightChangedIntervalSum_eq_remainderPVNormalized
          N w T ε hεT.le hlower hupper))

/-- Pointwise left raw-to-normalized PV remainder orientation on a positive
finite window. -/
theorem Complex.leftPVNormalizedRemainderOrientation_of_pos
    {w : ℂ}
    (hw : 0 < w.re)
    (T ε : ℝ)
    (hε : 0 < ε)
    (hεT : ε < T) :
    Complex.LeftPVNormalizedRemainderOrientation w T ε := by
  exact
    Complex.leftPVNormalizedRemainderOrientation_of_changedIntervalIntegrable
      w T ε hε hεT
      (Complex.intervalIntegrable_leftChangedLowerRemainderIntegrand
        hw T ε hε hεT)
      (Complex.intervalIntegrable_leftUpperRemainderIntegrand
        hw T ε hε hεT)

/-- Pointwise right raw-to-normalized PV remainder orientation on a positive
finite window. -/
theorem Complex.rightPVNormalizedRemainderOrientation_of_pos
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (T ε : ℝ)
    (hε : 0 < ε)
    (hεT : ε < T) :
    Complex.RightPVNormalizedRemainderOrientation N w T ε := by
  exact
    Complex.rightPVNormalizedRemainderOrientation_of_changedIntervalIntegrable
      N w T ε hε hεT
      (Complex.intervalIntegrable_rightChangedLowerRemainderIntegrand
        N hw T ε hε hεT)
      (Complex.intervalIntegrable_rightUpperRemainderIntegrand
        N hw T ε hε hεT)

/-- Algebraic assembly of the normalized PV rectangle side from its horizontal
and vertical split pieces. -/
theorem Complex.finiteAbelPlana_log_rectangleSideExpressionPVNormalized_eq_boundaryFaces_add_horizontalError_of_splits
    (N : ℕ)
    (w : ℂ)
    (T ε : ℝ)
    (hlower :
      Complex.finiteAbelPlanaLogFiniteHeightLowerSide N w T =
        Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
          Complex.finiteAbelPlanaLogBottomHorizontalEdge N w T)
    (hupper :
      Complex.finiteAbelPlanaLogFiniteHeightUpperSide N w T =
        Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T +
          Complex.finiteAbelPlanaLogTopHorizontalEdge N w T)
    (hleft :
      Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ε =
        Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSidePV w T ε +
          Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSidePV w T ε)
    (hright :
      Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ε =
        Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSidePV N w T ε +
          Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSidePV N w T ε)
    (hleftNorm : Complex.LeftPVNormalizedRemainderOrientation w T ε)
    (hrightNorm : Complex.RightPVNormalizedRemainderOrientation N w T ε) :
    Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ε =
      (Complex.finiteAbelPlanaLogLeftBoundaryFacePVNormalized N w T ε +
        Complex.finiteAbelPlanaLogRightBoundaryFacePVNormalized N w T ε) +
        Complex.finiteAbelPlanaLogHorizontalEdgeError N w T := by
  let q : ℂ := ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹
  let LC : ℂ := Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T
  let UC : ℂ := Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T
  let B : ℂ := Complex.finiteAbelPlanaLogBottomHorizontalEdge N w T
  let Top : ℂ := Complex.finiteAbelPlanaLogTopHorizontalEdge N w T
  let LV : ℂ := Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSidePV w T ε
  let LR : ℂ := Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSidePV w T ε
  let RV : ℂ := Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSidePV N w T ε
  let RR : ℂ := Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSidePV N w T ε
  have hrect :
      Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ε =
        q * (((LC + B) - (UC + Top)) +
          (Complex.I * (RV + RR) - Complex.I * (LV + LR))) := by
    unfold Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized
      Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPV
      Complex.finiteAbelPlanaLogFiniteHeightHorizontalSideExpression
      Complex.finiteAbelPlanaLogFiniteHeightRawVerticalSideExpressionPV
    exact congrArg
      (fun z : ℂ => ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ * z)
      (congrArg₂ HAdd.hAdd
        (congrArg₂ HSub.hSub hlower hupper)
        (congrArg₂ HSub.hSub
          (congrArg (fun z : ℂ => Complex.I * z) hright)
          (congrArg (fun z : ℂ => Complex.I * z) hleft)))
  have hcollect :
      q * (((LC + B) - (UC + Top)) +
          (Complex.I * (RV + RR) - Complex.I * (LV + LR))) =
        ((q * (-UC - Complex.I * LV)) + (q * (-Complex.I * LR)) +
          ((q * (LC + Complex.I * RV)) + (q * (Complex.I * RR)))) +
          (q * (B - Top)) := by
    have hhorizontal :
        (LC + B) - (UC + Top) = (LC - UC) + (B - Top) :=
      add_sub_add_comm LC B UC Top
    have hrightVertical :
        Complex.I * (RV + RR) = Complex.I * RV + Complex.I * RR :=
      mul_add Complex.I RV RR
    have hleftVertical :
        Complex.I * (LV + LR) = Complex.I * LV + Complex.I * LR :=
      mul_add Complex.I LV LR
    have hrawVertical :
        Complex.I * (RV + RR) - Complex.I * (LV + LR) =
          (Complex.I * RV + Complex.I * RR) +
            (-Complex.I * LV + -Complex.I * LR) := by
      calc
        Complex.I * (RV + RR) - Complex.I * (LV + LR) =
          (Complex.I * RV + Complex.I * RR) -
            (Complex.I * LV + Complex.I * LR) := by
          exact congrArg₂ HSub.hSub hrightVertical hleftVertical
        _ =
          (Complex.I * RV + Complex.I * RR) +
            -((Complex.I * LV + Complex.I * LR)) := by
          exact sub_eq_add_neg
            (Complex.I * RV + Complex.I * RR)
            (Complex.I * LV + Complex.I * LR)
        _ =
          (Complex.I * RV + Complex.I * RR) +
            (-(Complex.I * LV) + -(Complex.I * LR)) := by
          exact congrArg
            (fun z : ℂ => (Complex.I * RV + Complex.I * RR) + z)
            (neg_add (Complex.I * LV) (Complex.I * LR))
        _ =
          (Complex.I * RV + Complex.I * RR) +
            (-Complex.I * LV + -Complex.I * LR) := by
          exact congrArg
            (fun z : ℂ => (Complex.I * RV + Complex.I * RR) + z)
            (congrArg₂ HAdd.hAdd
              (neg_mul Complex.I LV).symm
              (neg_mul Complex.I LR).symm)
    have hcore :
        ((LC - UC) + (B - Top)) +
            ((Complex.I * RV + Complex.I * RR) +
              (-Complex.I * LV + -Complex.I * LR)) =
          ((-UC - Complex.I * LV) + (LC + Complex.I * RV)) +
            ((-Complex.I * LR + Complex.I * RR) + (B - Top)) := by
      calc
        ((LC - UC) + (B - Top)) +
            ((Complex.I * RV + Complex.I * RR) +
              (-Complex.I * LV + -Complex.I * LR)) =
          (LC + -UC + (B - Top)) +
            ((Complex.I * RV + Complex.I * RR) +
              (-Complex.I * LV + -Complex.I * LR)) := by
          exact congrArg
            (fun z : ℂ => (z + (B - Top)) +
              ((Complex.I * RV + Complex.I * RR) +
                (-Complex.I * LV + -Complex.I * LR)))
            (sub_eq_add_neg LC UC)
        _ =
          ((-UC + -(Complex.I * LV)) + (LC + Complex.I * RV)) +
            ((-Complex.I * LR + Complex.I * RR) + (B - Top)) := by
          have hvertical_repair :
              (Complex.I * RV + Complex.I * RR) +
                  (-Complex.I * LV + -Complex.I * LR) =
                (Complex.I * RV + -Complex.I * LV) +
                  (Complex.I * RR + -Complex.I * LR) :=
            add_add_add_comm
              (Complex.I * RV) (Complex.I * RR)
              (-Complex.I * LV) (-Complex.I * LR)
          have hfirst_pair :
              (LC + -UC) + (Complex.I * RV + -Complex.I * LV) =
                (-UC + -(Complex.I * LV)) + (LC + Complex.I * RV) := by
            calc
              (LC + -UC) + (Complex.I * RV + -Complex.I * LV) =
                (LC + Complex.I * RV) + (-UC + -Complex.I * LV) := by
                exact add_add_add_comm
                  LC (-UC) (Complex.I * RV) (-Complex.I * LV)
              _ =
                (LC + Complex.I * RV) + (-UC + -(Complex.I * LV)) := by
                exact congrArg
                  (fun z : ℂ => (LC + Complex.I * RV) + (-UC + z))
                  (neg_mul Complex.I LV)
              _ =
                (-UC + -(Complex.I * LV)) + (LC + Complex.I * RV) := by
                exact add_comm
                  (LC + Complex.I * RV)
                  (-UC + -(Complex.I * LV))
          have hsecond_pair :
              (B - Top) + (Complex.I * RR + -Complex.I * LR) =
                (-Complex.I * LR + Complex.I * RR) + (B - Top) := by
            calc
              (B - Top) + (Complex.I * RR + -Complex.I * LR) =
                (B - Top) + (-Complex.I * LR + Complex.I * RR) := by
                exact congrArg (fun z : ℂ => (B - Top) + z)
                  (add_comm (Complex.I * RR) (-Complex.I * LR))
              _ =
                (-Complex.I * LR + Complex.I * RR) + (B - Top) := by
                exact add_comm
                  (B - Top)
                  (-Complex.I * LR + Complex.I * RR)
          calc
            (LC + -UC + (B - Top)) +
                ((Complex.I * RV + Complex.I * RR) +
                  (-Complex.I * LV + -Complex.I * LR)) =
              (LC + -UC + (B - Top)) +
                ((Complex.I * RV + -Complex.I * LV) +
                  (Complex.I * RR + -Complex.I * LR)) := by
              exact congrArg
                (fun z : ℂ => (LC + -UC + (B - Top)) + z)
                hvertical_repair
            _ =
              ((LC + -UC) + (Complex.I * RV + -Complex.I * LV)) +
                ((B - Top) + (Complex.I * RR + -Complex.I * LR)) := by
              exact add_add_add_comm
                (LC + -UC) (B - Top)
                (Complex.I * RV + -Complex.I * LV)
                (Complex.I * RR + -Complex.I * LR)
            _ =
              ((-UC + -(Complex.I * LV)) + (LC + Complex.I * RV)) +
                ((-Complex.I * LR + Complex.I * RR) + (B - Top)) := by
              exact congrArg₂ HAdd.hAdd hfirst_pair hsecond_pair
        _ =
          ((-UC - Complex.I * LV) + (LC + Complex.I * RV)) +
            ((-Complex.I * LR + Complex.I * RR) + (B - Top)) := by
          exact congrArg
            (fun z : ℂ => (z + (LC + Complex.I * RV)) +
              ((-Complex.I * LR + Complex.I * RR) + (B - Top)))
            (sub_eq_add_neg (-UC) (Complex.I * LV)).symm
    have hsplit_right :
        q * ((-Complex.I * LR + Complex.I * RR) + (B - Top)) =
          (q * (-Complex.I * LR) + q * (Complex.I * RR)) + q * (B - Top) := by
      calc
        q * ((-Complex.I * LR + Complex.I * RR) + (B - Top)) =
          q * (-Complex.I * LR + Complex.I * RR) + q * (B - Top) := by
          exact mul_add q (-Complex.I * LR + Complex.I * RR) (B - Top)
        _ =
          (q * (-Complex.I * LR) + q * (Complex.I * RR)) + q * (B - Top) := by
          exact congrArg
            (fun z : ℂ => z + q * (B - Top))
            (mul_add q (-Complex.I * LR) (Complex.I * RR))
    have hsplit_all :
        q * (((-UC - Complex.I * LV) + (LC + Complex.I * RV)) +
            ((-Complex.I * LR + Complex.I * RR) + (B - Top))) =
          (q * (-UC - Complex.I * LV) + q * (LC + Complex.I * RV)) +
            ((q * (-Complex.I * LR) + q * (Complex.I * RR)) + q * (B - Top)) := by
      calc
        q * (((-UC - Complex.I * LV) + (LC + Complex.I * RV)) +
            ((-Complex.I * LR + Complex.I * RR) + (B - Top))) =
          q * ((-UC - Complex.I * LV) + (LC + Complex.I * RV)) +
            q * ((-Complex.I * LR + Complex.I * RR) + (B - Top)) := by
          exact mul_add q
            ((-UC - Complex.I * LV) + (LC + Complex.I * RV))
            ((-Complex.I * LR + Complex.I * RR) + (B - Top))
        _ =
          (q * (-UC - Complex.I * LV) + q * (LC + Complex.I * RV)) +
            ((q * (-Complex.I * LR) + q * (Complex.I * RR)) + q * (B - Top)) := by
          exact congrArg₂ HAdd.hAdd
            (mul_add q (-UC - Complex.I * LV) (LC + Complex.I * RV))
            hsplit_right
    have hfinal_collect :
        (q * (-UC - Complex.I * LV) + q * (LC + Complex.I * RV)) +
            ((q * (-Complex.I * LR) + q * (Complex.I * RR)) + q * (B - Top)) =
          ((q * (-UC - Complex.I * LV)) + (q * (-Complex.I * LR)) +
            ((q * (LC + Complex.I * RV)) + (q * (Complex.I * RR)))) +
            (q * (B - Top)) := by
      calc
        (q * (-UC - Complex.I * LV) + q * (LC + Complex.I * RV)) +
            ((q * (-Complex.I * LR) + q * (Complex.I * RR)) + q * (B - Top)) =
          ((q * (-UC - Complex.I * LV) + q * (LC + Complex.I * RV)) +
            (q * (-Complex.I * LR) + q * (Complex.I * RR))) +
              q * (B - Top) := by
          exact (add_assoc
            (q * (-UC - Complex.I * LV) + q * (LC + Complex.I * RV))
            (q * (-Complex.I * LR) + q * (Complex.I * RR))
            (q * (B - Top))).symm
        _ =
          ((q * (-UC - Complex.I * LV)) + (q * (-Complex.I * LR)) +
            ((q * (LC + Complex.I * RV)) + (q * (Complex.I * RR)))) +
              q * (B - Top) := by
          exact congrArg
            (fun z : ℂ => z + q * (B - Top))
            (add_add_add_comm
              (q * (-UC - Complex.I * LV))
              (q * (LC + Complex.I * RV))
              (q * (-Complex.I * LR))
              (q * (Complex.I * RR)))
    calc
      q * (((LC + B) - (UC + Top)) +
          (Complex.I * (RV + RR) - Complex.I * (LV + LR))) =
        q * (((LC - UC) + (B - Top)) +
          (Complex.I * (RV + RR) - Complex.I * (LV + LR))) := by
        exact congrArg
          (fun z : ℂ => q * (z +
            (Complex.I * (RV + RR) - Complex.I * (LV + LR))))
          hhorizontal
      _ =
        q * (((LC - UC) + (B - Top)) +
          ((Complex.I * RV + Complex.I * RR) +
            (-Complex.I * LV + -Complex.I * LR))) := by
        exact congrArg
          (fun z : ℂ => q * (((LC - UC) + (B - Top)) + z))
          hrawVertical
      _ =
        q * (((-UC - Complex.I * LV) + (LC + Complex.I * RV)) +
          ((-Complex.I * LR + Complex.I * RR) + (B - Top))) := by
        exact congrArg (fun z : ℂ => q * z) hcore
      _ =
        (q * (-UC - Complex.I * LV) + q * (LC + Complex.I * RV)) +
          ((q * (-Complex.I * LR) + q * (Complex.I * RR)) + q * (B - Top)) := by
        exact hsplit_all
      _ =
        ((q * (-UC - Complex.I * LV)) + (q * (-Complex.I * LR)) +
          ((q * (LC + Complex.I * RV)) + (q * (Complex.I * RR)))) +
          (q * (B - Top)) := by
        exact hfinal_collect
  have hfaces :
      ((q * (-UC - Complex.I * LV)) + (q * (-Complex.I * LR)) +
          ((q * (LC + Complex.I * RV)) + (q * (Complex.I * RR)))) +
          (q * (B - Top)) =
        (Complex.finiteAbelPlanaLogLeftBoundaryFacePVNormalized N w T ε +
          Complex.finiteAbelPlanaLogRightBoundaryFacePVNormalized N w T ε) +
          Complex.finiteAbelPlanaLogHorizontalEdgeError N w T := by
    unfold Complex.finiteAbelPlanaLogLeftBoundaryFacePVNormalized
      Complex.finiteAbelPlanaLogRightBoundaryFacePVNormalized
      Complex.finiteAbelPlanaLogHorizontalEdgeError
    exact congrArg
      (fun z : ℂ => z + (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ * (B - Top)))
      (congrArg₂ HAdd.hAdd
        (congrArg₂ HAdd.hAdd rfl hleftNorm)
        (congrArg₂ HAdd.hAdd rfl hrightNorm))
  exact hrect.trans (hcollect.trans hfaces)

/-- Pointwise normalized PV rectangle-to-boundary bridge on a positive
indentation radius below the finite height. -/
theorem Complex.finiteAbelPlana_log_finiteHeightPVRectangleBoundaryBridge_of_pos
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (T ε : ℝ)
    (hT : 0 < T)
    (hε : 0 < ε)
    (hεT : ε < T)
    (hleftNorm : Complex.LeftPVNormalizedRemainderOrientation w T ε)
    (hrightNorm : Complex.RightPVNormalizedRemainderOrientation N w T ε) :
    Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ε =
      (Complex.finiteAbelPlanaLogLeftBoundaryFacePVNormalized N w T ε +
        Complex.finiteAbelPlanaLogRightBoundaryFacePVNormalized N w T ε) +
        Complex.finiteAbelPlanaLogHorizontalEdgeError N w T := by
  have hlower :
      Complex.finiteAbelPlanaLogFiniteHeightLowerSide N w T =
        Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
          Complex.finiteAbelPlanaLogBottomHorizontalEdge N w T :=
    Complex.finiteAbelPlana_log_lowerHorizontalSide_eq_constant_add_bottomEdge
      N w T hw hT
  have hupper :
      Complex.finiteAbelPlanaLogFiniteHeightUpperSide N w T =
        Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T +
          Complex.finiteAbelPlanaLogTopHorizontalEdge N w T :=
    Complex.finiteAbelPlana_log_upperHorizontalSide_eq_constant_add_topEdge
      N w T hw hT
  have hleft :
      Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ε =
        Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSidePV w T ε +
          Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSidePV w T ε :=
    Complex.finiteAbelPlana_log_leftVerticalSidePV_eq_constant_add_remainder
      w T ε hw hε hεT
  have hright :
      Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ε =
        Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSidePV N w T ε +
          Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSidePV N w T ε :=
    Complex.finiteAbelPlana_log_rightVerticalSidePV_eq_constant_add_remainder
      N w T ε hw hε hεT
  exact
    Complex.finiteAbelPlana_log_rectangleSideExpressionPVNormalized_eq_boundaryFaces_add_horizontalError_of_splits
      N w T ε hlower hupper hleft hright hleftNorm hrightNorm

/-- Eventual normalized PV rectangle-to-boundary bridge from eventual
normalized-remainder orientations. -/
theorem Complex.finiteAbelPlana_log_finiteHeightPVRectangleBoundaryBridge_eventually
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (T : ℝ)
    (hT : 0 < T)
    (hleftNorm :
      ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
        Complex.LeftPVNormalizedRemainderOrientation w T ε)
    (hrightNorm :
      ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
        Complex.RightPVNormalizedRemainderOrientation N w T ε) :
    Complex.FiniteHeightPVRectangleBoundaryBridge N w T := by
  filter_upwards [Ioo_mem_nhdsWithin_Ioi ⟨le_rfl, hT⟩, hleftNorm, hrightNorm] with
    ε hε hleft hright
  exact
    Complex.finiteAbelPlana_log_finiteHeightPVRectangleBoundaryBridge_of_pos
      N hw T ε hT hε.1 hε.2 hleft hright

/-- Pointwise normalized PV rectangle-to-boundary bridge with the raw
remainder orientations discharged at the owner level. -/
theorem Complex.finiteAbelPlana_log_finiteHeightPVRectangleBoundaryBridge_of_pos_owner
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (T ε : ℝ)
    (hT : 0 < T)
    (hε : 0 < ε)
    (hεT : ε < T) :
    Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ε =
      (Complex.finiteAbelPlanaLogLeftBoundaryFacePVNormalized N w T ε +
        Complex.finiteAbelPlanaLogRightBoundaryFacePVNormalized N w T ε) +
        Complex.finiteAbelPlanaLogHorizontalEdgeError N w T := by
  exact
    Complex.finiteAbelPlana_log_finiteHeightPVRectangleBoundaryBridge_of_pos
      N hw T ε hT hε hεT
      (Complex.leftPVNormalizedRemainderOrientation_of_pos hw T ε hε hεT)
      (Complex.rightPVNormalizedRemainderOrientation_of_pos N hw T ε hε hεT)

/-- Eventual normalized PV rectangle-to-boundary bridge with raw remainder
orientations discharged at the owner level. -/
theorem Complex.finiteAbelPlana_log_finiteHeightPVRectangleBoundaryBridge_eventually_owner
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (T : ℝ)
    (hT : 0 < T) :
    Complex.FiniteHeightPVRectangleBoundaryBridge N w T := by
  filter_upwards [Ioo_mem_nhdsWithin_Ioi ⟨le_rfl, hT⟩] with ε hε
  exact
    Complex.finiteAbelPlana_log_finiteHeightPVRectangleBoundaryBridge_of_pos_owner
      N hw T ε hT hε.1 hε.2

/-- Fixed-`N` finite-height bridge package from pointwise target bridges and
eventual normalized-remainder orientations. -/
theorem Complex.finiteAbelPlana_log_finiteHeightPVBridgePackageAt_of_orientations
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (htarget :
      ∀ᶠ T : ℝ in atTop,
        Complex.FiniteHeightPVBoundaryTargetBridge N w T)
    (hleftNorm :
      ∀ᶠ T : ℝ in atTop,
        ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
          Complex.LeftPVNormalizedRemainderOrientation w T ε)
    (hrightNorm :
      ∀ᶠ T : ℝ in atTop,
        ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
          Complex.RightPVNormalizedRemainderOrientation N w T ε) :
    Complex.FiniteHeightPVBridgePackageAt N w := by
  filter_upwards [eventually_gt_atTop (0 : ℝ), htarget, hleftNorm, hrightNorm] with
    T hT htargetT hleftT hrightT
  exact ⟨hT,
    Complex.finiteAbelPlana_log_finiteHeightPVRectangleBoundaryBridge_eventually
      N hw T hT hleftT hrightT,
    htargetT⟩

/-- All-`N` finite-height bridge package from pointwise target bridges and
eventual normalized-remainder orientations. -/
theorem Complex.finiteAbelPlana_log_finiteHeightPVBridgePackage_of_orientations
    {w : ℂ}
    (hw : 0 < w.re)
    (htarget :
      ∀ N : ℕ,
        ∀ᶠ T : ℝ in atTop,
          Complex.FiniteHeightPVBoundaryTargetBridge N w T)
    (hleftNorm :
      ∀ᶠ T : ℝ in atTop,
        ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
          Complex.LeftPVNormalizedRemainderOrientation w T ε)
    (hrightNorm :
      ∀ N : ℕ,
        ∀ᶠ T : ℝ in atTop,
          ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
            Complex.RightPVNormalizedRemainderOrientation N w T ε) :
    Complex.FiniteHeightPVBridgePackage w := by
  intro N
  exact
    Complex.finiteAbelPlana_log_finiteHeightPVBridgePackageAt_of_orientations
      N hw (htarget N) hleftNorm (hrightNorm N)

/-- Fixed-`N` finite-height bridge package from target bridges, with
raw-remainder orientations discharged at the owner level. -/
theorem Complex.finiteAbelPlana_log_finiteHeightPVBridgePackageAt_of_targets
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (htarget :
      ∀ᶠ T : ℝ in atTop,
        Complex.FiniteHeightPVBoundaryTargetBridge N w T) :
    Complex.FiniteHeightPVBridgePackageAt N w := by
  filter_upwards [eventually_gt_atTop (0 : ℝ), htarget] with T hT htargetT
  exact ⟨hT,
    Complex.finiteAbelPlana_log_finiteHeightPVRectangleBoundaryBridge_eventually_owner
      N hw T hT,
    htargetT⟩

/-- All-`N` finite-height bridge package from target bridges, with
raw-remainder orientations discharged at the owner level. -/
theorem Complex.finiteAbelPlana_log_finiteHeightPVBridgePackage_of_targets
    {w : ℂ}
    (hw : 0 < w.re)
    (htarget :
      ∀ N : ℕ,
        ∀ᶠ T : ℝ in atTop,
          Complex.FiniteHeightPVBoundaryTargetBridge N w T) :
    Complex.FiniteHeightPVBridgePackage w := by
  intro N
  exact
    Complex.finiteAbelPlana_log_finiteHeightPVBridgePackageAt_of_targets
      N hw (htarget N)

/-- Fixed-`N` finite-height bridge package with the boundary target already
proved at the owner level. -/
theorem Complex.finiteAbelPlana_log_finiteHeightPVBridgePackageAt_of_ownerBoundaryTarget
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (hboundary :
      ∀ᶠ T : ℝ in atTop,
        (((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
              (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
                Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
            (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
          ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
              (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
                Complex.I *
                  Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
            (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) =
          Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T)
    (hleftNorm :
      ∀ᶠ T : ℝ in atTop,
        ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
          Complex.LeftPVNormalizedRemainderOrientation w T ε)
    (hrightNorm :
      ∀ᶠ T : ℝ in atTop,
        ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
          Complex.RightPVNormalizedRemainderOrientation N w T ε) :
    Complex.FiniteHeightPVBridgePackageAt N w := by
  have htarget :
      ∀ᶠ T : ℝ in atTop,
        Complex.FiniteHeightPVBoundaryTargetBridge N w T := by
    filter_upwards [hboundary] with T hT
    exact
      Complex.finiteAbelPlana_log_finiteHeightPVBoundaryTargetBridge_of_normalizedTarget
        N w T hT
  exact
    Complex.finiteAbelPlana_log_finiteHeightPVBridgePackageAt_of_orientations
      N hw htarget hleftNorm hrightNorm

/-- Fixed-`N` finite-height bridge package with the boundary target and
raw-remainder orientations discharged at the owner level. -/
theorem Complex.finiteAbelPlana_log_finiteHeightPVBridgePackageAt_of_ownerBoundaryTarget_owner
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (hboundary :
      ∀ᶠ T : ℝ in atTop,
        (((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
              (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
                Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
            (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
          ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
              (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
                Complex.I *
                  Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
            (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) =
          Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T) :
    Complex.FiniteHeightPVBridgePackageAt N w := by
  have htarget :
      ∀ᶠ T : ℝ in atTop,
        Complex.FiniteHeightPVBoundaryTargetBridge N w T := by
    filter_upwards [hboundary] with T hT
    exact
      Complex.finiteAbelPlana_log_finiteHeightPVBoundaryTargetBridge_of_normalizedTarget
        N w T hT
  exact
    Complex.finiteAbelPlana_log_finiteHeightPVBridgePackageAt_of_targets
      N hw htarget

/-- All-`N` finite-height bridge package with the boundary target already
proved at the owner level. -/
theorem Complex.finiteAbelPlana_log_finiteHeightPVBridgePackage_of_ownerBoundaryTarget
    {w : ℂ}
    (hw : 0 < w.re)
    (hboundary :
      ∀ N : ℕ,
        ∀ᶠ T : ℝ in atTop,
          (((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
                  Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
              (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
            ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
                  Complex.I *
                    Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
              (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) =
            Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T)
    (hleftNorm :
      ∀ᶠ T : ℝ in atTop,
        ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
          Complex.LeftPVNormalizedRemainderOrientation w T ε)
    (hrightNorm :
      ∀ N : ℕ,
        ∀ᶠ T : ℝ in atTop,
          ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
            Complex.RightPVNormalizedRemainderOrientation N w T ε) :
    Complex.FiniteHeightPVBridgePackage w := by
  intro N
  exact
    Complex.finiteAbelPlana_log_finiteHeightPVBridgePackageAt_of_ownerBoundaryTarget
      N hw (hboundary N) hleftNorm (hrightNorm N)

/-- All-`N` finite-height bridge package with the boundary target and
raw-remainder orientations discharged at the owner level. -/
theorem Complex.finiteAbelPlana_log_finiteHeightPVBridgePackage_of_ownerBoundaryTarget_owner
    {w : ℂ}
    (hw : 0 < w.re)
    (hboundary :
      ∀ N : ℕ,
        ∀ᶠ T : ℝ in atTop,
          (((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
                  Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
              (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
            ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
                  Complex.I *
                    Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
              (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) =
            Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T) :
    Complex.FiniteHeightPVBridgePackage w := by
  intro N
  exact
    Complex.finiteAbelPlana_log_finiteHeightPVBridgePackageAt_of_ownerBoundaryTarget_owner
      N hw (hboundary N)

/-- The principal-value finite-height rectangle side expression tends to the
principal-value residue contribution. -/
theorem Complex.finiteAbelPlana_log_rectangleSideExpressionPV_tendsto_namedSide_add_horizontalError
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (T : ℝ)
    (hT : 0 < T)
    (hevent : Complex.FiniteHeightPVRectangleBoundaryBridge N w T)
    (htarget : Complex.FiniteHeightPVBoundaryTargetBridge N w T) :
    Tendsto
      (fun ρ : ℝ =>
        Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ)
      (𝓝[>] (0 : ℝ))
      (𝓝
        (Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T +
          Complex.finiteAbelPlanaLogHorizontalEdgeError N w T)) := by
  have hfaces :
      Tendsto
        (fun ρ : ℝ =>
          Complex.finiteAbelPlanaLogLeftBoundaryFacePVNormalized N w T ρ +
            Complex.finiteAbelPlanaLogRightBoundaryFacePVNormalized N w T ρ)
        (𝓝[>] (0 : ℝ))
        (𝓝
          (((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
                  Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
              (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
            ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
                  Complex.I *
                    Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
              (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T)))) :=
    Complex.finiteAbelPlana_log_boundaryFacesPV_tendsto_namedBoundary
      N hw T hT
  have hsum :
      Tendsto
        (fun ρ : ℝ =>
          (Complex.finiteAbelPlanaLogLeftBoundaryFacePVNormalized N w T ρ +
            Complex.finiteAbelPlanaLogRightBoundaryFacePVNormalized N w T ρ) +
            Complex.finiteAbelPlanaLogHorizontalEdgeError N w T)
        (𝓝[>] (0 : ℝ))
        (𝓝
          ((((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
                  Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
              (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
            ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
                  Complex.I *
                    Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
              (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) +
            Complex.finiteAbelPlanaLogHorizontalEdgeError N w T)) :=
    hfaces.add tendsto_const_nhds
  have htarget_tendsto :
      Tendsto
        (fun ρ : ℝ =>
          (Complex.finiteAbelPlanaLogLeftBoundaryFacePVNormalized N w T ρ +
            Complex.finiteAbelPlanaLogRightBoundaryFacePVNormalized N w T ρ) +
            Complex.finiteAbelPlanaLogHorizontalEdgeError N w T)
        (𝓝[>] (0 : ℝ))
        (𝓝
          (Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T +
            Complex.finiteAbelPlanaLogHorizontalEdgeError N w T)) :=
    htarget ▸ hsum
  exact htarget_tendsto.congr' hevent.symm

/-- Addition of a negated term is subtraction. -/
theorem Complex.add_neg_eq_sub (a b : ℂ) :
    a + (-b) = a - b := by
  exact (sub_eq_add_neg a b).symm

/-- Moving a common summand from the right side of an equality to a
subtraction on the other side. -/
theorem Complex.eq_sub_of_add_eq
    {a b c : ℂ}
    (h : a + c = b) :
    a = b - c := by
  calc
    a = (a + c) - c := by
      exact (add_sub_cancel_right a c).symm
    _ = b - c := by
      exact congrArg (fun z : ℂ => z - c) h

/-- Subtracting a residue contribution from a residue-minus-error expression
leaves the negative error. -/
theorem Complex.residue_sub_error_sub_residue
    (residue error : ℂ) :
    (residue - error) - residue = -error := by
  calc
    (residue - error) - residue =
        (residue + -error) - residue := by
      exact congrArg (fun z : ℂ => z - residue)
        (sub_eq_add_neg residue error)
    _ = (residue + -error) + -residue := by
      exact sub_eq_add_neg (residue + -error) residue
    _ = (-error + residue) + -residue := by
      exact congrArg (fun z : ℂ => z + -residue)
        (add_comm residue (-error))
    _ = -error + (residue + -residue) := by
      exact add_assoc (-error) residue (-residue)
    _ = -error + 0 := by
      exact congrArg (fun z : ℂ => -error + z) (add_neg_cancel residue)
    _ = -error := by
      exact add_zero (-error)

/-- The finite-height named side expression unfolds to the boundary pieces
used in the contour-error definition. -/
theorem Complex.finiteAbelPlana_log_namedSideExpression_eq_residueSum_sub_horizontalError
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    ∀ T : ℝ,
      0 < T →
      Complex.FiniteHeightPVRectangleBoundaryBridge N w T →
      Complex.FiniteHeightPVBoundaryTargetBridge N w T →
      Complex.finiteAbelPlanaLogBoundaryNamedPiecesUpTo N w T =
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w -
          Complex.finiteAbelPlanaLogHorizontalEdgeError N w T := by
  intro T hT hevent htarget
  have hnamed_boundary :
      Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T =
        Complex.finiteAbelPlanaLogBoundaryNamedPiecesUpTo N w T :=
    Complex.finiteAbelPlana_log_finiteHeightNamedSideExpression_eq_boundaryNamedPiecesUpTo
      N w T
  have hresidue :
      Tendsto
        (fun ρ : ℝ =>
          Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ)
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w)) :=
    Complex.finiteAbelPlana_log_rectangleSideExpressionPV_tendsto_integerResidues
      hw N T hT
  have hside :
      Tendsto
        (fun ρ : ℝ =>
          Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ)
        (𝓝[>] (0 : ℝ))
        (𝓝
          (Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T +
            Complex.finiteAbelPlanaLogHorizontalEdgeError N w T)) :=
    Complex.finiteAbelPlana_log_rectangleSideExpressionPV_tendsto_namedSide_add_horizontalError
      N hw T hT hevent htarget
  have hsum :
      Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T +
          Complex.finiteAbelPlanaLogHorizontalEdgeError N w T =
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w :=
    tendsto_nhds_unique hside hresidue
  have hnamed :
      Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T =
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w -
          Complex.finiteAbelPlanaLogHorizontalEdgeError N w T :=
    Complex.eq_sub_of_add_eq hsum
  exact hnamed_boundary.symm ▸ hnamed

/-- Finite-height residue accounting unfolds the contour error against the
principal-value residue contribution. -/
theorem Complex.finiteAbelPlana_log_finiteHeightContourError_eq_neg_horizontalEdgeError_residueAccounting
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    ∀ T : ℝ,
      0 < T →
      Complex.FiniteHeightPVRectangleBoundaryBridge N w T →
      Complex.FiniteHeightPVBoundaryTargetBridge N w T →
      Complex.finiteAbelPlanaLogFiniteHeightContourError N w T =
        -Complex.finiteAbelPlanaLogHorizontalEdgeError N w T := by
  intro T hT hevent htarget
  have hboundary :
      Complex.finiteAbelPlanaLogBoundaryNamedPiecesUpTo N w T =
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w -
          Complex.finiteAbelPlanaLogHorizontalEdgeError N w T :=
    Complex.finiteAbelPlana_log_namedSideExpression_eq_residueSum_sub_horizontalError
      hw N T hT hevent htarget
  have herror :
      Complex.finiteAbelPlanaLogFiniteHeightContourError N w T =
        Complex.finiteAbelPlanaLogBoundaryNamedPiecesUpTo N w T -
          Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w :=
    Complex.finiteAbelPlana_log_finiteHeightContourError_unfold' N w T
  calc
    Complex.finiteAbelPlanaLogFiniteHeightContourError N w T =
        Complex.finiteAbelPlanaLogBoundaryNamedPiecesUpTo N w T -
          Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w :=
      herror
    _ =
        (Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w -
            Complex.finiteAbelPlanaLogHorizontalEdgeError N w T) -
          Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w := by
      exact congrArg
        (fun z : ℂ => z - Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w)
        hboundary
    _ = -Complex.finiteAbelPlanaLogHorizontalEdgeError N w T := by
      exact
        Complex.residue_sub_error_sub_residue
          (Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w)
          (Complex.finiteAbelPlanaLogHorizontalEdgeError N w T)

end

end LFunctions
end Boundary
