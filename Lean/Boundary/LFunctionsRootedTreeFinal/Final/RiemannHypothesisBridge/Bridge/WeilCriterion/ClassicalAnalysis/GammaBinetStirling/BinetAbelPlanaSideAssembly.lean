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

/-- Algebraic collection of finite-height side terms into vertical and
horizontal contributions. -/
theorem Complex.finiteAbelPlana_sideExpression_collect_horizontal
    (lowerConstant bottom upperConstant top rawVertical : ℂ) :
    (lowerConstant + bottom) - (upperConstant + top) + rawVertical =
      (lowerConstant - upperConstant + rawVertical) - (bottom - top) := by
  ring

/-- The constant horizontal cotangent pieces and raw vertical sides normalize
to the real-axis endpoint contribution plus the named Abel-Plana vertical
jump expression. -/
theorem Complex.finiteAbelPlana_log_constantHorizontal_rawVertical_eq_realEndpoint_namedVertical
    (N : ℕ)
    (w : ℂ)
    (T : ℝ)
    (hT : 0 < T) :
    Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T -
        Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T +
          Complex.finiteAbelPlanaLogFiniteHeightRawVerticalSideExpression N w T =
      Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N w +
        Complex.finiteAbelPlanaLogFiniteHeightNamedVerticalSideExpression N w T := by
  have hfaces_raw :
      Complex.finiteAbelPlanaLogLeftBoundaryFace N w T +
          Complex.finiteAbelPlanaLogRightBoundaryFace N w T =
        Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T -
          Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T +
            Complex.finiteAbelPlanaLogFiniteHeightRawVerticalSideExpression N w T :=
    Complex.finiteAbelPlana_log_boundaryFaces_sum_eq_constantHorizontal_rawVertical
      N w T
  have hfaces_named :
      Complex.finiteAbelPlanaLogLeftBoundaryFace N w T +
          Complex.finiteAbelPlanaLogRightBoundaryFace N w T =
        Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T :=
    Complex.finiteAbelPlana_log_boundaryFaces_reconstruct_namedBoundary
      N w T hT
  dsimp [Complex.finiteAbelPlanaLogNamedBoundaryFaceSum]
  exact hfaces_raw.symm.trans hfaces_named

/-- Lower/upper cotangent half-plane algebra for the full finite-height side
expression.

This is the exact side-normalization statement after the horizontal
constant-kernel pieces, the endpoint principal-value indentations, and the two
vertical jump integrals are collected. -/
theorem Complex.finiteAbelPlana_log_finiteHeightSideAlgebra_eq_realEndpoint_vertical_sub_horizontal
    (N : ℕ)
    (w : ℂ)
    (T : ℝ)
    (hT : 0 < T) :
    Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpression N w T =
      (Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N w +
        Complex.finiteAbelPlanaLogFiniteHeightNamedVerticalSideExpression N w T) -
        Complex.finiteAbelPlanaLogHorizontalEdgeError N w T := by
  have hlower :
      Complex.finiteAbelPlanaLogFiniteHeightLowerSide N w T =
        Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
          Complex.finiteAbelPlanaLogBottomHorizontalEdge N w T :=
    Complex.finiteAbelPlana_log_lowerHorizontalSide_eq_constant_add_bottomEdge
      N w T hT
  have hupper :
      Complex.finiteAbelPlanaLogFiniteHeightUpperSide N w T =
        Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T +
          Complex.finiteAbelPlanaLogTopHorizontalEdge N w T :=
    Complex.finiteAbelPlana_log_upperHorizontalSide_eq_constant_add_topEdge
      N w T hT
  have hvertical :
      Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T -
          Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T +
            Complex.finiteAbelPlanaLogFiniteHeightRawVerticalSideExpression N w T =
        Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N w +
          Complex.finiteAbelPlanaLogFiniteHeightNamedVerticalSideExpression N w T :=
    Complex.finiteAbelPlana_log_constantHorizontal_rawVertical_eq_realEndpoint_namedVertical
      N w T hT
  dsimp [Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpression,
    Complex.finiteAbelPlanaLogFiniteHeightRawVerticalSideExpression,
    Complex.finiteAbelPlanaLogHorizontalEdgeError]
  rw [hlower, hupper]
  calc
    (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
          Complex.finiteAbelPlanaLogBottomHorizontalEdge N w T) -
        (Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T +
          Complex.finiteAbelPlanaLogTopHorizontalEdge N w T) +
        (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSide N w T -
          Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSide w T) =
        (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T -
          Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T +
            Complex.finiteAbelPlanaLogFiniteHeightRawVerticalSideExpression N w T) -
          (Complex.finiteAbelPlanaLogBottomHorizontalEdge N w T -
            Complex.finiteAbelPlanaLogTopHorizontalEdge N w T) := by
      dsimp [Complex.finiteAbelPlanaLogFiniteHeightRawVerticalSideExpression]
      exact
        Complex.finiteAbelPlana_sideExpression_collect_horizontal
          (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T)
          (Complex.finiteAbelPlanaLogBottomHorizontalEdge N w T)
          (Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T)
          (Complex.finiteAbelPlanaLogTopHorizontalEdge N w T)
          (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSide N w T -
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSide w T)
    _ =
        (Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N w +
          Complex.finiteAbelPlanaLogFiniteHeightNamedVerticalSideExpression N w T) -
          (Complex.finiteAbelPlanaLogBottomHorizontalEdge N w T -
            Complex.finiteAbelPlanaLogTopHorizontalEdge N w T) := by
      exact congrArg
        (fun z : ℂ =>
          z -
            (Complex.finiteAbelPlanaLogBottomHorizontalEdge N w T -
              Complex.finiteAbelPlanaLogTopHorizontalEdge N w T))
        hvertical

/-- Raw side decomposition of the finite Abel-Plana rectangle after applying
the cotangent half-plane expansions.

The non-decaying constant terms in the horizontal and vertical cotangent
expansions give the real segment and endpoint principal-value contribution;
the vertical exponential pieces give the named lower/upper Abel-Plana
logarithmic-jump integrals; the remaining horizontal exponential pieces are
`finiteAbelPlanaLogHorizontalEdgeError`. -/
theorem Complex.finiteAbelPlana_log_finiteHeightCotangentSideRewrite
    (N : ℕ)
    (w : ℂ)
    (T : ℝ)
    (hT : 0 < T) :
    Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpression N w T =
      Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T -
        Complex.finiteAbelPlanaLogHorizontalEdgeError N w T := by
  have hside :
      Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpression N w T =
        (Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N w +
          Complex.finiteAbelPlanaLogFiniteHeightNamedVerticalSideExpression N w T) -
          Complex.finiteAbelPlanaLogHorizontalEdgeError N w T :=
    Complex.finiteAbelPlana_log_finiteHeightSideAlgebra_eq_realEndpoint_vertical_sub_horizontal
      N w T hT
  have hnamed :
      Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T =
        Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N w +
          Complex.finiteAbelPlanaLogFiniteHeightNamedVerticalSideExpression N w T :=
    Complex.finiteAbelPlana_log_finiteHeightNamedSideExpression_eq_realEndpoint_add_vertical
      N w T
  calc
    Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpression N w T =
        (Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N w +
          Complex.finiteAbelPlanaLogFiniteHeightNamedVerticalSideExpression N w T) -
          Complex.finiteAbelPlanaLogHorizontalEdgeError N w T :=
      hside
    _ =
        Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T -
          Complex.finiteAbelPlanaLogHorizontalEdgeError N w T :=
      congrArg
        (fun z : ℂ =>
          z - Complex.finiteAbelPlanaLogHorizontalEdgeError N w T)
        hnamed.symm

/-- Side decomposition of the finite Abel-Plana rectangle.

After the principal-value endpoint normalization, the real-axis part contributes
the logarithmic real segment plus the half-endpoints, the vertical sides become
the named lower and upper Abel-Plana jump integrals by the cotangent
half-plane rewrite, and the remaining bottom/top sides are exactly the
horizontal edge error. -/
theorem Complex.finiteAbelPlana_log_finiteHeightRectangle_sideDecomposition
    (N : ℕ)
    (w : ℂ)
    (T : ℝ)
    (hT : 0 < T) :
    Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpression N w T =
      Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T -
        Complex.finiteAbelPlanaLogHorizontalEdgeError N w T := by
  exact
    Complex.finiteAbelPlana_log_finiteHeightCotangentSideRewrite
      N w T hT

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

/-- The principal-value finite-height rectangle side expression tends to the
named finite-height Abel-Plana side expression plus the horizontal error.

This is the endpoint-indentation normalization bridge replacing the false raw
side equality. -/
theorem Complex.finiteAbelPlana_log_rectangleSideExpressionPV_tendsto_namedSide_add_horizontalError
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (T : ℝ)
    (hT : 0 < T) :
    Tendsto
      (fun ρ : ℝ =>
        Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ)
      (𝓝[>] (0 : ℝ))
      (𝓝
        (Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T +
          Complex.finiteAbelPlanaLogHorizontalEdgeError N w T)) := by
  have hfaces :
      Tendsto
        (fun ε : ℝ =>
          Complex.finiteAbelPlanaLogLeftBoundaryFacePVNormalized N w T ε +
            Complex.finiteAbelPlanaLogRightBoundaryFacePVNormalized N w T ε)
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T)) :=
    Complex.finiteAbelPlana_log_boundaryFacesPV_tendsto_namedBoundary
      N hw T hT
  have hshift :
      Tendsto
        (fun ε : ℝ =>
          (Complex.finiteAbelPlanaLogLeftBoundaryFacePVNormalized N w T ε +
            Complex.finiteAbelPlanaLogRightBoundaryFacePVNormalized N w T ε) +
            Complex.finiteAbelPlanaLogHorizontalEdgeError N w T)
        (𝓝[>] (0 : ℝ))
        (𝓝
          (Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T +
            Complex.finiteAbelPlanaLogHorizontalEdgeError N w T)) :=
    hfaces.add tendsto_const_nhds
  have hpoint :
      (fun ε : ℝ =>
        Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ε) =
      (fun ε : ℝ =>
        (Complex.finiteAbelPlanaLogLeftBoundaryFacePVNormalized N w T ε +
          Complex.finiteAbelPlanaLogRightBoundaryFacePVNormalized N w T ε) +
          Complex.finiteAbelPlanaLogHorizontalEdgeError N w T) := by
    funext ε
    dsimp [Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized,
      Complex.finiteAbelPlanaLogLeftBoundaryFacePVNormalized,
      Complex.finiteAbelPlanaLogRightBoundaryFacePVNormalized]
    ring
  have htarget :
      Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T +
          Complex.finiteAbelPlanaLogHorizontalEdgeError N w T =
        Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T +
          Complex.finiteAbelPlanaLogHorizontalEdgeError N w T := by
    dsimp [Complex.finiteAbelPlanaLogNamedBoundaryFaceSum,
      Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression,
      Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression,
      Complex.finiteAbelPlanaLogFiniteHeightNamedVerticalSideExpression,
      Complex.finiteAbelPlanaLogEndpointPVIndentationContribution]
    ring
  exact hpoint ▸ htarget ▸ hshift

/-- The named finite-height side expression is the residue sum minus the
horizontal error, with the sign forced by
`rectangle = namedSide + horizontalError`. -/
theorem Complex.finiteAbelPlana_log_namedSideExpression_eq_residueSum_sub_horizontalError
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    ∀ T : ℝ,
      0 < T →
      Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T =
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w -
          Complex.finiteAbelPlanaLogHorizontalEdgeError N w T := by
  intro T hT
  have hrectangle :
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
          (Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T -
            (-Complex.finiteAbelPlanaLogHorizontalEdgeError N w T))) :=
    by
      have hraw :=
        Complex.finiteAbelPlana_log_rectangleSideExpressionPV_tendsto_namedSide_add_horizontalError
          N hw T hT
      simpa [sub_neg_eq_add] using hraw
  have hlimit :
      Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T -
          (-Complex.finiteAbelPlanaLogHorizontalEdgeError N w T) =
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w :=
    tendsto_nhds_unique hside hrectangle
  calc
    Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T =
        (Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T -
          (-Complex.finiteAbelPlanaLogHorizontalEdgeError N w T)) +
          (-Complex.finiteAbelPlanaLogHorizontalEdgeError N w T) := by
      exact (sub_add_cancel
        (Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T)
        (-Complex.finiteAbelPlanaLogHorizontalEdgeError N w T)).symm
    _ =
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w +
          (-Complex.finiteAbelPlanaLogHorizontalEdgeError N w T) := by
      exact congrArg
        (fun z : ℂ =>
          z + (-Complex.finiteAbelPlanaLogHorizontalEdgeError N w T))
        hlimit
    _ =
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w -
          Complex.finiteAbelPlanaLogHorizontalEdgeError N w T := by
      ring

/-- Finite-height residue accounting identifies the contour error with the
negative of the oriented horizontal-edge error. -/
theorem Complex.finiteAbelPlana_log_finiteHeightContourError_eq_neg_horizontalEdgeError_residueAccounting
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    ∀ T : ℝ,
      0 < T →
      Complex.finiteAbelPlanaLogFiniteHeightContourError N w T =
        -Complex.finiteAbelPlanaLogHorizontalEdgeError N w T := by
  intro T hT
  have hnamed :
      Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T =
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w -
          Complex.finiteAbelPlanaLogHorizontalEdgeError N w T :=
    Complex.finiteAbelPlana_log_namedSideExpression_eq_residueSum_sub_horizontalError
      hw N T hT
  have hboundary :
      Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T =
        Complex.finiteAbelPlanaLogBoundaryNamedPiecesUpTo N w T :=
    Complex.finiteAbelPlana_log_finiteHeightNamedSideExpression_eq_boundaryNamedPiecesUpTo
      N w T
  have herror :
      Complex.finiteAbelPlanaLogBoundaryNamedPiecesUpTo N w T =
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w +
          Complex.finiteAbelPlanaLogFiniteHeightContourError N w T :=
    Complex.finiteAbelPlana_log_boundaryNamedPiecesUpTo_eq_residueSum_add_error
      N w T
  have hsame_sum :
      Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w +
          Complex.finiteAbelPlanaLogFiniteHeightContourError N w T =
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w +
          (-Complex.finiteAbelPlanaLogHorizontalEdgeError N w T) := by
    calc
      Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w +
          Complex.finiteAbelPlanaLogFiniteHeightContourError N w T =
          Complex.finiteAbelPlanaLogBoundaryNamedPiecesUpTo N w T := by
        exact herror.symm
      _ = Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T := by
        exact hboundary.symm
      _ =
          Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w +
            (-Complex.finiteAbelPlanaLogHorizontalEdgeError N w T) := by
        exact hnamed
  exact add_left_cancel hsame_sum

end

end LFunctions
end Boundary
