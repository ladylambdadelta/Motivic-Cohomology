import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaCore
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaHorizontalBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaVerticalLimits

/-!
# Finite-height Abel-Plana side vocabulary

This file owns the literal side expressions for the finite-height Abel-Plana
rectangle and their principal-value variants.  The punctured-rectangle
topology, residue accounting, and limiting theorems live downstream in
`BinetAbelPlanaFiniteHeightContour`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Left vertical side of the finite-height rectangle for the Abel-Plana
cotangent contour.

Mathlib's rectangle Cauchy API uses side-parametrized integrals.  This is the
literal left-side parametrization `z = I * y`, with `y` running from `-T` to
`T`. -/
noncomputable def Complex.finiteAbelPlanaLogFiniteHeightLeftSide
    (w : ℂ)
    (T : ℝ) : ℂ :=
  ∫ y : ℝ in (-T)..T,
    Complex.finiteAbelPlanaLogRectangleIntegrand w
      (Complex.I * (y : ℂ))

/-- Unfolding of the finite-height left vertical side. -/
theorem Complex.finiteAbelPlana_log_finiteHeightLeftSide_unfold
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogFiniteHeightLeftSide w T =
      ∫ y : ℝ in (-T)..T,
        Complex.finiteAbelPlanaLogRectangleIntegrand w
          (Complex.I * (y : ℂ)) := by
  rfl

/-- Right vertical side of the finite-height rectangle for the Abel-Plana
cotangent contour, at endpoint `M = N + 1`. -/
noncomputable def Complex.finiteAbelPlanaLogFiniteHeightRightSide
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) : ℂ :=
  let M : ℕ := N + 1
  ∫ y : ℝ in (-T)..T,
    Complex.finiteAbelPlanaLogRectangleIntegrand w
      ((M : ℂ) + Complex.I * (y : ℂ))

/-- Unfolding of the finite-height right vertical side. -/
theorem Complex.finiteAbelPlana_log_finiteHeightRightSide_unfold
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    let M : ℕ := N + 1
    Complex.finiteAbelPlanaLogFiniteHeightRightSide N w T =
      ∫ y : ℝ in (-T)..T,
        Complex.finiteAbelPlanaLogRectangleIntegrand w
          ((M : ℂ) + Complex.I * (y : ℂ)) := by
  rfl

/-- Lower horizontal side of the finite-height rectangle. -/
noncomputable def Complex.finiteAbelPlanaLogFiniteHeightLowerSide
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) : ℂ :=
  let M : ℕ := N + 1
  ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
    Complex.finiteAbelPlanaLogRectangleIntegrand w
      ((x : ℂ) - Complex.I * (T : ℂ))

/-- Unfolding of the finite-height lower horizontal side. -/
theorem Complex.finiteAbelPlana_log_finiteHeightLowerSide_unfold
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    let M : ℕ := N + 1
    Complex.finiteAbelPlanaLogFiniteHeightLowerSide N w T =
      ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
        Complex.finiteAbelPlanaLogRectangleIntegrand w
          ((x : ℂ) - Complex.I * (T : ℂ)) := by
  rfl

/-- Upper horizontal side of the finite-height rectangle. -/
noncomputable def Complex.finiteAbelPlanaLogFiniteHeightUpperSide
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) : ℂ :=
  let M : ℕ := N + 1
  ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
    Complex.finiteAbelPlanaLogRectangleIntegrand w
      ((x : ℂ) + Complex.I * (T : ℂ))

/-- Unfolding of the finite-height upper horizontal side. -/
theorem Complex.finiteAbelPlana_log_finiteHeightUpperSide_unfold
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    let M : ℕ := N + 1
    Complex.finiteAbelPlanaLogFiniteHeightUpperSide N w T =
      ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
        Complex.finiteAbelPlanaLogRectangleIntegrand w
          ((x : ℂ) + Complex.I * (T : ℂ)) := by
  rfl

/-- Oriented finite-height rectangle boundary expression in the side convention
of `Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`:
bottom minus top plus `I` times right minus `I` times left. -/
noncomputable def Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpression
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) : ℂ :=
  Complex.finiteAbelPlanaLogFiniteHeightLowerSide N w T -
    Complex.finiteAbelPlanaLogFiniteHeightUpperSide N w T +
      Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSide N w T -
        Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSide w T

/-- Unfolding of the finite-height rectangle side expression. -/
theorem Complex.finiteAbelPlana_log_finiteHeightRectangleSideExpression_unfold
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpression N w T =
      Complex.finiteAbelPlanaLogFiniteHeightLowerSide N w T -
        Complex.finiteAbelPlanaLogFiniteHeightUpperSide N w T +
          Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSide N w T -
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSide w T := by
  rfl

/-- The horizontal side contribution of the finite-height rectangle.  This is
kept separate because the Abel-Plana limit theorem later kills it by the
standard cotangent exponential decay on horizontal edges. -/
noncomputable def Complex.finiteAbelPlanaLogFiniteHeightHorizontalSideExpression
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) : ℂ :=
  Complex.finiteAbelPlanaLogFiniteHeightLowerSide N w T -
    Complex.finiteAbelPlanaLogFiniteHeightUpperSide N w T

/-- Unfolding of the finite-height horizontal side expression. -/
theorem Complex.finiteAbelPlana_log_finiteHeightHorizontalSideExpression_unfold
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogFiniteHeightHorizontalSideExpression N w T =
      Complex.finiteAbelPlanaLogFiniteHeightLowerSide N w T -
        Complex.finiteAbelPlanaLogFiniteHeightUpperSide N w T := by
  rfl

/-- The raw vertical side contribution before rewriting the cotangent kernel
into Abel-Plana exponential boundary terms. -/
noncomputable def Complex.finiteAbelPlanaLogFiniteHeightRawVerticalSideExpression
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) : ℂ :=
  Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSide N w T -
    Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSide w T

/-- The finite-height Abel-Plana vertical expression after the cotangent
upper/lower half-plane rewrite. -/
noncomputable def Complex.finiteAbelPlanaLogFiniteHeightNamedVerticalSideExpression
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) : ℂ :=
  -Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
    Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T

/-- Unfolding of the finite-height named vertical side expression. -/
theorem Complex.finiteAbelPlana_log_finiteHeightNamedVerticalSideExpression_unfold
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogFiniteHeightNamedVerticalSideExpression N w T =
      -Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
        Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T := by
  rfl

/-- Unfolding of the finite-height raw vertical side expression. -/
theorem Complex.finiteAbelPlana_log_finiteHeightRawVerticalSideExpression_unfold
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogFiniteHeightRawVerticalSideExpression N w T =
      Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSide N w T -
        Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSide w T := by
  rfl

/-- Principal-value left vertical side with a symmetric indentation of radius
`ε` around the cotangent pole at the endpoint `0`. -/
noncomputable def Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV
    (w : ℂ)
    (T ε : ℝ) : ℂ :=
  (∫ y : ℝ in (-T)..(-ε),
    Complex.finiteAbelPlanaLogRectangleIntegrand w
      (Complex.I * (y : ℂ))) +
  ∫ y : ℝ in ε..T,
    Complex.finiteAbelPlanaLogRectangleIntegrand w
      (Complex.I * (y : ℂ))

/-- Principal-value right vertical side with a symmetric indentation of radius
`ε` around the endpoint cotangent pole `N + 1`. -/
noncomputable def Complex.finiteAbelPlanaLogFiniteHeightRightSidePV
    (N : ℕ)
    (w : ℂ)
    (T ε : ℝ) : ℂ :=
  let M : ℕ := N + 1
  (∫ y : ℝ in (-T)..(-ε),
    Complex.finiteAbelPlanaLogRectangleIntegrand w
      ((M : ℂ) + Complex.I * (y : ℂ))) +
  ∫ y : ℝ in ε..T,
    Complex.finiteAbelPlanaLogRectangleIntegrand w
      ((M : ℂ) + Complex.I * (y : ℂ))

/-- Unfolding of the principal-value left vertical side. -/
theorem Complex.finiteAbelPlana_log_finiteHeightLeftSidePV_unfold
    (w : ℂ)
    (T ε : ℝ) :
    Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ε =
      (∫ y : ℝ in (-T)..(-ε),
        Complex.finiteAbelPlanaLogRectangleIntegrand w
          (Complex.I * (y : ℂ))) +
      ∫ y : ℝ in ε..T,
        Complex.finiteAbelPlanaLogRectangleIntegrand w
          (Complex.I * (y : ℂ)) := by
  rfl

/-- Unfolding of the principal-value right vertical side. -/
theorem Complex.finiteAbelPlana_log_finiteHeightRightSidePV_unfold
    (N : ℕ)
    (w : ℂ)
    (T ε : ℝ) :
    let M : ℕ := N + 1
    Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ε =
      (∫ y : ℝ in (-T)..(-ε),
        Complex.finiteAbelPlanaLogRectangleIntegrand w
          ((M : ℂ) + Complex.I * (y : ℂ))) +
      ∫ y : ℝ in ε..T,
        Complex.finiteAbelPlanaLogRectangleIntegrand w
          ((M : ℂ) + Complex.I * (y : ℂ)) := by
  rfl

/-- Principal-value raw vertical side contribution with radius `ε` around the
endpoint cotangent poles.  This is the honest vertical side object for the
finite Abel-Plana contour; the unindented raw vertical side is only a
post-normalization presentation. -/
noncomputable def Complex.finiteAbelPlanaLogFiniteHeightRawVerticalSideExpressionPV
    (N : ℕ)
    (w : ℂ)
    (T ε : ℝ) : ℂ :=
  Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ε -
    Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ε

/-- Principal-value finite-height rectangle side expression with radius `ε`
around the endpoint cotangent poles. -/
noncomputable def Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPV
    (N : ℕ)
    (w : ℂ)
    (T ε : ℝ) : ℂ :=
  Complex.finiteAbelPlanaLogFiniteHeightHorizontalSideExpression N w T +
    Complex.finiteAbelPlanaLogFiniteHeightRawVerticalSideExpressionPV N w T ε

/-- Residue-normalized principal-value finite-height rectangle side
expression.

This is the object that belongs in the finite residue theorem: it is the raw
oriented rectangle boundary multiplied by `(2πi)⁻¹`, matching the normalization
of the small-circle residue terms. -/
noncomputable def Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized
    (N : ℕ)
    (w : ℂ)
    (T ε : ℝ) : ℂ :=
  ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
    Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPV N w T ε

/-- Unfolding of the principal-value raw vertical side expression. -/
theorem Complex.finiteAbelPlana_log_finiteHeightRawVerticalSideExpressionPV_unfold
    (N : ℕ)
    (w : ℂ)
    (T ε : ℝ) :
    Complex.finiteAbelPlanaLogFiniteHeightRawVerticalSideExpressionPV N w T ε =
      Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ε -
        Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ε := by
  rfl

/-- Unfolding of the principal-value finite-height rectangle side expression. -/
theorem Complex.finiteAbelPlana_log_finiteHeightRectangleSideExpressionPV_unfold
    (N : ℕ)
    (w : ℂ)
    (T ε : ℝ) :
    Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPV N w T ε =
      Complex.finiteAbelPlanaLogFiniteHeightHorizontalSideExpression N w T +
        Complex.finiteAbelPlanaLogFiniteHeightRawVerticalSideExpressionPV N w T ε := by
  rfl

/-- Unfolding of the normalized principal-value finite-height rectangle side
expression. -/
theorem Complex.finiteAbelPlana_log_finiteHeightRectangleSideExpressionPVNormalized_unfold
    (N : ℕ)
    (w : ℂ)
    (T ε : ℝ) :
    Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ε =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPV N w T ε := by
  rfl

end

end LFunctions
end Boundary
