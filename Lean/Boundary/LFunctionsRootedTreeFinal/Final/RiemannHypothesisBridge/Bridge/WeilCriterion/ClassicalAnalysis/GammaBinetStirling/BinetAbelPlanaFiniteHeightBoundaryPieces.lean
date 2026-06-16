import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaIntegerResidueLocal

/-!
# Finite-height Abel-Plana boundary pieces

This file owns the endpoint principal-value indentation contribution,
finite-radius deleted boundary contribution, named finite-height side
expression, and their unfolding lemmas.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Endpoint principal-value indentation contribution.  The endpoint integer
poles at `0` and `N + 1` contribute the usual half-sample term. -/
noncomputable def Complex.finiteAbelPlanaLogEndpointPVIndentationContribution
    (N : ℕ)
    (w : ℂ) : ℂ :=
  Complex.finiteAbelPlanaLogSummandHalfEndpoints N w

/-- Unfolding of the endpoint principal-value indentation contribution. -/
theorem Complex.finiteAbelPlana_log_endpointPVIndentationContribution_unfold
    (N : ℕ)
    (w : ℂ) :
    Complex.finiteAbelPlanaLogEndpointPVIndentationContribution N w =
      Complex.finiteAbelPlanaLogSummandHalfEndpoints N w := by
  rfl

/-- Small-circle residue contribution from the integer poles inside the
finite principal-value contour. -/
noncomputable def Complex.finiteAbelPlanaLogSmallCircleIntegerResidueContribution
    (N : ℕ)
    (w : ℂ) : ℂ :=
  ∑ n in Finset.range (N + 2),
    Complex.finiteAbelPlanaLogIntegerResidue w n

/-- Principal-value small-circle contribution: half endpoint circles plus full
interior circles. -/
noncomputable def Complex.finiteAbelPlanaLogPVSmallCircleIntegralContribution
    (N : ℕ)
    (w : ℂ)
    (ρ : ℝ) : ℂ :=
  (Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w 0 ρ +
    Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w (N + 1 : ℂ) ρ) / 2 +
      ∑ n in Finset.range N,
        Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w (n + 1 : ℂ) ρ

/-- Normalized semicircular indentation integral around the left endpoint pole
`0`.

The left vertical side is oriented upward, so the endpoint indentation follows
the right semicircle from `-iρ` to `+iρ`. -/
noncomputable def Complex.finiteAbelPlanaLogLeftEndpointIndentationIntegral
    (w : ℂ)
    (ρ : ℝ) : ℂ :=
  ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
    ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
      Complex.finiteAbelPlanaLogRectangleIntegrand w
          ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
        (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- Normalized semicircular indentation integral around the right endpoint pole
`N + 1`.

The right vertical side is oriented downward, so the endpoint indentation
follows the left semicircle from `+iρ` to `-iρ`. -/
noncomputable def Complex.finiteAbelPlanaLogRightEndpointIndentationIntegral
    (N : ℕ)
    (w : ℂ)
    (ρ : ℝ) : ℂ :=
  let M : ℕ := N + 1
  ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
    ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
      Complex.finiteAbelPlanaLogRectangleIntegrand w
          ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
        (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- Principal-value deleted-boundary contribution at finite radius: true
endpoint semicircle indentations plus full interior small circles. -/
noncomputable def Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution
    (N : ℕ)
    (w : ℂ)
    (ρ : ℝ) : ℂ :=
  Complex.finiteAbelPlanaLogLeftEndpointIndentationIntegral w ρ +
    Complex.finiteAbelPlanaLogRightEndpointIndentationIntegral N w ρ +
      ∑ n in Finset.range N,
        Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w (n + 1 : ℂ) ρ

/-- Unfolding of the small-circle residue contribution. -/
theorem Complex.finiteAbelPlana_log_smallCircleIntegerResidueContribution_unfold'
    (N : ℕ)
    (w : ℂ) :
    Complex.finiteAbelPlanaLogSmallCircleIntegerResidueContribution N w =
      ∑ n in Finset.range (N + 2),
        Complex.finiteAbelPlanaLogIntegerResidue w n := by
  rfl

/-- Unfolding of the interior integer-pole residue contribution. -/
theorem Complex.finiteAbelPlana_log_interiorIntegerResidueContribution_unfold
    (N : ℕ)
    (w : ℂ) :
    Complex.finiteAbelPlanaLogInteriorIntegerResidueContribution N w =
      ∑ n in Finset.range N,
        Complex.finiteAbelPlanaLogIntegerResidue w (n + 1) := by
  rfl

/-- Unfolding of the endpoint integer-pole residue contribution. -/
theorem Complex.finiteAbelPlana_log_endpointIntegerResidueContribution_unfold
    (N : ℕ)
    (w : ℂ) :
    Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w =
      (Complex.finiteAbelPlanaLogIntegerResidue w 0 +
        Complex.finiteAbelPlanaLogIntegerResidue w (N + 1)) / 2 := by
  rfl

/-- Unfolding of the principal-value small-circle contribution. -/
theorem Complex.finiteAbelPlana_log_pvSmallCircleIntegralContribution_unfold
    (N : ℕ)
    (w : ℂ)
    (ρ : ℝ) :
    Complex.finiteAbelPlanaLogPVSmallCircleIntegralContribution N w ρ =
      (Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w 0 ρ +
        Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w (N + 1 : ℂ) ρ) / 2 +
          ∑ n in Finset.range N,
            Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w (n + 1 : ℂ) ρ := by
  rfl

/-- Unfolding of the principal-value integer residue contribution. -/
theorem Complex.finiteAbelPlana_log_pvIntegerResidueContribution_unfold
    (N : ℕ)
    (w : ℂ) :
    Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w =
      Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w +
        Complex.finiteAbelPlanaLogInteriorIntegerResidueContribution N w := by
  rfl

/-- The finite-height named Abel-Plana side expression: real segment,
endpoint principal-value indentation, and named vertical sides. -/
noncomputable def Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) : ℂ :=
  let M : ℕ := N + 1
  (∫ x : ℝ in (0 : ℝ)..(M : ℝ),
    Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
    Complex.finiteAbelPlanaLogEndpointPVIndentationContribution N w +
      Complex.finiteAbelPlanaLogFiniteHeightNamedVerticalSideExpression N w T

/-- Unfolding of the finite-height named side expression. -/
theorem Complex.finiteAbelPlana_log_finiteHeightNamedSideExpression_unfold
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    let M : ℕ := N + 1
    Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T =
      (∫ x : ℝ in (0 : ℝ)..(M : ℝ),
        Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
        Complex.finiteAbelPlanaLogEndpointPVIndentationContribution N w +
          Complex.finiteAbelPlanaLogFiniteHeightNamedVerticalSideExpression N w T := by
  rfl

/-- Unfolding of the finite-height named side expression into the boundary
object consumed by the core Abel-Plana wrapper. -/
theorem Complex.finiteAbelPlana_log_finiteHeightNamedSideExpression_eq_boundaryNamedPiecesUpTo
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T =
      Complex.finiteAbelPlanaLogBoundaryNamedPiecesUpTo N w T := by
  rfl

/-- Unfolding of the small-circle residue contribution. -/
theorem Complex.finiteAbelPlana_log_smallCircleIntegerResidueContribution_unfold
    (N : ℕ)
    (w : ℂ) :
    Complex.finiteAbelPlanaLogSmallCircleIntegerResidueContribution N w =
      ∑ n in Finset.range (N + 2),
        Complex.finiteAbelPlanaLogIntegerResidue w n := by
  rfl

/-- Unfolding of the finite-height contour error. -/
theorem Complex.finiteAbelPlana_log_finiteHeightContourError_unfold

end

end LFunctions
end Boundary
