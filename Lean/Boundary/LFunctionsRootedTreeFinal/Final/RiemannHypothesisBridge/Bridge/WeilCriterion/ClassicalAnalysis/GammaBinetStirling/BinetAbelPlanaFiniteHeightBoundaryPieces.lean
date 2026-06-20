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
    Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral
      w ((N + 1 : ℕ) : ℂ) ρ) / 2 +
      ∑ n in Finset.range N,
        Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral
          w ((n + 1 : ℕ) : ℂ) ρ

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
        Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral
          w ((n + 1 : ℕ) : ℂ) ρ

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
        Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral
          w ((N + 1 : ℕ) : ℂ) ρ) / 2 +
          ∑ n in Finset.range N,
            Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral
              w ((n + 1 : ℕ) : ℂ) ρ := by
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

/-- Normal form for adjoining a grouped pair of negative vertical terms to a
finite-height boundary sum. -/
theorem Complex.add_add_neg_sub_eq_add_sub_sub
    (a b c d : ℂ) :
    a + b + (-c - d) = a + b - c - d := by
  calc
    a + b + (-c - d) = a + b + (-c + -d) := by
      rfl
    _ = a + b + -c + -d :=
      (add_assoc (a + b) (-c) (-d)).symm
    _ = a + b - c - d := by
      rfl

/-- Unfolding of the finite-height named side expression into the boundary
object consumed by the core Abel-Plana wrapper. -/
theorem Complex.finiteAbelPlana_log_finiteHeightNamedSideExpression_eq_boundaryNamedPiecesUpTo
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T =
      Complex.finiteAbelPlanaLogBoundaryNamedPiecesUpTo N w T := by
  let M : ℕ := N + 1
  let R : ℂ :=
    ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
      Complex.finiteAbelPlanaLogSummand w (x : ℂ)
  let E : ℂ :=
    Complex.finiteAbelPlanaLogEndpointPVIndentationContribution N w
  let H : ℂ :=
    Complex.finiteAbelPlanaLogSummandHalfEndpoints N w
  let L : ℂ :=
    Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T
  let U : ℂ :=
    Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T
  let V : ℂ :=
    Complex.finiteAbelPlanaLogFiniteHeightNamedVerticalSideExpression N w T
  have hnamed :
      Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T =
        R + E + V :=
    Complex.finiteAbelPlana_log_finiteHeightNamedSideExpression_unfold N w T
  have hendpoint : E = H :=
    Complex.finiteAbelPlana_log_endpointPVIndentationContribution_unfold N w
  have hvertical : V = -L - U :=
    Complex.finiteAbelPlana_log_finiteHeightNamedVerticalSideExpression_unfold
      N w T
  have hboundary :
      Complex.finiteAbelPlanaLogBoundaryNamedPiecesUpTo N w T =
        R + H - L - U :=
    Complex.finiteAbelPlana_log_boundaryNamedPiecesUpTo_unfold N w T
  calc
    Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T =
        R + E + V :=
      hnamed
    _ = R + H + V := by
      exact congrArg
        (fun z : ℂ => R + z + V)
        hendpoint
    _ = R + H + (-L - U) := by
      exact congrArg
        (fun z : ℂ => R + H + z)
        hvertical
    _ = R + H - L - U :=
      Complex.add_add_neg_sub_eq_add_sub_sub R H L U
    _ = Complex.finiteAbelPlanaLogBoundaryNamedPiecesUpTo N w T :=
      hboundary.symm

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
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogFiniteHeightContourError N w T =
      Complex.finiteAbelPlanaLogBoundaryNamedPiecesUpTo N w T -
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w := by
  exact Complex.finiteAbelPlana_log_finiteHeightContourError_unfold' N w T

end

end LFunctions
end Boundary
