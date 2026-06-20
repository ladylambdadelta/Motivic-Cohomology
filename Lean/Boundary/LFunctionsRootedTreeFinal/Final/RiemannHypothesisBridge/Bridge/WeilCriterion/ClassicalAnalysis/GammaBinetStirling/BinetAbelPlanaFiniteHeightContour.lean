import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaHorizontalDecay

/-!
# Final finite-height Abel-Plana contour wrappers

This file contains only the final public finite-height Abel-Plana contour
wrappers.  Horizontal-edge decay and side reconstruction live upstream.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Finite-height principal-value cotangent contour theorem, after the
finite-height error has been identified with the vanishing horizontal edges. -/
theorem Complex.finiteAbelPlana_log_finiteHeightPrincipalValueContour_residueTheorem
    {w : ℂ}
    (hw : 0 < w.re)
    (hbridges : Complex.FiniteHeightPVBridgePackage w) :
    ∀ N : ℕ,
      Tendsto
        (fun T : ℝ =>
          Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T)
        atTop
        (𝓝 (Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w)) := by
  intro N
  have hside :
      (fun T : ℝ =>
          Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T) =
        (fun T : ℝ =>
          Complex.finiteAbelPlanaLogBoundaryNamedPiecesUpTo N w T) := by
    funext T
    exact
      Complex.finiteAbelPlana_log_finiteHeightNamedSideExpression_eq_boundaryNamedPiecesUpTo
      N w T
  have hdecomp :
      ∀ T : ℝ,
        Complex.finiteAbelPlanaLogBoundaryNamedPiecesUpTo N w T =
          Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w +
            Complex.finiteAbelPlanaLogFiniteHeightContourError N w T :=
    fun T =>
      Complex.finiteAbelPlana_log_boundaryNamedPiecesUpTo_eq_residueSum_add_error
        N w T
  have herror :
      Tendsto
        (fun T : ℝ =>
          Complex.finiteAbelPlanaLogFiniteHeightContourError N w T)
        atTop
        (𝓝 (0 : ℂ)) :=
    Complex.finiteAbelPlana_log_finiteHeightContourError_tendsto_zero_owner
      hw N (hbridges N)
  have hsum :
      Tendsto
        (fun T : ℝ =>
          Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w +
            Complex.finiteAbelPlanaLogFiniteHeightContourError N w T)
        atTop
        (𝓝 (Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w + 0)) :=
    tendsto_const_nhds.add herror
  have hboundary :
      Tendsto
        (fun T : ℝ =>
          Complex.finiteAbelPlanaLogBoundaryNamedPiecesUpTo N w T)
        atTop
        (𝓝 (Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w + 0)) := by
    have hfun :
        (fun T : ℝ =>
          Complex.finiteAbelPlanaLogBoundaryNamedPiecesUpTo N w T) =
        (fun T : ℝ =>
          Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w +
            Complex.finiteAbelPlanaLogFiniteHeightContourError N w T) := by
      funext T
      exact hdecomp T
    exact hfun.symm ▸ hsum
  have htarget :
      Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w + 0 =
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w := by
    exact add_zero _
  exact hside ▸ htarget ▸ hboundary

/-- The existing core finite-height formula is exactly the finite-height
principal-value contour theorem after unfolding the named side and residue
objects. -/
theorem Complex.finiteAbelPlana_log_finiteHeightPrincipalValueCotangentFormula_from_contour
    {w : ℂ}
    (hw : 0 < w.re)
    (hbridges : Complex.FiniteHeightPVBridgePackage w) :
    ∀ N : ℕ,
      Tendsto
        (fun T : ℝ =>
          Complex.finiteAbelPlanaLogBoundaryNamedPiecesUpTo N w T)
        atTop
        (𝓝 (Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w)) := by
  intro N
  have hcontour :
      Tendsto
        (fun T : ℝ =>
          Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T)
        atTop
        (𝓝 (Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w)) :=
    Complex.finiteAbelPlana_log_finiteHeightPrincipalValueContour_residueTheorem
      hw hbridges N
  have hside :
      (fun T : ℝ =>
          Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T) =
        (fun T : ℝ =>
          Complex.finiteAbelPlanaLogBoundaryNamedPiecesUpTo N w T) := by
    funext T
    exact
      Complex.finiteAbelPlana_log_finiteHeightNamedSideExpression_eq_boundaryNamedPiecesUpTo
      N w T
  exact hside ▸ hcontour

end

end LFunctions
end Boundary
