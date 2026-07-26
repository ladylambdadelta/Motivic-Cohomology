import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaContour.ZetaExplicitFormulaRectangleAPI.Owner
import Mathlib.Analysis.Complex.Basic

/-!
# Boundary explicit-formula contour paths

This file owns the bare path parametrizations for the explicit-formula
rectangle. It is intentionally minimal so both the contour file and the
analytic-control file can consume the same path API without a cycle.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The right vertical side parametrization of the rectangle. -/
def zetaCompletedExplicitFormulaRightPath
    (r : ExplicitFormulaRectangle) : ℝ → ℂ :=
  fun t => r.c + t * Complex.I

/-- The left vertical side parametrization of the rectangle. -/
def zetaCompletedExplicitFormulaLeftPath
    (r : ExplicitFormulaRectangle) : ℝ → ℂ :=
  fun t => (1 - r.c) + t * Complex.I

/-- The top horizontal side parametrization of the rectangle. -/
def zetaCompletedExplicitFormulaTopPath
    (r : ExplicitFormulaRectangle) : ℝ → ℂ :=
  fun x => x + r.T * Complex.I

/-- The bottom horizontal side parametrization of the rectangle. -/
def zetaCompletedExplicitFormulaBottomPath
    (r : ExplicitFormulaRectangle) : ℝ → ℂ :=
  fun x => x - r.T * Complex.I

theorem zetaCompletedExplicitFormulaTopPath_continuous
    (r : ExplicitFormulaRectangle) :
    Continuous (zetaCompletedExplicitFormulaTopPath r) := by
  change Continuous (fun x : ℝ => (x : ℂ) + (r.T : ℂ) * Complex.I)
  exact Complex.continuous_ofReal.add continuous_const

theorem zetaCompletedExplicitFormulaBottomPath_continuous
    (r : ExplicitFormulaRectangle) :
    Continuous (zetaCompletedExplicitFormulaBottomPath r) := by
  change Continuous (fun x : ℝ => (x : ℂ) - (r.T : ℂ) * Complex.I)
  exact Complex.continuous_ofReal.sub continuous_const

/-- The top path is the affine point used by the regular-strip estimates. -/
theorem zetaCompletedExplicitFormulaTopPath_eq_affinePoint
    (r : ExplicitFormulaRectangle) (x : ℝ) :
    zetaCompletedExplicitFormulaTopPath r x =
      (x : ℂ) + (r.T : ℂ) * Complex.I :=
  rfl

/-- The bottom path is the affine point with the reflected imaginary height. -/
theorem zetaCompletedExplicitFormulaBottomPath_eq_affinePoint
    (r : ExplicitFormulaRectangle) (x : ℝ) :
    zetaCompletedExplicitFormulaBottomPath r x =
      (x : ℂ) + ((-r.T : ℝ) : ℂ) * Complex.I := by
  calc
    zetaCompletedExplicitFormulaBottomPath r x =
        (x : ℂ) - (r.T : ℂ) * Complex.I := by
      rfl
    _ = (x : ℂ) + -((r.T : ℂ) * Complex.I) := by
      exact sub_eq_add_neg (x : ℂ) ((r.T : ℂ) * Complex.I)
    _ = (x : ℂ) + ((-r.T : ℝ) : ℂ) * Complex.I := by
      have hneg : ((-r.T : ℝ) : ℂ) = -(r.T : ℂ) :=
        Complex.ofReal_neg r.T
      exact Eq.trans
        (congrArg (fun z : ℂ => (x : ℂ) + z)
          (neg_mul (r.T : ℂ) Complex.I))
        (congrArg (fun z : ℂ => (x : ℂ) + z * Complex.I)
          hneg.symm)

/-- Centering the real coordinate at one half exposes the shifted-strip
coordinates used by the completed inverse-Gamma estimates. -/
theorem zetaCompletedExplicitFormulaTopPath_eq_centeredAffinePoint
    (r : ExplicitFormulaRectangle) (x : ℝ) :
    zetaCompletedExplicitFormulaTopPath r x =
      (1 / 2 : ℂ) + ((x - (1 / 2 : ℝ) : ℝ) : ℂ) +
        (r.T : ℂ) * Complex.I := by
  have hreal : (1 / 2 : ℝ) + (x - (1 / 2 : ℝ)) = x := by
    exact Eq.trans
      (add_comm (1 / 2 : ℝ) (x - (1 / 2 : ℝ)))
      (sub_add_cancel x (1 / 2 : ℝ))
  have hcomplex : (x : ℂ) =
      (1 / 2 : ℂ) + ((x - (1 / 2 : ℝ) : ℝ) : ℂ) := by
    exact Eq.trans
      (congrArg (fun y : ℝ => (y : ℂ)) hreal.symm)
      (Complex.ofReal_add (1 / 2 : ℝ) (x - (1 / 2 : ℝ))).symm
  exact Eq.trans
    (zetaCompletedExplicitFormulaTopPath_eq_affinePoint r x)
    (congrArg (fun z : ℂ => z + (r.T : ℂ) * Complex.I) hcomplex)

/-- The lower horizontal path has the same centered real coordinate and the
reflected imaginary height. -/
theorem zetaCompletedExplicitFormulaBottomPath_eq_centeredAffinePoint
    (r : ExplicitFormulaRectangle) (x : ℝ) :
    zetaCompletedExplicitFormulaBottomPath r x =
      (1 / 2 : ℂ) + ((x - (1 / 2 : ℝ) : ℝ) : ℂ) +
        ((-r.T : ℝ) : ℂ) * Complex.I := by
  have hreal : (1 / 2 : ℝ) + (x - (1 / 2 : ℝ)) = x := by
    exact Eq.trans
      (add_comm (1 / 2 : ℝ) (x - (1 / 2 : ℝ)))
      (sub_add_cancel x (1 / 2 : ℝ))
  have hcomplex : (x : ℂ) =
      (1 / 2 : ℂ) + ((x - (1 / 2 : ℝ) : ℝ) : ℂ) := by
    exact Eq.trans
      (congrArg (fun y : ℝ => (y : ℂ)) hreal.symm)
      (Complex.ofReal_add (1 / 2 : ℝ) (x - (1 / 2 : ℝ))).symm
  exact Eq.trans
    (zetaCompletedExplicitFormulaBottomPath_eq_affinePoint r x)
    (congrArg (fun z : ℂ => z + ((-r.T : ℝ) : ℂ) * Complex.I) hcomplex)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
