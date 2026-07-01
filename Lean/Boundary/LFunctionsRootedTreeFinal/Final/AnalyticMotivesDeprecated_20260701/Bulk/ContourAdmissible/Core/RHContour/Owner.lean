import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaAnalyticPackage.Owner

/-!
# RH-backed contour bulk core

This file is the constructive analytic bulk core for the first contour-theoretic
analytic motive lane.  It does not introduce a separate abstract carrier:
the carrier is the completed-zeta explicit-formula contour package already
constructed in the `Final` RH analytic lane.

The dependency direction is one-way: analytic motives import this RH analytic
owner; the RH lane does not import analytic motives.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace AnalyticMotives

/-- The RH-owner contour family used as the first analytic bulk carrier. -/
abbrev RHContourFamily :=
  ZetaAdmissibleFunction.ExplicitFormulaContourFamily

/-- The RH-owner rectangle at a contour height. -/
abbrev RHContourRectangle :=
  ZetaAdmissibleFunction.ExplicitFormulaRectangle

/-- The RH-owner analytic package for a packet and contour family. -/
abbrev RHContourAnalyticPackage
    (f : ZetaAdmissibleFunction) (F : RHContourFamily) :=
  ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage f F

/-- The RH-owner vertically regular contour-family package. -/
abbrev RHVerticallyRegularContourFamily :=
  ZetaAdmissibleFunction.ExplicitFormulaVerticallyRegularContourFamily

/--
Constructive contour bulk core backed directly by the completed-zeta
explicit-formula contour package.
-/
structure RHContourBulkCore where
  packet : ZetaAdmissibleFunction
  contourFamily : RHContourFamily
  analyticPackage : RHContourAnalyticPackage packet contourFamily

namespace RHContourBulkCore

/-- The rectangle selected by an RH-backed contour bulk at height `T`. -/
def rectangle (X : RHContourBulkCore) (T : ℝ) :
    RHContourRectangle :=
  X.contourFamily.rectangle T

/-- The contour boundary selected by an RH-backed contour bulk at height `T`. -/
def boundary (X : RHContourBulkCore) (T : ℝ) : Set ℂ :=
  ZetaAdmissibleFunction.explicitFormulaContourFamilyBoundary
    X.contourFamily T

/-- The contour interior selected by an RH-backed contour bulk at height `T`. -/
def interior (X : RHContourBulkCore) (T : ℝ) : Set ℂ :=
  ZetaAdmissibleFunction.explicitFormulaContourFamilyInterior
    X.contourFamily T

/-- The completed-zeta singular predicate used by the RH contour package. -/
def singularPoint (_X : RHContourBulkCore) (z : ℂ) : Prop :=
  ZetaAdmissibleFunction.explicitFormulaContourSingularPoint z

/-- Points of the selected RH rectangle at height `T`. -/
def rectangleSet (X : RHContourBulkCore) (T : ℝ) : Set ℂ :=
  {z : ℂ | z ∈ X.boundary T ∨ z ∈ X.interior T}

/-- Singular points contained in the selected RH rectangle at height `T`. -/
def rectangleSingularSupport (X : RHContourBulkCore) (T : ℝ) : Set ℂ :=
  {z : ℂ | X.singularPoint z ∧ z ∈ X.rectangleSet T}

/-- The right vertical path of the selected RH rectangle. -/
def rightPath (X : RHContourBulkCore) (T t : ℝ) : ℂ :=
  ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightPath
    (X.rectangle T) t

/-- The left vertical path of the selected RH rectangle. -/
def leftPath (X : RHContourBulkCore) (T t : ℝ) : ℂ :=
  ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftPath
    (X.rectangle T) t

/-- The top horizontal path of the selected RH rectangle. -/
def topPath (X : RHContourBulkCore) (T x : ℝ) : ℂ :=
  ZetaAdmissibleFunction.zetaCompletedExplicitFormulaTopPath
    (X.rectangle T) x

/-- The bottom horizontal path of the selected RH rectangle. -/
def bottomPath (X : RHContourBulkCore) (T x : ℝ) : ℂ :=
  ZetaAdmissibleFunction.zetaCompletedExplicitFormulaBottomPath
    (X.rectangle T) x

/-- The real edge parameter of the selected RH contour family. -/
def realEdge (X : RHContourBulkCore) : ℝ :=
  X.contourFamily.c

/-- The center-line real coordinate of the completed-zeta rectangle. -/
def centerLine (_X : RHContourBulkCore) : ℝ :=
  (1 : ℝ) / 2

/-- The right edge remembers the contour family's real edge. -/
theorem rectangle_c (X : RHContourBulkCore) (T : ℝ) :
    (X.rectangle T).c = X.realEdge :=
  ZetaAdmissibleFunction.ExplicitFormulaContourFamily.rectangle_c
    X.contourFamily T

/-- The rectangle remembers its height parameter. -/
theorem rectangle_T (X : RHContourBulkCore) (T : ℝ) :
    (X.rectangle T).T = T :=
  ZetaAdmissibleFunction.ExplicitFormulaContourFamily.rectangle_T
    X.contourFamily T

/-- The right vertical path has real part equal to the contour family's real edge. -/
theorem rightPath_re (X : RHContourBulkCore) (t : ℝ) :
    (X.rightPath t t).re = X.realEdge :=
  ZetaAdmissibleFunction.ExplicitFormulaContourFamily.rightPath_re
    X.contourFamily t

/-- A singular support point is singular by definition. -/
theorem rectangleSingularSupport_singular
    (X : RHContourBulkCore) (T : ℝ) (z : ℂ)
    (hz : z ∈ X.rectangleSingularSupport T) :
    X.singularPoint z :=
  hz.1

/-- A singular support point lies on the selected rectangle by definition. -/
theorem rectangleSingularSupport_mem_rectangleSet
    (X : RHContourBulkCore) (T : ℝ) (z : ℂ)
    (hz : z ∈ X.rectangleSingularSupport T) :
    z ∈ X.rectangleSet T :=
  hz.2

end RHContourBulkCore

end AnalyticMotives

end
end LFunctions
end Boundary
