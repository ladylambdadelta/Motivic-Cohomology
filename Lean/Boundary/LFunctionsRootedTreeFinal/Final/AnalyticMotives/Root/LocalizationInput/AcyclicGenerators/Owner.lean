import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Motives.Summary.LocalizationInput.AcyclicGenerators.Owner

/-!
# Public concrete acyclic-generator facade

This file exposes the concrete additive acyclic generators attached to analytic
localization inputs at the public root surface.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public root facade: the acyclic generator attached to a localization input. -/
def AnalyticMotivesRoot.rootFacade_acyclicGenerator
    (input : TraceLocalizationInput) :
    TraceAnalyticAdditiveAcyclicGenerator :=
  AnalyticMotivesRoot.rootSummary_acyclicGenerator input

/-- Public root facade: the acyclic object attached to a localization input. -/
def AnalyticMotivesRoot.rootFacade_acyclicGenerator_object
    (input : TraceLocalizationInput) :
    TraceAnalyticAdditiveHomotopyCategory :=
  AnalyticMotivesRoot.rootSummary_acyclicGenerator_object input

/-- Public root facade: the acyclic object is the input cone third vertex. -/
theorem AnalyticMotivesRoot.rootFacade_acyclicGenerator_object_eq_triangleThirdVertex
    (input : TraceLocalizationInput) :
    AnalyticMotivesRoot.rootFacade_acyclicGenerator_object input =
      input.boundedMappingConeTriangle.triangleThirdVertex :=
  AnalyticMotivesRoot.rootSummary_acyclicGenerator_object_eq_triangleThirdVertex input

/-- Public root facade: the acyclic generator cone triangle. -/
def AnalyticMotivesRoot.rootFacade_acyclicGenerator_triangle
    (input : TraceLocalizationInput) :
    CategoryTheory.Triangle TraceAnalyticAdditiveHomotopyCategory :=
  AnalyticMotivesRoot.rootSummary_acyclicGenerator_triangle input

/-- Public root facade: the acyclic generator cone triangle is distinguished. -/
theorem AnalyticMotivesRoot.rootFacade_acyclicGenerator_triangle_distinguished
    (input : TraceLocalizationInput) :
    AnalyticMotivesRoot.rootFacade_acyclicGenerator_triangle input ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  AnalyticMotivesRoot.rootSummary_acyclicGenerator_triangle_distinguished input

/-- Public root facade: the rotated acyclic generator cone triangle. -/
def AnalyticMotivesRoot.rootFacade_acyclicGenerator_rotatedTriangle
    (input : TraceLocalizationInput) :
    CategoryTheory.Triangle TraceAnalyticAdditiveHomotopyCategory :=
  AnalyticMotivesRoot.rootSummary_acyclicGenerator_rotatedTriangle input

/-- Public root facade: the rotated acyclic generator cone triangle is distinguished. -/
theorem AnalyticMotivesRoot.rootFacade_acyclicGenerator_rotatedTriangle_distinguished
    (input : TraceLocalizationInput) :
    AnalyticMotivesRoot.rootFacade_acyclicGenerator_rotatedTriangle input ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  AnalyticMotivesRoot.rootSummary_acyclicGenerator_rotatedTriangle_distinguished input

/-- Public root facade: the inverse-rotated acyclic generator cone triangle. -/
def AnalyticMotivesRoot.rootFacade_acyclicGenerator_inverseRotatedTriangle
    (input : TraceLocalizationInput) :
    CategoryTheory.Triangle TraceAnalyticAdditiveHomotopyCategory :=
  AnalyticMotivesRoot.rootSummary_acyclicGenerator_inverseRotatedTriangle input

/-- Public root facade: the inverse-rotated acyclic generator cone triangle is distinguished. -/
theorem AnalyticMotivesRoot.rootFacade_acyclicGenerator_inverseRotatedTriangle_distinguished
    (input : TraceLocalizationInput) :
    AnalyticMotivesRoot.rootFacade_acyclicGenerator_inverseRotatedTriangle input ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  AnalyticMotivesRoot.rootSummary_acyclicGenerator_inverseRotatedTriangle_distinguished input

/-- Public root facade: the acyclic generator short complex. -/
def AnalyticMotivesRoot.rootFacade_acyclicGenerator_shortComplex
    (input : TraceLocalizationInput) :
    CategoryTheory.ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  AnalyticMotivesRoot.rootSummary_acyclicGenerator_shortComplex input

/-- Public root facade: the acyclic generator short complex has zero composite. -/
theorem AnalyticMotivesRoot.rootFacade_acyclicGenerator_shortComplex_zero
    (input : TraceLocalizationInput) :
    (AnalyticMotivesRoot.rootFacade_acyclicGenerator_shortComplex input).f ≫
        (AnalyticMotivesRoot.rootFacade_acyclicGenerator_shortComplex input).g =
      0 :=
  AnalyticMotivesRoot.rootSummary_acyclicGenerator_shortComplex_zero input

/-- Public root facade: the rotated acyclic generator short complex. -/
def AnalyticMotivesRoot.rootFacade_acyclicGenerator_rotatedShortComplex
    (input : TraceLocalizationInput) :
    CategoryTheory.ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  AnalyticMotivesRoot.rootSummary_acyclicGenerator_rotatedShortComplex input

/-- Public root facade: the rotated acyclic generator short complex has zero composite. -/
theorem AnalyticMotivesRoot.rootFacade_acyclicGenerator_rotatedShortComplex_zero
    (input : TraceLocalizationInput) :
    (AnalyticMotivesRoot.rootFacade_acyclicGenerator_rotatedShortComplex input).f ≫
        (AnalyticMotivesRoot.rootFacade_acyclicGenerator_rotatedShortComplex input).g =
      0 :=
  AnalyticMotivesRoot.rootSummary_acyclicGenerator_rotatedShortComplex_zero input

/-- Public root facade: the inverse-rotated acyclic generator short complex. -/
def AnalyticMotivesRoot.rootFacade_acyclicGenerator_inverseRotatedShortComplex
    (input : TraceLocalizationInput) :
    CategoryTheory.ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  AnalyticMotivesRoot.rootSummary_acyclicGenerator_inverseRotatedShortComplex input

/-- Public root facade: the inverse-rotated acyclic generator short complex has zero composite. -/
theorem AnalyticMotivesRoot.rootFacade_acyclicGenerator_inverseRotatedShortComplex_zero
    (input : TraceLocalizationInput) :
    (AnalyticMotivesRoot.rootFacade_acyclicGenerator_inverseRotatedShortComplex input).f ≫
        (AnalyticMotivesRoot.rootFacade_acyclicGenerator_inverseRotatedShortComplex input).g =
      0 :=
  AnalyticMotivesRoot.rootSummary_acyclicGenerator_inverseRotatedShortComplex_zero input

end AnalyticMotives
end LFunctions
end Boundary
