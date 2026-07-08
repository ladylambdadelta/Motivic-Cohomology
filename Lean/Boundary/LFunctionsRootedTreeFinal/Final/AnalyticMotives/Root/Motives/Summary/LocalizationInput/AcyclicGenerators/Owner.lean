import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Summary.LocalizationInput.AcyclicGenerators.Owner

/-!
# Top-root motive summary for concrete acyclic generators

This file forwards the concrete additive acyclic generators attached to analytic
localization inputs to the top-root motive summary namespace.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root motive summary: the acyclic generator attached to a localization input. -/
def AnalyticMotivesRoot.rootSummary_acyclicGenerator
    (input : TraceLocalizationInput) :
    TraceAnalyticAdditiveAcyclicGenerator :=
  TraceAnalyticMotive.rootSummary_acyclicGenerator input

/-- Top-root motive summary: the acyclic object attached to a localization input. -/
def AnalyticMotivesRoot.rootSummary_acyclicGenerator_object
    (input : TraceLocalizationInput) :
    TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticMotive.rootSummary_acyclicGenerator_object input

/-- Top-root motive summary: the acyclic object is the input cone third vertex. -/
theorem AnalyticMotivesRoot.rootSummary_acyclicGenerator_object_eq_triangleThirdVertex
    (input : TraceLocalizationInput) :
    AnalyticMotivesRoot.rootSummary_acyclicGenerator_object input =
      input.boundedMappingConeTriangle.triangleThirdVertex :=
  TraceAnalyticMotive.rootSummary_acyclicGenerator_object_eq_triangleThirdVertex input

/-- Top-root motive summary: the acyclic generator cone triangle. -/
def AnalyticMotivesRoot.rootSummary_acyclicGenerator_triangle
    (input : TraceLocalizationInput) :
    CategoryTheory.Triangle TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticMotive.rootSummary_acyclicGenerator_triangle input

/-- Top-root motive summary: the acyclic generator cone triangle is distinguished. -/
theorem AnalyticMotivesRoot.rootSummary_acyclicGenerator_triangle_distinguished
    (input : TraceLocalizationInput) :
    AnalyticMotivesRoot.rootSummary_acyclicGenerator_triangle input ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceAnalyticMotive.rootSummary_acyclicGenerator_triangle_distinguished input

/-- Top-root motive summary: the rotated acyclic generator cone triangle. -/
def AnalyticMotivesRoot.rootSummary_acyclicGenerator_rotatedTriangle
    (input : TraceLocalizationInput) :
    CategoryTheory.Triangle TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticMotive.rootSummary_acyclicGenerator_rotatedTriangle input

/-- Top-root motive summary: the rotated acyclic generator cone triangle is distinguished. -/
theorem AnalyticMotivesRoot.rootSummary_acyclicGenerator_rotatedTriangle_distinguished
    (input : TraceLocalizationInput) :
    AnalyticMotivesRoot.rootSummary_acyclicGenerator_rotatedTriangle input ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceAnalyticMotive.rootSummary_acyclicGenerator_rotatedTriangle_distinguished input

/-- Top-root motive summary: the inverse-rotated acyclic generator cone triangle. -/
def AnalyticMotivesRoot.rootSummary_acyclicGenerator_inverseRotatedTriangle
    (input : TraceLocalizationInput) :
    CategoryTheory.Triangle TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticMotive.rootSummary_acyclicGenerator_inverseRotatedTriangle input

/-- Top-root motive summary: the inverse-rotated acyclic generator cone triangle is distinguished. -/
theorem AnalyticMotivesRoot.rootSummary_acyclicGenerator_inverseRotatedTriangle_distinguished
    (input : TraceLocalizationInput) :
    AnalyticMotivesRoot.rootSummary_acyclicGenerator_inverseRotatedTriangle input ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceAnalyticMotive.rootSummary_acyclicGenerator_inverseRotatedTriangle_distinguished input

/-- Top-root motive summary: the acyclic generator short complex. -/
def AnalyticMotivesRoot.rootSummary_acyclicGenerator_shortComplex
    (input : TraceLocalizationInput) :
    CategoryTheory.ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticMotive.rootSummary_acyclicGenerator_shortComplex input

/-- Top-root motive summary: the acyclic generator short complex has zero composite. -/
theorem AnalyticMotivesRoot.rootSummary_acyclicGenerator_shortComplex_zero
    (input : TraceLocalizationInput) :
    (AnalyticMotivesRoot.rootSummary_acyclicGenerator_shortComplex input).f ≫
        (AnalyticMotivesRoot.rootSummary_acyclicGenerator_shortComplex input).g =
      0 :=
  TraceAnalyticMotive.rootSummary_acyclicGenerator_shortComplex_zero input

/-- Top-root motive summary: the rotated acyclic generator short complex. -/
def AnalyticMotivesRoot.rootSummary_acyclicGenerator_rotatedShortComplex
    (input : TraceLocalizationInput) :
    CategoryTheory.ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticMotive.rootSummary_acyclicGenerator_rotatedShortComplex input

/-- Top-root motive summary: the rotated acyclic generator short complex has zero composite. -/
theorem AnalyticMotivesRoot.rootSummary_acyclicGenerator_rotatedShortComplex_zero
    (input : TraceLocalizationInput) :
    (AnalyticMotivesRoot.rootSummary_acyclicGenerator_rotatedShortComplex input).f ≫
        (AnalyticMotivesRoot.rootSummary_acyclicGenerator_rotatedShortComplex input).g =
      0 :=
  TraceAnalyticMotive.rootSummary_acyclicGenerator_rotatedShortComplex_zero input

/-- Top-root motive summary: the inverse-rotated acyclic generator short complex. -/
def AnalyticMotivesRoot.rootSummary_acyclicGenerator_inverseRotatedShortComplex
    (input : TraceLocalizationInput) :
    CategoryTheory.ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticMotive.rootSummary_acyclicGenerator_inverseRotatedShortComplex input

/-- Top-root motive summary: the inverse-rotated acyclic generator short complex has zero composite. -/
theorem AnalyticMotivesRoot.rootSummary_acyclicGenerator_inverseRotatedShortComplex_zero
    (input : TraceLocalizationInput) :
    (AnalyticMotivesRoot.rootSummary_acyclicGenerator_inverseRotatedShortComplex input).f ≫
        (AnalyticMotivesRoot.rootSummary_acyclicGenerator_inverseRotatedShortComplex input).g =
      0 :=
  TraceAnalyticMotive.rootSummary_acyclicGenerator_inverseRotatedShortComplex_zero input

end AnalyticMotives
end LFunctions
end Boundary
