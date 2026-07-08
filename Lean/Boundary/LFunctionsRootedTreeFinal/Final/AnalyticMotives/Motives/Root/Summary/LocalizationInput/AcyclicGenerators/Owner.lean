import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.LocalizationInput.AcyclicGenerators.Owner

/-!
# Motive-root summary for concrete acyclic generators

This file exposes the concrete additive acyclic generators attached to analytic
localization inputs through the motive-root summary namespace.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root summary: the acyclic generator attached to a localization input. -/
def TraceAnalyticMotive.rootSummary_acyclicGenerator
    (input : TraceLocalizationInput) :
    TraceAnalyticAdditiveAcyclicGenerator where
  input := input

/-- Motive-root summary: an acyclic generator remembers its localization input. -/
theorem TraceAnalyticMotive.rootSummary_acyclicGenerator_input
    (input : TraceLocalizationInput) :
    (TraceAnalyticMotive.rootSummary_acyclicGenerator input).input =
      input :=
  rfl

/-- Motive-root summary: the acyclic object attached to a localization input. -/
def TraceAnalyticMotive.rootSummary_acyclicGenerator_object
    (input : TraceLocalizationInput) :
    TraceAnalyticAdditiveHomotopyCategory :=
  (TraceAnalyticMotive.rootSummary_acyclicGenerator input).object

/-- Motive-root summary: the acyclic object is the input cone third vertex. -/
theorem TraceAnalyticMotive.rootSummary_acyclicGenerator_object_eq_triangleThirdVertex
    (input : TraceLocalizationInput) :
    TraceAnalyticMotive.rootSummary_acyclicGenerator_object input =
      input.boundedMappingConeTriangle.triangleThirdVertex :=
  rfl

/-- Motive-root summary: the acyclic generator cone triangle. -/
def TraceAnalyticMotive.rootSummary_acyclicGenerator_triangle
    (input : TraceLocalizationInput) :
    CategoryTheory.Triangle TraceAnalyticAdditiveHomotopyCategory :=
  (TraceAnalyticMotive.rootSummary_acyclicGenerator input).triangle

/-- Motive-root summary: the acyclic generator cone triangle is distinguished. -/
theorem TraceAnalyticMotive.rootSummary_acyclicGenerator_triangle_distinguished
    (input : TraceLocalizationInput) :
    TraceAnalyticMotive.rootSummary_acyclicGenerator_triangle input ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceAnalyticAdditiveAcyclicGenerator.triangle_distinguished
    (TraceAnalyticMotive.rootSummary_acyclicGenerator input)

/-- Motive-root summary: the rotated acyclic generator cone triangle. -/
def TraceAnalyticMotive.rootSummary_acyclicGenerator_rotatedTriangle
    (input : TraceLocalizationInput) :
    CategoryTheory.Triangle TraceAnalyticAdditiveHomotopyCategory :=
  (TraceAnalyticMotive.rootSummary_acyclicGenerator input).rotatedTriangle

/-- Motive-root summary: the rotated acyclic generator cone triangle is distinguished. -/
theorem TraceAnalyticMotive.rootSummary_acyclicGenerator_rotatedTriangle_distinguished
    (input : TraceLocalizationInput) :
    TraceAnalyticMotive.rootSummary_acyclicGenerator_rotatedTriangle input ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceAnalyticAdditiveAcyclicGenerator.rotatedTriangle_distinguished
    (TraceAnalyticMotive.rootSummary_acyclicGenerator input)

/-- Motive-root summary: the inverse-rotated acyclic generator cone triangle. -/
def TraceAnalyticMotive.rootSummary_acyclicGenerator_inverseRotatedTriangle
    (input : TraceLocalizationInput) :
    CategoryTheory.Triangle TraceAnalyticAdditiveHomotopyCategory :=
  (TraceAnalyticMotive.rootSummary_acyclicGenerator input).inverseRotatedTriangle

/-- Motive-root summary: the inverse-rotated acyclic generator cone triangle is distinguished. -/
theorem TraceAnalyticMotive.rootSummary_acyclicGenerator_inverseRotatedTriangle_distinguished
    (input : TraceLocalizationInput) :
    TraceAnalyticMotive.rootSummary_acyclicGenerator_inverseRotatedTriangle input ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceAnalyticAdditiveAcyclicGenerator.inverseRotatedTriangle_distinguished
    (TraceAnalyticMotive.rootSummary_acyclicGenerator input)

/-- Motive-root summary: the acyclic generator short complex. -/
def TraceAnalyticMotive.rootSummary_acyclicGenerator_shortComplex
    (input : TraceLocalizationInput) :
    CategoryTheory.ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  (TraceAnalyticMotive.rootSummary_acyclicGenerator input).shortComplex

/-- Motive-root summary: the acyclic generator short complex has zero composite. -/
theorem TraceAnalyticMotive.rootSummary_acyclicGenerator_shortComplex_zero
    (input : TraceLocalizationInput) :
    (TraceAnalyticMotive.rootSummary_acyclicGenerator_shortComplex input).f ≫
        (TraceAnalyticMotive.rootSummary_acyclicGenerator_shortComplex input).g =
      0 :=
  TraceAnalyticAdditiveAcyclicGenerator.shortComplex_zero
    (TraceAnalyticMotive.rootSummary_acyclicGenerator input)

/-- Motive-root summary: the rotated acyclic generator short complex. -/
def TraceAnalyticMotive.rootSummary_acyclicGenerator_rotatedShortComplex
    (input : TraceLocalizationInput) :
    CategoryTheory.ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  (TraceAnalyticMotive.rootSummary_acyclicGenerator input).rotatedShortComplex

/-- Motive-root summary: the rotated acyclic generator short complex has zero composite. -/
theorem TraceAnalyticMotive.rootSummary_acyclicGenerator_rotatedShortComplex_zero
    (input : TraceLocalizationInput) :
    (TraceAnalyticMotive.rootSummary_acyclicGenerator_rotatedShortComplex input).f ≫
        (TraceAnalyticMotive.rootSummary_acyclicGenerator_rotatedShortComplex input).g =
      0 :=
  TraceAnalyticAdditiveAcyclicGenerator.rotatedShortComplex_zero
    (TraceAnalyticMotive.rootSummary_acyclicGenerator input)

/-- Motive-root summary: the inverse-rotated acyclic generator short complex. -/
def TraceAnalyticMotive.rootSummary_acyclicGenerator_inverseRotatedShortComplex
    (input : TraceLocalizationInput) :
    CategoryTheory.ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  (TraceAnalyticMotive.rootSummary_acyclicGenerator input).inverseRotatedShortComplex

/-- Motive-root summary: the inverse-rotated acyclic generator short complex has zero composite. -/
theorem TraceAnalyticMotive.rootSummary_acyclicGenerator_inverseRotatedShortComplex_zero
    (input : TraceLocalizationInput) :
    (TraceAnalyticMotive.rootSummary_acyclicGenerator_inverseRotatedShortComplex input).f ≫
        (TraceAnalyticMotive.rootSummary_acyclicGenerator_inverseRotatedShortComplex input).g =
      0 :=
  TraceAnalyticAdditiveAcyclicGenerator.inverseRotatedShortComplex_zero
    (TraceAnalyticMotive.rootSummary_acyclicGenerator input)

end AnalyticMotives
end LFunctions
end Boundary
