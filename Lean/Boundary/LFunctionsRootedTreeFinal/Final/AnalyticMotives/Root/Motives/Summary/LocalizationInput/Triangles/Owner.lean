import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Summary.LocalizationInput.Triangles.Owner

/-!
# Top-root localization-input cone triangles

This file exposes the bounded mapping-cone triangle and its two rotations for
an arbitrary localization input under the public root namespace.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Public motive summary: the bounded mapping-cone triangle of a localization input. -/
def AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeTriangle
    (input : TraceLocalizationInput) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle
      input.additiveComplexCommonWeightBound :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeTriangle
    input

/-- Public motive summary: the rotated bounded mapping-cone triangle of a localization
input. -/
def AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeRotatedTriangle
    (input : TraceLocalizationInput) :
    Triangle TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeRotatedTriangle
    input

/-- Public motive summary: the inverse-rotated bounded mapping-cone triangle of a
localization input. -/
def AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeInverseRotatedTriangle
    (input : TraceLocalizationInput) :
    Triangle TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeInverseRotatedTriangle
    input

/-- Public motive summary: a localization-input bounded cone triangle is distinguished. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeTriangle_distinguished
    (input : TraceLocalizationInput) :
    input.boundedMappingConeTriangle.triangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeTriangle_distinguished
    input

/-- Public motive summary: a localization-input rotated cone triangle is distinguished. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeRotatedTriangle_distinguished
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedTriangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeRotatedTriangle_distinguished
    input

/-- Public motive summary: a localization-input inverse-rotated cone triangle is
distinguished. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeInverseRotatedTriangle_distinguished
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedTriangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeInverseRotatedTriangle_distinguished
    input

/-- Public motive summary: the first two morphisms of a localization-input cone triangle
compose to zero. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeTriangle_first_comp_second
    (input : TraceLocalizationInput) :
    input.boundedMappingConeTriangle.triangle.mor₁ ≫
        input.boundedMappingConeTriangle.triangle.mor₂ =
      0 :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeTriangle_first_comp_second
    input

/-- Public motive summary: the second and third morphisms of a localization-input cone
triangle compose to zero. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeTriangle_second_comp_third
    (input : TraceLocalizationInput) :
    input.boundedMappingConeTriangle.triangle.mor₂ ≫
        input.boundedMappingConeTriangle.triangle.mor₃ =
      0 :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeTriangle_second_comp_third
    input

/-- Public motive summary: the third morphism followed by the shifted first morphism of
a localization-input cone triangle is zero. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeTriangle_third_comp_shifted_first
    (input : TraceLocalizationInput) :
    input.boundedMappingConeTriangle.triangle.mor₃ ≫
        input.boundedMappingConeTriangle.triangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeTriangle_third_comp_shifted_first
    input

/-- Public motive summary: the first two morphisms of a rotated localization-input cone
triangle compose to zero. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeRotatedTriangle_first_comp_second
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedTriangle.mor₁ ≫
        input.boundedMappingConeRotatedTriangle.mor₂ =
      0 :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeRotatedTriangle_first_comp_second
    input

/-- Public motive summary: the second and third morphisms of a rotated localization-input
cone triangle compose to zero. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeRotatedTriangle_second_comp_third
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedTriangle.mor₂ ≫
        input.boundedMappingConeRotatedTriangle.mor₃ =
      0 :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeRotatedTriangle_second_comp_third
    input

/-- Public motive summary: the third morphism followed by the shifted first morphism of
a rotated localization-input cone triangle is zero. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeRotatedTriangle_third_comp_shifted_first
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedTriangle.mor₃ ≫
        input.boundedMappingConeRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeRotatedTriangle_third_comp_shifted_first
    input

/-- Public motive summary: the first two morphisms of an inverse-rotated localization-input
cone triangle compose to zero. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeInverseRotatedTriangle_first_comp_second
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedTriangle.mor₁ ≫
        input.boundedMappingConeInverseRotatedTriangle.mor₂ =
      0 :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeInverseRotatedTriangle_first_comp_second
    input

/-- Public motive summary: the second and third morphisms of an inverse-rotated
localization-input cone triangle compose to zero. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeInverseRotatedTriangle_second_comp_third
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedTriangle.mor₂ ≫
        input.boundedMappingConeInverseRotatedTriangle.mor₃ =
      0 :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeInverseRotatedTriangle_second_comp_third
    input

/-- Public motive summary: the third morphism followed by the shifted first morphism of
an inverse-rotated localization-input cone triangle is zero. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedTriangle.mor₃ ≫
        input.boundedMappingConeInverseRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first
    input

end AnalyticMotives
end LFunctions
end Boundary
