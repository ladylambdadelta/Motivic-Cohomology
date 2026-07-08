import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.LocalizationInput.Exactness.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.LocalizationInput.Rotation.Exactness.Owner

/-!
# Motive-root localization-input cone triangles

This file exposes the bounded mapping-cone triangle and its two rotations for
an arbitrary localization input.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Motive-root summary: the bounded mapping-cone triangle of a localization input. -/
def TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeTriangle
    (input : TraceLocalizationInput) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle
      input.additiveComplexCommonWeightBound :=
  input.boundedMappingConeTriangle

/-- Motive-root summary: the rotated bounded mapping-cone triangle of a localization input. -/
def TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeRotatedTriangle
    (input : TraceLocalizationInput) :
    Triangle TraceAnalyticAdditiveHomotopyCategory :=
  input.boundedMappingConeRotatedTriangle

/-- Motive-root summary: the inverse-rotated bounded mapping-cone triangle of a
localization input. -/
def TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeInverseRotatedTriangle
    (input : TraceLocalizationInput) :
    Triangle TraceAnalyticAdditiveHomotopyCategory :=
  input.boundedMappingConeInverseRotatedTriangle

/-- Motive-root summary: a localization-input bounded cone triangle is distinguished. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeTriangle_distinguished
    (input : TraceLocalizationInput) :
    input.boundedMappingConeTriangle.triangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceLocalizationInput.boundedMappingConeTriangle_distinguished
    input

/-- Motive-root summary: a localization-input rotated cone triangle is distinguished. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeRotatedTriangle_distinguished
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedTriangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_distinguished
    input

/-- Motive-root summary: a localization-input inverse-rotated cone triangle is
distinguished. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeInverseRotatedTriangle_distinguished
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedTriangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_distinguished
    input

/-- Motive-root summary: the first two morphisms of a localization-input cone triangle
compose to zero. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeTriangle_first_comp_second
    (input : TraceLocalizationInput) :
    input.boundedMappingConeTriangle.triangle.mor₁ ≫
        input.boundedMappingConeTriangle.triangle.mor₂ =
      0 :=
  TraceLocalizationInput.boundedMappingConeTriangle_first_comp_second
    input

/-- Motive-root summary: the second and third morphisms of a localization-input cone
triangle compose to zero. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeTriangle_second_comp_third
    (input : TraceLocalizationInput) :
    input.boundedMappingConeTriangle.triangle.mor₂ ≫
        input.boundedMappingConeTriangle.triangle.mor₃ =
      0 :=
  TraceLocalizationInput.boundedMappingConeTriangle_second_comp_third
    input

/-- Motive-root summary: the third morphism followed by the shifted first morphism of a
localization-input cone triangle is zero. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeTriangle_third_comp_shifted_first
    (input : TraceLocalizationInput) :
    input.boundedMappingConeTriangle.triangle.mor₃ ≫
        input.boundedMappingConeTriangle.triangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.boundedMappingConeTriangle_third_comp_shifted_first
    input

/-- Motive-root summary: the first two morphisms of a rotated localization-input cone
triangle compose to zero. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeRotatedTriangle_first_comp_second
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedTriangle.mor₁ ≫
        input.boundedMappingConeRotatedTriangle.mor₂ =
      0 :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_first_comp_second
    input

/-- Motive-root summary: the second and third morphisms of a rotated localization-input
cone triangle compose to zero. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeRotatedTriangle_second_comp_third
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedTriangle.mor₂ ≫
        input.boundedMappingConeRotatedTriangle.mor₃ =
      0 :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_second_comp_third
    input

/-- Motive-root summary: the third morphism followed by the shifted first morphism of a
rotated localization-input cone triangle is zero. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeRotatedTriangle_third_comp_shifted_first
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedTriangle.mor₃ ≫
        input.boundedMappingConeRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_third_comp_shifted_first
    input

/-- Motive-root summary: the first two morphisms of an inverse-rotated localization-input
cone triangle compose to zero. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeInverseRotatedTriangle_first_comp_second
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedTriangle.mor₁ ≫
        input.boundedMappingConeInverseRotatedTriangle.mor₂ =
      0 :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_first_comp_second
    input

/-- Motive-root summary: the second and third morphisms of an inverse-rotated
localization-input cone triangle compose to zero. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeInverseRotatedTriangle_second_comp_third
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedTriangle.mor₂ ≫
        input.boundedMappingConeInverseRotatedTriangle.mor₃ =
      0 :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_second_comp_third
    input

/-- Motive-root summary: the third morphism followed by the shifted first morphism of an
inverse-rotated localization-input cone triangle is zero. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedTriangle.mor₃ ≫
        input.boundedMappingConeInverseRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first
    input

end AnalyticMotives
end LFunctions
end Boundary
