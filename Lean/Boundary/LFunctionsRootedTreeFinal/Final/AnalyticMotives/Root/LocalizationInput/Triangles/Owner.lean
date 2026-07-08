import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Motives.Summary.LocalizationInput.Triangles.Owner

/-!
# Public localization-input cone triangle facade

This file exposes bounded cone triangles and rotated cone triangles for
arbitrary localization inputs at the top root surface.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Public root facade: the bounded mapping-cone triangle of a localization input. -/
def AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeTriangle
    (input : TraceLocalizationInput) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle
      input.additiveComplexCommonWeightBound :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeTriangle
    input

/-- Public root facade: the rotated bounded mapping-cone triangle of a localization
input. -/
def AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeRotatedTriangle
    (input : TraceLocalizationInput) :
    Triangle TraceAnalyticAdditiveHomotopyCategory :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeRotatedTriangle
    input

/-- Public root facade: the inverse-rotated bounded mapping-cone triangle of a
localization input. -/
def AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeInverseRotatedTriangle
    (input : TraceLocalizationInput) :
    Triangle TraceAnalyticAdditiveHomotopyCategory :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeInverseRotatedTriangle
    input

/-- Public root facade: a localization-input bounded cone triangle is distinguished. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeTriangle_distinguished
    (input : TraceLocalizationInput) :
    input.boundedMappingConeTriangle.triangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeTriangle_distinguished
    input

/-- Public root facade: a localization-input rotated cone triangle is distinguished. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeRotatedTriangle_distinguished
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedTriangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeRotatedTriangle_distinguished
    input

/-- Public root facade: a localization-input inverse-rotated cone triangle is
distinguished. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeInverseRotatedTriangle_distinguished
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedTriangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeInverseRotatedTriangle_distinguished
    input

/-- Public root facade: the first two morphisms of a localization-input cone triangle
compose to zero. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeTriangle_first_comp_second
    (input : TraceLocalizationInput) :
    input.boundedMappingConeTriangle.triangle.mor₁ ≫
        input.boundedMappingConeTriangle.triangle.mor₂ =
      0 :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeTriangle_first_comp_second
    input

/-- Public root facade: the second and third morphisms of a localization-input cone
triangle compose to zero. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeTriangle_second_comp_third
    (input : TraceLocalizationInput) :
    input.boundedMappingConeTriangle.triangle.mor₂ ≫
        input.boundedMappingConeTriangle.triangle.mor₃ =
      0 :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeTriangle_second_comp_third
    input

/-- Public root facade: the third morphism followed by the shifted first morphism of a
localization-input cone triangle is zero. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeTriangle_third_comp_shifted_first
    (input : TraceLocalizationInput) :
    input.boundedMappingConeTriangle.triangle.mor₃ ≫
        input.boundedMappingConeTriangle.triangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeTriangle_third_comp_shifted_first
    input

/-- Public root facade: the first two morphisms of a rotated localization-input cone
triangle compose to zero. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeRotatedTriangle_first_comp_second
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedTriangle.mor₁ ≫
        input.boundedMappingConeRotatedTriangle.mor₂ =
      0 :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeRotatedTriangle_first_comp_second
    input

/-- Public root facade: the second and third morphisms of a rotated localization-input
cone triangle compose to zero. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeRotatedTriangle_second_comp_third
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedTriangle.mor₂ ≫
        input.boundedMappingConeRotatedTriangle.mor₃ =
      0 :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeRotatedTriangle_second_comp_third
    input

/-- Public root facade: the third morphism followed by the shifted first morphism of a
rotated localization-input cone triangle is zero. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeRotatedTriangle_third_comp_shifted_first
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedTriangle.mor₃ ≫
        input.boundedMappingConeRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeRotatedTriangle_third_comp_shifted_first
    input

/-- Public root facade: the first two morphisms of an inverse-rotated localization-input
cone triangle compose to zero. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeInverseRotatedTriangle_first_comp_second
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedTriangle.mor₁ ≫
        input.boundedMappingConeInverseRotatedTriangle.mor₂ =
      0 :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeInverseRotatedTriangle_first_comp_second
    input

/-- Public root facade: the second and third morphisms of an inverse-rotated
localization-input cone triangle compose to zero. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeInverseRotatedTriangle_second_comp_third
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedTriangle.mor₂ ≫
        input.boundedMappingConeInverseRotatedTriangle.mor₃ =
      0 :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeInverseRotatedTriangle_second_comp_third
    input

/-- Public root facade: the third morphism followed by the shifted first morphism of an
inverse-rotated localization-input cone triangle is zero. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedTriangle.mor₃ ≫
        input.boundedMappingConeInverseRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first
    input

end AnalyticMotives
end LFunctions
end Boundary
