import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Summary.LocalizationInput.ShortComplex.Owner

/-!
# Motive-root localization-input short-complex projections

This file exposes the vertex and map projections for the three short complexes
attached to an arbitrary localization-input bounded cone.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Motive-root summary: the unrotated short complex has source as left vertex. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeShortComplex_X₁
    (input : TraceLocalizationInput) :
    input.boundedMappingConeShortComplex.X₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        input.boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeShortComplex_X₁
    input

/-- Motive-root summary: the unrotated short complex has target as middle vertex. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeShortComplex_X₂
    (input : TraceLocalizationInput) :
    input.boundedMappingConeShortComplex.X₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        input.boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeShortComplex_X₂
    input

/-- Motive-root summary: the unrotated short complex has cone as right vertex. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeShortComplex_X₃
    (input : TraceLocalizationInput) :
    input.boundedMappingConeShortComplex.X₃ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObject
        input.boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeShortComplex_X₃
    input

/-- Motive-root summary: the first unrotated short-complex map is the bounded map. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeShortComplex_f
    (input : TraceLocalizationInput) :
    input.boundedMappingConeShortComplex.f =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        input.boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeShortComplex_f
    input

/-- Motive-root summary: the second unrotated short-complex map is cone inclusion. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeShortComplex_g
    (input : TraceLocalizationInput) :
    input.boundedMappingConeShortComplex.g =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
        input.boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeShortComplex_g
    input

/-- Motive-root summary: the rotated short complex has target as left vertex. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeRotatedShortComplex_X₁
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedShortComplex.X₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        input.boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeRotatedShortComplex_X₁
    input

/-- Motive-root summary: the rotated short complex has cone as middle vertex. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeRotatedShortComplex_X₂
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedShortComplex.X₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObject
        input.boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeRotatedShortComplex_X₂
    input

/-- Motive-root summary: the rotated short complex has shifted source as right vertex. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeRotatedShortComplex_X₃
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedShortComplex.X₃ =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        input.boundedAdditiveComplexHom)⟦(1 : ℤ)⟧ :=
  TraceLocalizationInput.boundedMappingConeRotatedShortComplex_X₃
    input

/-- Motive-root summary: the first rotated short-complex map is cone inclusion. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeRotatedShortComplex_f
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedShortComplex.f =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
        input.boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeRotatedShortComplex_f
    input

/-- Motive-root summary: the second rotated short-complex map is the connecting map. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeRotatedShortComplex_g
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedShortComplex.g =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        input.boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeRotatedShortComplex_g
    input

/-- Motive-root summary: the inverse-rotated short complex has shifted cone as left
vertex. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeInverseRotatedShortComplex_X₁
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedShortComplex.X₁ =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObject
        input.boundedAdditiveComplexHom)⟦(-1 : ℤ)⟧ :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedShortComplex_X₁
    input

/-- Motive-root summary: the inverse-rotated short complex has source as middle vertex. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeInverseRotatedShortComplex_X₂
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedShortComplex.X₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        input.boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedShortComplex_X₂
    input

/-- Motive-root summary: the inverse-rotated short complex has target as right vertex. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeInverseRotatedShortComplex_X₃
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedShortComplex.X₃ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        input.boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedShortComplex_X₃
    input

/-- Motive-root summary: the first inverse-rotated map is shifted negative connecting
map with unit transport. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeInverseRotatedShortComplex_f
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedShortComplex.f =
      -(TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        input.boundedAdditiveComplexHom)⟦(-1 : ℤ)⟧' ≫
        (shiftEquiv TraceAnalyticAdditiveHomotopyCategory
          (1 : ℤ)).unitIso.inv.app _ :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedShortComplex_f
    input

/-- Motive-root summary: the second inverse-rotated map is the bounded map. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeInverseRotatedShortComplex_g
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedShortComplex.g =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        input.boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedShortComplex_g
    input

end AnalyticMotives
end LFunctions
end Boundary
