import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Summary.LocalizationInput.ShortComplex.Projections.Owner

/-!
# Top-root localization-input short-complex projections

This file exposes the vertex and map projections for arbitrary
localization-input bounded cone short complexes.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Public motive summary: the unrotated short complex has source as left vertex. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeShortComplex_X₁
    (input : TraceLocalizationInput) :
    input.boundedMappingConeShortComplex.X₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        input.boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeShortComplex_X₁
    input

/-- Public motive summary: the unrotated short complex has target as middle vertex. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeShortComplex_X₂
    (input : TraceLocalizationInput) :
    input.boundedMappingConeShortComplex.X₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        input.boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeShortComplex_X₂
    input

/-- Public motive summary: the unrotated short complex has cone as right vertex. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeShortComplex_X₃
    (input : TraceLocalizationInput) :
    input.boundedMappingConeShortComplex.X₃ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObject
        input.boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeShortComplex_X₃
    input

/-- Public motive summary: the first unrotated short-complex map is the bounded map. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeShortComplex_f
    (input : TraceLocalizationInput) :
    input.boundedMappingConeShortComplex.f =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        input.boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeShortComplex_f
    input

/-- Public motive summary: the second unrotated short-complex map is cone inclusion. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeShortComplex_g
    (input : TraceLocalizationInput) :
    input.boundedMappingConeShortComplex.g =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
        input.boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeShortComplex_g
    input

/-- Public motive summary: the rotated short complex has target as left vertex. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeRotatedShortComplex_X₁
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedShortComplex.X₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        input.boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeRotatedShortComplex_X₁
    input

/-- Public motive summary: the rotated short complex has cone as middle vertex. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeRotatedShortComplex_X₂
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedShortComplex.X₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObject
        input.boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeRotatedShortComplex_X₂
    input

/-- Public motive summary: the rotated short complex has shifted source as right vertex. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeRotatedShortComplex_X₃
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedShortComplex.X₃ =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        input.boundedAdditiveComplexHom)⟦(1 : ℤ)⟧ :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeRotatedShortComplex_X₃
    input

/-- Public motive summary: the first rotated short-complex map is cone inclusion. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeRotatedShortComplex_f
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedShortComplex.f =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
        input.boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeRotatedShortComplex_f
    input

/-- Public motive summary: the second rotated short-complex map is the connecting map. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeRotatedShortComplex_g
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedShortComplex.g =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        input.boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeRotatedShortComplex_g
    input

/-- Public motive summary: the inverse-rotated short complex has shifted cone as left
vertex. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeInverseRotatedShortComplex_X₁
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedShortComplex.X₁ =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObject
        input.boundedAdditiveComplexHom)⟦(-1 : ℤ)⟧ :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeInverseRotatedShortComplex_X₁
    input

/-- Public motive summary: the inverse-rotated short complex has source as middle vertex. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeInverseRotatedShortComplex_X₂
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedShortComplex.X₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        input.boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeInverseRotatedShortComplex_X₂
    input

/-- Public motive summary: the inverse-rotated short complex has target as right vertex. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeInverseRotatedShortComplex_X₃
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedShortComplex.X₃ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        input.boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeInverseRotatedShortComplex_X₃
    input

/-- Public motive summary: the first inverse-rotated map is shifted negative connecting
map with unit transport. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeInverseRotatedShortComplex_f
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedShortComplex.f =
      -(TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        input.boundedAdditiveComplexHom)⟦(-1 : ℤ)⟧' ≫
        (shiftEquiv TraceAnalyticAdditiveHomotopyCategory
          (1 : ℤ)).unitIso.inv.app _ :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeInverseRotatedShortComplex_f
    input

/-- Public motive summary: the second inverse-rotated map is the bounded map. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeInverseRotatedShortComplex_g
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedShortComplex.g =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        input.boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeInverseRotatedShortComplex_g
    input

end AnalyticMotives
end LFunctions
end Boundary
