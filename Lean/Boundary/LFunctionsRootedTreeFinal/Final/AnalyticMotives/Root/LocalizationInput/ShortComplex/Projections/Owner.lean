import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Motives.Summary.LocalizationInput.ShortComplex.Projections.Owner

/-!
# Public localization-input short-complex projection facade

This file exposes vertex and map projections for arbitrary localization-input
bounded cone short complexes at the top root surface.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Public root facade: the unrotated short complex has source as left vertex. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeShortComplex_X₁
    (input : TraceLocalizationInput) :
    input.boundedMappingConeShortComplex.X₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        input.boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeShortComplex_X₁
    input

/-- Public root facade: the unrotated short complex has target as middle vertex. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeShortComplex_X₂
    (input : TraceLocalizationInput) :
    input.boundedMappingConeShortComplex.X₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        input.boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeShortComplex_X₂
    input

/-- Public root facade: the unrotated short complex has cone as right vertex. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeShortComplex_X₃
    (input : TraceLocalizationInput) :
    input.boundedMappingConeShortComplex.X₃ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObject
        input.boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeShortComplex_X₃
    input

/-- Public root facade: the first unrotated short-complex map is the bounded map. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeShortComplex_f
    (input : TraceLocalizationInput) :
    input.boundedMappingConeShortComplex.f =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        input.boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeShortComplex_f
    input

/-- Public root facade: the second unrotated short-complex map is cone inclusion. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeShortComplex_g
    (input : TraceLocalizationInput) :
    input.boundedMappingConeShortComplex.g =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
        input.boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeShortComplex_g
    input

/-- Public root facade: the rotated short complex has target as left vertex. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeRotatedShortComplex_X₁
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedShortComplex.X₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        input.boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeRotatedShortComplex_X₁
    input

/-- Public root facade: the rotated short complex has cone as middle vertex. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeRotatedShortComplex_X₂
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedShortComplex.X₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObject
        input.boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeRotatedShortComplex_X₂
    input

/-- Public root facade: the rotated short complex has shifted source as right vertex. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeRotatedShortComplex_X₃
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedShortComplex.X₃ =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        input.boundedAdditiveComplexHom)⟦(1 : ℤ)⟧ :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeRotatedShortComplex_X₃
    input

/-- Public root facade: the first rotated short-complex map is cone inclusion. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeRotatedShortComplex_f
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedShortComplex.f =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
        input.boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeRotatedShortComplex_f
    input

/-- Public root facade: the second rotated short-complex map is the connecting map. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeRotatedShortComplex_g
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedShortComplex.g =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        input.boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeRotatedShortComplex_g
    input

/-- Public root facade: the inverse-rotated short complex has shifted cone as left
vertex. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeInverseRotatedShortComplex_X₁
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedShortComplex.X₁ =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObject
        input.boundedAdditiveComplexHom)⟦(-1 : ℤ)⟧ :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeInverseRotatedShortComplex_X₁
    input

/-- Public root facade: the inverse-rotated short complex has source as middle vertex. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeInverseRotatedShortComplex_X₂
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedShortComplex.X₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        input.boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeInverseRotatedShortComplex_X₂
    input

/-- Public root facade: the inverse-rotated short complex has target as right vertex. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeInverseRotatedShortComplex_X₃
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedShortComplex.X₃ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        input.boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeInverseRotatedShortComplex_X₃
    input

/-- Public root facade: the first inverse-rotated map is shifted negative connecting map
with unit transport. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeInverseRotatedShortComplex_f
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedShortComplex.f =
      -(TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        input.boundedAdditiveComplexHom)⟦(-1 : ℤ)⟧' ≫
        (shiftEquiv TraceAnalyticAdditiveHomotopyCategory
          (1 : ℤ)).unitIso.inv.app _ :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeInverseRotatedShortComplex_f
    input

/-- Public root facade: the second inverse-rotated map is the bounded map. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeInverseRotatedShortComplex_g
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedShortComplex.g =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        input.boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeInverseRotatedShortComplex_g
    input

end AnalyticMotives
end LFunctions
end Boundary
