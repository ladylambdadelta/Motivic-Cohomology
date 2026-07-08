import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Motives.Summary.LocalizationInput.ShortComplex.Owner

/-!
# Public localization-input short-complex facade

This file exposes arbitrary localization-input bounded cone short complexes at
the top root surface.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Public root facade: the short complex of a localization-input bounded mapping cone. -/
def AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeShortComplex
    (input : TraceLocalizationInput) :
    ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeShortComplex
    input

/-- Public root facade: the rotated short complex of a localization-input bounded
mapping cone. -/
def AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeRotatedShortComplex
    (input : TraceLocalizationInput) :
    ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeRotatedShortComplex
    input

/-- Public root facade: the inverse-rotated short complex of a localization-input
bounded mapping cone. -/
def AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeInverseRotatedShortComplex
    (input : TraceLocalizationInput) :
    ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeInverseRotatedShortComplex
    input

/-- Public root facade: a localization-input bounded cone short complex has zero
composite. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeShortComplex_zero
    (input : TraceLocalizationInput) :
    input.boundedMappingConeShortComplex.f ≫
        input.boundedMappingConeShortComplex.g =
      0 :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeShortComplex_zero
    input

/-- Public root facade: a localization-input rotated bounded cone short complex has zero
composite. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeRotatedShortComplex_zero
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedShortComplex.f ≫
        input.boundedMappingConeRotatedShortComplex.g =
      0 :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeRotatedShortComplex_zero
    input

/-- Public root facade: a localization-input inverse-rotated bounded cone short complex
has zero composite. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeInverseRotatedShortComplex_zero
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedShortComplex.f ≫
        input.boundedMappingConeInverseRotatedShortComplex.g =
      0 :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeInverseRotatedShortComplex_zero
    input

end AnalyticMotives
end LFunctions
end Boundary
