import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Summary.LocalizationInput.ShortComplex.Owner

/-!
# Top-root localization-input short-complex summaries

This file exposes arbitrary localization-input bounded cone short complexes
through the public `AnalyticMotivesRoot` namespace.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Public motive summary: the short complex of a localization-input bounded mapping
cone. -/
def AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeShortComplex
    (input : TraceLocalizationInput) :
    ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeShortComplex
    input

/-- Public motive summary: the rotated short complex of a localization-input bounded
mapping cone. -/
def AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeRotatedShortComplex
    (input : TraceLocalizationInput) :
    ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeRotatedShortComplex
    input

/-- Public motive summary: the inverse-rotated short complex of a localization-input
bounded mapping cone. -/
def AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeInverseRotatedShortComplex
    (input : TraceLocalizationInput) :
    ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeInverseRotatedShortComplex
    input

/-- Public motive summary: a localization-input bounded cone short complex has zero
composite. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeShortComplex_zero
    (input : TraceLocalizationInput) :
    input.boundedMappingConeShortComplex.f ≫
        input.boundedMappingConeShortComplex.g =
      0 :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeShortComplex_zero
    input

/-- Public motive summary: a localization-input rotated bounded cone short complex has
zero composite. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeRotatedShortComplex_zero
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedShortComplex.f ≫
        input.boundedMappingConeRotatedShortComplex.g =
      0 :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeRotatedShortComplex_zero
    input

/-- Public motive summary: a localization-input inverse-rotated bounded cone short
complex has zero composite. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeInverseRotatedShortComplex_zero
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedShortComplex.f ≫
        input.boundedMappingConeInverseRotatedShortComplex.g =
      0 :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeInverseRotatedShortComplex_zero
    input

end AnalyticMotives
end LFunctions
end Boundary
