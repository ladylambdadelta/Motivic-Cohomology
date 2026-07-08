import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.LocalizationInput.ShortComplex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.LocalizationInput.Rotation.ShortComplex.Owner

/-!
# Motive-root localization-input short-complex summaries

This file exposes the bounded mapping-cone short complexes attached to an
arbitrary localization input.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Motive-root summary: the short complex of a localization-input bounded mapping cone. -/
def TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeShortComplex
    (input : TraceLocalizationInput) :
    ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  input.boundedMappingConeShortComplex

/-- Motive-root summary: the rotated short complex of a localization-input bounded
mapping cone. -/
def TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeRotatedShortComplex
    (input : TraceLocalizationInput) :
    ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  input.boundedMappingConeRotatedShortComplex

/-- Motive-root summary: the inverse-rotated short complex of a localization-input
bounded mapping cone. -/
def TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeInverseRotatedShortComplex
    (input : TraceLocalizationInput) :
    ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  input.boundedMappingConeInverseRotatedShortComplex

/-- Motive-root summary: a localization-input bounded cone short complex has zero
composite. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeShortComplex_zero
    (input : TraceLocalizationInput) :
    input.boundedMappingConeShortComplex.f ≫
        input.boundedMappingConeShortComplex.g =
      0 :=
  TraceLocalizationInput.boundedMappingConeShortComplex_zero
    input

/-- Motive-root summary: a localization-input rotated bounded cone short complex has
zero composite. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeRotatedShortComplex_zero
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedShortComplex.f ≫
        input.boundedMappingConeRotatedShortComplex.g =
      0 :=
  TraceLocalizationInput.boundedMappingConeRotatedShortComplex_zero
    input

/-- Motive-root summary: a localization-input inverse-rotated bounded cone short complex
has zero composite. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeInverseRotatedShortComplex_zero
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedShortComplex.f ≫
        input.boundedMappingConeInverseRotatedShortComplex.g =
      0 :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedShortComplex_zero
    input

end AnalyticMotives
end LFunctions
end Boundary
