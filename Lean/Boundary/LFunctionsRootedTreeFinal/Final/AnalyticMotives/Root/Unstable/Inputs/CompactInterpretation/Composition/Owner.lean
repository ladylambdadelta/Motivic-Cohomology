import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.CompactInterpretation.Composition.Owner

/-!
# Public composition of forward compact interpretations

This file exposes composition formulas for the compact interpretation of
forward unstable localization-input arrows through the public root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: right-composition after the forward interpretation has the expected trace hom. -/
theorem AnalyticMotivesRoot.unstableForwardCompactInterpretation_comp_traceHom
    (input : TraceLocalizationInput)
    {target : TraceAnalyticGeometricGenerator}
    (tail : input.targetGenerator ⟶ target) :
    (input.unstableForwardCompactInterpretation ≫ tail).traceHom =
      input.traceHom ≫ tail.traceHom :=
  TraceAnalyticMotive.unstableForwardCompactInterpretation_comp_traceHom
    input
    tail

/-- Public wrapper: left-composition before the forward interpretation has the expected trace hom. -/
theorem AnalyticMotivesRoot.comp_unstableForwardCompactInterpretation_traceHom
    (input : TraceLocalizationInput)
    {source : TraceAnalyticGeometricGenerator}
    (lead : source ⟶ input.sourceGenerator) :
    (lead ≫ input.unstableForwardCompactInterpretation).traceHom =
      lead.traceHom ≫ input.traceHom :=
  TraceAnalyticMotive.comp_unstableForwardCompactInterpretation_traceHom
    input
    lead

/-- Public wrapper: right-composition after the forward interpretation has the expected presheaf map. -/
theorem AnalyticMotivesRoot.unstableForwardCompactInterpretation_comp_representableMap
    (input : TraceLocalizationInput)
    {target : TraceAnalyticGeometricGenerator}
    (tail : input.targetGenerator ⟶ target) :
    (input.unstableForwardCompactInterpretation ≫ tail).representableMap =
      input.map ≫ tail.representableMap :=
  TraceAnalyticMotive.unstableForwardCompactInterpretation_comp_representableMap
    input
    tail

/-- Public wrapper: left-composition before the forward interpretation has the expected presheaf map. -/
theorem AnalyticMotivesRoot.comp_unstableForwardCompactInterpretation_representableMap
    (input : TraceLocalizationInput)
    {source : TraceAnalyticGeometricGenerator}
    (lead : source ⟶ input.sourceGenerator) :
    (lead ≫ input.unstableForwardCompactInterpretation).representableMap =
      lead.representableMap ≫ input.map :=
  TraceAnalyticMotive.comp_unstableForwardCompactInterpretation_representableMap
    input
    lead

end AnalyticMotives
end LFunctions
end Boundary
