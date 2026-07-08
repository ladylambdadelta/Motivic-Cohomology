import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.CompactInterpretation.Associativity.Owner

/-!
# Motive-root associativity around forward compact interpretations

This file exposes compact associativity around forward compact
interpretations through the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: associativity around the forward compact interpretation. -/
theorem TraceAnalyticMotive.unstableForwardCompactInterpretation_assoc
    (input : TraceLocalizationInput)
    {source target : TraceAnalyticGeometricGenerator}
    (lead : source ⟶ input.sourceGenerator)
    (tail : input.targetGenerator ⟶ target) :
    (lead ≫ input.unstableForwardCompactInterpretation) ≫ tail =
      lead ≫ (input.unstableForwardCompactInterpretation ≫ tail) :=
  TraceLocalizationInput.unstableForwardCompactInterpretation_assoc
    input
    lead
    tail

/-- Motive-root wrapper: trace-hom associativity around the forward compact interpretation. -/
theorem TraceAnalyticMotive.unstableForwardCompactInterpretation_assoc_traceHom
    (input : TraceLocalizationInput)
    {source target : TraceAnalyticGeometricGenerator}
    (lead : source ⟶ input.sourceGenerator)
    (tail : input.targetGenerator ⟶ target) :
    ((lead ≫ input.unstableForwardCompactInterpretation) ≫ tail).traceHom =
      (lead ≫ (input.unstableForwardCompactInterpretation ≫ tail)).traceHom :=
  TraceLocalizationInput.unstableForwardCompactInterpretation_assoc_traceHom
    input
    lead
    tail

/-- Motive-root wrapper: presheaf-map associativity around the forward compact interpretation. -/
theorem TraceAnalyticMotive.unstableForwardCompactInterpretation_assoc_representableMap
    (input : TraceLocalizationInput)
    {source target : TraceAnalyticGeometricGenerator}
    (lead : source ⟶ input.sourceGenerator)
    (tail : input.targetGenerator ⟶ target) :
    ((lead ≫ input.unstableForwardCompactInterpretation) ≫ tail).representableMap =
      (lead ≫ (input.unstableForwardCompactInterpretation ≫ tail)).representableMap :=
  TraceLocalizationInput.unstableForwardCompactInterpretation_assoc_representableMap
    input
    lead
    tail

end AnalyticMotives
end LFunctions
end Boundary
