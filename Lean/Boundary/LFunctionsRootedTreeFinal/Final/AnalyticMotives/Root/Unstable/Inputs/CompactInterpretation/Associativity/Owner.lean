import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.CompactInterpretation.Associativity.Owner

/-!
# Public associativity around forward compact interpretations

This file exposes compact associativity around forward compact
interpretations through the public root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: associativity around the forward compact interpretation. -/
theorem AnalyticMotivesRoot.unstableForwardCompactInterpretation_assoc
    (input : TraceLocalizationInput)
    {source target : TraceAnalyticGeometricGenerator}
    (lead : source ⟶ input.sourceGenerator)
    (tail : input.targetGenerator ⟶ target) :
    (lead ≫ input.unstableForwardCompactInterpretation) ≫ tail =
      lead ≫ (input.unstableForwardCompactInterpretation ≫ tail) :=
  TraceAnalyticMotive.unstableForwardCompactInterpretation_assoc
    input
    lead
    tail

/-- Public wrapper: trace-hom associativity around the forward compact interpretation. -/
theorem AnalyticMotivesRoot.unstableForwardCompactInterpretation_assoc_traceHom
    (input : TraceLocalizationInput)
    {source target : TraceAnalyticGeometricGenerator}
    (lead : source ⟶ input.sourceGenerator)
    (tail : input.targetGenerator ⟶ target) :
    ((lead ≫ input.unstableForwardCompactInterpretation) ≫ tail).traceHom =
      (lead ≫ (input.unstableForwardCompactInterpretation ≫ tail)).traceHom :=
  TraceAnalyticMotive.unstableForwardCompactInterpretation_assoc_traceHom
    input
    lead
    tail

/-- Public wrapper: presheaf-map associativity around the forward compact interpretation. -/
theorem AnalyticMotivesRoot.unstableForwardCompactInterpretation_assoc_representableMap
    (input : TraceLocalizationInput)
    {source target : TraceAnalyticGeometricGenerator}
    (lead : source ⟶ input.sourceGenerator)
    (tail : input.targetGenerator ⟶ target) :
    ((lead ≫ input.unstableForwardCompactInterpretation) ≫ tail).representableMap =
      (lead ≫ (input.unstableForwardCompactInterpretation ≫ tail)).representableMap :=
  TraceAnalyticMotive.unstableForwardCompactInterpretation_assoc_representableMap
    input
    lead
    tail

end AnalyticMotives
end LFunctions
end Boundary
