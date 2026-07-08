import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.CompactInterpretation.Composition.Owner

/-!
# Associativity around forward compact interpretations

This file specializes compact-generator associativity to composites whose
middle factor is the compact interpretation of a forward unstable
localization-input arrow.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Associativity around the forward compact interpretation. -/
theorem TraceLocalizationInput.unstableForwardCompactInterpretation_assoc
    (input : TraceLocalizationInput)
    {source target : TraceAnalyticGeometricGenerator}
    (lead : source ⟶ input.sourceGenerator)
    (tail : input.targetGenerator ⟶ target) :
    (lead ≫ input.unstableForwardCompactInterpretation) ≫ tail =
      lead ≫ (input.unstableForwardCompactInterpretation ≫ tail) :=
  TraceCorQHom.comp_assoc
    lead
    input.unstableForwardCompactInterpretation
    tail

/-- Trace-hom associativity around the forward compact interpretation. -/
theorem TraceLocalizationInput.unstableForwardCompactInterpretation_assoc_traceHom
    (input : TraceLocalizationInput)
    {source target : TraceAnalyticGeometricGenerator}
    (lead : source ⟶ input.sourceGenerator)
    (tail : input.targetGenerator ⟶ target) :
    ((lead ≫ input.unstableForwardCompactInterpretation) ≫ tail).traceHom =
      (lead ≫ (input.unstableForwardCompactInterpretation ≫ tail)).traceHom :=
  congrArg
    (fun morphism =>
      morphism.traceHom)
    (TraceLocalizationInput.unstableForwardCompactInterpretation_assoc
      input
      lead
      tail)

/-- Presheaf-map associativity around the forward compact interpretation. -/
theorem TraceLocalizationInput.unstableForwardCompactInterpretation_assoc_representableMap
    (input : TraceLocalizationInput)
    {source target : TraceAnalyticGeometricGenerator}
    (lead : source ⟶ input.sourceGenerator)
    (tail : input.targetGenerator ⟶ target) :
    ((lead ≫ input.unstableForwardCompactInterpretation) ≫ tail).representableMap =
      (lead ≫ (input.unstableForwardCompactInterpretation ≫ tail)).representableMap :=
  congrArg
    (fun morphism =>
      morphism.representableMap)
    (TraceLocalizationInput.unstableForwardCompactInterpretation_assoc
      input
      lead
      tail)

end AnalyticMotives
end LFunctions
end Boundary
