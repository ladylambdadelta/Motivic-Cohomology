import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Summary.UnstablePayload.Owner

/-!
# Motive-root forward compact interpretation summaries

This file exposes root summary theorems for unstable forward word classes and
their compact-generator interpretations.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root summary: unstable forward is the forward input word class. -/
theorem TraceAnalyticMotive.rootSummary_unstableForward_eq_wordClass
    (input : TraceLocalizationInput) :
    input.unstableForward =
      TraceLocalizationWordClass.ofInputForward input :=
  TraceAnalyticMotive.unstableForward_eq_wordClass
    input

/-- Motive-root summary: unstable forward is represented by the forward input word. -/
theorem TraceAnalyticMotive.rootSummary_unstableForward_eq_ofWord
    (input : TraceLocalizationInput) :
    input.unstableForward =
      TraceLocalizationWordClass.ofWord
        (TraceLocalizationWord.ofInputForward input) :=
  TraceAnalyticMotive.unstableForward_eq_ofWord
    input

/-- Motive-root summary: the forward compact interpretation is the input generator hom. -/
theorem TraceAnalyticMotive.rootSummary_unstableForwardCompactInterpretation_eq_generatorHom
    (input : TraceLocalizationInput) :
    input.unstableForwardCompactInterpretation =
      input.generatorHom :=
  TraceAnalyticMotive.unstableForwardCompactInterpretation_eq_generatorHom
    input

/-- Motive-root summary: the forward compact interpretation has the input trace hom. -/
theorem TraceAnalyticMotive.rootSummary_unstableForwardCompactInterpretation_traceHom
    (input : TraceLocalizationInput) :
    input.unstableForwardCompactInterpretation.traceHom =
      input.traceHom :=
  TraceAnalyticMotive.unstableForwardCompactInterpretation_traceHom
    input

/-- Motive-root summary: the forward compact interpretation induces the input map. -/
theorem TraceAnalyticMotive.rootSummary_unstableForwardCompactInterpretation_representableMap
    (input : TraceLocalizationInput) :
    input.unstableForwardCompactInterpretation.representableMap =
      input.map :=
  TraceAnalyticMotive.unstableForwardCompactInterpretation_representableMap
    input

/-- Motive-root summary: the compact presheaf functor sends the forward interpretation to the input map. -/
theorem TraceAnalyticMotive.rootSummary_unstableForwardCompactInterpretation_presheafFunctor_map
    (input : TraceLocalizationInput) :
    TraceAnalyticGeometricGenerator.presheafFunctor.map
        input.unstableForwardCompactInterpretation =
      input.map :=
  TraceAnalyticMotive.unstableForwardCompactInterpretation_presheafFunctor_map
    input

/-- Motive-root summary: right-composition after the forward compact interpretation has the expected trace hom. -/
theorem TraceAnalyticMotive.rootSummary_unstableForwardCompactInterpretation_comp_traceHom
    (input : TraceLocalizationInput)
    {target : TraceAnalyticGeometricGenerator}
    (tail : input.targetGenerator ⟶ target) :
    (input.unstableForwardCompactInterpretation ≫ tail).traceHom =
      input.traceHom ≫ tail.traceHom :=
  TraceAnalyticMotive.unstableForwardCompactInterpretation_comp_traceHom
    input
    tail

/-- Motive-root summary: left-composition before the forward compact interpretation has the expected trace hom. -/
theorem TraceAnalyticMotive.rootSummary_comp_unstableForwardCompactInterpretation_traceHom
    (input : TraceLocalizationInput)
    {source : TraceAnalyticGeometricGenerator}
    (lead : source ⟶ input.sourceGenerator) :
    (lead ≫ input.unstableForwardCompactInterpretation).traceHom =
      lead.traceHom ≫ input.traceHom :=
  TraceAnalyticMotive.comp_unstableForwardCompactInterpretation_traceHom
    input
    lead

/-- Motive-root summary: right-composition after the forward compact interpretation has the expected presheaf map. -/
theorem TraceAnalyticMotive.rootSummary_unstableForwardCompactInterpretation_comp_representableMap
    (input : TraceLocalizationInput)
    {target : TraceAnalyticGeometricGenerator}
    (tail : input.targetGenerator ⟶ target) :
    (input.unstableForwardCompactInterpretation ≫ tail).representableMap =
      input.map ≫ tail.representableMap :=
  TraceAnalyticMotive.unstableForwardCompactInterpretation_comp_representableMap
    input
    tail

/-- Motive-root summary: left-composition before the forward compact interpretation has the expected presheaf map. -/
theorem TraceAnalyticMotive.rootSummary_comp_unstableForwardCompactInterpretation_representableMap
    (input : TraceLocalizationInput)
    {source : TraceAnalyticGeometricGenerator}
    (lead : source ⟶ input.sourceGenerator) :
    (lead ≫ input.unstableForwardCompactInterpretation).representableMap =
      lead.representableMap ≫ input.map :=
  TraceAnalyticMotive.comp_unstableForwardCompactInterpretation_representableMap
    input
    lead

/-- Motive-root summary: right identity for the forward compact interpretation. -/
theorem TraceAnalyticMotive.rootSummary_unstableForwardCompactInterpretation_comp_id
    (input : TraceLocalizationInput) :
    input.unstableForwardCompactInterpretation ≫
        (𝟙 input.targetGenerator : input.targetGenerator ⟶ input.targetGenerator) =
      input.unstableForwardCompactInterpretation :=
  TraceAnalyticMotive.unstableForwardCompactInterpretation_comp_id
    input

/-- Motive-root summary: left identity for the forward compact interpretation. -/
theorem TraceAnalyticMotive.rootSummary_id_comp_unstableForwardCompactInterpretation
    (input : TraceLocalizationInput) :
    (𝟙 input.sourceGenerator : input.sourceGenerator ⟶ input.sourceGenerator) ≫
        input.unstableForwardCompactInterpretation =
      input.unstableForwardCompactInterpretation :=
  TraceAnalyticMotive.id_comp_unstableForwardCompactInterpretation
    input

/-- Motive-root summary: right identity preserves the forward interpretation trace hom. -/
theorem TraceAnalyticMotive.rootSummary_unstableForwardCompactInterpretation_comp_id_traceHom
    (input : TraceLocalizationInput) :
    (input.unstableForwardCompactInterpretation ≫
        (𝟙 input.targetGenerator : input.targetGenerator ⟶ input.targetGenerator)).traceHom =
      input.traceHom :=
  TraceAnalyticMotive.unstableForwardCompactInterpretation_comp_id_traceHom
    input

/-- Motive-root summary: left identity preserves the forward interpretation trace hom. -/
theorem TraceAnalyticMotive.rootSummary_id_comp_unstableForwardCompactInterpretation_traceHom
    (input : TraceLocalizationInput) :
    ((𝟙 input.sourceGenerator : input.sourceGenerator ⟶ input.sourceGenerator) ≫
        input.unstableForwardCompactInterpretation).traceHom =
      input.traceHom :=
  TraceAnalyticMotive.id_comp_unstableForwardCompactInterpretation_traceHom
    input

/-- Motive-root summary: associativity around the forward compact interpretation. -/
theorem TraceAnalyticMotive.rootSummary_unstableForwardCompactInterpretation_assoc
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

/-- Motive-root summary: trace-hom associativity around the forward compact interpretation. -/
theorem TraceAnalyticMotive.rootSummary_unstableForwardCompactInterpretation_assoc_traceHom
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

/-- Motive-root summary: presheaf-map associativity around the forward compact interpretation. -/
theorem TraceAnalyticMotive.rootSummary_unstableForwardCompactInterpretation_assoc_representableMap
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
