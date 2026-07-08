import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Summary.ForwardInterpretation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Motives.Summary.UnstablePayload.Owner

/-!
# Top-root forward compact interpretation summaries

This file exposes unstable forward word classes and their compact-generator
interpretations under the public analytic-motives root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public motive summary: unstable forward is the forward input word class. -/
theorem AnalyticMotivesRoot.rootSummary_unstableForward_eq_wordClass
    (input : TraceLocalizationInput) :
    input.unstableForward =
      TraceLocalizationWordClass.ofInputForward input :=
  TraceAnalyticMotive.rootSummary_unstableForward_eq_wordClass
    input

/-- Public motive summary: unstable forward is represented by the forward input word. -/
theorem AnalyticMotivesRoot.rootSummary_unstableForward_eq_ofWord
    (input : TraceLocalizationInput) :
    input.unstableForward =
      TraceLocalizationWordClass.ofWord
        (TraceLocalizationWord.ofInputForward input) :=
  TraceAnalyticMotive.rootSummary_unstableForward_eq_ofWord
    input

/-- Public motive summary: the forward compact interpretation is the input generator hom. -/
theorem AnalyticMotivesRoot.rootSummary_unstableForwardCompactInterpretation_eq_generatorHom
    (input : TraceLocalizationInput) :
    input.unstableForwardCompactInterpretation =
      input.generatorHom :=
  TraceAnalyticMotive.rootSummary_unstableForwardCompactInterpretation_eq_generatorHom
    input

/-- Public motive summary: the forward compact interpretation has the input trace hom. -/
theorem AnalyticMotivesRoot.rootSummary_unstableForwardCompactInterpretation_traceHom
    (input : TraceLocalizationInput) :
    input.unstableForwardCompactInterpretation.traceHom =
      input.traceHom :=
  TraceAnalyticMotive.rootSummary_unstableForwardCompactInterpretation_traceHom
    input

/-- Public motive summary: the forward compact interpretation induces the input map. -/
theorem AnalyticMotivesRoot.rootSummary_unstableForwardCompactInterpretation_representableMap
    (input : TraceLocalizationInput) :
    input.unstableForwardCompactInterpretation.representableMap =
      input.map :=
  TraceAnalyticMotive.rootSummary_unstableForwardCompactInterpretation_representableMap
    input

/-- Public motive summary: the compact presheaf functor sends the forward interpretation to the input map. -/
theorem AnalyticMotivesRoot.rootSummary_unstableForwardCompactInterpretation_presheafFunctor_map
    (input : TraceLocalizationInput) :
    TraceAnalyticGeometricGenerator.presheafFunctor.map
        input.unstableForwardCompactInterpretation =
      input.map :=
  TraceAnalyticMotive.rootSummary_unstableForwardCompactInterpretation_presheafFunctor_map
    input

/-- Public motive summary: right-composition after the forward compact interpretation has the expected trace hom. -/
theorem AnalyticMotivesRoot.rootSummary_unstableForwardCompactInterpretation_comp_traceHom
    (input : TraceLocalizationInput)
    {target : TraceAnalyticGeometricGenerator}
    (tail : input.targetGenerator ⟶ target) :
    (input.unstableForwardCompactInterpretation ≫ tail).traceHom =
      input.traceHom ≫ tail.traceHom :=
  TraceAnalyticMotive.rootSummary_unstableForwardCompactInterpretation_comp_traceHom
    input
    tail

/-- Public motive summary: left-composition before the forward compact interpretation has the expected trace hom. -/
theorem AnalyticMotivesRoot.rootSummary_comp_unstableForwardCompactInterpretation_traceHom
    (input : TraceLocalizationInput)
    {source : TraceAnalyticGeometricGenerator}
    (lead : source ⟶ input.sourceGenerator) :
    (lead ≫ input.unstableForwardCompactInterpretation).traceHom =
      lead.traceHom ≫ input.traceHom :=
  TraceAnalyticMotive.rootSummary_comp_unstableForwardCompactInterpretation_traceHom
    input
    lead

/-- Public motive summary: right-composition after the forward compact interpretation has the expected presheaf map. -/
theorem AnalyticMotivesRoot.rootSummary_unstableForwardCompactInterpretation_comp_representableMap
    (input : TraceLocalizationInput)
    {target : TraceAnalyticGeometricGenerator}
    (tail : input.targetGenerator ⟶ target) :
    (input.unstableForwardCompactInterpretation ≫ tail).representableMap =
      input.map ≫ tail.representableMap :=
  TraceAnalyticMotive.rootSummary_unstableForwardCompactInterpretation_comp_representableMap
    input
    tail

/-- Public motive summary: left-composition before the forward compact interpretation has the expected presheaf map. -/
theorem AnalyticMotivesRoot.rootSummary_comp_unstableForwardCompactInterpretation_representableMap
    (input : TraceLocalizationInput)
    {source : TraceAnalyticGeometricGenerator}
    (lead : source ⟶ input.sourceGenerator) :
    (lead ≫ input.unstableForwardCompactInterpretation).representableMap =
      lead.representableMap ≫ input.map :=
  TraceAnalyticMotive.rootSummary_comp_unstableForwardCompactInterpretation_representableMap
    input
    lead

/-- Public motive summary: right identity for the forward compact interpretation. -/
theorem AnalyticMotivesRoot.rootSummary_unstableForwardCompactInterpretation_comp_id
    (input : TraceLocalizationInput) :
    input.unstableForwardCompactInterpretation ≫
        (𝟙 input.targetGenerator : input.targetGenerator ⟶ input.targetGenerator) =
      input.unstableForwardCompactInterpretation :=
  TraceAnalyticMotive.rootSummary_unstableForwardCompactInterpretation_comp_id
    input

/-- Public motive summary: left identity for the forward compact interpretation. -/
theorem AnalyticMotivesRoot.rootSummary_id_comp_unstableForwardCompactInterpretation
    (input : TraceLocalizationInput) :
    (𝟙 input.sourceGenerator : input.sourceGenerator ⟶ input.sourceGenerator) ≫
        input.unstableForwardCompactInterpretation =
      input.unstableForwardCompactInterpretation :=
  TraceAnalyticMotive.rootSummary_id_comp_unstableForwardCompactInterpretation
    input

/-- Public motive summary: right identity preserves the forward interpretation trace hom. -/
theorem AnalyticMotivesRoot.rootSummary_unstableForwardCompactInterpretation_comp_id_traceHom
    (input : TraceLocalizationInput) :
    (input.unstableForwardCompactInterpretation ≫
        (𝟙 input.targetGenerator : input.targetGenerator ⟶ input.targetGenerator)).traceHom =
      input.traceHom :=
  TraceAnalyticMotive.rootSummary_unstableForwardCompactInterpretation_comp_id_traceHom
    input

/-- Public motive summary: left identity preserves the forward interpretation trace hom. -/
theorem AnalyticMotivesRoot.rootSummary_id_comp_unstableForwardCompactInterpretation_traceHom
    (input : TraceLocalizationInput) :
    ((𝟙 input.sourceGenerator : input.sourceGenerator ⟶ input.sourceGenerator) ≫
        input.unstableForwardCompactInterpretation).traceHom =
      input.traceHom :=
  TraceAnalyticMotive.rootSummary_id_comp_unstableForwardCompactInterpretation_traceHom
    input

/-- Public motive summary: associativity around the forward compact interpretation. -/
theorem AnalyticMotivesRoot.rootSummary_unstableForwardCompactInterpretation_assoc
    (input : TraceLocalizationInput)
    {source target : TraceAnalyticGeometricGenerator}
    (lead : source ⟶ input.sourceGenerator)
    (tail : input.targetGenerator ⟶ target) :
    (lead ≫ input.unstableForwardCompactInterpretation) ≫ tail =
      lead ≫ (input.unstableForwardCompactInterpretation ≫ tail) :=
  TraceAnalyticMotive.rootSummary_unstableForwardCompactInterpretation_assoc
    input
    lead
    tail

/-- Public motive summary: trace-hom associativity around the forward compact interpretation. -/
theorem AnalyticMotivesRoot.rootSummary_unstableForwardCompactInterpretation_assoc_traceHom
    (input : TraceLocalizationInput)
    {source target : TraceAnalyticGeometricGenerator}
    (lead : source ⟶ input.sourceGenerator)
    (tail : input.targetGenerator ⟶ target) :
    ((lead ≫ input.unstableForwardCompactInterpretation) ≫ tail).traceHom =
      (lead ≫ (input.unstableForwardCompactInterpretation ≫ tail)).traceHom :=
  TraceAnalyticMotive.rootSummary_unstableForwardCompactInterpretation_assoc_traceHom
    input
    lead
    tail

/-- Public motive summary: presheaf-map associativity around the forward compact interpretation. -/
theorem AnalyticMotivesRoot.rootSummary_unstableForwardCompactInterpretation_assoc_representableMap
    (input : TraceLocalizationInput)
    {source target : TraceAnalyticGeometricGenerator}
    (lead : source ⟶ input.sourceGenerator)
    (tail : input.targetGenerator ⟶ target) :
    ((lead ≫ input.unstableForwardCompactInterpretation) ≫ tail).representableMap =
      (lead ≫ (input.unstableForwardCompactInterpretation ≫ tail)).representableMap :=
  TraceAnalyticMotive.rootSummary_unstableForwardCompactInterpretation_assoc_representableMap
    input
    lead
    tail

end AnalyticMotives
end LFunctions
end Boundary
