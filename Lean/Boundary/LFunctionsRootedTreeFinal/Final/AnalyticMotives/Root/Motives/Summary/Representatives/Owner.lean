import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Summary.Representatives.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Motives.Summary.ForwardInterpretation.Owner

/-!
# Top-root representative summaries

This file exposes one-atom localization representatives, inverse inputs,
rewrite-map recovery, and compact evaluation under the public root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public motive summary: the unstable forward representative has one atom. -/
theorem AnalyticMotivesRoot.rootSummary_unstableForward_representative_atomCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationWord.ofInputForward input).atomCount =
      0 + 1 :=
  TraceAnalyticMotive.rootSummary_unstableForward_representative_atomCount
    input

/-- Public motive summary: unstable inverse is the inverse input word class. -/
theorem AnalyticMotivesRoot.rootSummary_unstableInverse_eq_wordClass
    (input : TraceLocalizationInput) :
    input.unstableInverse =
      TraceLocalizationWordClass.ofInputInverse input :=
  TraceAnalyticMotive.rootSummary_unstableInverse_eq_wordClass
    input

/-- Public motive summary: unstable inverse is represented by the inverse input word. -/
theorem AnalyticMotivesRoot.rootSummary_unstableInverse_eq_ofWord
    (input : TraceLocalizationInput) :
    input.unstableInverse =
      TraceLocalizationWordClass.ofWord
        (TraceLocalizationWord.ofInputInverse input) :=
  TraceAnalyticMotive.rootSummary_unstableInverse_eq_ofWord
    input

/-- Public motive summary: the unstable inverse representative has one atom. -/
theorem AnalyticMotivesRoot.rootSummary_unstableInverse_representative_atomCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationWord.ofInputInverse input).atomCount =
      0 + 1 :=
  TraceAnalyticMotive.rootSummary_unstableInverse_representative_atomCount
    input

/-- Public motive summary: descent-channel localization hom has a one-atom representative. -/
theorem AnalyticMotivesRoot.rootSummary_descentChannel_hom_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputForward
      (TraceLocalizationInput.descentChannel source target)).atomCount =
      0 + 1 :=
  TraceAnalyticMotive.rootSummary_descentChannel_hom_atomCount
    source
    target

/-- Public motive summary: a one-step rewrite representable map recovers its trace hom. -/
theorem AnalyticMotivesRoot.rootSummary_rewriteRepresentableMap_preimage
    (generator : TraceRewriteGenerator) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticMotive.rewriteRepresentableMap generator) =
      TraceAnalyticMotive.rewriteTraceHom generator :=
  TraceAnalyticMotive.rootSummary_rewriteRepresentableMap_preimage
    generator

/-- Public motive summary: compact generator evaluation returns sections. -/
theorem AnalyticMotivesRoot.rootSummary_compactGenerator_evaluation_obj
    (generator : TraceAnalyticGeometricGenerator)
    (presheaf : TraceCorQPresheaf) :
    generator.evaluation.obj presheaf =
      generator.sections presheaf :=
  TraceAnalyticMotive.rootSummary_compactGenerator_evaluation_obj
    generator
    presheaf

end AnalyticMotives
end LFunctions
end Boundary
