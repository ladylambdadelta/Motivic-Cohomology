import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Summary.ForwardInterpretation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Localization.Representatives.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.RewriteMaps.Owner

/-!
# Motive-root representative summaries

This file exposes root summary theorems for one-atom localization
representatives, inverse inputs, rewrite-map recovery, and compact evaluation.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root summary: the unstable forward representative has one atom. -/
theorem TraceAnalyticMotive.rootSummary_unstableForward_representative_atomCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationWord.ofInputForward input).atomCount =
      0 + 1 :=
  TraceAnalyticMotive.unstableForward_representative_atomCount
    input

/-- Motive-root summary: unstable inverse is the inverse input word class. -/
theorem TraceAnalyticMotive.rootSummary_unstableInverse_eq_wordClass
    (input : TraceLocalizationInput) :
    input.unstableInverse =
      TraceLocalizationWordClass.ofInputInverse input :=
  TraceAnalyticMotive.unstableInverse_eq_wordClass
    input

/-- Motive-root summary: unstable inverse is represented by the inverse input word. -/
theorem TraceAnalyticMotive.rootSummary_unstableInverse_eq_ofWord
    (input : TraceLocalizationInput) :
    input.unstableInverse =
      TraceLocalizationWordClass.ofWord
        (TraceLocalizationWord.ofInputInverse input) :=
  TraceAnalyticMotive.unstableInverse_eq_ofWord
    input

/-- Motive-root summary: the unstable inverse representative has one atom. -/
theorem TraceAnalyticMotive.rootSummary_unstableInverse_representative_atomCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationWord.ofInputInverse input).atomCount =
      0 + 1 :=
  TraceAnalyticMotive.unstableInverse_representative_atomCount
    input

/-- Motive-root summary: descent-channel localization hom has a one-atom representative. -/
theorem TraceAnalyticMotive.rootSummary_descentChannel_hom_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputForward
      (TraceLocalizationInput.descentChannel source target)).atomCount =
      0 + 1 :=
  TraceAnalyticMotive.descentChannelIso_hom_localizationSummary_atomCount
    source
    target

/-- Motive-root summary: a one-step rewrite representable map recovers its trace hom. -/
theorem TraceAnalyticMotive.rootSummary_rewriteRepresentableMap_preimage
    (generator : TraceRewriteGenerator) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticMotive.rewriteRepresentableMap generator) =
      TraceAnalyticMotive.rewriteTraceHom generator :=
  TraceAnalyticMotive.rewriteRepresentableMap_preimage
    generator

/-- Motive-root summary: compact generator evaluation is evaluation at its trace object. -/
theorem TraceAnalyticMotive.rootSummary_compactGenerator_evaluation_obj
    (generator : TraceAnalyticGeometricGenerator)
    (presheaf : TraceCorQPresheaf) :
    generator.evaluation.obj presheaf =
      generator.sections presheaf :=
  TraceAnalyticMotive.compactGenerator_evaluation_obj
    generator
    presheaf

end AnalyticMotives
end LFunctions
end Boundary
