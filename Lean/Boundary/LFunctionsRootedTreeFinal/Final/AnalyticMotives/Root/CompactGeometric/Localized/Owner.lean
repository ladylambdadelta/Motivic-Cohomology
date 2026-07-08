import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Localized.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Localized.InputEndpoints.ComposablePairs.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Localized.InputEndpoints.Composition.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Localized.InputEndpoints.EndpointTransport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Localized.InputEndpoints.Functoriality.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Localized.InputEndpoints.Identities.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Localized.InputEndpoints.Linear.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Localized.InputEndpoints.UnitLaws.Owner

/-!
# Top-root compact-generator localized-word wrappers

This file mirrors motive-root localized-word object and identity facts under
`AnalyticMotivesRoot`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root localized-word object is the generator localized object. -/
theorem AnalyticMotivesRoot.compactGenerator_localizedWordObject_eq_localizedObject
    (generator : TraceAnalyticGeometricGenerator) :
    generator.localizedWordObject =
      generator.localizedObject :=
  TraceAnalyticMotive.compactGenerator_localizedWordObject_eq_localizedObject
    generator

/-- Top-root localized-word object is the wrapped trace object. -/
theorem AnalyticMotivesRoot.compactGenerator_localizedWordObject_eq_ofTraceObject
    (generator : TraceAnalyticGeometricGenerator) :
    generator.localizedWordObject =
      TraceLocalizedWordObject.ofTraceObject generator.traceObject :=
  TraceAnalyticMotive.compactGenerator_localizedWordObject_eq_ofTraceObject
    generator

/-- Top-root localized-word object underlying trace object wrapper. -/
theorem AnalyticMotivesRoot.compactGenerator_localizedWordObject_underlying
    (generator : TraceAnalyticGeometricGenerator) :
    generator.localizedWordObject.underlying =
      generator.traceObject :=
  TraceAnalyticMotive.compactGenerator_localizedWordObject_underlying
    generator

/-- Top-root localized-word object is obtained from the forgetful functor object. -/
theorem AnalyticMotivesRoot.compactGenerator_localizedWordObject_eq_forgetful_obj
    (generator : TraceAnalyticGeometricGenerator) :
    generator.localizedWordObject =
      TraceLocalizedWordObject.ofTraceObject
        (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj generator) :=
  TraceAnalyticMotive.compactGenerator_localizedWordObject_eq_forgetful_obj
    generator

/-- Top-root localized identity is the identity word class. -/
theorem AnalyticMotivesRoot.compactGenerator_localizedIdentity_eq_wordClass
    (generator : TraceAnalyticGeometricGenerator) :
    generator.localizedIdentity =
      TraceLocalizationWordClass.identity generator.traceObject :=
  TraceAnalyticMotive.compactGenerator_localizedIdentity_eq_wordClass
    generator

/-- Top-root localized identity is represented by the identity localization word. -/
theorem AnalyticMotivesRoot.compactGenerator_localizedIdentity_eq_ofWord
    (generator : TraceAnalyticGeometricGenerator) :
    generator.localizedIdentity =
      TraceLocalizationWordClass.ofWord
        (TraceLocalizationWord.identity generator.traceObject) :=
  TraceAnalyticMotive.compactGenerator_localizedIdentity_eq_ofWord
    generator

/-- Top-root localized identity representative has no localization atoms. -/
theorem AnalyticMotivesRoot.compactGenerator_localizedIdentity_representative_atomCount
    (generator : TraceAnalyticGeometricGenerator) :
    (TraceLocalizationWord.identity generator.traceObject).atomCount =
      0 :=
  TraceAnalyticMotive.compactGenerator_localizedIdentity_representative_atomCount
    generator

end AnalyticMotives
end LFunctions
end Boundary
