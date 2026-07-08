import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Localized.InputEndpoints.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Localized.InputEndpoints.ComposablePairs.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Localized.InputEndpoints.Composition.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Localized.InputEndpoints.EndpointTransport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Localized.InputEndpoints.Functoriality.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Localized.InputEndpoints.Identities.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Localized.InputEndpoints.Linear.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Localized.InputEndpoints.UnitLaws.Owner

/-!
# Motive-root compact-generator localized-word wrappers

This file mirrors the localized-word object and identity facts attached to
compact geometric analytic generators under `TraceAnalyticMotive`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root localized-word object is the generator localized object. -/
theorem TraceAnalyticMotive.compactGenerator_localizedWordObject_eq_localizedObject
    (generator : TraceAnalyticGeometricGenerator) :
    generator.localizedWordObject =
      generator.localizedObject :=
  TraceAnalyticGeometricGenerator.localizedWordObject_eq_localizedObject
    generator

/-- Motive-root localized-word object is the wrapped trace object. -/
theorem TraceAnalyticMotive.compactGenerator_localizedWordObject_eq_ofTraceObject
    (generator : TraceAnalyticGeometricGenerator) :
    generator.localizedWordObject =
      TraceLocalizedWordObject.ofTraceObject generator.traceObject :=
  TraceAnalyticGeometricGenerator.localizedWordObject_eq_ofTraceObject
    generator

/-- Motive-root localized-word object underlying trace object wrapper. -/
theorem TraceAnalyticMotive.compactGenerator_localizedWordObject_underlying
    (generator : TraceAnalyticGeometricGenerator) :
    generator.localizedWordObject.underlying =
      generator.traceObject :=
  TraceAnalyticGeometricGenerator.localizedWordObject_underlying
    generator

/-- Motive-root localized-word object is obtained from the forgetful functor object. -/
theorem TraceAnalyticMotive.compactGenerator_localizedWordObject_eq_forgetful_obj
    (generator : TraceAnalyticGeometricGenerator) :
    generator.localizedWordObject =
      TraceLocalizedWordObject.ofTraceObject
        (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj generator) :=
  TraceAnalyticGeometricGenerator.localizedWordObject_eq_forgetful_obj
    generator

/-- Motive-root localized identity is the identity word class. -/
theorem TraceAnalyticMotive.compactGenerator_localizedIdentity_eq_wordClass
    (generator : TraceAnalyticGeometricGenerator) :
    generator.localizedIdentity =
      TraceLocalizationWordClass.identity generator.traceObject :=
  TraceAnalyticGeometricGenerator.localizedIdentity_eq_wordClass
    generator

/-- Motive-root localized identity is represented by the identity localization word. -/
theorem TraceAnalyticMotive.compactGenerator_localizedIdentity_eq_ofWord
    (generator : TraceAnalyticGeometricGenerator) :
    generator.localizedIdentity =
      TraceLocalizationWordClass.ofWord
        (TraceLocalizationWord.identity generator.traceObject) :=
  TraceAnalyticGeometricGenerator.localizedIdentity_eq_ofWord
    generator

/-- Motive-root localized identity representative has no localization atoms. -/
theorem TraceAnalyticMotive.compactGenerator_localizedIdentity_representative_atomCount
    (generator : TraceAnalyticGeometricGenerator) :
    (TraceLocalizationWord.identity generator.traceObject).atomCount =
      0 :=
  TraceAnalyticGeometricGenerator.localizedIdentity_representative_atomCount
    generator

end AnalyticMotives
end LFunctions
end Boundary
