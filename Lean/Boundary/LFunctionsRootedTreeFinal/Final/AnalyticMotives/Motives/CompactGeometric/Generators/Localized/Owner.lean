import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Functors.Forgetful.Owner

/-!
# Localized objects attached to compact geometric analytic generators

This file records the object-level bridge from compact analytic generators to
the formal localized-word category.  A compact generator determines a localized
word object by wrapping its underlying certified trace object.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The localized-word object attached to a compact analytic generator. -/
def TraceAnalyticGeometricGenerator.localizedWordObject
    (generator : TraceAnalyticGeometricGenerator) :
    TraceLocalizedWordObject :=
  generator.localizedObject

/-- The localized-word object is the localized object already carried by the generator. -/
theorem TraceAnalyticGeometricGenerator.localizedWordObject_eq_localizedObject
    (generator : TraceAnalyticGeometricGenerator) :
    generator.localizedWordObject =
      generator.localizedObject :=
  rfl

/-- The localized-word object is the wrapped underlying trace object. -/
theorem TraceAnalyticGeometricGenerator.localizedWordObject_eq_ofTraceObject
    (generator : TraceAnalyticGeometricGenerator) :
    generator.localizedWordObject =
      TraceLocalizedWordObject.ofTraceObject generator.traceObject :=
  rfl

/-- The localized-word object has the generator trace object as underlying object. -/
theorem TraceAnalyticGeometricGenerator.localizedWordObject_underlying
    (generator : TraceAnalyticGeometricGenerator) :
    generator.localizedWordObject.underlying =
      generator.traceObject :=
  rfl

/-- The localized-word object is obtained by wrapping the forgetful functor object. -/
theorem TraceAnalyticGeometricGenerator.localizedWordObject_eq_forgetful_obj
    (generator : TraceAnalyticGeometricGenerator) :
    generator.localizedWordObject =
      TraceLocalizedWordObject.ofTraceObject
        (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj generator) :=
  rfl

/-- The identity localized word on a compact generator's localized object. -/
def TraceAnalyticGeometricGenerator.localizedIdentity
    (generator : TraceAnalyticGeometricGenerator) :
    generator.localizedWordObject ⟶ generator.localizedWordObject :=
  𝟙 generator.localizedWordObject

/-- The localized identity is the identity word class of the underlying trace object. -/
theorem TraceAnalyticGeometricGenerator.localizedIdentity_eq_wordClass
    (generator : TraceAnalyticGeometricGenerator) :
    generator.localizedIdentity =
      TraceLocalizationWordClass.identity generator.traceObject :=
  rfl

/-- The localized identity is represented by the identity localization word. -/
theorem TraceAnalyticGeometricGenerator.localizedIdentity_eq_ofWord
    (generator : TraceAnalyticGeometricGenerator) :
    generator.localizedIdentity =
      TraceLocalizationWordClass.ofWord
        (TraceLocalizationWord.identity generator.traceObject) :=
  rfl

/-- The chosen representative of the localized identity has no localization atoms. -/
theorem TraceAnalyticGeometricGenerator.localizedIdentity_representative_atomCount
    (generator : TraceAnalyticGeometricGenerator) :
    (TraceLocalizationWord.identity generator.traceObject).atomCount =
      0 :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
