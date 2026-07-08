import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Owner

/-!
# Compact generators in the unstable analytic-motive envelope

This file connects compact geometric analytic generators to the current
unstable envelope.  The construction is object-level: a compact generator
already carries a certified trace object, hence an object of the localized-word
category.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The unstable analytic motive attached to a compact geometric generator. -/
def TraceAnalyticGeometricGenerator.unstableMotive
    (generator : TraceAnalyticGeometricGenerator) :
    TraceUnstableAnalyticMotive :=
  TraceUnstableAnalyticMotive.ofTraceObject generator.traceObject

/-- The compact generator's unstable motive is its localized-word object. -/
theorem TraceAnalyticGeometricGenerator.unstableMotive_eq_localizedWordObject
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableMotive =
      generator.localizedWordObject :=
  rfl

/-- The compact generator's unstable motive is the wrapped trace object. -/
theorem TraceAnalyticGeometricGenerator.unstableMotive_eq_ofTraceObject
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableMotive =
      TraceUnstableAnalyticMotive.ofTraceObject generator.traceObject :=
  rfl

/-- The compact generator's unstable motive has the generator trace object underneath. -/
theorem TraceAnalyticGeometricGenerator.unstableMotive_underlying
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableMotive.underlying =
      generator.traceObject :=
  TraceUnstableAnalyticMotive.ofTraceObject_underlying
    generator.traceObject

/-- The identity of a compact generator in the unstable envelope. -/
def TraceAnalyticGeometricGenerator.unstableIdentity
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableMotive ⟶ generator.unstableMotive :=
  𝟙 generator.unstableMotive

/-- The unstable identity is the compact generator's localized identity. -/
theorem TraceAnalyticGeometricGenerator.unstableIdentity_eq_localizedIdentity
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableIdentity =
      generator.localizedIdentity :=
  rfl

/-- The unstable identity is the category identity on the attached unstable motive. -/
theorem TraceAnalyticGeometricGenerator.unstableIdentity_eq_categoryIdentity
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableIdentity =
      (𝟙 generator.unstableMotive :
        TraceUnstableAnalyticMotiveHom
          generator.unstableMotive
          generator.unstableMotive) :=
  rfl

/-- The unstable identity is the identity localization word class. -/
theorem TraceAnalyticGeometricGenerator.unstableIdentity_eq_wordClass
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableIdentity =
      TraceLocalizationWordClass.identity generator.traceObject :=
  rfl

/-- The unstable identity is the identity word class of the unstable underlying object. -/
theorem TraceAnalyticGeometricGenerator.unstableIdentity_eq_underlyingWordClass
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableIdentity =
      TraceLocalizationWordClass.identity
        generator.unstableMotive.underlying :=
  TraceUnstableAnalyticMotive.id_eq
    generator.unstableMotive

/-- The unstable identity is represented by the identity localization word. -/
theorem TraceAnalyticGeometricGenerator.unstableIdentity_eq_ofWord
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableIdentity =
      TraceLocalizationWordClass.ofWord
        (TraceLocalizationWord.identity generator.traceObject) :=
  rfl

/-- The chosen representative of the unstable identity has no localization atoms. -/
theorem TraceAnalyticGeometricGenerator.unstableIdentity_representative_atomCount
    (generator : TraceAnalyticGeometricGenerator) :
    (TraceLocalizationWord.identity generator.traceObject).atomCount =
      0 :=
  TraceAnalyticGeometricGenerator.localizedIdentity_representative_atomCount
    generator

end AnalyticMotives
end LFunctions
end Boundary
