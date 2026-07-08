import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Functors.Forgetful.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Functors.Presheaf.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Functors.Yoneda.Owner

/-!
# Motive-root compact-generator functor wrappers

This file collects motive-root facades for the compact-generator forgetful,
presheaf, lifted representable, and Yoneda comparison functors.  The aggregate
surface records how compact morphisms are seen by each functor.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root aggregate forgetful functor sends a compact generator to its trace object. -/
theorem TraceAnalyticMotive.compactGenerator_functorSummary_forgetful_obj
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticGeometricGenerator.forgetfulFunctor.obj generator =
      generator.traceObject :=
  TraceAnalyticMotive.compactGenerator_forgetfulFunctor_obj
    generator

/-- Motive-root aggregate forgetful functor sends a compact morphism to its trace hom. -/
theorem TraceAnalyticMotive.compactGenerator_functorSummary_forgetful_map
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.forgetfulFunctor.map morphism =
      morphism.traceHom :=
  TraceAnalyticMotive.compactGenerator_forgetfulFunctor_map
    morphism

/-- Motive-root aggregate presheaf functor sends a compact morphism to its representable map. -/
theorem TraceAnalyticMotive.compactGenerator_functorSummary_presheaf_map
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.presheafFunctor.map morphism =
      morphism.representableMap :=
  TraceAnalyticMotive.compactGenerator_presheafFunctor_map
    morphism

/-- Motive-root aggregate lifted representable functor sends a compact morphism to its lifted map. -/
theorem TraceAnalyticMotive.compactGenerator_functorSummary_representableObject_map
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.representableObjectFunctor.map morphism =
      morphism.representableObjectMap :=
  TraceAnalyticMotive.compactGenerator_representableObjectFunctor_map
    morphism

/-- Motive-root aggregate Yoneda preimage recovers a compact morphism from its lifted map. -/
theorem TraceAnalyticMotive.compactGenerator_functorSummary_yonedaPreimage
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.yonedaPreimage
        morphism.representableObjectMap =
      morphism :=
  TraceAnalyticMotive.compactGenerator_yonedaPreimage_representableObjectMap
    morphism

end AnalyticMotives
end LFunctions
end Boundary
