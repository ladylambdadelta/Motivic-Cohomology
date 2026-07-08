import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Functors.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Functors.Forgetful.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Functors.Presheaf.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Functors.Yoneda.Owner

/-!
# Top-root compact-generator functor wrappers

This file collects top-root facades for the compact-generator forgetful,
presheaf, lifted representable, and Yoneda comparison functors.  The aggregate
surface records how compact morphisms are seen by each functor.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root aggregate forgetful functor sends a compact generator to its trace object. -/
theorem AnalyticMotivesRoot.compactGenerator_functorSummary_forgetful_obj
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticGeometricGenerator.forgetfulFunctor.obj generator =
      generator.traceObject :=
  TraceAnalyticMotive.compactGenerator_functorSummary_forgetful_obj
    generator

/-- Top-root aggregate forgetful functor sends a compact morphism to its trace hom. -/
theorem AnalyticMotivesRoot.compactGenerator_functorSummary_forgetful_map
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.forgetfulFunctor.map morphism =
      morphism.traceHom :=
  TraceAnalyticMotive.compactGenerator_functorSummary_forgetful_map
    morphism

/-- Top-root aggregate presheaf functor sends a compact morphism to its representable map. -/
theorem AnalyticMotivesRoot.compactGenerator_functorSummary_presheaf_map
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.presheafFunctor.map morphism =
      morphism.representableMap :=
  TraceAnalyticMotive.compactGenerator_functorSummary_presheaf_map
    morphism

/-- Top-root aggregate lifted representable functor sends a compact morphism to its lifted map. -/
theorem AnalyticMotivesRoot.compactGenerator_functorSummary_representableObject_map
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.representableObjectFunctor.map morphism =
      morphism.representableObjectMap :=
  TraceAnalyticMotive.compactGenerator_functorSummary_representableObject_map
    morphism

/-- Top-root aggregate Yoneda preimage recovers a compact morphism from its lifted map. -/
theorem AnalyticMotivesRoot.compactGenerator_functorSummary_yonedaPreimage
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.yonedaPreimage
        morphism.representableObjectMap =
      morphism :=
  TraceAnalyticMotive.compactGenerator_functorSummary_yonedaPreimage
    morphism

end AnalyticMotives
end LFunctions
end Boundary
