import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Morphisms.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Morphisms.Payload.Owner

/-!
# Top-root compact morphism wrappers

This file collects public root facades for compact geometric generator morphism
data.  The morphism facts expose the underlying trace-correspondence maps,
their representable images, and their lifted-Yoneda preimages.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root construction of a compact-generator morphism from a trace hom. -/
theorem AnalyticMotivesRoot.compactGenerator_ofTraceHom_traceHom
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source.traceObject ⟶ target.traceObject) :
    (TraceAnalyticGeometricGenerator.Hom.ofTraceHom morphism).traceHom =
      morphism :=
  TraceAnalyticMotive.compactGenerator_ofTraceHom_traceHom
    morphism

/-- Top-root trace hom projection of a compact-generator morphism. -/
theorem AnalyticMotivesRoot.compactGenerator_traceHom_eq_self
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.traceHom =
      morphism :=
  TraceAnalyticMotive.compactGenerator_traceHom_eq_self
    morphism

/-- Top-root identity compact-generator morphism is trace identity. -/
theorem AnalyticMotivesRoot.compactGenerator_id_eq_trace_id
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticGeometricGenerator.id generator =
      𝟙 generator.traceObject :=
  TraceAnalyticMotive.compactGenerator_id_eq_trace_id
    generator

/-- Top-root compact-generator composition is trace composition. -/
theorem AnalyticMotivesRoot.compactGenerator_comp_eq_trace_comp
    {first second third : TraceAnalyticGeometricGenerator}
    (left : TraceAnalyticGeometricGenerator.Hom first second)
    (right : TraceAnalyticGeometricGenerator.Hom second third) :
    TraceAnalyticGeometricGenerator.comp left right =
      left ≫ right :=
  TraceAnalyticMotive.compactGenerator_comp_eq_trace_comp
    left
    right

/-- Top-root compact morphism induces the representable map of its trace hom. -/
theorem AnalyticMotivesRoot.compactGenerator_representableMap_eq
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.representableMap =
      TraceCorQPresheaf.representableMap morphism.traceHom :=
  TraceAnalyticMotive.compactGenerator_representableMap_eq
    morphism

/-- Top-root compact morphism induces the lifted-Yoneda map of its trace hom. -/
theorem AnalyticMotivesRoot.compactGenerator_representableObjectMap_eq
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.representableObjectMap =
      (TraceCorQRepresentablePresheaf.yoneda).map morphism.traceHom :=
  TraceAnalyticMotive.compactGenerator_representableObjectMap_eq
    morphism

/-- Top-root inclusion of the lifted map is the representable presheaf map. -/
theorem AnalyticMotivesRoot.compactGenerator_representableObjectMap_inclusion
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    TraceCorQRepresentablePresheaf.inclusion.map
        morphism.representableObjectMap =
      morphism.representableMap :=
  TraceAnalyticMotive.compactGenerator_representableObjectMap_inclusion
    morphism

/-- Top-root lifted-Yoneda preimage recovers the compact morphism trace hom. -/
theorem AnalyticMotivesRoot.compactGenerator_yonedaPreimage_representableObjectMap
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    TraceCorQRepresentablePresheaf.yonedaPreimage
        morphism.representableObjectMap =
      morphism.traceHom :=
  TraceAnalyticMotive.compactGenerator_yonedaPreimage_representableObjectMap
    morphism

end AnalyticMotives
end LFunctions
end Boundary
