import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Morphisms.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Morphisms.Payload.Owner

/-!
# Motive-root compact morphism wrappers

This file collects motive-root facades for compact geometric generator
morphism data.  The morphisms are the trace correspondences between the
underlying certified trace objects.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root construction of a compact-generator morphism from a trace hom. -/
theorem TraceAnalyticMotive.compactGenerator_ofTraceHom_traceHom
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source.traceObject ⟶ target.traceObject) :
    (TraceAnalyticGeometricGenerator.Hom.ofTraceHom morphism).traceHom =
      morphism :=
  TraceAnalyticGeometricGenerator.Hom.ofTraceHom_traceHom
    morphism

/-- Motive-root trace hom projection of a compact-generator morphism. -/
theorem TraceAnalyticMotive.compactGenerator_traceHom_eq_self
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.traceHom =
      morphism :=
  TraceAnalyticGeometricGenerator.Hom.traceHom_eq_self
    morphism

/-- Motive-root identity compact-generator morphism is trace identity. -/
theorem TraceAnalyticMotive.compactGenerator_id_eq_trace_id
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticGeometricGenerator.id generator =
      𝟙 generator.traceObject :=
  TraceAnalyticGeometricGenerator.id_eq_trace_id
    generator

/-- Motive-root compact-generator composition is trace composition. -/
theorem TraceAnalyticMotive.compactGenerator_comp_eq_trace_comp
    {first second third : TraceAnalyticGeometricGenerator}
    (left : TraceAnalyticGeometricGenerator.Hom first second)
    (right : TraceAnalyticGeometricGenerator.Hom second third) :
    TraceAnalyticGeometricGenerator.comp left right =
      left ≫ right :=
  TraceAnalyticGeometricGenerator.comp_eq_trace_comp
    left
    right

/-- Motive-root compact morphism induces the representable map of its trace hom. -/
theorem TraceAnalyticMotive.compactGenerator_representableMap_eq
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.representableMap =
      TraceCorQPresheaf.representableMap morphism.traceHom :=
  TraceAnalyticGeometricGenerator.Hom.representableMap_eq
    morphism

/-- Motive-root compact morphism induces the lifted-Yoneda map of its trace hom. -/
theorem TraceAnalyticMotive.compactGenerator_representableObjectMap_eq
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.representableObjectMap =
      (TraceCorQRepresentablePresheaf.yoneda).map morphism.traceHom :=
  TraceAnalyticGeometricGenerator.Hom.representableObjectMap_eq
    morphism

/-- Motive-root inclusion of the lifted map is the representable presheaf map. -/
theorem TraceAnalyticMotive.compactGenerator_representableObjectMap_inclusion
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    TraceCorQRepresentablePresheaf.inclusion.map
        morphism.representableObjectMap =
      morphism.representableMap :=
  TraceAnalyticGeometricGenerator.Hom.representableObjectMap_inclusion
    morphism

/-- Motive-root lifted-Yoneda preimage recovers the compact morphism trace hom. -/
theorem TraceAnalyticMotive.compactGenerator_yonedaPreimage_representableObjectMap
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    TraceCorQRepresentablePresheaf.yonedaPreimage
        morphism.representableObjectMap =
      morphism.traceHom :=
  TraceAnalyticGeometricGenerator.Hom.yonedaPreimage_representableObjectMap
    morphism

end AnalyticMotives
end LFunctions
end Boundary
