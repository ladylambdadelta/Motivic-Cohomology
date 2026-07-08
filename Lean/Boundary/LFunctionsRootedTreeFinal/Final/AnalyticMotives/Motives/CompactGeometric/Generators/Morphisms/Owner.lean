import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Owner

/-!
# Morphisms of compact geometric analytic generators

This file records the concrete morphisms available between compact analytic
generators before any stable closure: they are exactly trace correspondences
between the underlying certified trace objects, with their induced
representable-presheaf maps.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open scoped CategoryTheory

/-- Morphisms between compact analytic generators are trace correspondences. -/
abbrev TraceAnalyticGeometricGenerator.Hom
    (source target : TraceAnalyticGeometricGenerator) :=
  source.traceObject ⟶ target.traceObject

/-- The identity morphism of a compact analytic generator. -/
def TraceAnalyticGeometricGenerator.id
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticGeometricGenerator.Hom generator generator :=
  𝟙 generator.traceObject

/-- Composition of compact analytic generator morphisms. -/
def TraceAnalyticGeometricGenerator.comp
    {first second third : TraceAnalyticGeometricGenerator}
    (left : TraceAnalyticGeometricGenerator.Hom first second)
    (right : TraceAnalyticGeometricGenerator.Hom second third) :
    TraceAnalyticGeometricGenerator.Hom first third :=
  left ≫ right

/-- Build a compact-generator morphism from a trace correspondence. -/
def TraceAnalyticGeometricGenerator.Hom.ofTraceHom
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source.traceObject ⟶ target.traceObject) :
    TraceAnalyticGeometricGenerator.Hom source target :=
  morphism

/-- The underlying trace correspondence of a compact-generator morphism. -/
def TraceAnalyticGeometricGenerator.Hom.traceHom
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    source.traceObject ⟶ target.traceObject :=
  morphism

/-- Constructing a compact-generator morphism from a trace hom returns that trace hom. -/
theorem TraceAnalyticGeometricGenerator.Hom.ofTraceHom_traceHom
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source.traceObject ⟶ target.traceObject) :
    (TraceAnalyticGeometricGenerator.Hom.ofTraceHom morphism).traceHom =
      morphism :=
  rfl

/-- The trace hom underlying a compact-generator morphism is the morphism itself. -/
theorem TraceAnalyticGeometricGenerator.Hom.traceHom_eq_self
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.traceHom =
      morphism :=
  rfl

/-- Identity compact-generator morphism is the identity trace correspondence. -/
theorem TraceAnalyticGeometricGenerator.id_eq_trace_id
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticGeometricGenerator.id generator =
      𝟙 generator.traceObject :=
  rfl

/-- Composition of compact-generator morphisms is trace-correspondence composition. -/
theorem TraceAnalyticGeometricGenerator.comp_eq_trace_comp
    {first second third : TraceAnalyticGeometricGenerator}
    (left : TraceAnalyticGeometricGenerator.Hom first second)
    (right : TraceAnalyticGeometricGenerator.Hom second third) :
    TraceAnalyticGeometricGenerator.comp left right =
      left ≫ right :=
  rfl

/-- The representable-presheaf map induced by a compact-generator morphism. -/
def TraceAnalyticGeometricGenerator.Hom.representableMap
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    TraceCorQPresheafHom source.presheaf target.presheaf :=
  TraceCorQPresheaf.representableMap morphism.traceHom

/-- The lifted representable-subcategory map induced by a compact-generator morphism. -/
def TraceAnalyticGeometricGenerator.Hom.representableObjectMap
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    source.representableObject ⟶ target.representableObject :=
  (TraceCorQRepresentablePresheaf.yoneda).map morphism.traceHom

/-- The induced presheaf map is the Yoneda representable map of the trace hom. -/
theorem TraceAnalyticGeometricGenerator.Hom.representableMap_eq
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.representableMap =
      TraceCorQPresheaf.representableMap morphism.traceHom :=
  rfl

/-- The induced lifted map is the lifted-Yoneda map of the trace hom. -/
theorem TraceAnalyticGeometricGenerator.Hom.representableObjectMap_eq
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.representableObjectMap =
      (TraceCorQRepresentablePresheaf.yoneda).map morphism.traceHom :=
  rfl

/-- Forgetting the lifted map gives the induced representable-presheaf map. -/
theorem TraceAnalyticGeometricGenerator.Hom.representableObjectMap_inclusion
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    TraceCorQRepresentablePresheaf.inclusion.map
        morphism.representableObjectMap =
      morphism.representableMap :=
  rfl

/-- The lifted-Yoneda preimage of the induced lifted map is the trace hom. -/
theorem TraceAnalyticGeometricGenerator.Hom.yonedaPreimage_representableObjectMap
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    TraceCorQRepresentablePresheaf.yonedaPreimage
        morphism.representableObjectMap =
      morphism.traceHom :=
  TraceCorQRepresentablePresheaf.yonedaPreimage_yonedaMap
    morphism.traceHom

end AnalyticMotives
end LFunctions
end Boundary
