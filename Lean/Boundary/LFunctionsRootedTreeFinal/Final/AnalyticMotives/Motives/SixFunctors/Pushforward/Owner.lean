import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Category.Owner

/-!
# Concrete compact-generator pushforward functional

This file owns the compact-generator pushforward functional currently available
in the analytic motives lane.  On compact representable generators it is the
Yoneda map induced by the underlying trace correspondence.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open scoped CategoryTheory

/-- The compact-generator pushforward functional on representable trace presheaves. -/
def TraceSixFunctorPushforward.compactGenerator
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    source.presheaf ⟶ target.presheaf :=
  morphism.representableMap

/-- The compact-generator pushforward functional in the representable subcategory. -/
def TraceSixFunctorPushforward.compactGeneratorObject
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    source.representableObject ⟶ target.representableObject :=
  morphism.representableObjectMap

/-- Compact-generator pushforward is the representable map induced by the morphism. -/
theorem TraceSixFunctorPushforward.compactGenerator_eq_representableMap
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGenerator morphism =
      morphism.representableMap :=
  rfl

/-- Lifted compact-generator pushforward is the lifted representable map. -/
theorem TraceSixFunctorPushforward.compactGeneratorObject_eq_representableObjectMap
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGeneratorObject morphism =
      morphism.representableObjectMap :=
  rfl

/-- Forgetting the lifted pushforward gives the ambient presheaf pushforward. -/
theorem TraceSixFunctorPushforward.compactGeneratorObject_inclusion
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceCorQRepresentablePresheaf.inclusion.map
        (TraceSixFunctorPushforward.compactGeneratorObject morphism) =
      TraceSixFunctorPushforward.compactGenerator morphism :=
  TraceAnalyticGeometricGenerator.Hom.representableObjectMap_inclusion
    morphism

/-- Compact-generator pushforward is the Yoneda map of the underlying trace hom. -/
theorem TraceSixFunctorPushforward.compactGenerator_eq_yonedaMap
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGenerator morphism =
      TraceCorQPresheaf.representableMap morphism.traceHom :=
  TraceAnalyticGeometricGenerator.Hom.representableMap_eq morphism

/-- Compact-generator pushforward is functorial for identities. -/
theorem TraceSixFunctorPushforward.compactGenerator_id
    (generator : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPushforward.compactGenerator
        (𝟙 generator) =
      𝟙 generator.presheaf :=
  TraceCorQPresheaf.representableMap_id generator.traceObject

/-- Lifted compact-generator pushforward is functorial for identities. -/
theorem TraceSixFunctorPushforward.compactGeneratorObject_id
    (generator : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPushforward.compactGeneratorObject
        (𝟙 generator) =
      𝟙 generator.representableObject :=
  (TraceCorQRepresentablePresheaf.yoneda).map_id generator.traceObject

/-- Compact-generator pushforward is covariantly functorial for composition. -/
theorem TraceSixFunctorPushforward.compactGenerator_comp
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPushforward.compactGenerator
        (left ≫ right) =
      TraceSixFunctorPushforward.compactGenerator left ≫
        TraceSixFunctorPushforward.compactGenerator right :=
  TraceCorQPresheaf.representableMap_comp left.traceHom right.traceHom

/-- Lifted compact-generator pushforward is covariantly functorial for composition. -/
theorem TraceSixFunctorPushforward.compactGeneratorObject_comp
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPushforward.compactGeneratorObject
        (left ≫ right) =
      TraceSixFunctorPushforward.compactGeneratorObject left ≫
        TraceSixFunctorPushforward.compactGeneratorObject right :=
  (TraceCorQRepresentablePresheaf.yoneda).map_comp
    left.traceHom
    right.traceHom

end AnalyticMotives
end LFunctions
end Boundary
