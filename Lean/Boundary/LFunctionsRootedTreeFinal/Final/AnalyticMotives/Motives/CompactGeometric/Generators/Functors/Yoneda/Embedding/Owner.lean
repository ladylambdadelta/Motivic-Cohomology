import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Functors.Yoneda.Owner

/-!
# Embedding consequences of compact-generator Yoneda

This file records the concrete full-faithfulness consequences of the compact
Yoneda hom equivalence as explicit equality-reflection and lift statements.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Equality of lifted representable maps reflects equality of compact-generator morphisms. -/
theorem TraceAnalyticGeometricGenerator.eq_of_representableObjectMap_eq
    {source target : TraceAnalyticGeometricGenerator}
    {left right : source ⟶ target}
    (map_eq :
      left.representableObjectMap =
        right.representableObjectMap) :
    left = right :=
  Eq.trans
    (Eq.symm
      (TraceAnalyticGeometricGenerator.yonedaPreimage_representableObjectMap
        left))
    (Eq.trans
      (congrArg
        (fun morphism =>
          TraceAnalyticGeometricGenerator.yonedaPreimage morphism)
        map_eq)
      (TraceAnalyticGeometricGenerator.yonedaPreimage_representableObjectMap
        right))

/-- Every lifted representable morphism is represented by a compact-generator morphism. -/
theorem TraceAnalyticGeometricGenerator.exists_representableObjectMap_eq
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source.representableObject ⟶ target.representableObject) :
    ∃ traceMorphism : source ⟶ target,
      traceMorphism.representableObjectMap =
        morphism :=
  Exists.intro
    (TraceAnalyticGeometricGenerator.yonedaPreimage morphism)
    (TraceAnalyticGeometricGenerator.representableObjectMap_yonedaPreimage
      morphism)

/-- The chosen compact-generator lift of a lifted representable morphism. -/
noncomputable def TraceAnalyticGeometricGenerator.liftRepresentableObjectMap
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source.representableObject ⟶ target.representableObject) :
    source ⟶ target :=
  TraceAnalyticGeometricGenerator.yonedaPreimage morphism

/-- The chosen lift maps back to the original lifted representable morphism. -/
theorem TraceAnalyticGeometricGenerator.liftRepresentableObjectMap_spec
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source.representableObject ⟶ target.representableObject) :
    (TraceAnalyticGeometricGenerator.liftRepresentableObjectMap morphism).representableObjectMap =
      morphism :=
  TraceAnalyticGeometricGenerator.representableObjectMap_yonedaPreimage
    morphism

/-- The chosen lift of an induced representable map is the original compact morphism. -/
theorem TraceAnalyticGeometricGenerator.liftRepresentableObjectMap_representableObjectMap
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.liftRepresentableObjectMap
        morphism.representableObjectMap =
      morphism :=
  TraceAnalyticGeometricGenerator.yonedaPreimage_representableObjectMap
    morphism

end AnalyticMotives
end LFunctions
end Boundary
