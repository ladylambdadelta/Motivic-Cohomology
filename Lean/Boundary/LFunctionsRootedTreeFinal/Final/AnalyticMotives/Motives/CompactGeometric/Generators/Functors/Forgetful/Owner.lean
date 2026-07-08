import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Functors.Owner

/-!
# Forgetful functor from compact generators to trace correspondences

This file records the concrete bridge from compact analytic generators back to
the underlying `TraceCorQ` category: send a generator to its certified trace
object and a generator morphism to its underlying trace correspondence.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The forgetful functor from compact analytic generators to trace correspondences. -/
def TraceAnalyticGeometricGenerator.forgetfulFunctor :
    TraceAnalyticGeometricGenerator ⥤ TraceCorQObject where
  obj := fun generator =>
    generator.traceObject
  map := fun morphism =>
    morphism.traceHom
  map_id := fun generator =>
    rfl
  map_comp := fun left right =>
    rfl

/-- The forgetful functor sends a generator to its underlying trace object. -/
theorem TraceAnalyticGeometricGenerator.forgetfulFunctor_obj
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticGeometricGenerator.forgetfulFunctor.obj generator =
      generator.traceObject :=
  rfl

/-- The forgetful functor sends a morphism to its underlying trace hom. -/
theorem TraceAnalyticGeometricGenerator.forgetfulFunctor_map
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.forgetfulFunctor.map morphism =
      morphism.traceHom :=
  rfl

/-- The lifted representable functor is forgetful followed by lifted Yoneda. -/
theorem TraceAnalyticGeometricGenerator.representableObjectFunctor_eq_forgetful_comp_yoneda :
    TraceAnalyticGeometricGenerator.representableObjectFunctor =
      TraceAnalyticGeometricGenerator.forgetfulFunctor ⋙
        TraceCorQRepresentablePresheaf.yoneda :=
  rfl

/-- The presheaf functor is forgetful followed by linear Yoneda. -/
theorem TraceAnalyticGeometricGenerator.presheafFunctor_eq_forgetful_comp_yoneda :
    TraceAnalyticGeometricGenerator.presheafFunctor =
      TraceAnalyticGeometricGenerator.forgetfulFunctor ⋙
        TraceCorQPresheaf.yoneda :=
  rfl

/-- Forgetful functor preserves identity as trace identity. -/
theorem TraceAnalyticGeometricGenerator.forgetfulFunctor_map_id
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticGeometricGenerator.forgetfulFunctor.map
        (𝟙 generator) =
      𝟙 generator.traceObject :=
  rfl

/-- Forgetful functor preserves composition as trace composition. -/
theorem TraceAnalyticGeometricGenerator.forgetfulFunctor_map_comp
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceAnalyticGeometricGenerator.forgetfulFunctor.map
        (left ≫ right) =
      left.traceHom ≫ right.traceHom :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
