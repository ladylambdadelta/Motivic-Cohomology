import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Functors.Forgetful.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Functors.Forgetful.Payload.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Functors.Forgetful.Payload.LedgerRectangles.Lengths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Functors.Forgetful.Payload.LedgerRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Functors.Forgetful.Payload.Owner

/-!
# Motive-root compact-generator forgetful functor wrappers

This file mirrors the compact-generator forgetful functor facts under
`TraceAnalyticMotive`, and re-exports the forgetful payload subtree.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root forgetful functor object wrapper. -/
theorem TraceAnalyticMotive.compactGenerator_forgetfulFunctor_obj
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticGeometricGenerator.forgetfulFunctor.obj generator =
      generator.traceObject :=
  TraceAnalyticGeometricGenerator.forgetfulFunctor_obj
    generator

/-- Motive-root forgetful functor map wrapper. -/
theorem TraceAnalyticMotive.compactGenerator_forgetfulFunctor_map
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.forgetfulFunctor.map morphism =
      morphism.traceHom :=
  TraceAnalyticGeometricGenerator.forgetfulFunctor_map
    morphism

/-- Motive-root lifted representable functor factors through forgetful and lifted Yoneda. -/
theorem TraceAnalyticMotive.compactGenerator_representableObjectFunctor_eq_forgetful_comp_yoneda :
    TraceAnalyticGeometricGenerator.representableObjectFunctor =
      TraceAnalyticGeometricGenerator.forgetfulFunctor ⋙
        TraceCorQRepresentablePresheaf.yoneda :=
  TraceAnalyticGeometricGenerator.representableObjectFunctor_eq_forgetful_comp_yoneda

/-- Motive-root presheaf functor factors through forgetful and linear Yoneda. -/
theorem TraceAnalyticMotive.compactGenerator_presheafFunctor_eq_forgetful_comp_yoneda :
    TraceAnalyticGeometricGenerator.presheafFunctor =
      TraceAnalyticGeometricGenerator.forgetfulFunctor ⋙
        TraceCorQPresheaf.yoneda :=
  TraceAnalyticGeometricGenerator.presheafFunctor_eq_forgetful_comp_yoneda

/-- Motive-root forgetful functor preserves identity as trace identity. -/
theorem TraceAnalyticMotive.compactGenerator_forgetfulFunctor_map_id
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticGeometricGenerator.forgetfulFunctor.map
        (𝟙 generator) =
      𝟙 generator.traceObject :=
  TraceAnalyticGeometricGenerator.forgetfulFunctor_map_id
    generator

/-- Motive-root forgetful functor preserves composition as trace composition. -/
theorem TraceAnalyticMotive.compactGenerator_forgetfulFunctor_map_comp
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceAnalyticGeometricGenerator.forgetfulFunctor.map
        (left ≫ right) =
      left.traceHom ≫ right.traceHom :=
  TraceAnalyticGeometricGenerator.forgetfulFunctor_map_comp
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
