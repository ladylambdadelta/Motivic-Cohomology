import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Functors.Forgetful.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Functors.Forgetful.Payload.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Functors.Forgetful.Payload.LedgerRectangles.Lengths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Functors.Forgetful.Payload.LedgerRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Functors.Forgetful.Payload.Owner

/-!
# Top-root compact-generator forgetful functor wrappers

This file mirrors motive-root compact-generator forgetful functor facts under
`AnalyticMotivesRoot`, and re-exports the forgetful payload subtree.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root forgetful functor object wrapper. -/
theorem AnalyticMotivesRoot.compactGenerator_forgetfulFunctor_obj
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticGeometricGenerator.forgetfulFunctor.obj generator =
      generator.traceObject :=
  TraceAnalyticMotive.compactGenerator_forgetfulFunctor_obj
    generator

/-- Top-root forgetful functor map wrapper. -/
theorem AnalyticMotivesRoot.compactGenerator_forgetfulFunctor_map
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.forgetfulFunctor.map morphism =
      morphism.traceHom :=
  TraceAnalyticMotive.compactGenerator_forgetfulFunctor_map
    morphism

/-- Top-root lifted representable functor factors through forgetful and lifted Yoneda. -/
theorem AnalyticMotivesRoot.compactGenerator_representableObjectFunctor_eq_forgetful_comp_yoneda :
    TraceAnalyticGeometricGenerator.representableObjectFunctor =
      TraceAnalyticGeometricGenerator.forgetfulFunctor ⋙
        TraceCorQRepresentablePresheaf.yoneda :=
  TraceAnalyticMotive.compactGenerator_representableObjectFunctor_eq_forgetful_comp_yoneda

/-- Top-root presheaf functor factors through forgetful and linear Yoneda. -/
theorem AnalyticMotivesRoot.compactGenerator_presheafFunctor_eq_forgetful_comp_yoneda :
    TraceAnalyticGeometricGenerator.presheafFunctor =
      TraceAnalyticGeometricGenerator.forgetfulFunctor ⋙
        TraceCorQPresheaf.yoneda :=
  TraceAnalyticMotive.compactGenerator_presheafFunctor_eq_forgetful_comp_yoneda

/-- Top-root forgetful functor preserves identity as trace identity. -/
theorem AnalyticMotivesRoot.compactGenerator_forgetfulFunctor_map_id
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticGeometricGenerator.forgetfulFunctor.map
        (𝟙 generator) =
      𝟙 generator.traceObject :=
  TraceAnalyticMotive.compactGenerator_forgetfulFunctor_map_id
    generator

/-- Top-root forgetful functor preserves composition as trace composition. -/
theorem AnalyticMotivesRoot.compactGenerator_forgetfulFunctor_map_comp
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceAnalyticGeometricGenerator.forgetfulFunctor.map
        (left ≫ right) =
      left.traceHom ≫ right.traceHom :=
  TraceAnalyticMotive.compactGenerator_forgetfulFunctor_map_comp
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
