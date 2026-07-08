import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Complexes.Owner

/-!
# Morphisms of analytic trace complexes

Chain maps are the morphisms in the first stable analytic-motive category.
The component law records that trace-correspondence components commute with the
analytic differentials.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A morphism of analytic trace cochain complexes is a chain map. -/
abbrev TraceAnalyticCochainComplex.Hom
    (source target : TraceAnalyticCochainComplex) :=
  source ⟶ target

/-- The component of a morphism of analytic trace cochain complexes in one degree. -/
def TraceAnalyticCochainComplex.Hom.component
    {source target : TraceAnalyticCochainComplex}
    (hom : TraceAnalyticCochainComplex.Hom source target)
    (degree : ℤ) :
    source.objectAt degree ⟶ target.objectAt degree :=
  hom.f degree

/-- The component projection is the underlying homological-complex map field. -/
theorem TraceAnalyticCochainComplex.Hom.component_eq
    {source target : TraceAnalyticCochainComplex}
    (hom : TraceAnalyticCochainComplex.Hom source target)
    (degree : ℤ) :
    hom.component degree =
      hom.f degree :=
  rfl

/-- Components of analytic trace cochain-complex morphisms commute with differentials. -/
theorem TraceAnalyticCochainComplex.Hom.component_comm
    {source target : TraceAnalyticCochainComplex}
    (hom : TraceAnalyticCochainComplex.Hom source target)
    (sourceDegree targetDegree : ℤ) :
    source.differential sourceDegree targetDegree ≫
        hom.component targetDegree =
      hom.component sourceDegree ≫
        target.differential sourceDegree targetDegree :=
  HomologicalComplex.Hom.comm hom sourceDegree targetDegree

end AnalyticMotives
end LFunctions
end Boundary
