import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.BoundedSubcategory.Shift.Owner

/-!
# Functoriality of bounded stable shifts

The bounded stable source is a full subcategory of the ambient analytic
comparison source.  Since boundedness is closed under shifts, ambient shifted
morphisms give morphisms between the packaged shifted bounded objects.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace BoundedStable

/-- The shift of a bounded-source morphism, with source and target packaged as
bounded shifted objects. -/
def shiftedMap
    {source target : TraceAnalyticDMgmComparisonSource.BoundedStable}
    (degree : ℤ)
    (hom : source ⟶ target) :
    TraceAnalyticDMgmComparisonSource.BoundedStable.shiftedObject
        source
        degree ⟶
      TraceAnalyticDMgmComparisonSource.BoundedStable.shiftedObject
        target
        degree :=
  hom⟦degree⟧'

/-- The bounded shifted map is definitionally the ambient shifted morphism. -/
theorem shiftedMap_eq
    {source target : TraceAnalyticDMgmComparisonSource.BoundedStable}
    (degree : ℤ)
    (hom : source ⟶ target) :
    TraceAnalyticDMgmComparisonSource.BoundedStable.shiftedMap
        degree
        hom =
      hom⟦degree⟧' :=
  rfl

/-- Bounded shifted maps preserve identities. -/
theorem shiftedMap_id
    (degree : ℤ)
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable) :
    TraceAnalyticDMgmComparisonSource.BoundedStable.shiftedMap
        degree
        (𝟙 object) =
      𝟙
        (TraceAnalyticDMgmComparisonSource.BoundedStable
          .shiftedObject object degree) :=
  (shiftFunctor
    TraceAnalyticDMgmComparisonSource
    degree).map_id object.object

/-- Bounded shifted maps preserve composition. -/
theorem shiftedMap_comp
    (degree : ℤ)
    {left middle right : TraceAnalyticDMgmComparisonSource.BoundedStable}
    (first : left ⟶ middle)
    (second : middle ⟶ right) :
    TraceAnalyticDMgmComparisonSource.BoundedStable.shiftedMap
        degree
        (first ≫ second) =
      TraceAnalyticDMgmComparisonSource.BoundedStable.shiftedMap
          degree
          first ≫
        TraceAnalyticDMgmComparisonSource.BoundedStable.shiftedMap
          degree
          second :=
  (shiftFunctor
    TraceAnalyticDMgmComparisonSource
    degree).map_comp first second

end BoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
