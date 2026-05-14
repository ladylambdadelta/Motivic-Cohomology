import TraceCalc.LayerA.CategoryInfra.FreeDG

universe u v

namespace TraceCalc
namespace CategoryInfra

/-- Abstract pretriangulated-hull package on top of a dg category. -/
structure PretriangulatedHull (C : DGCategoryLike.{u, v}) where
  hull : DGCategoryLike.{u, v}
  includeObj : C.Obj → hull.Obj
  shiftClosed : Prop
  coneClosed : Prop
  universalProperty : Prop
  shiftClosedWitness : shiftClosed
  coneClosedWitness : coneClosed
  universalPropertyWitness : universalProperty

namespace PretriangulatedHull

end PretriangulatedHull

end CategoryInfra
end TraceCalc