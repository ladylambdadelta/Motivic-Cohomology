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
  shiftClosed_holds : shiftClosed
  coneClosed_holds : coneClosed
  universalProperty_holds : universalProperty

namespace PretriangulatedHull

end PretriangulatedHull

end CategoryInfra
end TraceCalc