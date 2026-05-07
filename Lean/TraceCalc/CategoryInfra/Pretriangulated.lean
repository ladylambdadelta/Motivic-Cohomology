import TraceCalc.CategoryInfra.FreeDG

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

def existenceTarget {C : DGCategoryLike.{u, v}}
    (P : PretriangulatedHull C) : Prop :=
  Nonempty (PretriangulatedHull.{u, v} C)

theorem existenceTarget_holds {C : DGCategoryLike.{u, v}}
    (P : PretriangulatedHull C) : P.existenceTarget := by
  exact ⟨P⟩

def shiftClosureTarget {C : DGCategoryLike.{u, v}}
    (P : PretriangulatedHull C) : Prop :=
  P.shiftClosed

theorem shiftClosureTarget_holds {C : DGCategoryLike.{u, v}}
    (P : PretriangulatedHull C) : P.shiftClosureTarget :=
  P.shiftClosed_holds

def coneClosureTarget {C : DGCategoryLike.{u, v}}
    (P : PretriangulatedHull C) : Prop :=
  P.coneClosed

theorem coneClosureTarget_holds {C : DGCategoryLike.{u, v}}
    (P : PretriangulatedHull C) : P.coneClosureTarget :=
  P.coneClosed_holds

def universalPropertyTarget {C : DGCategoryLike.{u, v}}
    (P : PretriangulatedHull C) : Prop :=
  P.universalProperty

theorem universalPropertyTarget_holds {C : DGCategoryLike.{u, v}}
    (P : PretriangulatedHull C) : P.universalPropertyTarget :=
  P.universalProperty_holds

def theoremTarget {C : DGCategoryLike.{u, v}}
    (P : PretriangulatedHull C) : Prop :=
  P.existenceTarget ∧
    P.shiftClosureTarget ∧
      P.coneClosureTarget ∧
        P.universalPropertyTarget

theorem theoremTarget_holds {C : DGCategoryLike.{u, v}}
    (P : PretriangulatedHull C) : P.theoremTarget := by
  exact ⟨P.existenceTarget_holds, P.shiftClosureTarget_holds,
    P.coneClosureTarget_holds, P.universalPropertyTarget_holds⟩

end PretriangulatedHull

end CategoryInfra
end TraceCalc