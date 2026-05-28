import TraceCalc.LayerA.CategoryInfra.FreeDG

universe u v

namespace TraceCalc
namespace CategoryInfra

/-- Standard pretriangulated-hull surface over an honest dg category: shifts are
indexed by integers and cones are attached to closed degree-zero morphisms. -/
structure StandardPretriangulatedHull (C : StandardDGCategoryLike.{u, v}) where
  hull : StandardDGCategoryLike.{u, v}
  includeObj : C.Obj → hull.Obj
  shiftObj : Int → hull.Obj → hull.Obj
  coneObj :
    ∀ {X Y : hull.Obj}, hull.CycleHom X Y → hull.Obj

namespace StandardPretriangulatedHull

abbrev closedDegreeZeroMorphism
    {C : StandardDGCategoryLike.{u, v}}
    (P : StandardPretriangulatedHull C)
    (X Y : P.hull.Obj) : Type v :=
  P.hull.CycleHom X Y

end StandardPretriangulatedHull

/-- The shift operation carried by a pretriangulated hull. -/
structure ShiftStructure (Obj : Type u) where
  obj : Obj → Obj

/-- The cone operation carried by a pretriangulated hull. -/
structure ConeStructure (Obj : Type u) where
  obj : Obj → Obj → Obj

/-- Explicit object-level extension data expressing the hull universal property. -/
structure PretriangulatedUniversalProperty
    (sourceObj : Type u)
    (hullObj : Type u)
    (includeObj : sourceObj → hullObj)
    (shiftObj : hullObj → hullObj)
    (coneObj : hullObj → hullObj → hullObj) where
  liftObj :
    ∀ {D : Type u},
      (ι : sourceObj → D) →
        (shift : D → D) →
          (cone : D → D → D) → hullObj → D
  lift_include :
    ∀ {D : Type u}
      (ι : sourceObj → D)
      (shift : D → D)
      (cone : D → D → D)
      (p : sourceObj),
        liftObj ι shift cone (includeObj p) = ι p
  lift_shift :
    ∀ {D : Type u}
      (ι : sourceObj → D)
      (shift : D → D)
      (cone : D → D → D)
      (X : hullObj),
        liftObj ι shift cone (shiftObj X) = shift (liftObj ι shift cone X)
  lift_cone :
    ∀ {D : Type u}
      (ι : sourceObj → D)
      (shift : D → D)
      (cone : D → D → D)
      (X Y : hullObj),
        liftObj ι shift cone (coneObj X Y) = cone (liftObj ι shift cone X) (liftObj ι shift cone Y)

/-- Abstract pretriangulated-hull package on top of a dg category. -/
structure PretriangulatedHull (C : DGCategoryLike.{u, v}) where
  hull : DGCategoryLike.{u, v}
  includeObj : C.Obj → hull.Obj
  shift : ShiftStructure hull.Obj
  cone : ConeStructure hull.Obj
  universalProperty :
    PretriangulatedUniversalProperty C.Obj hull.Obj includeObj shift.obj cone.obj

namespace PretriangulatedHull

abbrev shiftObj {C : DGCategoryLike.{u, v}} (P : PretriangulatedHull C) :
    P.hull.Obj → P.hull.Obj :=
  P.shift.obj

abbrev coneObj {C : DGCategoryLike.{u, v}} (P : PretriangulatedHull C) :
    P.hull.Obj → P.hull.Obj → P.hull.Obj :=
  P.cone.obj

end PretriangulatedHull

end CategoryInfra
end TraceCalc