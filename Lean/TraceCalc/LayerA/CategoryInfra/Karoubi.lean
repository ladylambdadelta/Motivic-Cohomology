import TraceCalc.LayerA.CategoryInfra.H0Category

universe u v

namespace TraceCalc
namespace CategoryInfra

/-- Abstract Karoubi-envelope package attached to an `H0Category`. -/
structure KaroubiEnvelope {C : DGCategoryLike.{u, v}} {P : PretriangulatedHull C}
    (H : H0Category P) where
  Obj : Type u
  includeObj : P.hull.Obj → Obj
  Hom : Obj → Obj → Type v
  id : ∀ X : Obj, Hom X X
  comp : ∀ {X Y Z : Obj}, Hom X Y → Hom Y Z → Hom X Z
  idempotentSplitting : Prop
  universalProperty : Prop
  idempotentSplitting_holds : idempotentSplitting
  universalProperty_holds : universalProperty

namespace KaroubiEnvelope

end KaroubiEnvelope

end CategoryInfra
end TraceCalc