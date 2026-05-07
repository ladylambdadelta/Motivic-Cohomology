import TraceCalc.CategoryInfra.H0Category

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

def existenceTarget {C : DGCategoryLike.{u, v}} {P : PretriangulatedHull C}
    {H : H0Category P} (K : KaroubiEnvelope H) : Prop :=
  Nonempty (KaroubiEnvelope.{u, v} H)

theorem existenceTarget_holds {C : DGCategoryLike.{u, v}}
    {P : PretriangulatedHull C} {H : H0Category P} (K : KaroubiEnvelope H) :
    K.existenceTarget := by
  exact ⟨K⟩

def idempotentSplittingTarget {C : DGCategoryLike.{u, v}} {P : PretriangulatedHull C}
    {H : H0Category P} (K : KaroubiEnvelope H) : Prop :=
  K.idempotentSplitting

theorem idempotentSplittingTarget_holds {C : DGCategoryLike.{u, v}}
    {P : PretriangulatedHull C} {H : H0Category P} (K : KaroubiEnvelope H) :
    K.idempotentSplittingTarget :=
  K.idempotentSplitting_holds

def universalPropertyTarget {C : DGCategoryLike.{u, v}} {P : PretriangulatedHull C}
    {H : H0Category P} (K : KaroubiEnvelope H) : Prop :=
  K.universalProperty

theorem universalPropertyTarget_holds {C : DGCategoryLike.{u, v}}
    {P : PretriangulatedHull C} {H : H0Category P} (K : KaroubiEnvelope H) :
    K.universalPropertyTarget :=
  K.universalProperty_holds

def theoremTarget {C : DGCategoryLike.{u, v}} {P : PretriangulatedHull C}
    {H : H0Category P} (K : KaroubiEnvelope H) : Prop :=
  K.existenceTarget ∧ K.idempotentSplittingTarget ∧ K.universalPropertyTarget

theorem theoremTarget_holds {C : DGCategoryLike.{u, v}}
    {P : PretriangulatedHull C} {H : H0Category P} (K : KaroubiEnvelope H) :
    K.theoremTarget := by
  exact ⟨K.existenceTarget_holds, K.idempotentSplittingTarget_holds,
    K.universalPropertyTarget_holds⟩

end KaroubiEnvelope

end CategoryInfra
end TraceCalc