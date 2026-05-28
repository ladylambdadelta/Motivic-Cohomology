import TraceCalc.LayerA.CategoryInfra.H0Category
import TraceCalc.LayerA.CategoryInfra.MonoidalPresentation

universe u v

open CategoryTheory

namespace TraceCalc
namespace CategoryInfra

abbrev H0KaroubiCompletion {C : StandardDGCategoryLike.{u, v}}
    (H : StandardH0CategoryTarget C) : Type _ :=
  StandardH0CategoryTarget.AsCategory.KaroubiCompletion H

structure H0TensorAssociator {C : StandardDGCategoryLike.{u, v}}
    (H : StandardH0CategoryTarget C)
    (tensorOnH0 : C.Obj → C.Obj → C.Obj) where
  hom :
    ∀ X Y Z : C.Obj,
      H.H0Hom (tensorOnH0 (tensorOnH0 X Y) Z) (tensorOnH0 X (tensorOnH0 Y Z))
  inv :
    ∀ X Y Z : C.Obj,
      H.H0Hom (tensorOnH0 X (tensorOnH0 Y Z)) (tensorOnH0 (tensorOnH0 X Y) Z)
  hom_inv_id :
    ∀ X Y Z : C.Obj,
      H.compose (hom X Y Z) (inv X Y Z) =
        H.identity (tensorOnH0 (tensorOnH0 X Y) Z)
  inv_hom_id :
    ∀ X Y Z : C.Obj,
      H.compose (inv X Y Z) (hom X Y Z) =
        H.identity (tensorOnH0 X (tensorOnH0 Y Z))

structure KaroubiTensorAssociator {C : StandardDGCategoryLike.{u, v}}
    (H : StandardH0CategoryTarget C)
    (tensorOnKaroubi : H0KaroubiCompletion H → H0KaroubiCompletion H → H0KaroubiCompletion H) where
  hom :
    ∀ X Y Z : H0KaroubiCompletion H,
      tensorOnKaroubi (tensorOnKaroubi X Y) Z ⟶ tensorOnKaroubi X (tensorOnKaroubi Y Z)
  inv :
    ∀ X Y Z : H0KaroubiCompletion H,
      tensorOnKaroubi X (tensorOnKaroubi Y Z) ⟶ tensorOnKaroubi (tensorOnKaroubi X Y) Z
  hom_inv_id :
    ∀ X Y Z : H0KaroubiCompletion H,
      (hom X Y Z) ≫ (inv X Y Z) =
        𝟙 (tensorOnKaroubi (tensorOnKaroubi X Y) Z)
  inv_hom_id :
    ∀ X Y Z : H0KaroubiCompletion H,
      (inv X Y Z) ≫ (hom X Y Z) =
        𝟙 (tensorOnKaroubi X (tensorOnKaroubi Y Z))

/-- Abstract monoidal-transport target through the completion ladder. -/
structure MonoidalTransportTarget {presentation : Type u}
    [MonoidalPresentation presentation]
    (F : FreeDGEnvelope.{u, v} presentation)
    (P : PretriangulatedHull F.envelope)
    {C : StandardDGCategoryLike.{u, v}}
    (H : StandardH0CategoryTarget C) where
  h0ObjOfHull : P.hull.Obj → C.Obj
  tensorOnDG : F.envelope.Obj → F.envelope.Obj → F.envelope.Obj
  tensorOnH0 : C.Obj → C.Obj → C.Obj
  tensorOnKaroubi : H0KaroubiCompletion H → H0KaroubiCompletion H → H0KaroubiCompletion H

structure MonoidalTransportCompatibility {presentation : Type u}
    [MonoidalPresentation presentation]
    {F : FreeDGEnvelope.{u, v} presentation}
    {P : PretriangulatedHull F.envelope}
    {C : StandardDGCategoryLike.{u, v}}
    {H : StandardH0CategoryTarget C}
    (target : MonoidalTransportTarget F P H) where
  throughDGEnvelope :
    ∀ p q : presentation,
      target.tensorOnDG (F.includeObj p) (F.includeObj q) =
        F.includeObj (MonoidalPresentation.tensorObj p q)
  throughPretriangulatedHull :
    ∀ X Y : F.envelope.Obj,
      target.tensorOnH0 (target.h0ObjOfHull (P.includeObj X))
          (target.h0ObjOfHull (P.includeObj Y)) =
        target.h0ObjOfHull (P.includeObj (target.tensorOnDG X Y))
  throughKaroubiCompletion :
    ∀ X Y : C.Obj,
      target.tensorOnKaroubi
          (StandardH0CategoryTarget.AsCategory.karoubiOfObj H X)
          (StandardH0CategoryTarget.AsCategory.karoubiOfObj H Y) =
        StandardH0CategoryTarget.AsCategory.karoubiOfObj H (target.tensorOnH0 X Y)

structure MonoidalTransportData {presentation : Type u}
  [MonoidalPresentation presentation]
    {F : FreeDGEnvelope.{u, v} presentation}
    {P : PretriangulatedHull F.envelope}
    {C : StandardDGCategoryLike.{u, v}}
    {H : StandardH0CategoryTarget C}
    (target : MonoidalTransportTarget F P H) where
  compatibility : MonoidalTransportCompatibility target
  h0Associator : H0TensorAssociator H target.tensorOnH0
  karoubiAssociator : KaroubiTensorAssociator H target.tensorOnKaroubi

namespace MonoidalTransport

end MonoidalTransport

end CategoryInfra
end TraceCalc