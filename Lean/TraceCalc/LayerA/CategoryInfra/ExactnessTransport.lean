import TraceCalc.LayerA.CategoryInfra.H0Category

universe u v

namespace TraceCalc
namespace CategoryInfra

/-- Abstract exactness-transport package through the completion ladder. -/
structure ExactnessTransportTarget {presentation : Type u}
    (F : FreeDGEnvelope.{u, v} presentation)
    (P : PretriangulatedHull F.envelope)
    {C : StandardDGCategoryLike.{u, v}}
    (H : StandardH0CategoryTarget C) where
  exactnessForH0 : H0TriangulatedData P
  exactnessForKaroubiCompletion :
    CategoryTheory.IsIdempotentComplete (StandardH0CategoryTarget.AsCategory.KaroubiCompletion H)
  distinguishedTriangleTransport : ConeStructure P.hull.Obj

structure ExactnessTransportLaws {presentation : Type u}
    {F : FreeDGEnvelope.{u, v} presentation}
    {P : PretriangulatedHull F.envelope}
    {C : StandardDGCategoryLike.{u, v}}
    {H : StandardH0CategoryTarget C}
    (target : ExactnessTransportTarget F P H) where
  exactnessForDGEnvelope :
    F.envelope.differentialSquaredZero
  exactnessForPretriangulatedHull :
    P.hull.differentialSquaredZero

structure ExactnessTransportData {presentation : Type u}
    {F : FreeDGEnvelope.{u, v} presentation}
    {P : PretriangulatedHull F.envelope}
    {C : StandardDGCategoryLike.{u, v}}
    {H : StandardH0CategoryTarget C}
    (target : ExactnessTransportTarget F P H) where
  laws : ExactnessTransportLaws target

namespace ExactnessTransport

end ExactnessTransport

end CategoryInfra
end TraceCalc