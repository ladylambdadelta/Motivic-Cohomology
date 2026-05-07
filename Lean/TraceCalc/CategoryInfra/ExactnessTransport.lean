import TraceCalc.CategoryInfra.Karoubi

universe u v

namespace TraceCalc
namespace CategoryInfra

/-- Abstract exactness-transport package through the completion ladder. -/
structure ExactnessTransport {presentation : Type u}
    (F : FreeDGEnvelope.{u, v} presentation)
    (P : PretriangulatedHull F.envelope)
    (H : H0Category P)
    (K : KaroubiEnvelope H) where
  exactnessForDGEnvelope : Prop
  exactnessForPretriangulatedHull : Prop
  exactnessForH0 : Prop
  exactnessForKaroubiEnvelope : Prop
  distinguishedTriangleTransport : Prop
  exactnessForDGEnvelope_holds : exactnessForDGEnvelope
  exactnessForPretriangulatedHull_holds : exactnessForPretriangulatedHull
  exactnessForH0_holds : exactnessForH0
  exactnessForKaroubiEnvelope_holds : exactnessForKaroubiEnvelope
  distinguishedTriangleTransport_holds : distinguishedTriangleTransport

namespace ExactnessTransport

def theoremTarget {presentation : Type u}
    {F : FreeDGEnvelope.{u, v} presentation}
    {P : PretriangulatedHull F.envelope}
    {H : H0Category P}
    {K : KaroubiEnvelope H}
    (E : ExactnessTransport F P H K) : Prop :=
  E.exactnessForDGEnvelope ∧
    E.exactnessForPretriangulatedHull ∧
      E.exactnessForH0 ∧
        E.exactnessForKaroubiEnvelope ∧
          E.distinguishedTriangleTransport

theorem theoremTarget_holds {presentation : Type u}
    {F : FreeDGEnvelope.{u, v} presentation}
    {P : PretriangulatedHull F.envelope}
    {H : H0Category P}
    {K : KaroubiEnvelope H}
    (E : ExactnessTransport F P H K) : E.theoremTarget := by
  exact ⟨E.exactnessForDGEnvelope_holds,
    E.exactnessForPretriangulatedHull_holds, E.exactnessForH0_holds,
    E.exactnessForKaroubiEnvelope_holds,
    E.distinguishedTriangleTransport_holds⟩

end ExactnessTransport

end CategoryInfra
end TraceCalc