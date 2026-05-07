import TraceCalc.CategoryInfra.Karoubi

universe u v

namespace TraceCalc
namespace CategoryInfra

/-- Abstract monoidal-transport package through the completion ladder. -/
structure MonoidalTransport {presentation : Type u}
    (F : FreeDGEnvelope.{u, v} presentation)
    (P : PretriangulatedHull F.envelope)
    (H : H0Category P)
    (K : KaroubiEnvelope H) where
  tensorOnPresentation : presentation → presentation → presentation
  tensorOnDG : F.envelope.Obj → F.envelope.Obj → F.envelope.Obj
  tensorOnH0 : P.hull.Obj → P.hull.Obj → P.hull.Obj
  tensorOnKaroubi : K.Obj → K.Obj → K.Obj
  throughDGEnvelope : Prop
  throughPretriangulatedHull : Prop
  throughH0 : Prop
  throughKaroubiEnvelope : Prop
  coherenceTransport : Prop
  throughDGEnvelope_holds : throughDGEnvelope
  throughPretriangulatedHull_holds : throughPretriangulatedHull
  throughH0_holds : throughH0
  throughKaroubiEnvelope_holds : throughKaroubiEnvelope
  coherenceTransport_holds : coherenceTransport

namespace MonoidalTransport

def theoremTarget {presentation : Type u}
    {F : FreeDGEnvelope.{u, v} presentation}
    {P : PretriangulatedHull F.envelope}
    {H : H0Category P}
    {K : KaroubiEnvelope H}
    (M : MonoidalTransport F P H K) : Prop :=
  M.throughDGEnvelope ∧
    M.throughPretriangulatedHull ∧
      M.throughH0 ∧
        M.throughKaroubiEnvelope ∧
          M.coherenceTransport

theorem theoremTarget_holds {presentation : Type u}
    {F : FreeDGEnvelope.{u, v} presentation}
    {P : PretriangulatedHull F.envelope}
    {H : H0Category P}
    {K : KaroubiEnvelope H}
    (M : MonoidalTransport F P H K) : M.theoremTarget := by
  exact ⟨M.throughDGEnvelope_holds, M.throughPretriangulatedHull_holds,
    M.throughH0_holds, M.throughKaroubiEnvelope_holds,
    M.coherenceTransport_holds⟩

end MonoidalTransport

end CategoryInfra
end TraceCalc