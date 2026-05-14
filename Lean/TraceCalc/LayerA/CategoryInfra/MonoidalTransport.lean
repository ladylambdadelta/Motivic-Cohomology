import TraceCalc.LayerA.CategoryInfra.Karoubi

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
  throughDGEnvelope :
    ∀ p q : presentation,
      tensorOnDG (F.includeObj p) (F.includeObj q) = F.includeObj (tensorOnPresentation p q)
  throughPretriangulatedHull :
    ∀ X Y : F.envelope.Obj,
      tensorOnH0 (P.includeObj X) (P.includeObj Y) = P.includeObj (tensorOnDG X Y)
  throughH0 :
    ∀ X Y Z : P.hull.Obj,
      tensorOnH0 (tensorOnH0 X Y) Z = tensorOnH0 X (tensorOnH0 Y Z)
  throughKaroubiEnvelope :
    ∀ X Y : P.hull.Obj,
      tensorOnKaroubi (K.includeObj X) (K.includeObj Y) = K.includeObj (tensorOnH0 X Y)
  coherenceTransport :
    ∀ X Y Z : K.Obj,
      tensorOnKaroubi (tensorOnKaroubi X Y) Z = tensorOnKaroubi X (tensorOnKaroubi Y Z)

namespace MonoidalTransport

end MonoidalTransport

end CategoryInfra
end TraceCalc