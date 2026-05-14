import TraceCalc.LayerA.CategoryInfra.Karoubi

universe u v

namespace TraceCalc
namespace CategoryInfra

/-- Abstract exactness-transport package through the completion ladder. -/
structure ExactnessTransport {presentation : Type u}
    (F : FreeDGEnvelope.{u, v} presentation)
    (P : PretriangulatedHull F.envelope)
    (H : H0Category P)
    (K : KaroubiEnvelope H) where
  exactnessForDGEnvelope :
    ∀ {X Y : F.envelope.Obj} (f : F.envelope.HomComplex X Y),
      F.envelope.differential (F.envelope.differential f) = f
  exactnessForPretriangulatedHull :
    ∀ {X Y : P.hull.Obj} (f : P.hull.HomComplex X Y),
      P.hull.differential (P.hull.differential f) = f
  exactnessForH0 : P.shiftClosed ∧ P.coneClosed
  exactnessForKaroubiEnvelope : K.idempotentSplitting
  distinguishedTriangleTransport : P.coneClosed

namespace ExactnessTransport

end ExactnessTransport

end CategoryInfra
end TraceCalc