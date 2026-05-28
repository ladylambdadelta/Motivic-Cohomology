universe u

namespace TraceCalc
namespace LayerE

/-- Realizable-image boundary: a target object is realizable if it comes from a chosen source map. -/
structure RealizableImage (A B : Type u) where
  sourceMap : A → B
  IsRealizable : B → Prop
  realizable_iff : ∀ b, IsRealizable b ↔ Nonempty { a : A // sourceMap a = b }

namespace RealizableImage

variable {A B : Type u}

end RealizableImage

end LayerE
end TraceCalc
