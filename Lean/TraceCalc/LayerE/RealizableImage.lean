import TraceCalc.LayerD.Comparison

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

/-- Constructor from a map using the direct image predicate. -/
def fromMap (f : A → B) : RealizableImage A B where
  sourceMap := f
  IsRealizable := fun b => Nonempty { a : A // f a = b }
  realizable_iff := by
    intro b
    rfl

/-- Any explicit preimage witness gives realizability. -/
theorem mk_reachable {R : RealizableImage A B} {a : A} :
    R.IsRealizable (R.sourceMap a) := by
  have h : Nonempty { x : A // R.sourceMap x = R.sourceMap a } :=
    ⟨⟨a, rfl⟩⟩
  exact (R.realizable_iff (R.sourceMap a)).2 h

end RealizableImage

end LayerE
end TraceCalc
