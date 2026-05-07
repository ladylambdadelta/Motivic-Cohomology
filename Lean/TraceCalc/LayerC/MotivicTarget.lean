import TraceCalc.LayerA.Base

universe u v

open CategoryTheory

namespace TraceCalc
namespace LayerC

/-- Abstract motivic target used for external recognition/comparison.
The fields are intentionally explicit to avoid silent strengthening. -/
structure MotivicTargetInterface where
  M : Type u
  [catM : Category.{v} M]
  stableLike : LayerA.StableLike M
  symmetricMonoidalData : Prop
  presentableLikeData : Prop
  nisnevichDescent : Prop
  a1Invariant : Prop
  tateInvertible : Prop

attribute [instance] MotivicTargetInterface.catM

namespace MotivicTargetInterface

/-- API accessor exposing the primary geometry assumptions as a single conjunction `Prop`. -/
def geometric_axioms (T : MotivicTargetInterface) : Prop :=
  T.nisnevichDescent ∧ T.a1Invariant ∧ T.tateInvertible

end MotivicTargetInterface

end LayerC
end TraceCalc
