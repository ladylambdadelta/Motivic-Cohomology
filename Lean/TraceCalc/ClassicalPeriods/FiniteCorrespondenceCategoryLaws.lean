import TraceCalc.ClassicalPeriods.FiniteCorrespondenceComposition

noncomputable section

namespace TraceCalc
namespace ClassicalPeriods
namespace Wall10A

namespace SchemeOverQ

namespace ConcreteFiniteCorrespondenceCategory

theorem identity_left {composition : CorrespondenceCompositionData}
    {X Y : SchemeOverQ} (D : DiagonalFiniteCorrespondenceData X)
    (a : ConcreteFiniteCorrespondence X Y) :
    composition.compose (ConcreteFiniteCorrespondence.identity D) a = a :=
  composition.compose_left_identity D a

theorem identity_right {composition : CorrespondenceCompositionData}
    {X Y : SchemeOverQ} (a : ConcreteFiniteCorrespondence X Y)
    (D : DiagonalFiniteCorrespondenceData Y) :
    composition.compose a (ConcreteFiniteCorrespondence.identity D) = a :=
  composition.compose_right_identity a D

theorem composition_assoc {composition : CorrespondenceCompositionData}
    {W X Y Z : SchemeOverQ}
    (a : ConcreteFiniteCorrespondence W X)
    (b : ConcreteFiniteCorrespondence X Y)
    (c : ConcreteFiniteCorrespondence Y Z) :
    composition.compose (composition.compose a b) c =
      composition.compose a (composition.compose b c) :=
  composition.compose_assoc a b c

end ConcreteFiniteCorrespondenceCategory
end SchemeOverQ
end Wall10A
end ClassicalPeriods
end TraceCalc
