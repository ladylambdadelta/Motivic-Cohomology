import TraceCalc.ClassicalPeriods.GraphCorrespondences
import TraceCalc.ClassicalPeriods.VoevodskyFiniteCorrespondences

noncomputable section

namespace TraceCalc
namespace ClassicalPeriods
namespace Wall10A

namespace SchemeOverQ

open VoevodskyFiniteCorrespondences

def geometricBase : GeometricBase where
  Scheme := SchemeOverQ
  product := prod
  tripleProduct := tripleProduct

structure Wall10BCycleTermRealization {X : SchemeOverQ} (Z : ClosedIntegralSubscheme X) where
  genericPoint : Z.carrier.X

def toWall10BCycleTerm {X : SchemeOverQ} (Z : ClosedIntegralSubscheme X)
    (R : Wall10BCycleTermRealization Z) :
    CycleTerm geometricBase X where
  support :=
    { carrier := Z.carrier.X
      genericPoint := R.genericPoint }
  multiplicity := 1

def toWall10BFiniteCorrespondence {X Y : SchemeOverQ}
    (C : ConcreteFiniteCorrespondence X Y) :
    FiniteCorrespondence geometricBase X Y where
  representative :=
    { cycle := CycleClass.zero
      finiteOverSource :=
        { finiteWitness := ConcreteFiniteCorrespondence X Y
          finiteProof := C } }

structure ConcreteWall10ABridgeData
    (diagonal : ∀ X : SchemeOverQ, DiagonalFiniteCorrespondenceData X)
    (composition : CorrespondenceCompositionData) where
  graphLaws : GraphCorrespondenceLawData composition

namespace ConcreteWall10ABridgeData

theorem identity_holds
    {diagonal : ∀ X : SchemeOverQ, DiagonalFiniteCorrespondenceData X}
    {composition : CorrespondenceCompositionData}
    (_bridge : ConcreteWall10ABridgeData diagonal composition)
    {X Y : SchemeOverQ} (a : ConcreteFiniteCorrespondence X Y) :
    composition.compose (ConcreteFiniteCorrespondence.identity (diagonal X)) a = a :=
  ConcreteFiniteCorrespondenceCategory.identity_left (diagonal X) a

theorem composition_assoc
    {diagonal : ∀ X : SchemeOverQ, DiagonalFiniteCorrespondenceData X}
    {composition : CorrespondenceCompositionData}
    (_bridge : ConcreteWall10ABridgeData diagonal composition)
    {W X Y Z : SchemeOverQ}
    (a : ConcreteFiniteCorrespondence W X)
    (b : ConcreteFiniteCorrespondence X Y)
    (c : ConcreteFiniteCorrespondence Y Z) :
    composition.compose (composition.compose a b) c =
      composition.compose a (composition.compose b c) :=
  ConcreteFiniteCorrespondenceCategory.composition_assoc a b c

end ConcreteWall10ABridgeData
end SchemeOverQ
end Wall10A
end ClassicalPeriods
end TraceCalc
