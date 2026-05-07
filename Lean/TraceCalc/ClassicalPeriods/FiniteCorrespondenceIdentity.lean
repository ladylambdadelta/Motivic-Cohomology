import TraceCalc.ClassicalPeriods.ConcreteFiniteCorrespondences

noncomputable section

namespace TraceCalc
namespace ClassicalPeriods
namespace Wall10A

namespace SchemeOverQ

structure DiagonalFiniteCorrespondenceData (X : SchemeOverQ) where
  diagonalSupport : ClosedIntegralSubscheme (prod X X)
  diagonalSource : diagonalSupport.carrier = X
  diagonalMorphism : Hom X (prod X X)
  diagonalMorphism_eq : diagonalMorphism = prod_universal (id X) (id X)
  finiteOverSource : diagonalSupport.IsFiniteOver

namespace ConcreteFiniteCorrespondence

def identity {X : SchemeOverQ} (D : DiagonalFiniteCorrespondenceData X) :
    ConcreteFiniteCorrespondence X X where
  cycle := FiniteCorrespondenceCycle.ofGenerator
    { support := D.diagonalSupport, finiteOverSource := D.finiteOverSource }

end ConcreteFiniteCorrespondence
end SchemeOverQ
end Wall10A
end ClassicalPeriods
end TraceCalc
