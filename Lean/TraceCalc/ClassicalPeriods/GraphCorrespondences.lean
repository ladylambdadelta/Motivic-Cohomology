import TraceCalc.ClassicalPeriods.FiniteCorrespondenceCategoryLaws

noncomputable section

namespace TraceCalc
namespace ClassicalPeriods
namespace Wall10A

namespace SchemeOverQ

structure GraphFiniteCorrespondenceData {X Y : SchemeOverQ} (f : Hom X Y) where
  graphSupport : ClosedIntegralSubscheme (prod X Y)
  graphSource : graphSupport.carrier = X
  graphMorphism : Hom X (prod X Y)
  graphMorphism_eq : graphMorphism = prod_universal (id X) f
  finiteOverSource : graphSupport.IsFiniteOver

def graphCorrespondence {X Y : SchemeOverQ} {f : Hom X Y}
    (G : GraphFiniteCorrespondenceData f) : ConcreteFiniteCorrespondence X Y where
  cycle := FiniteCorrespondenceCycle.ofGenerator
    { support := G.graphSupport, finiteOverSource := G.finiteOverSource }

structure GraphCorrespondenceLawData (composition : CorrespondenceCompositionData) where
  graph_id : ∀ {X : SchemeOverQ} (G : GraphFiniteCorrespondenceData (id X)),
    composition.normalize (graphCorrespondence G) = FiniteCorrespondenceCompositionNF.identity
  graph_comp : ∀ {X Y Z : SchemeOverQ} (f : Hom X Y) (g : Hom Y Z)
    (Gf : GraphFiniteCorrespondenceData f)
    (Gg : GraphFiniteCorrespondenceData g)
    (Ggf : GraphFiniteCorrespondenceData (comp f g)),
    composition.normalize (graphCorrespondence Ggf) =
      FiniteCorrespondenceCompositionNF.comp
        (composition.normalize (graphCorrespondence Gf))
        (composition.normalize (graphCorrespondence Gg))

end SchemeOverQ
end Wall10A
end ClassicalPeriods
end TraceCalc
