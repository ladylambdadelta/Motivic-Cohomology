import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Core.Map.Owner

/-!
# Lift condition for the restricted-core upper projection

The restricted-core upper projection extends across the zero side of the GE
embedding because every incoming differential into a boundary degree is killed
by the opcycles quotient used in the boundary component.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
variable {ι ι' : Type*} {shape : ComplexShape ι} {ambientShape : ComplexShape ι'}

/-- The restricted-core upper projection satisfies Mathlib's `HasLift`
condition for extending a restricted map across the GE embedding. -/
theorem truncGEProjectionCoreMap_hasLift
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree] :
    embedding.HasLift
      (truncGEProjectionCoreMap embedding complex) :=
  fun tail hboundary incoming hincoming =>
    let incomingDifferential :
        complex.X incoming ⟶ complex.X (embedding.f tail) :=
      complex.d incoming (embedding.f tail)
    let boundaryProjection :
        complex.X (embedding.f tail) ⟶
          complex.opcycles (embedding.f tail) :=
      complex.pOpcycles (embedding.f tail)
    let boundaryIsoInv :
        complex.opcycles (embedding.f tail) ⟶
          (complex.truncGE' embedding).X tail :=
      (_root_.HomologicalComplex.truncGE'XIsoOpcycles
        complex
        embedding
        rfl
        hboundary).inv
    let mapComponent :
        incomingDifferential ≫
            (truncGEProjectionCoreMap embedding complex).f tail =
          incomingDifferential ≫
            truncGEProjectionCoreComponent embedding complex tail :=
      congrArg
        (fun component => incomingDifferential ≫ component)
        (truncGEProjectionCoreMap_f embedding complex tail)
    let boundaryComponent :
        incomingDifferential ≫
            truncGEProjectionCoreComponent embedding complex tail =
          incomingDifferential ≫
            (boundaryProjection ≫ boundaryIsoInv) :=
      congrArg
        (fun component => incomingDifferential ≫ component)
        (truncGEProjectionCoreComponent_of_boundary
          embedding
          complex
          tail
          hboundary)
    let reassociate :
        incomingDifferential ≫ (boundaryProjection ≫ boundaryIsoInv) =
          (incomingDifferential ≫ boundaryProjection) ≫ boundaryIsoInv :=
      Eq.symm
        (Category.assoc incomingDifferential boundaryProjection boundaryIsoInv)
    let boundaryVanishing :
        incomingDifferential ≫ boundaryProjection = 0 :=
      truncGEProjectionBoundary_d_pOpcycles
        embedding
        complex
        tail
        incoming
        hboundary
        hincoming
    let vanishAfterIso :
        (incomingDifferential ≫ boundaryProjection) ≫ boundaryIsoInv = 0 :=
      Eq.trans
        (congrArg
          (fun morphism => morphism ≫ boundaryIsoInv)
          boundaryVanishing)
        (zero_comp boundaryIsoInv)
    Eq.trans
      mapComponent
      (Eq.trans
        boundaryComponent
        (Eq.trans reassociate vanishAfterIso))

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
