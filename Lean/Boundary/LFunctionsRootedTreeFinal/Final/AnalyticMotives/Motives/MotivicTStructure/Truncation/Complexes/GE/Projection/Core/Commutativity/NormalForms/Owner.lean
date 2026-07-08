import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Core.Commutativity.BoundaryCancellation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Core.Commutativity.NonboundaryCancellation.Owner

/-!
# Normal forms for restricted-core projection commutativity

After expanding Mathlib's truncation and restriction differential formulas, both
the boundary and nonboundary commutativity squares reduce to the ambient
differential followed by the target nonboundary truncation isomorphism.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
variable {ι ι' : Type*} {shape : ComplexShape ι} {ambientShape : ComplexShape ι'}

/-- The common normal form for restricted-core upper projection commutativity
at a related source and target in the embedded tail. -/
def truncGEProjectionCoreCommNormalForm
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (source target : ι)
    (hrel : shape.Rel source target) :
    (complex.restriction embedding).X source ⟶
      (complex.truncGE' embedding).X target :=
  complex.d (embedding.f source) (embedding.f target) ≫
    (_root_.HomologicalComplex.truncGE'XIso
      complex
      embedding
      rfl
      (embedding.not_boundaryGE_next hrel)).inv

/-- Projection formula for the common normal form. -/
theorem truncGEProjectionCoreCommNormalForm_eq
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (source target : ι)
    (hrel : shape.Rel source target) :
    truncGEProjectionCoreCommNormalForm
        embedding
        complex
        source
        target
        hrel =
      complex.d (embedding.f source) (embedding.f target) ≫
        (_root_.HomologicalComplex.truncGE'XIso
          complex
          embedding
          rfl
          (embedding.not_boundaryGE_next hrel)).inv :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
