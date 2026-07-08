import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Core.Commutativity.NonboundaryReduction.Owner

/-!
# Nonboundary cancellation for restricted-core projection commutativity

The nonboundary equality reduces to cancellation of the inverse and hom of
Mathlib's nonboundary `truncGE'` isomorphism.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
variable {ι ι' : Type*} {shape : ComplexShape ι} {ambientShape : ComplexShape ι'}

/-- The nonboundary truncation isomorphism cancels in the source degree. -/
theorem truncGEProjectionCoreNonboundary_inv_hom_id
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (source : ι)
    (hsource : ¬ embedding.BoundaryGE source) :
    (_root_.HomologicalComplex.truncGE'XIso
        complex
        embedding
        rfl
        hsource).inv ≫
      (_root_.HomologicalComplex.truncGE'XIso
        complex
        embedding
        rfl
        hsource).hom =
      𝟙 ((complex.restriction embedding).X source) :=
  (_root_.HomologicalComplex.truncGE'XIso
    complex
    embedding
    rfl
    hsource).inv_hom_id

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
