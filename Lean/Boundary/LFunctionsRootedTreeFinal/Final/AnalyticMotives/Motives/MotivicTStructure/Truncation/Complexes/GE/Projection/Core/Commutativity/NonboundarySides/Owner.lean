import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Core.Components.Owner

/-!
# Nonboundary sides of restricted-core projection commutativity

This file names the two concrete morphism expressions appearing in the
nonboundary case of the restricted-core upper projection commutativity square.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
variable {ι ι' : Type*} {shape : ComplexShape ι} {ambientShape : ComplexShape ι'}

/-- Nonboundary left side:
the nonboundary source core component followed by the truncated differential. -/
def truncGEProjectionCoreNonboundaryCommLeft
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (source target : ι)
    (hsource : ¬ embedding.BoundaryGE source) :
    (complex.restriction embedding).X source ⟶
      (complex.truncGE' embedding).X target :=
  (_root_.HomologicalComplex.truncGE'XIso
      complex
      embedding
      rfl
      hsource).inv ≫
    (complex.truncGE' embedding).d source target

/-- Nonboundary right side:
the restricted differential followed by the nonboundary target core component. -/
def truncGEProjectionCoreNonboundaryCommRight
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (source target : ι)
    (hrel : shape.Rel source target) :
    (complex.restriction embedding).X source ⟶
      (complex.truncGE' embedding).X target :=
  (complex.restriction embedding).d source target ≫
    (_root_.HomologicalComplex.truncGE'XIso
      complex
      embedding
      rfl
      (embedding.not_boundaryGE_next hrel)).inv

/-- Projection formula for the nonboundary left side. -/
theorem truncGEProjectionCoreNonboundaryCommLeft_eq
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (source target : ι)
    (hsource : ¬ embedding.BoundaryGE source) :
    truncGEProjectionCoreNonboundaryCommLeft
        embedding
        complex
        source
        target
        hsource =
      (_root_.HomologicalComplex.truncGE'XIso
          complex
          embedding
          rfl
          hsource).inv ≫
        (complex.truncGE' embedding).d source target :=
  rfl

/-- Projection formula for the nonboundary right side. -/
theorem truncGEProjectionCoreNonboundaryCommRight_eq
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (source target : ι)
    (hrel : shape.Rel source target) :
    truncGEProjectionCoreNonboundaryCommRight
        embedding
        complex
        source
        target
        hrel =
      (complex.restriction embedding).d source target ≫
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
