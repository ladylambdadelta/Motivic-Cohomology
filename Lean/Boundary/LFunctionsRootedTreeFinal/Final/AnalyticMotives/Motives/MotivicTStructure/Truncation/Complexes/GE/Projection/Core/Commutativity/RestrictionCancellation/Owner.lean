import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Core.Commutativity.NormalForms.Owner

/-!
# Restriction-isomorphism cancellation for core commutativity

The right-hand reduced side of restricted-core upper projection commutativity
contains the self restriction isomorphisms `restrictionXIso rfl`.  These are
definitionally identity maps; this file owns those identities as named cuts.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
variable {ι ι' : Type*} {shape : ComplexShape ι} {ambientShape : ComplexShape ι'}

/-- The self restriction isomorphism has identity hom map. -/
theorem truncGEProjectionCoreRestrictionXIso_hom_id
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    (tail : ι) :
    (_root_.HomologicalComplex.restrictionXIso
        complex
        embedding
        (rfl : embedding.f tail = embedding.f tail)).hom =
      𝟙 ((complex.restriction embedding).X tail) :=
  rfl

/-- The self restriction isomorphism has identity inverse map. -/
theorem truncGEProjectionCoreRestrictionXIso_inv_id
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    (tail : ι) :
    (_root_.HomologicalComplex.restrictionXIso
        complex
        embedding
        (rfl : embedding.f tail = embedding.f tail)).inv =
      𝟙 (complex.X (embedding.f tail)) :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
