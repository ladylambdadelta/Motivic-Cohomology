import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Core.Commutativity.NonboundarySides.Owner

/-!
# Nonboundary reduction for restricted-core projection commutativity

This file reduces the nonboundary left side of the restricted-core projection
commutativity square to the ordinary ambient differential formula, and reduces
the right side to the same restricted ambient expression.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
variable {ι ι' : Type*} {shape : ComplexShape ι} {ambientShape : ComplexShape ι'}

/-- Nonboundary left side after expanding Mathlib's nonboundary truncation
differential. -/
theorem truncGEProjectionCoreNonboundaryCommLeft_eq_differential
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (source target : ι)
    (hrel : shape.Rel source target)
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
        ((_root_.HomologicalComplex.truncGE'XIso
            complex
            embedding
            rfl
            hsource).hom ≫
          complex.d (embedding.f source) (embedding.f target) ≫
          (_root_.HomologicalComplex.truncGE'XIso
            complex
            embedding
            rfl
            (embedding.not_boundaryGE_next hrel)).inv) :=
  congrArg
    (fun differential =>
      (_root_.HomologicalComplex.truncGE'XIso
          complex
          embedding
          rfl
          hsource).inv ≫
        differential)
    (_root_.HomologicalComplex.truncGE'_d_eq
      complex
      embedding
      hrel
      rfl
      rfl
      hsource)

/-- Nonboundary right side after expanding the restricted differential. -/
theorem truncGEProjectionCoreNonboundaryCommRight_eq_restrictionFormula
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
      ((_root_.HomologicalComplex.restrictionXIso
          complex
          embedding
          (rfl : embedding.f source = embedding.f source)).hom ≫
        complex.d (embedding.f source) (embedding.f target) ≫
        (_root_.HomologicalComplex.restrictionXIso
          complex
          embedding
          (rfl : embedding.f target = embedding.f target)).inv) ≫
        (_root_.HomologicalComplex.truncGE'XIso
          complex
          embedding
          rfl
          (embedding.not_boundaryGE_next hrel)).inv :=
  congrArg
    (fun differential =>
      differential ≫
        (_root_.HomologicalComplex.truncGE'XIso
          complex
          embedding
          rfl
          (embedding.not_boundaryGE_next hrel)).inv)
    (_root_.HomologicalComplex.restriction_d_eq
      complex
      embedding
      rfl
      rfl)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
