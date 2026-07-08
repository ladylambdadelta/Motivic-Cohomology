import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Map.Support.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Components.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Core.Commutativity.RestrictionCancellation.Owner

/-!
# Degree components of the full upper projection map

This file identifies the actual `liftExtend` projection map with the explicit
degreewise component formulas used by the truncation decomposition.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
variable {ι ι' : Type*} {shape : ComplexShape ι} {ambientShape : ComplexShape ι'}

/-- At a nonboundary upper-tail degree, the full upper projection map component
is the inverse of Mathlib's extended nonboundary truncation isomorphism. -/
theorem truncGEProjectionMap_f_of_not_boundary
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (tail : ι)
    (degree : ι')
    (hdegree : embedding.f tail = degree)
    (hboundary : ¬ embedding.BoundaryGE tail) :
    (truncGEProjectionMap embedding complex).f degree =
      (_root_.HomologicalComplex.truncGEXIso
        complex
        embedding
        hdegree
        hboundary).inv :=
  match hdegree with
  | rfl =>
      let mapFormula :
          (truncGEProjectionMap embedding complex).f (embedding.f tail) =
            (_root_.HomologicalComplex.restrictionXIso
                complex
                embedding
                (rfl : embedding.f tail = embedding.f tail)).inv ≫
              (truncGEProjectionCoreMap embedding complex).f tail ≫
              (_root_.HomologicalComplex.extendXIso
                (complex.truncGE' embedding)
                embedding
                (rfl : embedding.f tail = embedding.f tail)).inv :=
        truncGEProjectionMap_f_of_tail
          embedding
          complex
          tail
          (embedding.f tail)
          rfl
      let restrictionInv :
          (_root_.HomologicalComplex.restrictionXIso
              complex
              embedding
              (rfl : embedding.f tail = embedding.f tail)).inv =
            𝟙 (complex.X (embedding.f tail)) :=
        truncGEProjectionCoreRestrictionXIso_inv_id
          embedding
          complex
          tail
      let coreFormula :
          (truncGEProjectionCoreMap embedding complex).f tail =
            (_root_.HomologicalComplex.truncGE'XIso
              complex
              embedding
              (rfl : embedding.f tail = embedding.f tail)
              hboundary).inv :=
        Eq.trans
          (truncGEProjectionCoreMap_f embedding complex tail)
          (truncGEProjectionCoreComponent_of_not_boundary
            embedding
            complex
            tail
            hboundary)
      let extendedIsoInv :
          (complex.truncGE' embedding).X tail ⟶
            (complex.truncGE embedding).X (embedding.f tail) :=
        (_root_.HomologicalComplex.extendXIso
          (complex.truncGE' embedding)
          embedding
          (rfl : embedding.f tail = embedding.f tail)).inv
      let restrictedCore :
          complex.X (embedding.f tail) ⟶
            (complex.truncGE' embedding).X tail :=
        (truncGEProjectionCoreMap embedding complex).f tail
      let removeRestriction :
          ((_root_.HomologicalComplex.restrictionXIso
                complex
                embedding
                (rfl : embedding.f tail = embedding.f tail)).inv ≫
              restrictedCore) ≫
              extendedIsoInv =
            restrictedCore ≫ extendedIsoInv :=
        Eq.trans
          (congrArg
            (fun morphism => (morphism ≫ restrictedCore) ≫ extendedIsoInv)
            restrictionInv)
          (congrArg
            (fun morphism => morphism ≫ extendedIsoInv)
            (Category.id_comp restrictedCore))
      let replaceCore :
          restrictedCore ≫ extendedIsoInv =
            (_root_.HomologicalComplex.truncGE'XIso
              complex
              embedding
              (rfl : embedding.f tail = embedding.f tail)
              hboundary).inv ≫
              extendedIsoInv :=
        congrArg
          (fun morphism => morphism ≫ extendedIsoInv)
          coreFormula
      let liftFormulaReduced :
          (_root_.HomologicalComplex.restrictionXIso
                complex
                embedding
                (rfl : embedding.f tail = embedding.f tail)).inv ≫
              (truncGEProjectionCoreMap embedding complex).f tail ≫
              extendedIsoInv =
            (_root_.HomologicalComplex.truncGE'XIso
              complex
              embedding
              (rfl : embedding.f tail = embedding.f tail)
              hboundary).inv ≫
              extendedIsoInv :=
        Eq.trans
          removeRestriction
          replaceCore
      Eq.trans
        mapFormula
        liftFormulaReduced

/-- At a boundary upper-tail degree, the full upper projection map component
is `pOpcycles` followed by the inverse of Mathlib's extended opcycles
truncation isomorphism. -/
theorem truncGEProjectionMap_f_of_boundary
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (tail : ι)
    (degree : ι')
    (hdegree : embedding.f tail = degree)
    (hboundary : embedding.BoundaryGE tail) :
    (truncGEProjectionMap embedding complex).f degree =
      complex.pOpcycles degree ≫
        (_root_.HomologicalComplex.truncGEXIsoOpcycles
          complex
          embedding
          hdegree
          hboundary).inv :=
  match hdegree with
  | rfl =>
      let mapFormula :
          (truncGEProjectionMap embedding complex).f (embedding.f tail) =
            (_root_.HomologicalComplex.restrictionXIso
                complex
                embedding
                (rfl : embedding.f tail = embedding.f tail)).inv ≫
              (truncGEProjectionCoreMap embedding complex).f tail ≫
              (_root_.HomologicalComplex.extendXIso
                (complex.truncGE' embedding)
                embedding
                (rfl : embedding.f tail = embedding.f tail)).inv :=
        truncGEProjectionMap_f_of_tail
          embedding
          complex
          tail
          (embedding.f tail)
          rfl
      let restrictionInv :
          (_root_.HomologicalComplex.restrictionXIso
              complex
              embedding
              (rfl : embedding.f tail = embedding.f tail)).inv =
            𝟙 (complex.X (embedding.f tail)) :=
        truncGEProjectionCoreRestrictionXIso_inv_id
          embedding
          complex
          tail
      let coreFormula :
          (truncGEProjectionCoreMap embedding complex).f tail =
            complex.pOpcycles (embedding.f tail) ≫
              (_root_.HomologicalComplex.truncGE'XIsoOpcycles
                complex
                embedding
                (rfl : embedding.f tail = embedding.f tail)
                hboundary).inv :=
        Eq.trans
          (truncGEProjectionCoreMap_f embedding complex tail)
          (truncGEProjectionCoreComponent_of_boundary
            embedding
            complex
            tail
            hboundary)
      let extendedIsoInv :
          (complex.truncGE' embedding).X tail ⟶
            (complex.truncGE embedding).X (embedding.f tail) :=
        (_root_.HomologicalComplex.extendXIso
          (complex.truncGE' embedding)
          embedding
          (rfl : embedding.f tail = embedding.f tail)).inv
      let restrictedCore :
          complex.X (embedding.f tail) ⟶
            (complex.truncGE' embedding).X tail :=
        (truncGEProjectionCoreMap embedding complex).f tail
      let removeRestriction :
          ((_root_.HomologicalComplex.restrictionXIso
                complex
                embedding
                (rfl : embedding.f tail = embedding.f tail)).inv ≫
              restrictedCore) ≫
              extendedIsoInv =
            restrictedCore ≫ extendedIsoInv :=
        Eq.trans
          (congrArg
            (fun morphism => (morphism ≫ restrictedCore) ≫ extendedIsoInv)
            restrictionInv)
          (congrArg
            (fun morphism => morphism ≫ extendedIsoInv)
            (Category.id_comp restrictedCore))
      let replaceCore :
          restrictedCore ≫ extendedIsoInv =
            (complex.pOpcycles (embedding.f tail) ≫
                (_root_.HomologicalComplex.truncGE'XIsoOpcycles
                  complex
                  embedding
                  (rfl : embedding.f tail = embedding.f tail)
                  hboundary).inv) ≫
              extendedIsoInv :=
        congrArg
          (fun morphism => morphism ≫ extendedIsoInv)
          coreFormula
      let reassociateOpcycles :
          (complex.pOpcycles (embedding.f tail) ≫
              (_root_.HomologicalComplex.truncGE'XIsoOpcycles
                complex
                embedding
                (rfl : embedding.f tail = embedding.f tail)
                hboundary).inv) ≫
            extendedIsoInv =
          complex.pOpcycles (embedding.f tail) ≫
            ((_root_.HomologicalComplex.truncGE'XIsoOpcycles
                complex
                embedding
                (rfl : embedding.f tail = embedding.f tail)
                hboundary).inv ≫
              extendedIsoInv) :=
        Category.assoc
          (complex.pOpcycles (embedding.f tail))
          ((_root_.HomologicalComplex.truncGE'XIsoOpcycles
            complex
            embedding
            (rfl : embedding.f tail = embedding.f tail)
            hboundary).inv)
          extendedIsoInv
      let liftFormulaReduced :
          (_root_.HomologicalComplex.restrictionXIso
                complex
                embedding
                (rfl : embedding.f tail = embedding.f tail)).inv ≫
              (truncGEProjectionCoreMap embedding complex).f tail ≫
              extendedIsoInv =
            complex.pOpcycles (embedding.f tail) ≫
              ((_root_.HomologicalComplex.truncGE'XIsoOpcycles
                  complex
                  embedding
                  (rfl : embedding.f tail = embedding.f tail)
                  hboundary).inv ≫
                extendedIsoInv) :=
        Eq.trans
          removeRestriction
          (Eq.trans
            replaceCore
            reassociateOpcycles)
      Eq.trans
        mapFormula
        liftFormulaReduced

/-- Analytic integer specialization of the nonboundary component formula for
the full upper truncation projection map. -/
theorem additiveTruncGEProjectionMap_f_of_not_boundary
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (tail : ℕ)
    (degree : ℤ)
    (hdegree :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail =
        degree)
    (hboundary :
      ¬ (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail) :
    (TraceAnalyticMotivicTStructure.additiveTruncGEProjectionMap
        cut
        complex).f degree =
      (_root_.HomologicalComplex.truncGEXIso
        complex
        (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
        hdegree
        hboundary).inv :=
  TraceAnalyticMotivicTStructure.truncGEProjectionMap_f_of_not_boundary
    (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
    complex
    tail
    degree
    hdegree
    hboundary

/-- Analytic integer specialization of the boundary component formula for the
full upper truncation projection map. -/
theorem additiveTruncGEProjectionMap_f_of_boundary
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (tail : ℕ)
    (degree : ℤ)
    (hdegree :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail =
        degree)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail) :
    (TraceAnalyticMotivicTStructure.additiveTruncGEProjectionMap
        cut
        complex).f degree =
      complex.pOpcycles degree ≫
        (_root_.HomologicalComplex.truncGEXIsoOpcycles
          complex
          (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
          hdegree
          hboundary).inv :=
  TraceAnalyticMotivicTStructure.truncGEProjectionMap_f_of_boundary
    (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
    complex
    tail
    degree
    hdegree
    hboundary

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
