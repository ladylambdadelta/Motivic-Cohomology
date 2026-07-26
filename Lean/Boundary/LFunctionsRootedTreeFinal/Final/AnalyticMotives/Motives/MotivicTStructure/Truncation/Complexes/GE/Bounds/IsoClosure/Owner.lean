import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Bounds.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Complexes.IsoBounded.IsoClosure.Owner

/-!
# Iso-closure bounded upper analytic truncations

This file proves that the concrete upper truncation preserves degreewise
boundedness up to iso-closure.  The proof is pointwise in the degree object:
outside the upper tail the truncation is zero, at the boundary it is the
opcycles object, and away from the boundary it is the original degree object.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

open CategoryTheory

/-- The uniform iso-closure bound for the upper truncation of a degreewise
iso-closure bounded complex. -/
def additiveTruncGEIsoClosureBound
    (cut : ℤ)
    (bound : Nat)
    (complex : TraceAnalyticAdditiveCochainComplex) :
    Nat :=
  Nat.max
    bound
    ((complex.opcycles cut).weightLevel)

/-- The original bound maps into the upper truncation iso-closure bound. -/
theorem additiveTruncGEIsoClosureBound_original_le
    (cut : ℤ)
    (bound : Nat)
    (complex : TraceAnalyticAdditiveCochainComplex) :
    bound ≤
      TraceAnalyticMotivicTStructure.additiveTruncGEIsoClosureBound
        cut
        bound
        complex :=
  Nat.le_max_left
    bound
    ((complex.opcycles cut).weightLevel)

/-- The boundary opcycles weight maps into the upper truncation iso-closure
bound. -/
theorem additiveTruncGEIsoClosureBound_boundary_le
    (cut : ℤ)
    (bound : Nat)
    (complex : TraceAnalyticAdditiveCochainComplex) :
    (complex.opcycles cut).weightLevel ≤
      TraceAnalyticMotivicTStructure.additiveTruncGEIsoClosureBound
        cut
        bound
        complex :=
  Nat.le_max_right
    bound
    ((complex.opcycles cut).weightLevel)

/-- Outside the upper tail, the upper truncation degree object is in the
bounded iso-closure by the zero object. -/
theorem additiveTruncGE_degree_mem_isoClosure_of_r_eq_none
    (cut : ℤ)
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (degree : ℤ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).r degree =
        none) :
    CategoryTheory.isoClosure
      (TraceAnalyticAdditiveObject.boundedObjectRepresentative
        (TraceAnalyticMotivicTStructure.additiveTruncGEIsoClosureBound
          cut
          bound
          complex))
      ((TraceAnalyticMotivicTStructure.additiveTruncGE cut complex).objectAt
        degree) :=
  let object_eq :
      (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex).objectAt
          degree =
        TraceAnalyticAdditiveObject.zero :=
    TraceAnalyticMotivicTStructure.additiveTruncGE_X_of_r_eq_none
      cut
      complex
      degree
      htail
  let zero_mem :
      CategoryTheory.isoClosure
        (TraceAnalyticAdditiveObject.boundedObjectRepresentative
          (TraceAnalyticMotivicTStructure.additiveTruncGEIsoClosureBound
            cut
            bound
            complex))
        TraceAnalyticAdditiveObject.zero :=
    CategoryTheory.le_isoClosure
      (TraceAnalyticAdditiveObject.boundedObjectRepresentative
        (TraceAnalyticMotivicTStructure.additiveTruncGEIsoClosureBound
          cut
          bound
          complex))
      TraceAnalyticAdditiveObject.zero
      (TraceAnalyticAdditiveObject.boundedObjectRepresentative_of_bounded
        (TraceAnalyticAdditiveObject.zeroBoundedBy
          (TraceAnalyticMotivicTStructure.additiveTruncGEIsoClosureBound
            cut
            bound
            complex)))
  Eq.subst
    (motive := fun object =>
      CategoryTheory.isoClosure
        (TraceAnalyticAdditiveObject.boundedObjectRepresentative
          (TraceAnalyticMotivicTStructure.additiveTruncGEIsoClosureBound
            cut
            bound
            complex))
        object)
    (Eq.symm object_eq)
    zero_mem

/-- At the boundary degree, the upper truncation degree object is represented
by the boundary opcycles object. -/
theorem additiveTruncGE_degree_mem_isoClosure_of_boundary
    (cut : ℤ)
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (degree : ℤ)
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).r degree =
        some tail)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail) :
    CategoryTheory.isoClosure
      (TraceAnalyticAdditiveObject.boundedObjectRepresentative
        (TraceAnalyticMotivicTStructure.additiveTruncGEIsoClosureBound
          cut
          bound
          complex))
      ((TraceAnalyticMotivicTStructure.additiveTruncGE cut complex).objectAt
        degree) :=
  let object_eq :
      (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex).objectAt
          degree =
        complex.opcycles degree :=
    TraceAnalyticMotivicTStructure.additiveTruncGE_X_of_boundary
      cut
      complex
      degree
      tail
      htail
      hboundary
  let degree_eq_cut :
      degree = cut :=
    TraceAnalyticMotivicTStructure.truncGEEmbedding_boundary_degree_eq
      cut
      degree
      tail
      htail
      hboundary
  let cut_mem :
      CategoryTheory.isoClosure
        (TraceAnalyticAdditiveObject.boundedObjectRepresentative
          (TraceAnalyticMotivicTStructure.additiveTruncGEIsoClosureBound
            cut
            bound
            complex))
        (complex.opcycles cut) :=
    CategoryTheory.le_isoClosure
      (TraceAnalyticAdditiveObject.boundedObjectRepresentative
        (TraceAnalyticMotivicTStructure.additiveTruncGEIsoClosureBound
          cut
          bound
          complex))
      (complex.opcycles cut)
      (TraceAnalyticAdditiveObject.boundedObjectRepresentative_of_bounded
        ⟨complex.opcycles cut,
          TraceAnalyticMotivicTStructure
            .additiveTruncGEIsoClosureBound_boundary_le
              cut
              bound
              complex⟩)
  let degree_mem :
      CategoryTheory.isoClosure
        (TraceAnalyticAdditiveObject.boundedObjectRepresentative
          (TraceAnalyticMotivicTStructure.additiveTruncGEIsoClosureBound
            cut
            bound
            complex))
        (complex.opcycles degree) :=
    Eq.subst
      (motive := fun boundaryDegree =>
        CategoryTheory.isoClosure
          (TraceAnalyticAdditiveObject.boundedObjectRepresentative
            (TraceAnalyticMotivicTStructure.additiveTruncGEIsoClosureBound
              cut
              bound
              complex))
          (complex.opcycles boundaryDegree))
      (Eq.symm degree_eq_cut)
      cut_mem
  Eq.subst
    (motive := fun object =>
      CategoryTheory.isoClosure
        (TraceAnalyticAdditiveObject.boundedObjectRepresentative
          (TraceAnalyticMotivicTStructure.additiveTruncGEIsoClosureBound
            cut
            bound
            complex))
        object)
    (Eq.symm object_eq)
    degree_mem

/-- On nonboundary upper-tail degrees, upper truncation preserves the existing
degreewise iso-closure bound, after rebounding. -/
theorem additiveTruncGE_degree_mem_isoClosure_of_not_boundary
    (cut : ℤ)
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex)
    (bounded :
      TraceAnalyticAdditiveCochainComplex.DegreewiseIsoClosureBoundedBy
        complex
        bound)
    [∀ degree, complex.HasHomology degree]
    (degree : ℤ)
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).r degree =
        some tail)
    (hboundary :
      ¬ (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail) :
    CategoryTheory.isoClosure
      (TraceAnalyticAdditiveObject.boundedObjectRepresentative
        (TraceAnalyticMotivicTStructure.additiveTruncGEIsoClosureBound
          cut
          bound
          complex))
      ((TraceAnalyticMotivicTStructure.additiveTruncGE cut complex).objectAt
        degree) :=
  let object_eq :
      (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex).objectAt
          degree =
        complex.objectAt degree :=
    TraceAnalyticMotivicTStructure.additiveTruncGE_X_of_not_boundary
      cut
      complex
      degree
      tail
      htail
      hboundary
  let old_mem :
      CategoryTheory.isoClosure
        (TraceAnalyticAdditiveObject.boundedObjectRepresentative
          (TraceAnalyticMotivicTStructure.additiveTruncGEIsoClosureBound
            cut
            bound
            complex))
        (complex.objectAt degree) :=
    TraceAnalyticAdditiveObject.boundedObjectRepresentative_isoClosure_monotone
      (TraceAnalyticMotivicTStructure
        .additiveTruncGEIsoClosureBound_original_le cut bound complex)
      (complex.objectAt degree)
      (bounded degree)
  Eq.subst
    (motive := fun object =>
      CategoryTheory.isoClosure
        (TraceAnalyticAdditiveObject.boundedObjectRepresentative
          (TraceAnalyticMotivicTStructure.additiveTruncGEIsoClosureBound
            cut
            bound
            complex))
        object)
    (Eq.symm object_eq)
    old_mem

/-- Upper analytic truncation preserves degreewise source boundedness up to
iso-closure. -/
theorem additiveTruncGE_sourceComplexDegreewiseIsoClosureBoundedBy
    (cut : ℤ)
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex)
    (bounded :
      TraceAnalyticAdditiveCochainComplex.DegreewiseIsoClosureBoundedBy
        complex
        bound)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticAdditiveCochainComplex.DegreewiseIsoClosureBoundedBy
      (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex)
      (TraceAnalyticMotivicTStructure.additiveTruncGEIsoClosureBound
        cut
        bound
        complex) :=
  fun degree =>
    match htail :
        (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).r degree with
    | none =>
        TraceAnalyticMotivicTStructure
          .additiveTruncGE_degree_mem_isoClosure_of_r_eq_none
            cut
            complex
            degree
            htail
    | some tail =>
        if hboundary :
            (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
              tail then
          TraceAnalyticMotivicTStructure
            .additiveTruncGE_degree_mem_isoClosure_of_boundary
              cut
              complex
              degree
              tail
              htail
              hboundary
        else
          TraceAnalyticMotivicTStructure
            .additiveTruncGE_degree_mem_isoClosure_of_not_boundary
              cut
              complex
              bounded
              degree
              tail
              htail
              hboundary

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
