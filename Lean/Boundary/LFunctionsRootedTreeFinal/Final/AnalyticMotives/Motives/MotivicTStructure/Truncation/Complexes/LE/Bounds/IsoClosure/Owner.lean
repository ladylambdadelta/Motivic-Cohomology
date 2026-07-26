import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.LE.Bounds.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Complexes.IsoBounded.IsoClosure.Owner

/-!
# Iso-closure bounded lower analytic truncations

This file proves that the concrete lower truncation preserves degreewise
boundedness up to iso-closure.  The proof follows the concrete lower-tail
normal forms and uses the actual boundary degree object introduced at the cut
as the extra bounded representative.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

open CategoryTheory

/-- The uniform iso-closure bound for the lower truncation of a degreewise
iso-closure bounded complex. -/
def additiveTruncLEIsoClosureBound
    (cut : ℤ)
    (bound : Nat)
    (complex : TraceAnalyticAdditiveCochainComplex) :
    Nat :=
  Nat.max
    bound
    ((TraceAnalyticMotivicTStructure.additiveTruncLE
      cut
      complex).degreeWeight cut)

/-- The original bound maps into the lower truncation iso-closure bound. -/
theorem additiveTruncLEIsoClosureBound_original_le
    (cut : ℤ)
    (bound : Nat)
    (complex : TraceAnalyticAdditiveCochainComplex) :
    bound ≤
      TraceAnalyticMotivicTStructure.additiveTruncLEIsoClosureBound
        cut
        bound
        complex :=
  Nat.le_max_left
    bound
    ((TraceAnalyticMotivicTStructure.additiveTruncLE
      cut
      complex).degreeWeight cut)

/-- The lower truncation boundary degree weight maps into the lower truncation
iso-closure bound. -/
theorem additiveTruncLEIsoClosureBound_boundary_le
    (cut : ℤ)
    (bound : Nat)
    (complex : TraceAnalyticAdditiveCochainComplex) :
    (TraceAnalyticMotivicTStructure.additiveTruncLE
      cut
      complex).degreeWeight cut ≤
      TraceAnalyticMotivicTStructure.additiveTruncLEIsoClosureBound
        cut
        bound
        complex :=
  Nat.le_max_right
    bound
    ((TraceAnalyticMotivicTStructure.additiveTruncLE
      cut
      complex).degreeWeight cut)

/-- Outside the lower tail, the lower truncation degree object is in the
bounded iso-closure by the zero object. -/
theorem additiveTruncLE_degree_mem_isoClosure_of_r_eq_none
    (cut : ℤ)
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (degree : ℤ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).r degree =
        none) :
    CategoryTheory.isoClosure
      (TraceAnalyticAdditiveObject.boundedObjectRepresentative
        (TraceAnalyticMotivicTStructure.additiveTruncLEIsoClosureBound
          cut
          bound
          complex))
      ((TraceAnalyticMotivicTStructure.additiveTruncLE cut complex).objectAt
        degree) :=
  let object_eq :
      (TraceAnalyticMotivicTStructure.additiveTruncLE cut complex).objectAt
          degree =
        TraceAnalyticAdditiveObject.zero :=
    TraceAnalyticMotivicTStructure.additiveTruncLE_X_of_r_eq_none
      cut
      complex
      degree
      htail
  let zero_mem :
      CategoryTheory.isoClosure
        (TraceAnalyticAdditiveObject.boundedObjectRepresentative
          (TraceAnalyticMotivicTStructure.additiveTruncLEIsoClosureBound
            cut
            bound
            complex))
        TraceAnalyticAdditiveObject.zero :=
    CategoryTheory.le_isoClosure
      (TraceAnalyticAdditiveObject.boundedObjectRepresentative
        (TraceAnalyticMotivicTStructure.additiveTruncLEIsoClosureBound
          cut
          bound
          complex))
      TraceAnalyticAdditiveObject.zero
      (TraceAnalyticAdditiveObject.boundedObjectRepresentative_of_bounded
        (TraceAnalyticAdditiveObject.zeroBoundedBy
          (TraceAnalyticMotivicTStructure.additiveTruncLEIsoClosureBound
            cut
            bound
            complex)))
  Eq.subst
    (motive := fun object =>
      CategoryTheory.isoClosure
        (TraceAnalyticAdditiveObject.boundedObjectRepresentative
          (TraceAnalyticMotivicTStructure.additiveTruncLEIsoClosureBound
            cut
            bound
            complex))
        object)
    (Eq.symm object_eq)
    zero_mem

/-- At the lower boundary degree, the lower truncation degree object is bounded
by the boundary degree built into the enlarged bound. -/
theorem additiveTruncLE_degree_mem_isoClosure_of_boundary
    (cut : ℤ)
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (degree : ℤ)
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).r degree =
        some tail)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op.BoundaryGE
        tail) :
    CategoryTheory.isoClosure
      (TraceAnalyticAdditiveObject.boundedObjectRepresentative
        (TraceAnalyticMotivicTStructure.additiveTruncLEIsoClosureBound
          cut
          bound
          complex))
      ((TraceAnalyticMotivicTStructure.additiveTruncLE cut complex).objectAt
        degree) :=
  let degree_eq_cut :
      degree = cut :=
    TraceAnalyticMotivicTStructure.truncLEEmbedding_boundary_degree_eq
      cut
      degree
      tail
      htail
      hboundary
  let cut_mem :
      CategoryTheory.isoClosure
        (TraceAnalyticAdditiveObject.boundedObjectRepresentative
          (TraceAnalyticMotivicTStructure.additiveTruncLEIsoClosureBound
            cut
            bound
            complex))
        ((TraceAnalyticMotivicTStructure.additiveTruncLE cut complex).objectAt
          cut) :=
    CategoryTheory.le_isoClosure
      (TraceAnalyticAdditiveObject.boundedObjectRepresentative
        (TraceAnalyticMotivicTStructure.additiveTruncLEIsoClosureBound
          cut
          bound
          complex))
      ((TraceAnalyticMotivicTStructure.additiveTruncLE cut complex).objectAt
        cut)
      (TraceAnalyticAdditiveObject.boundedObjectRepresentative_of_bounded
        ⟨(TraceAnalyticMotivicTStructure.additiveTruncLE
            cut
            complex).objectAt cut,
          Eq.subst
            (motive := fun weight =>
              weight ≤
                TraceAnalyticMotivicTStructure.additiveTruncLEIsoClosureBound
                  cut
                  bound
                  complex)
            (Eq.symm
              (TraceAnalyticAdditiveCochainComplex.degreeWeight_eq
                (TraceAnalyticMotivicTStructure.additiveTruncLE cut complex)
                cut))
            (TraceAnalyticMotivicTStructure
              .additiveTruncLEIsoClosureBound_boundary_le
                cut
                bound
                complex)⟩)
  Eq.subst
    (motive := fun boundaryDegree =>
      CategoryTheory.isoClosure
        (TraceAnalyticAdditiveObject.boundedObjectRepresentative
          (TraceAnalyticMotivicTStructure.additiveTruncLEIsoClosureBound
            cut
            bound
            complex))
        ((TraceAnalyticMotivicTStructure.additiveTruncLE cut complex).objectAt
          boundaryDegree))
    (Eq.symm degree_eq_cut)
    cut_mem

/-- On nonboundary lower-tail degrees, lower truncation preserves the existing
degreewise iso-closure bound, after rebounding. -/
theorem additiveTruncLE_degree_mem_isoClosure_of_not_boundary
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
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).r degree =
        some tail)
    (hboundary :
      ¬ (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op.BoundaryGE
        tail) :
    CategoryTheory.isoClosure
      (TraceAnalyticAdditiveObject.boundedObjectRepresentative
        (TraceAnalyticMotivicTStructure.additiveTruncLEIsoClosureBound
          cut
          bound
          complex))
      ((TraceAnalyticMotivicTStructure.additiveTruncLE cut complex).objectAt
        degree) :=
  let object_eq :
      (TraceAnalyticMotivicTStructure.additiveTruncLE cut complex).objectAt
          degree =
        complex.objectAt degree :=
    TraceAnalyticMotivicTStructure.additiveTruncLE_X_of_not_boundary
      cut
      complex
      degree
      tail
      htail
      hboundary
  let old_mem :
      CategoryTheory.isoClosure
        (TraceAnalyticAdditiveObject.boundedObjectRepresentative
          (TraceAnalyticMotivicTStructure.additiveTruncLEIsoClosureBound
            cut
            bound
            complex))
        (complex.objectAt degree) :=
    TraceAnalyticAdditiveObject.boundedObjectRepresentative_isoClosure_monotone
      (TraceAnalyticMotivicTStructure
        .additiveTruncLEIsoClosureBound_original_le cut bound complex)
      (complex.objectAt degree)
      (bounded degree)
  Eq.subst
    (motive := fun object =>
      CategoryTheory.isoClosure
        (TraceAnalyticAdditiveObject.boundedObjectRepresentative
          (TraceAnalyticMotivicTStructure.additiveTruncLEIsoClosureBound
            cut
            bound
            complex))
        object)
    (Eq.symm object_eq)
    old_mem

/-- Lower analytic truncation preserves degreewise source boundedness up to
iso-closure. -/
theorem additiveTruncLE_sourceComplexDegreewiseIsoClosureBoundedBy
    (cut : ℤ)
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex)
    (bounded :
      TraceAnalyticAdditiveCochainComplex.DegreewiseIsoClosureBoundedBy
        complex
        bound)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticAdditiveCochainComplex.DegreewiseIsoClosureBoundedBy
      (TraceAnalyticMotivicTStructure.additiveTruncLE cut complex)
      (TraceAnalyticMotivicTStructure.additiveTruncLEIsoClosureBound
        cut
        bound
        complex) :=
  fun degree =>
    match htail :
        (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).r degree with
    | none =>
        TraceAnalyticMotivicTStructure
          .additiveTruncLE_degree_mem_isoClosure_of_r_eq_none
            cut
            complex
            degree
            htail
    | some tail =>
        if hboundary :
            (TraceAnalyticMotivicTStructure.truncLEEmbedding cut)
              .op
              .BoundaryGE
              tail then
          TraceAnalyticMotivicTStructure
            .additiveTruncLE_degree_mem_isoClosure_of_boundary
              cut
              complex
              degree
              tail
              htail
              hboundary
        else
          TraceAnalyticMotivicTStructure
            .additiveTruncLE_degree_mem_isoClosure_of_not_boundary
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
