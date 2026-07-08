import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.DegreeObject.Actual.Owner

/-!
# Concrete bounded representatives for actual mapping-cone degrees

The actual degree object of Mathlib's mapping cone is canonically isomorphic to
the concrete concatenation direct sum used by the analytic additive envelope.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Limits

/-- The explicit concatenation bicone for the shifted-source/target cone degree. -/
def TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom.mappingConeDegreeBinaryBicone
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (degree : ℤ) :
    BinaryBicone
      (source.complex.objectAt (degree + (1 : ℤ)))
      (target.complex.objectAt degree) :=
  TraceAnalyticAdditiveCategory.directSumBinaryBicone
    (source.complex.objectAt (degree + (1 : ℤ)))
    (target.complex.objectAt degree)

/-- The explicit cone-degree bicone is a binary bilimit. -/
def TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom.mappingConeDegreeBinaryBiconeIsBilimit
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (degree : ℤ) :
    (hom.mappingConeDegreeBinaryBicone degree).IsBilimit :=
  isBinaryBilimitOfTotal
    (hom.mappingConeDegreeBinaryBicone degree)
    (TraceAnalyticAdditiveCategory.directSumBinaryBicone_total
      (source.complex.objectAt (degree + (1 : ℤ)))
      (target.complex.objectAt degree))

/-- The abstract biproduct cone degree is isomorphic to the concrete direct-sum object. -/
def TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom.mappingConeDegreeBiprodIsoStandard
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (degree : ℤ) :
    source.complex.objectAt (degree + (1 : ℤ)) ⊞
        target.complex.objectAt degree ≅
      (hom.mappingConeDegreeObject degree).object :=
  (biprod.uniqueUpToIso
    (source.complex.objectAt (degree + (1 : ℤ)))
    (target.complex.objectAt degree)
    (hom.mappingConeDegreeBinaryBiconeIsBilimit degree)).symm

/-- The actual Mathlib cone degree is isomorphic to the concrete bounded degree object. -/
def TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom.actualMappingConeDegreeIsoStandard
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (degree : ℤ) :
    hom.actualMappingConeDegreeObject degree ≅
      (hom.mappingConeDegreeObject degree).object :=
  hom.actualMappingConeDegreeIsoBiprod degree ≪≫
    hom.mappingConeDegreeBiprodIsoStandard degree

end AnalyticMotives
end LFunctions
end Boundary
