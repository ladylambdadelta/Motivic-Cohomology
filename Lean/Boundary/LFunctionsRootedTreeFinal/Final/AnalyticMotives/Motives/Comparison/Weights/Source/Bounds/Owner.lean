import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Weights.Source.Complexes.Owner

/-!
# Source bounded weights for analytic comparison

This file exposes concrete boundedness data for comparison-source weights:
bounded additive objects, degreewise bounded additive complexes, and chain maps
between bounded complexes.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Comparison-facing boundedness predicate for additive analytic objects. -/
def TraceAnalyticMotiveComparison.sourceAdditiveObjectIsBoundedBy
    (object : TraceAnalyticAdditiveObject)
    (bound : Nat) :
    Prop :=
  object.IsBoundedBy bound

/-- Comparison-facing additive-object boundedness is the concrete weight
inequality. -/
theorem TraceAnalyticMotiveComparison.sourceAdditiveObjectIsBoundedBy_eq
    (object : TraceAnalyticAdditiveObject)
    (bound : Nat) :
    TraceAnalyticMotiveComparison.sourceAdditiveObjectIsBoundedBy object bound =
      (TraceAnalyticMotiveComparison.sourceAdditiveObjectWeight object ≤ bound) :=
  rfl

/-- Comparison-facing additive objects bounded by a numeric weight. -/
abbrev TraceAnalyticMotiveComparison.SourceAdditiveObjectBoundedBy
    (bound : Nat) :=
  TraceAnalyticAdditiveObject.BoundedBy bound

/-- The underlying object of a comparison-source bounded additive object. -/
def TraceAnalyticMotiveComparison.SourceAdditiveObjectBoundedBy.object
    {bound : Nat}
    (object :
      TraceAnalyticMotiveComparison.SourceAdditiveObjectBoundedBy bound) :
    TraceAnalyticAdditiveObject :=
  object.object

/-- A comparison-source bounded additive object supplies its weight
inequality. -/
theorem TraceAnalyticMotiveComparison.SourceAdditiveObjectBoundedBy.weight_le
    {bound : Nat}
    (object :
      TraceAnalyticMotiveComparison.SourceAdditiveObjectBoundedBy bound) :
    TraceAnalyticMotiveComparison.sourceAdditiveObjectWeight object.object ≤
      bound :=
  object.weightLevel_le

/-- The zero additive object is bounded by every comparison-source weight
bound. -/
def TraceAnalyticMotiveComparison.sourceZeroAdditiveObjectBoundedBy
    (bound : Nat) :
    TraceAnalyticMotiveComparison.SourceAdditiveObjectBoundedBy bound :=
  TraceAnalyticAdditiveObject.zeroBoundedBy bound

/-- The underlying object of the bounded zero additive object is zero. -/
theorem TraceAnalyticMotiveComparison.sourceZeroAdditiveObjectBoundedBy_object
    (bound : Nat) :
    (TraceAnalyticMotiveComparison.sourceZeroAdditiveObjectBoundedBy
      bound).object =
      TraceAnalyticAdditiveObject.zero :=
  TraceAnalyticAdditiveObject.zeroBoundedBy_object bound

/-- Comparison-facing boundedness predicate for additive analytic complexes. -/
def TraceAnalyticMotiveComparison.sourceComplexIsWeightBoundedBy
    (complex : TraceAnalyticAdditiveCochainComplex)
    (bound : Nat) :
    Prop :=
  complex.IsWeightBoundedBy bound

/-- Comparison-facing complex boundedness is degreewise boundedness of concrete
source weights. -/
theorem TraceAnalyticMotiveComparison.sourceComplexIsWeightBoundedBy_eq
    (complex : TraceAnalyticAdditiveCochainComplex)
    (bound : Nat) :
    TraceAnalyticMotiveComparison.sourceComplexIsWeightBoundedBy complex bound =
      ((degree : ℤ) →
        TraceAnalyticMotiveComparison.sourceComplexDegreeWeight
          complex
          degree ≤ bound) :=
  rfl

/-- Comparison-facing additive complexes bounded by a numeric weight. -/
abbrev TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
    (bound : Nat) :=
  TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound

/-- The underlying complex of a comparison-source bounded complex. -/
def TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.complex
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    TraceAnalyticAdditiveCochainComplex :=
  complex.complex

/-- A comparison-source bounded complex supplies a degreewise weight bound. -/
theorem TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.degreeWeight_le
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticMotiveComparison.sourceComplexDegreeWeight
        complex.complex
        degree ≤
      bound :=
  complex.degreeWeight_le degree

/-- A degree object of a comparison-source bounded complex is a bounded
additive object. -/
def TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.degreeObject
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticMotiveComparison.SourceAdditiveObjectBoundedBy bound :=
  complex.degreeObject degree

/-- The bounded degree object has the underlying object of the complex in that
degree. -/
theorem TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.degreeObject_object
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (complex.degreeObject degree).object =
      complex.complex.objectAt degree :=
  TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.degreeObject_object
    complex
    degree

/-- Comparison-facing chain maps between bounded additive analytic complexes. -/
abbrev TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
    {bound : Nat}
    (source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :=
  TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target

/-- Identity chain map on a comparison-source bounded complex. -/
def TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.id
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
      complex
      complex :=
  TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.id complex

/-- Composition of chain maps between comparison-source bounded complexes. -/
def TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.comp
    {bound : Nat}
    {first second third :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (left :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        first
        second)
    (right :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        second
        third) :
    TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
      first
      third :=
  TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.comp left right

/-- The comparison-source bounded-complex identity is the underlying complex
identity. -/
theorem TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.id_eq
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.id complex =
      𝟙 complex.complex :=
  TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.id_eq complex

/-- The comparison-source bounded-complex composition is underlying chain-map
composition. -/
theorem TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.comp_eq
    {bound : Nat}
    {first second third :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (left :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        first
        second)
    (right :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        second
        third) :
    TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.comp left right =
      left ≫ right :=
  TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.comp_eq left right

end AnalyticMotives
end LFunctions
end Boundary
