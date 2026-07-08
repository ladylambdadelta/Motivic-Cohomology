import Mathlib.Algebra.Homology.HomologicalComplex
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.DirectSum.Owner

/-!
# Complexes in the analytic additive envelope

The triangulated analytic-motive lane is based on cochain complexes of finite
analytic trace families.  The underlying category is the concrete matrix
additive envelope, equipped with its proved zero object and binary biproducts.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Integer cochain complexes in the analytic additive envelope. -/
abbrev TraceAnalyticAdditiveCochainComplex :=
  CochainComplex TraceAnalyticAdditiveCategoryObject ℤ

/-- An additive analytic cochain complex has a finite trace family in each degree. -/
def TraceAnalyticAdditiveCochainComplex.objectAt
    (complex : TraceAnalyticAdditiveCochainComplex)
    (degree : ℤ) :
    TraceAnalyticAdditiveCategoryObject :=
  complex.X degree

/-- Differentials in additive analytic complexes are matrix trace correspondences. -/
def TraceAnalyticAdditiveCochainComplex.differential
    (complex : TraceAnalyticAdditiveCochainComplex)
    (sourceDegree targetDegree : ℤ) :
    complex.objectAt sourceDegree ⟶ complex.objectAt targetDegree :=
  complex.d sourceDegree targetDegree

/-- The object projection is the underlying homological-complex object field. -/
theorem TraceAnalyticAdditiveCochainComplex.objectAt_eq
    (complex : TraceAnalyticAdditiveCochainComplex)
    (degree : ℤ) :
    complex.objectAt degree =
      complex.X degree :=
  rfl

/-- The differential projection is the underlying homological-complex differential. -/
theorem TraceAnalyticAdditiveCochainComplex.differential_eq
    (complex : TraceAnalyticAdditiveCochainComplex)
    (sourceDegree targetDegree : ℤ) :
    complex.differential sourceDegree targetDegree =
      complex.d sourceDegree targetDegree :=
  rfl

/-- Additive analytic differentials square to zero. -/
theorem TraceAnalyticAdditiveCochainComplex.differential_comp_differential
    (complex : TraceAnalyticAdditiveCochainComplex)
    (first second third : ℤ) :
    complex.differential first second ≫
        complex.differential second third =
      0 :=
  HomologicalComplex.d_comp_d complex first second third

/-- The additive analytic cochain-complex category is the standard complex category. -/
def TraceAnalyticAdditiveCochainComplex.categoryStructure :
    CategoryTheory.Category TraceAnalyticAdditiveCochainComplex :=
  inferInstance

end AnalyticMotives
end LFunctions
end Boundary
