import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Complexes.Owner

/-!
# Weight profiles of additive analytic chain maps

For a chain map between additive analytic complexes, the source and target
weight levels in each degree are computed from the concrete degree objects.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The source weight level of a chain map in one degree. -/
def TraceAnalyticAdditiveCochainComplex.Hom.sourceDegreeWeight
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    (degree : ℤ) :
    Nat :=
  source.degreeWeight degree

/-- The target weight level of a chain map in one degree. -/
def TraceAnalyticAdditiveCochainComplex.Hom.targetDegreeWeight
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    (degree : ℤ) :
    Nat :=
  target.degreeWeight degree

/-- Chain-map source degree weight is the source complex degree weight. -/
theorem TraceAnalyticAdditiveCochainComplex.Hom.sourceDegreeWeight_eq
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    (degree : ℤ) :
    hom.sourceDegreeWeight degree =
      source.degreeWeight degree :=
  rfl

/-- Chain-map target degree weight is the target complex degree weight. -/
theorem TraceAnalyticAdditiveCochainComplex.Hom.targetDegreeWeight_eq
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    (degree : ℤ) :
    hom.targetDegreeWeight degree =
      target.degreeWeight degree :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
