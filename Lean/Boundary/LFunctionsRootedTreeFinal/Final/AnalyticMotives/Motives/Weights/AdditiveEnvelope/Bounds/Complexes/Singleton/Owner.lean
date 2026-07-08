import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Complexes.Singleton.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Complexes.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Objects.Singleton.Owner

/-!
# Bounded concentrated singleton complexes

This file packages the degree-zero singleton cochain complex as a bounded
additive analytic complex using the concrete singleton weight bound.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Away from degree zero, a concentrated singleton complex has the concrete zero
additive object. -/
theorem TraceAnalyticAdditiveCochainComplex.concentratedSingleton_objectAt_ne_zero
    (object : TraceCorQObject)
    (degree : ℤ)
    (degree_ne : degree ≠ 0) :
    (TraceAnalyticAdditiveCochainComplex.concentratedSingleton object).objectAt degree =
      TraceAnalyticAdditiveCategory.zeroObject :=
  if_neg degree_ne

/-- The degree-zero weight of a concentrated singleton complex is its singleton weight
bound. -/
theorem TraceAnalyticAdditiveCochainComplex.concentratedSingleton_degreeWeight_zero
    (object : TraceCorQObject) :
    (TraceAnalyticAdditiveCochainComplex.concentratedSingleton object).degreeWeight 0 =
      TraceAnalyticAdditiveObject.singletonWeightBound object :=
  Eq.trans
    (congrArg
      TraceAnalyticAdditiveObject.weightLevel
      (TraceAnalyticAdditiveCochainComplex.concentratedSingleton_objectAt_zero
        object))
    (TraceAnalyticAdditiveObject.singleton_weightLevel object)

/-- A degree identified with zero has the singleton weight bound. -/
theorem TraceAnalyticAdditiveCochainComplex.concentratedSingleton_degreeWeight_of_eq_zero
    (object : TraceCorQObject)
    (degree : ℤ)
    (degree_eq : degree = 0) :
    (TraceAnalyticAdditiveCochainComplex.concentratedSingleton object).degreeWeight degree =
      TraceAnalyticAdditiveObject.singletonWeightBound object :=
  Eq.subst
    (motive := fun shiftedDegree =>
      (TraceAnalyticAdditiveCochainComplex.concentratedSingleton object).degreeWeight
          shiftedDegree =
        TraceAnalyticAdditiveObject.singletonWeightBound object)
    (Eq.symm degree_eq)
    (TraceAnalyticAdditiveCochainComplex.concentratedSingleton_degreeWeight_zero
      object)

/-- Every nonzero degree of a concentrated singleton complex has zero weight. -/
theorem TraceAnalyticAdditiveCochainComplex.concentratedSingleton_degreeWeight_ne_zero
    (object : TraceCorQObject)
    (degree : ℤ)
    (degree_ne : degree ≠ 0) :
    (TraceAnalyticAdditiveCochainComplex.concentratedSingleton object).degreeWeight degree =
      0 :=
  Eq.trans
    (congrArg
      TraceAnalyticAdditiveObject.weightLevel
      (TraceAnalyticAdditiveCochainComplex.concentratedSingleton_objectAt_ne_zero
        object
        degree
        degree_ne))
    TraceAnalyticAdditiveObject.weightLevel_zero

/-- A concentrated singleton complex is bounded by its concrete singleton weight. -/
def TraceAnalyticAdditiveCochainComplex.concentratedSingletonBoundedBy
    (object : TraceCorQObject) :
    TraceAnalyticAdditiveCochainComplex.WeightBoundedBy
      (TraceAnalyticAdditiveObject.singletonWeightBound object) :=
  ⟨TraceAnalyticAdditiveCochainComplex.concentratedSingleton object,
    fun degree =>
      match Classical.decEq degree 0 with
      | isTrue degree_eq =>
          Eq.subst
            (motive := fun weight =>
              weight ≤ TraceAnalyticAdditiveObject.singletonWeightBound object)
            (Eq.symm
              (TraceAnalyticAdditiveCochainComplex.concentratedSingleton_degreeWeight_of_eq_zero
                object
                degree
                degree_eq))
            (Nat.le_refl
              (TraceAnalyticAdditiveObject.singletonWeightBound object))
      | isFalse degree_ne =>
          Eq.subst
            (motive := fun weight =>
              weight ≤ TraceAnalyticAdditiveObject.singletonWeightBound object)
            (Eq.symm
              (TraceAnalyticAdditiveCochainComplex.concentratedSingleton_degreeWeight_ne_zero
                object
                degree
                degree_ne))
            (Nat.zero_le
              (TraceAnalyticAdditiveObject.singletonWeightBound object))⟩

/-- The bounded concentrated singleton package has the concentrated singleton complex
underneath. -/
theorem TraceAnalyticAdditiveCochainComplex.concentratedSingletonBoundedBy_complex
    (object : TraceCorQObject) :
    (TraceAnalyticAdditiveCochainComplex.concentratedSingletonBoundedBy object).complex =
      TraceAnalyticAdditiveCochainComplex.concentratedSingleton object :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
