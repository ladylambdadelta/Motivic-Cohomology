import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.Zero.Mathlib.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Complexes.Owner

/-!
# The bounded zero additive analytic complex

This file owns a concrete zero cochain complex whose every degree is the
analytic additive-envelope zero object, and proves that it is bounded by every
numeric weight level.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The concrete zero additive analytic cochain complex. -/
def TraceAnalyticAdditiveCochainComplex.zeroConcrete :
    TraceAnalyticAdditiveCochainComplex where
  X :=
    fun _ =>
      TraceAnalyticAdditiveCategory.zeroObject
  d :=
    fun _ _ =>
      0
  shape :=
    fun _ _ _ =>
      rfl
  d_comp_d' :=
    fun _ _ _ _ _ =>
      TraceAnalyticAdditiveCategory.hom_to_zero_ext
        TraceAnalyticAdditiveCategory.zeroObject
        (0 ≫ 0)
        0

/-- Every degree object of the concrete zero complex is the analytic additive
zero object. -/
theorem TraceAnalyticAdditiveCochainComplex.zeroConcrete_objectAt
    (degree : ℤ) :
    TraceAnalyticAdditiveCochainComplex.zeroConcrete.objectAt degree =
      TraceAnalyticAdditiveCategory.zeroObject :=
  rfl

/-- Every degree of the concrete zero complex has weight zero. -/
theorem TraceAnalyticAdditiveCochainComplex.zeroConcrete_degreeWeight
    (degree : ℤ) :
    TraceAnalyticAdditiveCochainComplex.zeroConcrete.degreeWeight degree =
      0 :=
  TraceAnalyticAdditiveObject.weightLevel_zero

/-- The concrete zero cochain complex is bounded by every numeric weight
level. -/
def TraceAnalyticAdditiveCochainComplex.zeroBoundedBy
    (bound : Nat) :
    TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound :=
  ⟨TraceAnalyticAdditiveCochainComplex.zeroConcrete,
    fun degree =>
      Eq.subst
        (motive := fun weight =>
          weight ≤ bound)
        (Eq.symm
          (TraceAnalyticAdditiveCochainComplex.zeroConcrete_degreeWeight
            degree))
        (Nat.zero_le bound)⟩

/-- The bounded zero complex has the concrete zero complex underneath. -/
theorem TraceAnalyticAdditiveCochainComplex.zeroBoundedBy_complex
    (bound : Nat) :
    (TraceAnalyticAdditiveCochainComplex.zeroBoundedBy bound).complex =
      TraceAnalyticAdditiveCochainComplex.zeroConcrete :=
  rfl

/-- The bounded zero complex has the analytic additive zero object in every
degree. -/
theorem TraceAnalyticAdditiveCochainComplex.zeroBoundedBy_degreeObject_object
    (bound : Nat)
    (degree : ℤ) :
    ((TraceAnalyticAdditiveCochainComplex.zeroBoundedBy bound).degreeObject
        degree).object =
      TraceAnalyticAdditiveCategory.zeroObject :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
