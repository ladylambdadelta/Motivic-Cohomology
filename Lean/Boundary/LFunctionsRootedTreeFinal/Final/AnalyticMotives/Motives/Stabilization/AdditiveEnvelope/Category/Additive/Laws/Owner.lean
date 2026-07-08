import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.Additive.Entries.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homs.Ext.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Add.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Neg.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Smul.Laws.CoefficientAdditivity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Smul.Laws.ZeroCoefficient.Owner

/-!
# Additive laws for category-level matrix homs

The finite-family category homs inherit their additive laws entrywise from
typed analytic trace correspondences.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The zero category hom is a left unit for category-level hom addition. -/
theorem TraceAnalyticAdditiveCategory.zero_addHom
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : TraceAnalyticAdditiveCategoryHom source target) :
    TraceAnalyticAdditiveCategory.addHom
      (TraceAnalyticAdditiveCategory.zeroHom source target)
      hom =
      hom :=
  TraceAnalyticAdditiveHom.ext
    (fun sourceIndex targetIndex =>
      TraceCorQHom.zero_add
        (hom.entry sourceIndex targetIndex))

/-- The zero category hom is a right unit for category-level hom addition. -/
theorem TraceAnalyticAdditiveCategory.addHom_zero
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : TraceAnalyticAdditiveCategoryHom source target) :
    TraceAnalyticAdditiveCategory.addHom
      hom
      (TraceAnalyticAdditiveCategory.zeroHom source target) =
      hom :=
  TraceAnalyticAdditiveHom.ext
    (fun sourceIndex targetIndex =>
      TraceCorQHom.add_zero
        (hom.entry sourceIndex targetIndex))

/-- Category-level hom addition is associative. -/
theorem TraceAnalyticAdditiveCategory.addHom_assoc
    {source target : TraceAnalyticAdditiveCategoryObject}
    (first second third : TraceAnalyticAdditiveCategoryHom source target) :
    TraceAnalyticAdditiveCategory.addHom
      (TraceAnalyticAdditiveCategory.addHom first second)
      third =
      TraceAnalyticAdditiveCategory.addHom
        first
        (TraceAnalyticAdditiveCategory.addHom second third) :=
  TraceAnalyticAdditiveHom.ext
    (fun sourceIndex targetIndex =>
      TraceCorQHom.add_assoc
        (first.entry sourceIndex targetIndex)
        (second.entry sourceIndex targetIndex)
        (third.entry sourceIndex targetIndex))

/-- Category-level hom addition is commutative. -/
theorem TraceAnalyticAdditiveCategory.addHom_comm
    {source target : TraceAnalyticAdditiveCategoryObject}
    (left right : TraceAnalyticAdditiveCategoryHom source target) :
    TraceAnalyticAdditiveCategory.addHom left right =
      TraceAnalyticAdditiveCategory.addHom right left :=
  TraceAnalyticAdditiveHom.ext
    (fun sourceIndex targetIndex =>
      TraceCorQHom.add_comm
        (left.entry sourceIndex targetIndex)
        (right.entry sourceIndex targetIndex))

/-- Category-level hom negation is a left additive inverse. -/
theorem TraceAnalyticAdditiveCategory.negHom_addHom_self
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : TraceAnalyticAdditiveCategoryHom source target) :
    TraceAnalyticAdditiveCategory.addHom
      (TraceAnalyticAdditiveCategory.negHom hom)
      hom =
      TraceAnalyticAdditiveCategory.zeroHom source target :=
  TraceAnalyticAdditiveHom.ext
    (fun sourceIndex targetIndex =>
      TraceCorQHom.neg_add_self
        (hom.entry sourceIndex targetIndex))

/-- Category-level hom negation is a right additive inverse. -/
theorem TraceAnalyticAdditiveCategory.addHom_negHom_self
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : TraceAnalyticAdditiveCategoryHom source target) :
    TraceAnalyticAdditiveCategory.addHom
      hom
      (TraceAnalyticAdditiveCategory.negHom hom) =
      TraceAnalyticAdditiveCategory.zeroHom source target :=
  TraceAnalyticAdditiveHom.ext
    (fun sourceIndex targetIndex =>
      TraceCorQHom.add_neg_self
        (hom.entry sourceIndex targetIndex))

/-- Scaling the zero category hom gives the zero category hom. -/
theorem TraceAnalyticAdditiveCategory.smulHom_zeroHom
    (coefficient : Rat)
    (source target : TraceAnalyticAdditiveCategoryObject) :
    TraceAnalyticAdditiveCategory.smulHom
      coefficient
      (TraceAnalyticAdditiveCategory.zeroHom source target) =
      TraceAnalyticAdditiveCategory.zeroHom source target :=
  TraceAnalyticAdditiveHom.ext
    (fun sourceIndex targetIndex =>
      TraceCorQHom.smul_zero
        (source.component sourceIndex)
        (target.component targetIndex)
        coefficient)

/-- Scaling a category hom by zero gives the zero category hom. -/
theorem TraceAnalyticAdditiveCategory.zero_smulHom
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : TraceAnalyticAdditiveCategoryHom source target) :
    TraceAnalyticAdditiveCategory.smulHom 0 hom =
      TraceAnalyticAdditiveCategory.zeroHom source target :=
  TraceAnalyticAdditiveHom.ext
    (fun sourceIndex targetIndex =>
      TraceCorQHom.zero_smul
        (hom.entry sourceIndex targetIndex))

/-- Scaling a category hom by one leaves it unchanged. -/
theorem TraceAnalyticAdditiveCategory.one_smulHom
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : TraceAnalyticAdditiveCategoryHom source target) :
    TraceAnalyticAdditiveCategory.smulHom 1 hom =
      hom :=
  TraceAnalyticAdditiveHom.ext
    (fun sourceIndex targetIndex =>
      TraceCorQHom.one_smul
        (hom.entry sourceIndex targetIndex))

/-- Scalar multiplication distributes over category-level hom addition. -/
theorem TraceAnalyticAdditiveCategory.smulHom_addHom
    (coefficient : Rat)
    {source target : TraceAnalyticAdditiveCategoryObject}
    (left right : TraceAnalyticAdditiveCategoryHom source target) :
    TraceAnalyticAdditiveCategory.smulHom
      coefficient
      (TraceAnalyticAdditiveCategory.addHom left right) =
      TraceAnalyticAdditiveCategory.addHom
        (TraceAnalyticAdditiveCategory.smulHom coefficient left)
        (TraceAnalyticAdditiveCategory.smulHom coefficient right) :=
  TraceAnalyticAdditiveHom.ext
    (fun sourceIndex targetIndex =>
      TraceCorQHom.smul_add
        coefficient
        (left.entry sourceIndex targetIndex)
        (right.entry sourceIndex targetIndex))

/-- Scalar multiplication is additive in the scalar coefficient. -/
theorem TraceAnalyticAdditiveCategory.add_smulHom
    (leftCoefficient rightCoefficient : Rat)
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : TraceAnalyticAdditiveCategoryHom source target) :
    TraceAnalyticAdditiveCategory.smulHom
      (leftCoefficient + rightCoefficient)
      hom =
      TraceAnalyticAdditiveCategory.addHom
        (TraceAnalyticAdditiveCategory.smulHom leftCoefficient hom)
        (TraceAnalyticAdditiveCategory.smulHom rightCoefficient hom) :=
  TraceAnalyticAdditiveHom.ext
    (fun sourceIndex targetIndex =>
      TraceCorQHom.add_smul
        leftCoefficient
        rightCoefficient
        (hom.entry sourceIndex targetIndex))

end AnalyticMotives
end LFunctions
end Boundary
