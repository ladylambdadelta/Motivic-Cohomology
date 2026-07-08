import Mathlib.CategoryTheory.Preadditive.Biproducts
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.Linear.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.Zero.Mathlib.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.DirectSum.CategoryMaps.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.DirectSum.Biproduct.Composites.Full.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.DirectSum.Biproduct.Composites.RightFull.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.DirectSum.Biproduct.Composites.CrossRightLeft.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.DirectSum.Biproduct.Reassembly.Entrywise.Owner

/-!
# Mathlib binary biproducts for analytic additive-envelope direct sums

The concatenation direct sum carries Mathlib's binary-biproduct structure.  The
proof uses the concrete projection/inclusion composite laws and the analytic
matrix reassembly identity.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Limits

/-- The Mathlib binary bicone carried by concatenation of finite trace families. -/
def TraceAnalyticAdditiveCategory.directSumBinaryBicone
    (left right : TraceAnalyticAdditiveCategoryObject) :
    BinaryBicone left right where
  pt :=
    TraceAnalyticAdditiveObject.directSum left right
  fst :=
    TraceAnalyticAdditiveCategory.leftDirectSumProjection left right
  snd :=
    TraceAnalyticAdditiveCategory.rightDirectSumProjection left right
  inl :=
    TraceAnalyticAdditiveCategory.leftDirectSumInclusion left right
  inr :=
    TraceAnalyticAdditiveCategory.rightDirectSumInclusion left right
  inl_fst :=
    TraceAnalyticAdditiveCategory.leftInclusion_comp_leftProjection_eq_id
      left
      right
  inl_snd :=
    Eq.trans
      (TraceAnalyticAdditiveCategory.leftInclusion_comp_rightProjection_eq_zero
        left
        right)
      (TraceAnalyticAdditiveCategory.zeroHom_eq_zero left right)
  inr_fst :=
    Eq.trans
      (TraceAnalyticAdditiveCategory.rightInclusion_comp_leftProjection_eq_zero
        left
        right)
      (TraceAnalyticAdditiveCategory.zeroHom_eq_zero right left)
  inr_snd :=
    TraceAnalyticAdditiveCategory.rightInclusion_comp_rightProjection_eq_id
      left
      right

/-- The direct-sum bicone satisfies Mathlib's binary total identity. -/
theorem TraceAnalyticAdditiveCategory.directSumBinaryBicone_total
    (left right : TraceAnalyticAdditiveCategoryObject) :
    (TraceAnalyticAdditiveCategory.directSumBinaryBicone left right).fst ≫
        (TraceAnalyticAdditiveCategory.directSumBinaryBicone left right).inl +
      (TraceAnalyticAdditiveCategory.directSumBinaryBicone left right).snd ≫
        (TraceAnalyticAdditiveCategory.directSumBinaryBicone left right).inr =
      𝟙 (TraceAnalyticAdditiveCategory.directSumBinaryBicone left right).pt :=
  Eq.trans
    (Eq.symm
      (TraceAnalyticAdditiveHom.add_eq_add
        (TraceAnalyticAdditiveCategory.leftProjection_comp_leftInclusion
          left
          right)
        (TraceAnalyticAdditiveCategory.rightProjection_comp_rightInclusion
          left
          right)))
    (TraceAnalyticAdditiveCategory.directSumReassembly_eq_id
      left
      right)

/-- Concatenation is a binary biproduct in the analytic additive envelope. -/
theorem TraceAnalyticAdditiveCategory.hasBinaryBiproduct
    (left right : TraceAnalyticAdditiveCategoryObject) :
    HasBinaryBiproduct left right :=
  hasBinaryBiproduct_of_total
    (TraceAnalyticAdditiveCategory.directSumBinaryBicone left right)
    (TraceAnalyticAdditiveCategory.directSumBinaryBicone_total left right)

/-- The analytic additive envelope has binary biproducts. -/
instance traceAnalyticAdditiveCategory_hasBinaryBiproducts :
    HasBinaryBiproducts TraceAnalyticAdditiveCategoryObject where
  has_binary_biproduct :=
    fun left right =>
      TraceAnalyticAdditiveCategory.hasBinaryBiproduct left right

end AnalyticMotives
end LFunctions
end Boundary
