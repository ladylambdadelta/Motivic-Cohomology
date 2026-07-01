import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.CategoryLaws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.LinearTransfers.QLinearization.Owner

/-!
# Comparison with the presheaf transfer linearization

This owner compares the `ContourCor_Q` formal-sum presentation with the older
`RationalContourCombination` presentation used by the transfer-presheaf layer.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace ContourCorQFormalSum

/-- Convert a `ContourCor_Q` formal sum to the transfer-presheaf linearization. -/
def toRationalContourCombination {X Y : ContourCorQObject}
    (S : ContourCorQFormalSum X Y) :
    RationalContourCombination X Y where
  Index := S.Index
  finiteIndex := S.finiteIndex
  coefficient := S.coefficient
  correspondence := S.correspondence

/-- Convert a transfer-presheaf rational combination to a `ContourCor_Q` formal sum. -/
def ofRationalContourCombination {X Y : ContourCorQObject}
    (S : RationalContourCombination X Y) :
    ContourCorQFormalSum X Y where
  Index := S.Index
  finiteIndex := S.finiteIndex
  coefficient := S.coefficient
  correspondence := S.correspondence

/-- Coefficients are unchanged by conversion to the presheaf linearization. -/
theorem toRationalContourCombination_coefficient {X Y : ContourCorQObject}
    (S : ContourCorQFormalSum X Y)
    (i : S.Index) :
    (toRationalContourCombination S).coefficient i = S.coefficient i :=
  rfl

/-- Correspondences are unchanged by conversion to the presheaf linearization. -/
theorem toRationalContourCombination_correspondence {X Y : ContourCorQObject}
    (S : ContourCorQFormalSum X Y)
    (i : S.Index) :
    (toRationalContourCombination S).correspondence i = S.correspondence i :=
  rfl

/-- Converting a presheaf rational combination to `ContourCor_Q` and back is exact. -/
theorem to_of_RationalContourCombination {X Y : ContourCorQObject}
    (S : RationalContourCombination X Y) :
    toRationalContourCombination (ofRationalContourCombination S) = S :=
  rfl

/-- Converting a `ContourCor_Q` formal sum to the presheaf presentation and back is exact. -/
theorem of_to_RationalContourCombination {X Y : ContourCorQObject}
    (S : ContourCorQFormalSum X Y) :
    ofRationalContourCombination (toRationalContourCombination S) = S :=
  rfl

/-- `ContourCor_Q` reindexing gives presheaf rational-combination reindexing. -/
def reindexing_toRationalContourCombination {X Y : ContourCorQObject}
    {S T : ContourCorQFormalSum X Y}
    (R : ContourCorQFormalSumReindexing S T) :
    RationalContourCombinationReindexing
      (toRationalContourCombination S)
      (toRationalContourCombination T) where
  indexEquiv := R.indexEquiv
  coefficient_eq := R.coefficient_eq
  correspondence_eq := R.correspondence_eq

/-- Presheaf rational-combination reindexing gives `ContourCor_Q` reindexing. -/
def reindexing_ofRationalContourCombination {X Y : ContourCorQObject}
    {S T : RationalContourCombination X Y}
    (R : RationalContourCombinationReindexing S T) :
    ContourCorQFormalSumReindexing
      (ofRationalContourCombination S)
      (ofRationalContourCombination T) where
  indexEquiv := R.indexEquiv
  coefficient_eq := R.coefficient_eq
  correspondence_eq := R.correspondence_eq

/-- The `ContourCor_Q` identity sum agrees with the presheaf identity combination. -/
theorem identity_toRationalContourCombination
    (C : ContourCorrespondenceCalculus)
    (X : ContourCorQObject) :
    toRationalContourCombination
        (ContourCorQFormalSum.single (C.identityAt X)) =
      RationalContourCombination.identity C.laws X :=
  rfl

/-- `ContourCor_Q` formal composition agrees with presheaf rational composition. -/
theorem comp_toRationalContourCombination
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQObject}
    (S : ContourCorQFormalSum X Y)
    (T : ContourCorQFormalSum Y Z) :
    toRationalContourCombination (ContourCorQFormalSum.comp C S T) =
      RationalContourCombination.comp
        C.laws
        (toRationalContourCombination S)
        (toRationalContourCombination T) :=
  rfl

end ContourCorQFormalSum

end AnalyticMotives
end LFunctions
end Boundary
