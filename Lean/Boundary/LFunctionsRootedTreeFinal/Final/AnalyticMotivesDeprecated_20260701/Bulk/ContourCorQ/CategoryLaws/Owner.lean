import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.Composition.Identity.Quotient.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.Composition.Associativity.Quotient.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.Composition.Quotient.Laws.Owner

/-!
# Category laws for `ContourCor_Q`

This owner packages the rationally linearized contour-correspondence category
modulo finite reindexing.  The identity and associativity laws are inherited
from the raw contour-correspondence calculus through explicit formal-sum
reindexing.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Objects of the reindexing quotient contour-correspondence category. -/
def ContourCorQQuotientObject : Type :=
  ContourCorQObject

/-- Homs of the reindexing quotient contour-correspondence category. -/
def ContourCorQQuotientHom
    (X Y : ContourCorQQuotientObject) : Type :=
  ContourCorQFormalSum.QuotientHom X Y

namespace ContourCorQQuotientHom

/-- Identity hom in the reindexing quotient category. -/
def identity
    (C : ContourCorrespondenceCalculus)
    (X : ContourCorQQuotientObject) :
    ContourCorQQuotientHom X X :=
  ContourCorQFormalSum.identityClass C X

/-- Composition in the reindexing quotient category. -/
def comp
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQQuotientObject}
    (F : ContourCorQQuotientHom X Y)
    (G : ContourCorQQuotientHom Y Z) :
    ContourCorQQuotientHom X Z :=
  ContourCorQFormalSum.compClass C F G

/-- Left identity law for reindexing quotient contour homs. -/
theorem identity_comp
    (C : ContourCorrespondenceCalculus)
    {X Y : ContourCorQQuotientObject}
    (F : ContourCorQQuotientHom X Y) :
    comp C (identity C X) F = F :=
  ContourCorQFormalSum.compClass_identity_left C F

/-- Right identity law for reindexing quotient contour homs. -/
theorem comp_identity
    (C : ContourCorrespondenceCalculus)
    {X Y : ContourCorQQuotientObject}
    (F : ContourCorQQuotientHom X Y) :
    comp C F (identity C Y) = F :=
  ContourCorQFormalSum.compClass_identity_right C F

/-- Associativity law for reindexing quotient contour homs. -/
theorem comp_assoc
    (C : ContourCorrespondenceCalculus)
    {W X Y Z : ContourCorQQuotientObject}
    (F : ContourCorQQuotientHom W X)
    (G : ContourCorQQuotientHom X Y)
    (H : ContourCorQQuotientHom Y Z) :
    comp C (comp C F G) H = comp C F (comp C G H) :=
  ContourCorQFormalSum.compClass_assoc C F G H

/-- Composition with a zero left input is zero. -/
theorem comp_zero_left
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQQuotientObject}
    (G : ContourCorQQuotientHom Y Z) :
    comp C (ContourCorQFormalSum.zeroClass X Y) G =
      ContourCorQFormalSum.zeroClass X Z :=
  ContourCorQFormalSum.compClass_zero_left C G

/-- Composition with a zero right input is zero. -/
theorem comp_zero_right
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQQuotientObject}
    (F : ContourCorQQuotientHom X Y) :
    comp C F (ContourCorQFormalSum.zeroClass Y Z) =
      ContourCorQFormalSum.zeroClass X Z :=
  ContourCorQFormalSum.compClass_zero_right C F

/-- Composition is additive in the left input. -/
theorem comp_add_left
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQQuotientObject}
    (F₁ F₂ : ContourCorQQuotientHom X Y)
    (G : ContourCorQQuotientHom Y Z) :
    comp C (ContourCorQFormalSum.addClass F₁ F₂) G =
      ContourCorQFormalSum.addClass (comp C F₁ G) (comp C F₂ G) :=
  ContourCorQFormalSum.compClass_add_left C F₁ F₂ G

/-- Composition is additive in the right input. -/
theorem comp_add_right
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQQuotientObject}
    (F : ContourCorQQuotientHom X Y)
    (G₁ G₂ : ContourCorQQuotientHom Y Z) :
    comp C F (ContourCorQFormalSum.addClass G₁ G₂) =
      ContourCorQFormalSum.addClass (comp C F G₁) (comp C F G₂) :=
  ContourCorQFormalSum.compClass_add_right C F G₁ G₂

/-- Composition is compatible with scalar multiplication in the left input. -/
theorem comp_scale_left
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQQuotientObject}
    (q : Rat)
    (F : ContourCorQQuotientHom X Y)
    (G : ContourCorQQuotientHom Y Z) :
    comp C (ContourCorQFormalSum.scaleClass q F) G =
      ContourCorQFormalSum.scaleClass q (comp C F G) :=
  ContourCorQFormalSum.compClass_scale_left C q F G

/-- Composition is compatible with scalar multiplication in the right input. -/
theorem comp_scale_right
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQQuotientObject}
    (q : Rat)
    (F : ContourCorQQuotientHom X Y)
    (G : ContourCorQQuotientHom Y Z) :
    comp C F (ContourCorQFormalSum.scaleClass q G) =
      ContourCorQFormalSum.scaleClass q (comp C F G) :=
  ContourCorQFormalSum.compClass_scale_right C q F G

/-- Composition is compatible with negation in the left input. -/
theorem comp_neg_left
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQQuotientObject}
    (F : ContourCorQQuotientHom X Y)
    (G : ContourCorQQuotientHom Y Z) :
    comp C (ContourCorQFormalSum.negClass F) G =
      ContourCorQFormalSum.negClass (comp C F G) :=
  ContourCorQFormalSum.compClass_neg_left C F G

/-- Composition is compatible with negation in the right input. -/
theorem comp_neg_right
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQQuotientObject}
    (F : ContourCorQQuotientHom X Y)
    (G : ContourCorQQuotientHom Y Z) :
    comp C F (ContourCorQFormalSum.negClass G) =
      ContourCorQFormalSum.negClass (comp C F G) :=
  ContourCorQFormalSum.compClass_neg_right C F G

/-- Composition expands subtraction in the left input. -/
theorem comp_sub_left
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQQuotientObject}
    (F₁ F₂ : ContourCorQQuotientHom X Y)
    (G : ContourCorQQuotientHom Y Z) :
    comp C (ContourCorQFormalSum.subClass F₁ F₂) G =
      ContourCorQFormalSum.addClass
        (comp C F₁ G)
        (ContourCorQFormalSum.negClass (comp C F₂ G)) :=
  ContourCorQFormalSum.compClass_sub_left C F₁ F₂ G

/-- Composition expands subtraction in the right input. -/
theorem comp_sub_right
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQQuotientObject}
    (F : ContourCorQQuotientHom X Y)
    (G₁ G₂ : ContourCorQQuotientHom Y Z) :
    comp C F (ContourCorQFormalSum.subClass G₁ G₂) =
      ContourCorQFormalSum.addClass
        (comp C F G₁)
        (ContourCorQFormalSum.negClass (comp C F G₂)) :=
  ContourCorQFormalSum.compClass_sub_right C F G₁ G₂

end ContourCorQQuotientHom

end AnalyticMotives
end LFunctions
end Boundary
