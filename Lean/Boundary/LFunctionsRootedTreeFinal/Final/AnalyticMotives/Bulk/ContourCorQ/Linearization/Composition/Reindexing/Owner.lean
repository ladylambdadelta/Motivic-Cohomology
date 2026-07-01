import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.Composition.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.Reindexing.Owner

/-!
# Reindexing laws for formal composition

This owner records the structural bilinearity laws for formal composition as
explicit finite-index reindexings.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace ContourCorQFormalSumReindexing

/-- Formal composition preserves reindexing in the left formal sum. -/
def comp_reindex_left
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQObject}
    {S T : ContourCorQFormalSum X Y}
    (R : ContourCorQFormalSumReindexing S T)
    (U : ContourCorQFormalSum Y Z) :
    ContourCorQFormalSumReindexing
      (ContourCorQFormalSum.comp C S U)
      (ContourCorQFormalSum.comp C T U) where
  indexEquiv := {
    toFun := fun p => (R.indexEquiv p.1, p.2)
    invFun := fun p => (R.indexEquiv.symm p.1, p.2)
    left_inv := fun p =>
      Prod.ext
        (R.indexEquiv.left_inv p.1)
        rfl
    right_inv := fun p =>
      Prod.ext
        (R.indexEquiv.right_inv p.1)
        rfl
  }
  coefficient_eq := fun p =>
    congrArg₂
      (fun a b => a * b)
      (R.coefficient_eq p.1)
      rfl
  correspondence_eq := fun p =>
    congrArg₂
      (fun f g => C.composeAt f g)
      (R.correspondence_eq p.1)
      rfl

/-- Formal composition preserves reindexing in the right formal sum. -/
def comp_reindex_right
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQObject}
    (S : ContourCorQFormalSum X Y)
    {T U : ContourCorQFormalSum Y Z}
    (R : ContourCorQFormalSumReindexing T U) :
    ContourCorQFormalSumReindexing
      (ContourCorQFormalSum.comp C S T)
      (ContourCorQFormalSum.comp C S U) where
  indexEquiv := {
    toFun := fun p => (p.1, R.indexEquiv p.2)
    invFun := fun p => (p.1, R.indexEquiv.symm p.2)
    left_inv := fun p =>
      Prod.ext
        rfl
        (R.indexEquiv.left_inv p.2)
    right_inv := fun p =>
      Prod.ext
        rfl
        (R.indexEquiv.right_inv p.2)
  }
  coefficient_eq := fun p =>
    congrArg₂
      (fun a b => a * b)
      rfl
      (R.coefficient_eq p.2)
  correspondence_eq := fun p =>
    congrArg₂
      (fun f g => C.composeAt f g)
      rfl
      (R.correspondence_eq p.2)

/-- Composing the zero formal sum on the left gives a zero formal sum. -/
def comp_zero_left
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQObject}
    (T : ContourCorQFormalSum Y Z) :
    ContourCorQFormalSumReindexing
      (ContourCorQFormalSum.comp C (ContourCorQFormalSum.zero X Y) T)
      (ContourCorQFormalSum.zero X Z) where
  indexEquiv := {
    toFun := fun p => nomatch p.1
    invFun := fun e => nomatch e
    left_inv := fun p => nomatch p.1
    right_inv := fun e => nomatch e
  }
  coefficient_eq := fun p => nomatch p.1
  correspondence_eq := fun p => nomatch p.1

/-- Composing the zero formal sum on the right gives a zero formal sum. -/
def comp_zero_right
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQObject}
    (S : ContourCorQFormalSum X Y) :
    ContourCorQFormalSumReindexing
      (ContourCorQFormalSum.comp C S (ContourCorQFormalSum.zero Y Z))
      (ContourCorQFormalSum.zero X Z) where
  indexEquiv := {
    toFun := fun p => nomatch p.2
    invFun := fun e => nomatch e
    left_inv := fun p => nomatch p.2
    right_inv := fun e => nomatch e
  }
  coefficient_eq := fun p => nomatch p.2
  correspondence_eq := fun p => nomatch p.2

/-- Formal composition is additive in the left formal sum, up to reindexing. -/
def comp_add_left
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQObject}
    (S₁ S₂ : ContourCorQFormalSum X Y)
    (T : ContourCorQFormalSum Y Z) :
    ContourCorQFormalSumReindexing
      (ContourCorQFormalSum.comp C (ContourCorQFormalSum.add S₁ S₂) T)
      (ContourCorQFormalSum.add
        (ContourCorQFormalSum.comp C S₁ T)
        (ContourCorQFormalSum.comp C S₂ T)) where
  indexEquiv := {
    toFun := fun p =>
      match p.1 with
      | Sum.inl i => Sum.inl (i, p.2)
      | Sum.inr i => Sum.inr (i, p.2)
    invFun := fun p =>
      match p with
      | Sum.inl q => (Sum.inl q.1, q.2)
      | Sum.inr q => (Sum.inr q.1, q.2)
    left_inv := fun p =>
      match p.1 with
      | Sum.inl _ => rfl
      | Sum.inr _ => rfl
    right_inv := fun p =>
      match p with
      | Sum.inl _ => rfl
      | Sum.inr _ => rfl
  }
  coefficient_eq := fun p =>
    match p.1 with
    | Sum.inl _ => rfl
    | Sum.inr _ => rfl
  correspondence_eq := fun p =>
    match p.1 with
    | Sum.inl _ => rfl
    | Sum.inr _ => rfl

/-- Formal composition is additive in the right formal sum, up to reindexing. -/
def comp_add_right
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQObject}
    (S : ContourCorQFormalSum X Y)
    (T₁ T₂ : ContourCorQFormalSum Y Z) :
    ContourCorQFormalSumReindexing
      (ContourCorQFormalSum.comp C S (ContourCorQFormalSum.add T₁ T₂))
      (ContourCorQFormalSum.add
        (ContourCorQFormalSum.comp C S T₁)
        (ContourCorQFormalSum.comp C S T₂)) where
  indexEquiv := {
    toFun := fun p =>
      match p.2 with
      | Sum.inl j => Sum.inl (p.1, j)
      | Sum.inr j => Sum.inr (p.1, j)
    invFun := fun p =>
      match p with
      | Sum.inl q => (q.1, Sum.inl q.2)
      | Sum.inr q => (q.1, Sum.inr q.2)
    left_inv := fun p =>
      match p.2 with
      | Sum.inl _ => rfl
      | Sum.inr _ => rfl
    right_inv := fun p =>
      match p with
      | Sum.inl _ => rfl
      | Sum.inr _ => rfl
  }
  coefficient_eq := fun p =>
    match p.2 with
    | Sum.inl _ => rfl
    | Sum.inr _ => rfl
  correspondence_eq := fun p =>
    match p.2 with
    | Sum.inl _ => rfl
    | Sum.inr _ => rfl

/-- Formal composition is compatible with left scalar multiplication. -/
def comp_scale_left
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQObject}
    (q : Rat)
    (S : ContourCorQFormalSum X Y)
    (T : ContourCorQFormalSum Y Z) :
    ContourCorQFormalSumReindexing
      (ContourCorQFormalSum.comp C (ContourCorQFormalSum.scale q S) T)
      (ContourCorQFormalSum.scale q (ContourCorQFormalSum.comp C S T)) where
  indexEquiv := Equiv.refl (S.Index × T.Index)
  coefficient_eq := fun p =>
    mul_assoc q (S.coefficient p.1) (T.coefficient p.2)
  correspondence_eq := fun _ => rfl

/-- Formal composition is compatible with right scalar multiplication. -/
def comp_scale_right
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQObject}
    (q : Rat)
    (S : ContourCorQFormalSum X Y)
    (T : ContourCorQFormalSum Y Z) :
    ContourCorQFormalSumReindexing
      (ContourCorQFormalSum.comp C S (ContourCorQFormalSum.scale q T))
      (ContourCorQFormalSum.scale q (ContourCorQFormalSum.comp C S T)) where
  indexEquiv := Equiv.refl (S.Index × T.Index)
  coefficient_eq := fun p =>
    Eq.trans
      (mul_assoc (S.coefficient p.1) q (T.coefficient p.2))
      (Eq.trans
        (congrArg
          (fun a => a * T.coefficient p.2)
          (mul_comm (S.coefficient p.1) q))
        (Eq.symm (mul_assoc q (S.coefficient p.1) (T.coefficient p.2))))
  correspondence_eq := fun _ => rfl

end ContourCorQFormalSumReindexing

end AnalyticMotives
end LFunctions
end Boundary
