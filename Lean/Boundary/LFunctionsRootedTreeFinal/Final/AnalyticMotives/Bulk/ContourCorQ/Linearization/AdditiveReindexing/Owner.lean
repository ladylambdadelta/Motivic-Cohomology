import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.Reindexing.Owner

/-!
# Additive reindexing for finite rational contour sums

This owner proves the structural additive laws for formal finite sums as
explicit reindexings.  The quotient layer can later turn these witnesses into
equalities of quotient homs.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace ContourCorQFormalSumReindexing

/-- Swapping the two finite summand blocks gives a reindexing. -/
def add_comm {X Y : ContourCorQObject}
    (S T : ContourCorQFormalSum X Y) :
    ContourCorQFormalSumReindexing
      (ContourCorQFormalSum.add S T)
      (ContourCorQFormalSum.add T S) where
  indexEquiv := {
    toFun := fun i =>
      match i with
      | Sum.inl s => Sum.inr s
      | Sum.inr t => Sum.inl t
    invFun := fun i =>
      match i with
      | Sum.inl t => Sum.inr t
      | Sum.inr s => Sum.inl s
    left_inv := fun i =>
      match i with
      | Sum.inl _ => rfl
      | Sum.inr _ => rfl
    right_inv := fun i =>
      match i with
      | Sum.inl _ => rfl
      | Sum.inr _ => rfl
  }
  coefficient_eq := fun i =>
    match i with
    | Sum.inl _ => rfl
    | Sum.inr _ => rfl
  correspondence_eq := fun i =>
    match i with
    | Sum.inl _ => rfl
    | Sum.inr _ => rfl

/-- Reassociating three finite summand blocks gives a reindexing. -/
def add_assoc {X Y : ContourCorQObject}
    (S T U : ContourCorQFormalSum X Y) :
    ContourCorQFormalSumReindexing
      (ContourCorQFormalSum.add (ContourCorQFormalSum.add S T) U)
      (ContourCorQFormalSum.add S (ContourCorQFormalSum.add T U)) where
  indexEquiv := {
    toFun := fun i =>
      match i with
      | Sum.inl (Sum.inl s) => Sum.inl s
      | Sum.inl (Sum.inr t) => Sum.inr (Sum.inl t)
      | Sum.inr u => Sum.inr (Sum.inr u)
    invFun := fun i =>
      match i with
      | Sum.inl s => Sum.inl (Sum.inl s)
      | Sum.inr (Sum.inl t) => Sum.inl (Sum.inr t)
      | Sum.inr (Sum.inr u) => Sum.inr u
    left_inv := fun i =>
      match i with
      | Sum.inl (Sum.inl _) => rfl
      | Sum.inl (Sum.inr _) => rfl
      | Sum.inr _ => rfl
    right_inv := fun i =>
      match i with
      | Sum.inl _ => rfl
      | Sum.inr (Sum.inl _) => rfl
      | Sum.inr (Sum.inr _) => rfl
  }
  coefficient_eq := fun i =>
    match i with
    | Sum.inl (Sum.inl _) => rfl
    | Sum.inl (Sum.inr _) => rfl
    | Sum.inr _ => rfl
  correspondence_eq := fun i =>
    match i with
    | Sum.inl (Sum.inl _) => rfl
    | Sum.inl (Sum.inr _) => rfl
    | Sum.inr _ => rfl

/-- Adding the empty formal sum on the left gives a reindexing. -/
def zero_add {X Y : ContourCorQObject}
    (S : ContourCorQFormalSum X Y) :
    ContourCorQFormalSumReindexing
      (ContourCorQFormalSum.add (ContourCorQFormalSum.zero X Y) S)
      S where
  indexEquiv := {
    toFun := fun i =>
      match i with
      | Sum.inl e => nomatch e
      | Sum.inr s => s
    invFun := fun s => Sum.inr s
    left_inv := fun i =>
      match i with
      | Sum.inl e => nomatch e
      | Sum.inr _ => rfl
    right_inv := fun _ => rfl
  }
  coefficient_eq := fun i =>
    match i with
    | Sum.inl e => nomatch e
    | Sum.inr _ => rfl
  correspondence_eq := fun i =>
    match i with
    | Sum.inl e => nomatch e
    | Sum.inr _ => rfl

/-- Adding the empty formal sum on the right gives a reindexing. -/
def add_zero {X Y : ContourCorQObject}
    (S : ContourCorQFormalSum X Y) :
    ContourCorQFormalSumReindexing
      (ContourCorQFormalSum.add S (ContourCorQFormalSum.zero X Y))
      S where
  indexEquiv := {
    toFun := fun i =>
      match i with
      | Sum.inl s => s
      | Sum.inr e => nomatch e
    invFun := fun s => Sum.inl s
    left_inv := fun i =>
      match i with
      | Sum.inl _ => rfl
      | Sum.inr e => nomatch e
    right_inv := fun _ => rfl
  }
  coefficient_eq := fun i =>
    match i with
    | Sum.inl _ => rfl
    | Sum.inr e => nomatch e
  correspondence_eq := fun i =>
    match i with
    | Sum.inl _ => rfl
    | Sum.inr e => nomatch e

end ContourCorQFormalSumReindexing

end AnalyticMotives
end LFunctions
end Boundary
