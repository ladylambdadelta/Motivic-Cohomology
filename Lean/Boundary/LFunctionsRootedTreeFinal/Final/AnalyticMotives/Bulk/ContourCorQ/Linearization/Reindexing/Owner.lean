import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.Owner

/-!
# Reindexing finite rational contour sums

This owner records the native equality witness for formal finite rational sums
before quotienting: a finite index equivalence preserving coefficients and
raw contour correspondences.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Reindexing equivalence between two formal rational contour sums. -/
structure ContourCorQFormalSumReindexing
    {X Y : ContourCorQObject}
    (S T : ContourCorQFormalSum X Y) where
  indexEquiv : S.Index ≃ T.Index
  coefficient_eq :
    (i : S.Index) →
      S.coefficient i = T.coefficient (indexEquiv i)
  correspondence_eq :
    (i : S.Index) →
      S.correspondence i = T.correspondence (indexEquiv i)

namespace ContourCorQFormalSumReindexing

/-- The index equivalence selected by a reindexing. -/
def indexEquivOf {X Y : ContourCorQObject}
    {S T : ContourCorQFormalSum X Y}
    (R : ContourCorQFormalSumReindexing S T) :
    S.Index ≃ T.Index :=
  R.indexEquiv

/-- Coefficients are preserved along a reindexing. -/
theorem coefficient_eq_of {X Y : ContourCorQObject}
    {S T : ContourCorQFormalSum X Y}
    (R : ContourCorQFormalSumReindexing S T)
    (i : S.Index) :
    S.coefficient i = T.coefficient (R.indexEquiv i) :=
  R.coefficient_eq i

/-- Raw contour correspondences are preserved along a reindexing. -/
theorem correspondence_eq_of {X Y : ContourCorQObject}
    {S T : ContourCorQFormalSum X Y}
    (R : ContourCorQFormalSumReindexing S T)
    (i : S.Index) :
    S.correspondence i = T.correspondence (R.indexEquiv i) :=
  R.correspondence_eq i

/-- Reflexive reindexing of a formal rational contour sum. -/
def refl {X Y : ContourCorQObject}
    (S : ContourCorQFormalSum X Y) :
    ContourCorQFormalSumReindexing S S where
  indexEquiv := Equiv.refl S.Index
  coefficient_eq := fun _ => rfl
  correspondence_eq := fun _ => rfl

/-- Symmetric reindexing of formal rational contour sums. -/
def symm {X Y : ContourCorQObject}
    {S T : ContourCorQFormalSum X Y}
    (R : ContourCorQFormalSumReindexing S T) :
    ContourCorQFormalSumReindexing T S where
  indexEquiv := R.indexEquiv.symm
  coefficient_eq := fun j =>
    Eq.symm
      (Eq.trans
        (R.coefficient_eq (R.indexEquiv.symm j))
        (congrArg T.coefficient
          (R.indexEquiv.apply_symm_apply j)))
  correspondence_eq := fun j =>
    Eq.symm
      (Eq.trans
        (R.correspondence_eq (R.indexEquiv.symm j))
        (congrArg T.correspondence
          (R.indexEquiv.apply_symm_apply j)))

/-- Transitive reindexing of formal rational contour sums. -/
def trans {X Y : ContourCorQObject}
    {S T U : ContourCorQFormalSum X Y}
    (R : ContourCorQFormalSumReindexing S T)
    (Q : ContourCorQFormalSumReindexing T U) :
    ContourCorQFormalSumReindexing S U where
  indexEquiv := R.indexEquiv.trans Q.indexEquiv
  coefficient_eq := fun i =>
    Eq.trans
      (R.coefficient_eq i)
      (Q.coefficient_eq (R.indexEquiv i))
  correspondence_eq := fun i =>
    Eq.trans
      (R.correspondence_eq i)
      (Q.correspondence_eq (R.indexEquiv i))

/-- Reindexing is preserved by scaling coefficients. -/
def scale {X Y : ContourCorQObject}
    {S T : ContourCorQFormalSum X Y}
    (q : Rat)
    (R : ContourCorQFormalSumReindexing S T) :
    ContourCorQFormalSumReindexing
      (ContourCorQFormalSum.scale q S)
      (ContourCorQFormalSum.scale q T) where
  indexEquiv := R.indexEquiv
  coefficient_eq := fun i =>
    congrArg (fun a => q * a) (R.coefficient_eq i)
  correspondence_eq := fun i =>
    R.correspondence_eq i

/-- Reindexing is preserved by addition of finite formal sums. -/
def add {X Y : ContourCorQObject}
    {S₁ S₂ T₁ T₂ : ContourCorQFormalSum X Y}
    (R₁ : ContourCorQFormalSumReindexing S₁ T₁)
    (R₂ : ContourCorQFormalSumReindexing S₂ T₂) :
    ContourCorQFormalSumReindexing
      (ContourCorQFormalSum.add S₁ S₂)
      (ContourCorQFormalSum.add T₁ T₂) where
  indexEquiv := Equiv.sumCongr R₁.indexEquiv R₂.indexEquiv
  coefficient_eq := fun i =>
    match i with
    | Sum.inl i₁ => R₁.coefficient_eq i₁
    | Sum.inr i₂ => R₂.coefficient_eq i₂
  correspondence_eq := fun i =>
    match i with
    | Sum.inl i₁ => R₁.correspondence_eq i₁
    | Sum.inr i₂ => R₂.correspondence_eq i₂

/-- Reindexing is preserved by negating finite formal sums. -/
def neg {X Y : ContourCorQObject}
    {S T : ContourCorQFormalSum X Y}
    (R : ContourCorQFormalSumReindexing S T) :
    ContourCorQFormalSumReindexing
      (ContourCorQFormalSum.neg S)
      (ContourCorQFormalSum.neg T) :=
  scale (-1) R

/-- Reindexing is preserved by subtracting finite formal sums. -/
def sub {X Y : ContourCorQObject}
    {S₁ S₂ T₁ T₂ : ContourCorQFormalSum X Y}
    (R₁ : ContourCorQFormalSumReindexing S₁ T₁)
    (R₂ : ContourCorQFormalSumReindexing S₂ T₂) :
    ContourCorQFormalSumReindexing
      (ContourCorQFormalSum.sub S₁ S₂)
      (ContourCorQFormalSum.sub T₁ T₂) :=
  add R₁ (neg R₂)

end ContourCorQFormalSumReindexing

end AnalyticMotives
end LFunctions
end Boundary
