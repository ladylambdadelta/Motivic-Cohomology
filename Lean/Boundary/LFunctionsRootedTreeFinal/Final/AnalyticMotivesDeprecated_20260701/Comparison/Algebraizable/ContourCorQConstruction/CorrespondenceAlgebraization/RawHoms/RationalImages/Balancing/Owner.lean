import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.Balancing.Closure.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.CorrespondenceAlgebraization.RawHoms.RationalImages.FormalSums.Operations.Owner

/-!
# Balanced images for raw-hom rational image systems

This file proves that the broad rational-image evaluator on formal contour
sums respects elementary balancing and its closure.
-/

universe u

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

noncomputable section

variable {G : PerfectAnalyticGround.{u}}

namespace ContourCorQRawHomRationalImageSystem

/-- Adding a zero term preserves the broad parent rational image. -/
theorem formalSumImage_zero_term
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomRationalImageSystem sourceBulk targetBulk)
    (S : ContourCorQFormalSum X Y)
    (f : ContourCorQRawHom X Y) :
    H.formalSumImage
        (ContourCorQFormalSum.add S (ContourCorQFormalSum.term 0 f)) =
      H.formalSumImage S :=
  Eq.trans
    (H.formalSumImage_add S (ContourCorQFormalSum.term 0 f))
    (Eq.trans
      (congrArg
        (fun R =>
          H.formalSumImage S + R)
        (H.formalSumImage_term 0 f))
      (Eq.trans
        (congrArg
          (fun R =>
            H.formalSumImage S + R)
          (zero_smul Rat (H.at f)))
        (add_zero (H.formalSumImage S))))

/-- Collecting equal raw contour terms preserves the broad parent rational image. -/
theorem formalSumImage_collect_terms
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomRationalImageSystem sourceBulk targetBulk)
    (q r : Rat)
    (f : ContourCorQRawHom X Y) :
    H.formalSumImage
        (ContourCorQFormalSum.add
          (ContourCorQFormalSum.term q f)
          (ContourCorQFormalSum.term r f)) =
      H.formalSumImage (ContourCorQFormalSum.term (q + r) f) :=
  Eq.trans
    (H.formalSumImage_add
      (ContourCorQFormalSum.term q f)
      (ContourCorQFormalSum.term r f))
    (Eq.trans
      (congrArg₂
        (fun R S =>
          R + S)
        (H.formalSumImage_term q f)
        (H.formalSumImage_term r f))
      (Eq.trans
        (Eq.symm (add_smul q r (H.at f)))
        (Eq.symm (H.formalSumImage_term (q + r) f))))

/-- Elementary balancing preserves the broad parent rational image. -/
theorem elementaryBalancedRel_formalSumImage
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomRationalImageSystem sourceBulk targetBulk)
    {S T : ContourCorQFormalSum X Y}
    (h : ContourCorQFormalSum.ElementaryBalancedRel S T) :
    H.formalSumImage S = H.formalSumImage T :=
  match h with
  | ContourCorQFormalSum.ElementaryBalancedRel.reindexing hR =>
      match hR with
      | Nonempty.intro R =>
          H.formalSumImage_reindexing R
  | ContourCorQFormalSum.ElementaryBalancedRel.zero_term S f =>
      H.formalSumImage_zero_term S f
  | ContourCorQFormalSum.ElementaryBalancedRel.collect_terms q r f =>
      H.formalSumImage_collect_terms q r f

/-- Balanced formal sums have equal broad parent rational images. -/
theorem balancedRel_formalSumImage
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomRationalImageSystem sourceBulk targetBulk)
    {S T : ContourCorQFormalSum X Y}
    (h : ContourCorQFormalSum.BalancedRel S T) :
    H.formalSumImage S = H.formalSumImage T :=
  match h with
  | ContourCorQFormalSum.BalancedRel.elementary hE =>
      H.elementaryBalancedRel_formalSumImage hE
  | ContourCorQFormalSum.BalancedRel.refl S =>
      rfl
  | ContourCorQFormalSum.BalancedRel.symm hST =>
      Eq.symm (H.balancedRel_formalSumImage hST)
  | ContourCorQFormalSum.BalancedRel.trans hST hTU =>
      Eq.trans
        (H.balancedRel_formalSumImage hST)
        (H.balancedRel_formalSumImage hTU)
  | ContourCorQFormalSum.BalancedRel.add
      (S₁ := S₁) (S₂ := S₂) (T₁ := T₁) (T₂ := T₂) h₁ h₂ =>
      Eq.trans
        (H.formalSumImage_add S₁ S₂)
        (Eq.trans
          (congrArg₂
            (fun R S =>
              R + S)
            (H.balancedRel_formalSumImage h₁)
            (H.balancedRel_formalSumImage h₂))
          (Eq.symm (H.formalSumImage_add T₁ T₂)))
  | ContourCorQFormalSum.BalancedRel.scale q
      (S := S) (T := T) hST =>
      Eq.trans
        (H.formalSumImage_scale q S)
        (Eq.trans
          (congrArg
            (fun R =>
              q • R)
            (H.balancedRel_formalSumImage hST))
          (Eq.symm (H.formalSumImage_scale q T)))

end ContourCorQRawHomRationalImageSystem

end

end AnalyticMotives
end LFunctions
end Boundary
