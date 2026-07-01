import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.Balancing.Closure.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.CorrespondenceAlgebraization.Balancing.ElementaryImages.Owner

/-!
# Parent images of balanced-relation closure

This file proves that the balanced relation on rational contour formal sums is
sent to equality of parent rational finite correspondences by a compatible
raw-hom algebraization system.
-/

universe u

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

noncomputable section

variable {G : PerfectAnalyticGround.{u}}

namespace ContourCorQRawHomAlgebraizationSystem

/--
Balanced formal contour sums have equal parent rational finite-correspondence
images under a compatible raw-hom algebraization system.
-/
theorem balancedRel_parentRationalCorrespondence
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomAlgebraizationSystem sourceBulk targetBulk)
    {S T : ContourCorQFormalSum X Y}
    (h : ContourCorQFormalSum.BalancedRel S T) :
    (H.formalSum S).parentRationalCorrespondence =
      (H.formalSum T).parentRationalCorrespondence :=
  match h with
  | ContourCorQFormalSum.BalancedRel.elementary hE =>
      H.elementaryBalancedRel_parentRationalCorrespondence hE
  | ContourCorQFormalSum.BalancedRel.refl S =>
      rfl
  | ContourCorQFormalSum.BalancedRel.symm hST =>
      Eq.symm (H.balancedRel_parentRationalCorrespondence hST)
  | ContourCorQFormalSum.BalancedRel.trans hST hTU =>
      Eq.trans
        (H.balancedRel_parentRationalCorrespondence hST)
        (H.balancedRel_parentRationalCorrespondence hTU)
  | ContourCorQFormalSum.BalancedRel.add
      (S₁ := S₁) (S₂ := S₂) (T₁ := T₁) (T₂ := T₂) h₁ h₂ =>
      Eq.trans
        (congrArg
          AlgebraizedContourFormalSum.parentRationalCorrespondence
          (ContourCorQRawHomAlgebraizationSystem.formalSum_add
            H S₁ S₂))
        (Eq.trans
          (AlgebraizedContourFormalSum.add_parentRationalCorrespondence
            (H.formalSum S₁) (H.formalSum S₂))
          (Eq.trans
            (congrArg₂
              (fun R S =>
                R + S)
              (H.balancedRel_parentRationalCorrespondence h₁)
              (H.balancedRel_parentRationalCorrespondence h₂))
            (Eq.trans
              (Eq.symm
                (AlgebraizedContourFormalSum.add_parentRationalCorrespondence
                  (H.formalSum T₁) (H.formalSum T₂)))
              (congrArg
                AlgebraizedContourFormalSum.parentRationalCorrespondence
                (Eq.symm
                  (ContourCorQRawHomAlgebraizationSystem.formalSum_add
                    H T₁ T₂))))))
  | ContourCorQFormalSum.BalancedRel.scale q
      (S := S) (T := T) hST =>
      Eq.trans
        (congrArg
          AlgebraizedContourFormalSum.parentRationalCorrespondence
          (ContourCorQRawHomAlgebraizationSystem.formalSum_scale
            H q S))
        (Eq.trans
          (AlgebraizedContourFormalSum.scale_parentRationalCorrespondence
            q (H.formalSum S))
          (Eq.trans
            (congrArg
              (fun R => q • R)
              (H.balancedRel_parentRationalCorrespondence hST))
            (Eq.trans
              (Eq.symm
                (AlgebraizedContourFormalSum.scale_parentRationalCorrespondence
                  q (H.formalSum T)))
              (congrArg
                AlgebraizedContourFormalSum.parentRationalCorrespondence
                (Eq.symm
                  (ContourCorQRawHomAlgebraizationSystem.formalSum_scale
                    H q T))))))

end ContourCorQRawHomAlgebraizationSystem

end

end AnalyticMotives
end LFunctions
end Boundary
