import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ProbeInterface.ZetaAdmissibleFunction.ZetaAdmissibleFunctionCore.Owner
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# Constant-coefficient differential operators on admissible probes

Physical differentiation preserves the compactly supported smooth probe space.
The first-order operator `D + a` is the owner construction used to force a
Laplace transform to vanish at a prescribed spectral point.
-/

namespace Boundary
namespace LFunctions
noncomputable section

open scoped ContDiff

namespace ZetaAdmissibleFunction

noncomputable def physicalDerivative
    (f : ZetaAdmissibleFunction) : ZetaAdmissibleFunction := by
  have hsmoothDerivative : ContDiff ℝ ∞ (fun t : ℝ => deriv f t) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ ((∞ : WithTop ℕ∞) + 1) (fun t : ℝ => f t) by
      exact f.smooth)).2.2
  have hcontinuousDerivative : Continuous (fun t : ℝ => deriv f t) :=
    hsmoothDerivative.continuous
  have hcompactDerivative : HasCompactSupport (fun t : ℝ => deriv f t) :=
    f.toZetaTestFunction.hasCompactSupport.deriv
  exact
    ⟨CompactlySupportedContinuousMap.mk
      (ContinuousMap.mk (fun t : ℝ => deriv f t) hcontinuousDerivative)
      hcompactDerivative,
      hsmoothDerivative⟩

theorem physicalDerivative_apply
    (f : ZetaAdmissibleFunction)
    (t : ℝ) :
    physicalDerivative f t = deriv f t := by
  rfl

theorem hasDerivAt_physicalDerivative_source
    (f : ZetaAdmissibleFunction)
    (t : ℝ) :
    HasDerivAt f (physicalDerivative f t) t := by
  exact Eq.subst
    (motive := fun value : ℂ => HasDerivAt f value t)
    (physicalDerivative_apply f t).symm
    ((f.smooth.differentiable
      (show 1 ≤ (∞ : WithTop ℕ∞) from
        WithTop.coe_le_coe.2 (OrderTop.le_top (1 : ℕ∞))) t).hasDerivAt)

noncomputable def physicalDerivativeLinearMap :
    ZetaAdmissibleFunction →ₗ[ℂ] ZetaAdmissibleFunction where
  toFun := physicalDerivative
  map_add' := fun f g => by
    apply ZetaAdmissibleFunction.ext
    intro t
    have hf := hasDerivAt_physicalDerivative_source f t
    have hg := hasDerivAt_physicalDerivative_source g t
    exact Eq.trans
      (physicalDerivative_apply (f + g) t)
      (Eq.trans
        (hf.add hg).deriv
        (congrArg₂ HAdd.hAdd
          (physicalDerivative_apply f t).symm
          (physicalDerivative_apply g t).symm))
  map_smul' := fun c f => by
    apply ZetaAdmissibleFunction.ext
    intro t
    have hf := hasDerivAt_physicalDerivative_source f t
    exact Eq.trans
      (physicalDerivative_apply (c • f) t)
      (Eq.trans
        (hf.const_mul c).deriv
        (congrArg (fun value : ℂ => c * value)
          (physicalDerivative_apply f t).symm))

theorem physicalDerivativeLinearMap_apply
    (f : ZetaAdmissibleFunction) :
    physicalDerivativeLinearMap f = physicalDerivative f := by
  rfl

noncomputable def firstOrderSpectralZeroOperator
    (a : ℂ)
    (f : ZetaAdmissibleFunction) : ZetaAdmissibleFunction :=
  physicalDerivative f + a • f

theorem firstOrderSpectralZeroOperator_apply
    (a : ℂ)
    (f : ZetaAdmissibleFunction)
    (t : ℝ) :
    firstOrderSpectralZeroOperator a f t = deriv f t + a * f t := by
  rfl

noncomputable def firstOrderSpectralZeroLinearMap
    (a : ℂ) : ZetaAdmissibleFunction →ₗ[ℂ] ZetaAdmissibleFunction where
  toFun := firstOrderSpectralZeroOperator a
  map_add' := fun f g => by
    exact Eq.trans
      (congrArg
        (fun value : ZetaAdmissibleFunction => value + a • (f + g))
        (physicalDerivativeLinearMap.map_add f g))
      (calc
        physicalDerivative f + physicalDerivative g + a • (f + g) =
            physicalDerivative f + physicalDerivative g + (a • f + a • g) := by
          exact congrArg
            (fun value : ZetaAdmissibleFunction =>
              physicalDerivative f + physicalDerivative g + value)
            (smul_add a f g)
        _ = (physicalDerivative f + a • f) +
              (physicalDerivative g + a • g) := by
          exact add_add_add_comm
            (physicalDerivative f) (physicalDerivative g) (a • f) (a • g))
  map_smul' := fun c f => by
    exact Eq.trans
      (congrArg
        (fun value : ZetaAdmissibleFunction => value + a • (c • f))
        (physicalDerivativeLinearMap.map_smul c f))
      (calc
        c • physicalDerivative f + a • (c • f) =
            c • physicalDerivative f + (a * c) • f := by
          exact congrArg
            (fun value : ZetaAdmissibleFunction => c • physicalDerivative f + value)
            (mul_smul a c f).symm
        _ = c • physicalDerivative f + (c * a) • f := by
          exact congrArg
            (fun value : ℂ => c • physicalDerivative f + value • f)
            (mul_comm a c)
        _ = c • physicalDerivative f + c • (a • f) := by
          exact congrArg
            (fun value : ZetaAdmissibleFunction => c • physicalDerivative f + value)
            (mul_smul c a f)
        _ = c • (physicalDerivative f + a • f) :=
          (smul_add c (physicalDerivative f) (a • f)).symm)

theorem firstOrderSpectralZeroLinearMap_apply
    (a : ℂ)
    (f : ZetaAdmissibleFunction) :
    firstOrderSpectralZeroLinearMap a f = firstOrderSpectralZeroOperator a f := by
  rfl

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
