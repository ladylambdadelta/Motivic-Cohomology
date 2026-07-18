import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.AtomicDistributionGeometry
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.FiniteSpectralZeroOperator

/-!
# Finite exceptional window for atomic Fourier localization

Before applying the Gaussian tail separator, remove every nearby completed zero
outside the target imaginary fiber by one finite constant-coefficient
differential operator.  The resulting multiplier remains nonzero on the target
fiber.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

/-- The embedding of completed-zero coordinates into spectral values. -/
def completedZeroSpectralValueEmbedding : ZetaCompletedZeroCoordinate ↪ ℂ where
  toFun := fun rho => (rho : ℂ)
  inj' := Subtype.val_injective

/-- Nearby completed zeros outside the exact target imaginary fiber. -/
noncomputable def completedZeroImaginaryExceptionalCoordinates
    (height radius : ℝ)
    (hradius : 0 ≤ radius) : Finset ZetaCompletedZeroCoordinate :=
  (completedZeroImaginaryNeighborhoodFinset height radius hradius).filter
    (fun rho => (rho : ℂ).im ≠ height)

/-- Spectral values of the finite nearby off-fiber exceptional set. -/
noncomputable def completedZeroImaginaryExceptionalValues
    (height radius : ℝ)
    (hradius : 0 ≤ radius) : Finset ℂ :=
  (completedZeroImaginaryExceptionalCoordinates
    height radius hradius).map completedZeroSpectralValueEmbedding

/-- Coordinate membership in the exceptional set has the expected two
conditions. -/
theorem mem_completedZeroImaginaryExceptionalCoordinates_iff
    (height radius : ℝ)
    (hradius : 0 ≤ radius)
    (rho : ZetaCompletedZeroCoordinate) :
    rho ∈ completedZeroImaginaryExceptionalCoordinates height radius hradius ↔
      |(rho : ℂ).im - height| ≤ radius ∧
        (rho : ℂ).im ≠ height := by
  have hfilterMembership :
      rho ∈ completedZeroImaginaryExceptionalCoordinates
          height radius hradius ↔
        rho ∈ completedZeroImaginaryNeighborhoodFinset
          height radius hradius ∧
          (rho : ℂ).im ≠ height :=
    Finset.mem_filter
  have hneighborhoodMembership :=
    mem_completedZeroImaginaryNeighborhoodFinset_iff
      height radius hradius rho
  exact Iff.trans hfilterMembership
    (and_congr hneighborhoodMembership Iff.rfl)

/-- A coordinate belongs to the exceptional value finset exactly when its
completed-zero coordinate belongs to the exceptional coordinate finset. -/
theorem mem_completedZeroImaginaryExceptionalValues_iff
    (height radius : ℝ)
    (hradius : 0 ≤ radius)
    (rho : ZetaCompletedZeroCoordinate) :
    (rho : ℂ) ∈ completedZeroImaginaryExceptionalValues
        height radius hradius ↔
      rho ∈ completedZeroImaginaryExceptionalCoordinates
        height radius hradius := by
  exact Iff.intro
    (fun hvalue =>
      match Finset.mem_map.mp hvalue with
      | ⟨eta, heta, hequal⟩ =>
          have hetaRho : eta = rho :=
            completedZeroSpectralValueEmbedding.injective hequal
          Eq.subst
            (motive := fun coordinate : ZetaCompletedZeroCoordinate =>
              coordinate ∈ completedZeroImaginaryExceptionalCoordinates
                height radius hradius)
            hetaRho
            heta)
    (fun hrho =>
      Finset.mem_map.mpr ⟨rho, hrho, Eq.refl (rho : ℂ)⟩)

/-- Every nearby off-fiber completed zero is in the exceptional value set. -/
theorem mem_completedZeroImaginaryExceptionalValues_of_near_of_offFiber
    (height radius : ℝ)
    (hradius : 0 ≤ radius)
    (rho : ZetaCompletedZeroCoordinate)
    (hnear : |(rho : ℂ).im - height| ≤ radius)
    (hoffFiber : (rho : ℂ).im ≠ height) :
    (rho : ℂ) ∈ completedZeroImaginaryExceptionalValues
      height radius hradius :=
  (mem_completedZeroImaginaryExceptionalValues_iff
    height radius hradius rho).mpr
    ((mem_completedZeroImaginaryExceptionalCoordinates_iff
      height radius hradius rho).mpr ⟨hnear, hoffFiber⟩)

/-- No member of the exact target fiber lies in the exceptional value set. -/
theorem not_mem_completedZeroImaginaryExceptionalValues_of_fiber
    (height radius : ℝ)
    (hradius : 0 ≤ radius)
    (rho : ZetaCompletedZeroCoordinate)
    (hfiber : (rho : ℂ).im = height) :
    (rho : ℂ) ∉ completedZeroImaginaryExceptionalValues
      height radius hradius := by
  intro hmembership
  have hcoordinateMembership :
      rho ∈ completedZeroImaginaryExceptionalCoordinates
        height radius hradius :=
    (mem_completedZeroImaginaryExceptionalValues_iff
      height radius hradius rho).mp hmembership
  have hoffFiber : (rho : ℂ).im ≠ height :=
    ((mem_completedZeroImaginaryExceptionalCoordinates_iff
      height radius hradius rho).mp hcoordinateMembership).2
  exact hoffFiber hfiber

/-- The exceptional-window multiplier remains nonzero on the target fiber. -/
theorem completedZeroImaginaryExceptionalMultiplier_ne_zero_of_fiber
    (height radius : ℝ)
    (hradius : 0 ≤ radius)
    (rho : ZetaCompletedZeroCoordinate)
    (hfiber : (rho : ℂ).im = height) :
    ((completedZeroImaginaryExceptionalValues height radius hradius).toList.map
      (fun sample : ℂ => sample - (rho : ℂ))).prod ≠ 0 :=
  finiteSpectralZeroOperator_multiplier_ne_zero_of_not_mem
    (completedZeroImaginaryExceptionalValues height radius hradius)
    (rho : ℂ)
    (not_mem_completedZeroImaginaryExceptionalValues_of_fiber
      height radius hradius rho hfiber)

/-- The exceptional-window differential operator kills every nearby off-fiber
completed-zero evaluation. -/
theorem zetaSpectralEval_exceptionalWindowOperator_eq_zero
    (height radius : ℝ)
    (hradius : 0 ≤ radius)
    (rho : ZetaCompletedZeroCoordinate)
    (hnear : |(rho : ℂ).im - height| ≤ radius)
    (hoffFiber : (rho : ℂ).im ≠ height)
    (f : ZetaAdmissibleFunction) :
    zetaSpectralEval
      (finiteSpectralZeroOperator
        (completedZeroImaginaryExceptionalValues height radius hradius) f)
      (rho : ℂ) = 0 :=
  zetaSpectralEval_finiteSpectralZeroOperator_eq_zero_of_mem
    (completedZeroImaginaryExceptionalValues height radius hradius)
    f
    (rho : ℂ)
    (mem_completedZeroImaginaryExceptionalValues_of_near_of_offFiber
      height radius hradius rho hnear hoffFiber)

/-- Nearby completed-zero coordinates other than one selected target. -/
noncomputable def completedZeroTargetExceptionalCoordinates
    (target : ZetaCompletedZeroCoordinate)
    (radius : ℝ)
    (hradius : 0 ≤ radius) : Finset ZetaCompletedZeroCoordinate :=
  (completedZeroImaginaryNeighborhoodFinset
    (target : ℂ).im radius hradius).filter
      (fun rho => rho ≠ target)

/-- Spectral values of the finite targeted exceptional coordinate set. -/
noncomputable def completedZeroTargetExceptionalValues
    (target : ZetaCompletedZeroCoordinate)
    (radius : ℝ)
    (hradius : 0 ≤ radius) : Finset ℂ :=
  (completedZeroTargetExceptionalCoordinates target radius hradius).map
    completedZeroSpectralValueEmbedding

/-- Membership in the targeted exceptional coordinate set. -/
theorem mem_completedZeroTargetExceptionalCoordinates_iff
    (target : ZetaCompletedZeroCoordinate)
    (radius : ℝ)
    (hradius : 0 ≤ radius)
    (rho : ZetaCompletedZeroCoordinate) :
    rho ∈ completedZeroTargetExceptionalCoordinates target radius hradius ↔
      |(rho : ℂ).im - (target : ℂ).im| ≤ radius ∧ rho ≠ target := by
  have hfilterMembership :
      rho ∈ completedZeroTargetExceptionalCoordinates
          target radius hradius ↔
        rho ∈ completedZeroImaginaryNeighborhoodFinset
          (target : ℂ).im radius hradius ∧ rho ≠ target :=
    Finset.mem_filter
  have hneighborhoodMembership :=
    mem_completedZeroImaginaryNeighborhoodFinset_iff
      (target : ℂ).im radius hradius rho
  exact Iff.trans hfilterMembership
    (and_congr hneighborhoodMembership Iff.rfl)

/-- Targeted exceptional value membership is coordinate membership. -/
theorem mem_completedZeroTargetExceptionalValues_iff
    (target : ZetaCompletedZeroCoordinate)
    (radius : ℝ)
    (hradius : 0 ≤ radius)
    (rho : ZetaCompletedZeroCoordinate) :
    (rho : ℂ) ∈ completedZeroTargetExceptionalValues
        target radius hradius ↔
      rho ∈ completedZeroTargetExceptionalCoordinates
        target radius hradius := by
  exact Iff.intro
    (fun hvalue =>
      match Finset.mem_map.mp hvalue with
      | ⟨eta, heta, hequal⟩ =>
          have hetaRho : eta = rho :=
            completedZeroSpectralValueEmbedding.injective hequal
          Eq.subst
            (motive := fun coordinate : ZetaCompletedZeroCoordinate =>
              coordinate ∈ completedZeroTargetExceptionalCoordinates
                target radius hradius)
            hetaRho
            heta)
    (fun hrho =>
      Finset.mem_map.mpr ⟨rho, hrho, Eq.refl (rho : ℂ)⟩)

/-- Every nearby nontarget coordinate lies in the targeted exceptional set. -/
theorem mem_completedZeroTargetExceptionalValues_of_near_of_ne
    (target : ZetaCompletedZeroCoordinate)
    (radius : ℝ)
    (hradius : 0 ≤ radius)
    (rho : ZetaCompletedZeroCoordinate)
    (hnear : |(rho : ℂ).im - (target : ℂ).im| ≤ radius)
    (hne : rho ≠ target) :
    (rho : ℂ) ∈ completedZeroTargetExceptionalValues
      target radius hradius :=
  (mem_completedZeroTargetExceptionalValues_iff
    target radius hradius rho).mpr
    ((mem_completedZeroTargetExceptionalCoordinates_iff
      target radius hradius rho).mpr ⟨hnear, hne⟩)

/-- The selected target is not one of its own exceptional values. -/
theorem target_not_mem_completedZeroTargetExceptionalValues
    (target : ZetaCompletedZeroCoordinate)
    (radius : ℝ)
    (hradius : 0 ≤ radius) :
    (target : ℂ) ∉ completedZeroTargetExceptionalValues
      target radius hradius := by
  intro hmembership
  have hcoordinateMembership :
      target ∈ completedZeroTargetExceptionalCoordinates
        target radius hradius :=
    (mem_completedZeroTargetExceptionalValues_iff
      target radius hradius target).mp hmembership
  have htargetNe : target ≠ target :=
    ((mem_completedZeroTargetExceptionalCoordinates_iff
      target radius hradius target).mp hcoordinateMembership).2
  exact htargetNe rfl

/-- The targeted exceptional multiplier is nonzero at its selected target. -/
theorem completedZeroTargetExceptionalMultiplier_ne_zero
    (target : ZetaCompletedZeroCoordinate)
    (radius : ℝ)
    (hradius : 0 ≤ radius) :
    ((completedZeroTargetExceptionalValues target radius hradius).toList.map
      (fun sample : ℂ => sample - (target : ℂ))).prod ≠ 0 :=
  finiteSpectralZeroOperator_multiplier_ne_zero_of_not_mem
    (completedZeroTargetExceptionalValues target radius hradius)
    (target : ℂ)
    (target_not_mem_completedZeroTargetExceptionalValues
      target radius hradius)

/-- The targeted exceptional operator kills every nearby nontarget completed
zero. -/
theorem zetaSpectralEval_targetExceptionalOperator_eq_zero
    (target : ZetaCompletedZeroCoordinate)
    (radius : ℝ)
    (hradius : 0 ≤ radius)
    (rho : ZetaCompletedZeroCoordinate)
    (hnear : |(rho : ℂ).im - (target : ℂ).im| ≤ radius)
    (hne : rho ≠ target)
    (f : ZetaAdmissibleFunction) :
    zetaSpectralEval
      (finiteSpectralZeroOperator
        (completedZeroTargetExceptionalValues target radius hradius) f)
      (rho : ℂ) = 0 :=
  zetaSpectralEval_finiteSpectralZeroOperator_eq_zero_of_mem
    (completedZeroTargetExceptionalValues target radius hradius)
    f
    (rho : ℂ)
    (mem_completedZeroTargetExceptionalValues_of_near_of_ne
      target radius hradius rho hnear hne)

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
