import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Annihilator.DistributionalClassification.GlobalTranslationCharacter

/-!
# Geometry of completed-zero atomic fibers

Fourier localization in the physical translation variable separates completed
zeros by imaginary ordinate.  Local finiteness of completed zeros then makes
each exact ordinate fiber finite.  This file owns that reduction independently
of the weighted-tail density argument.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

/-- The completed-zero coordinates on one fixed imaginary ordinate. -/
def completedZeroImaginaryFiber (height : ℝ) : Set ZetaCompletedZeroCoordinate :=
  {rho : ZetaCompletedZeroCoordinate | (rho : ℂ).im = height}

/-- A fixed imaginary fiber lies in the corresponding bounded imaginary band. -/
theorem completedZeroImaginaryFiber_subset_imaginaryBand
    (height : ℝ) :
    completedZeroImaginaryFiber height ⊆
      {rho : ZetaCompletedZeroCoordinate | |(rho : ℂ).im| ≤ |height|} :=
  fun rho hrho =>
    Eq.subst
      (motive := fun value : ℝ => |value| ≤ |height|)
      hrho.symm
      (le_refl |height|)

/-- Every exact completed-zero imaginary fiber is finite. -/
theorem finite_completedZeroImaginaryFiber
    (height : ℝ) :
    (completedZeroImaginaryFiber height).Finite :=
  Set.Finite.subset
    (finite_completedZeroCoordinate_imaginaryBand |height|)
    (completedZeroImaginaryFiber_subset_imaginaryBand height)

/-- The finite coordinate set carried by one completed-zero imaginary fiber. -/
noncomputable def completedZeroImaginaryFiberFinset
    (height : ℝ) : Finset ZetaCompletedZeroCoordinate :=
  (finite_completedZeroImaginaryFiber height).toFinset

/-- Membership in the finite fiber is exactly equality of imaginary ordinate. -/
theorem mem_completedZeroImaginaryFiberFinset_iff
    (height : ℝ)
    (rho : ZetaCompletedZeroCoordinate) :
    rho ∈ completedZeroImaginaryFiberFinset height ↔
      (rho : ℂ).im = height := by
  have hfiniteMembership :
      rho ∈ (finite_completedZeroImaginaryFiber height).toFinset ↔
        rho ∈ completedZeroImaginaryFiber height :=
    (finite_completedZeroImaginaryFiber height).mem_toFinset
  have hfiberMembership :
      rho ∈ completedZeroImaginaryFiber height ↔
        (rho : ℂ).im = height :=
    Iff.rfl
  exact Iff.trans hfiniteMembership hfiberMembership

/-- A completed zero belongs to the finite fiber at its own ordinate. -/
theorem mem_completedZeroImaginaryFiberFinset_self
    (rho : ZetaCompletedZeroCoordinate) :
    rho ∈ completedZeroImaginaryFiberFinset (rho : ℂ).im :=
  (mem_completedZeroImaginaryFiberFinset_iff (rho : ℂ).im rho).mpr rfl

/-- Distinct members of one imaginary fiber have distinct real coordinates. -/
theorem completedZeroImaginaryFiber_real_injective
    (height : ℝ) :
    Set.InjOn
      (fun rho : ZetaCompletedZeroCoordinate => (rho : ℂ).re)
      (completedZeroImaginaryFiber height) :=
  fun rho hrho eta heta hreal =>
    Subtype.ext
      (Complex.ext
        hreal
        (Eq.trans hrho (Eq.trans heta.symm rfl)))

/-- The real-coordinate map is injective on the finite fiber finset. -/
theorem completedZeroImaginaryFiberFinset_real_injective
    (height : ℝ) :
    Set.InjOn
      (fun rho : ZetaCompletedZeroCoordinate => (rho : ℂ).re)
      (completedZeroImaginaryFiberFinset height :
        Set ZetaCompletedZeroCoordinate) :=
  fun rho hrho eta heta hreal =>
    completedZeroImaginaryFiber_real_injective height
      ((mem_completedZeroImaginaryFiberFinset_iff height rho).mp hrho)
      ((mem_completedZeroImaginaryFiberFinset_iff height eta).mp heta)
      hreal

/-- Completed zeros in a closed neighborhood of one imaginary ordinate. -/
def completedZeroImaginaryNeighborhood
    (height radius : ℝ) : Set ZetaCompletedZeroCoordinate :=
  {rho : ZetaCompletedZeroCoordinate |
    |(rho : ℂ).im - height| ≤ radius}

/-- An ordinate neighborhood lies in a bounded imaginary band. -/
theorem completedZeroImaginaryNeighborhood_subset_imaginaryBand
    (height radius : ℝ)
    (hradius : 0 ≤ radius) :
    completedZeroImaginaryNeighborhood height radius ⊆
      {rho : ZetaCompletedZeroCoordinate |
        |(rho : ℂ).im| ≤ |height| + radius} := by
  intro rho hrho
  have hdecomposition :
      (rho : ℂ).im = ((rho : ℂ).im - height) + height :=
    (sub_add_cancel (rho : ℂ).im height).symm
  have habsoluteTriangle :
      |(rho : ℂ).im| ≤
        |(rho : ℂ).im - height| + |height| :=
    Eq.subst
      (motive := fun value : ℝ =>
        |value| ≤ |(rho : ℂ).im - height| + |height|)
      hdecomposition.symm
      (abs_add_le ((rho : ℂ).im - height) height)
  have hreplaceRadius :
      |(rho : ℂ).im - height| + |height| ≤ radius + |height| :=
    add_le_add_right hrho |height|
  have hcommute : radius + |height| = |height| + radius :=
    add_comm radius |height|
  have hboundTransport :
      (|(rho : ℂ).im - height| + |height| ≤ radius + |height|) =
        (|(rho : ℂ).im - height| + |height| ≤ |height| + radius) :=
    congrArg
      (fun bound : ℝ =>
        |(rho : ℂ).im - height| + |height| ≤ bound)
      hcommute
  exact le_trans habsoluteTriangle
    (Eq.mp hboundTransport hreplaceRadius)

/-- Every closed nonnegative-radius ordinate neighborhood is finite. -/
theorem finite_completedZeroImaginaryNeighborhood
    (height radius : ℝ)
    (hradius : 0 ≤ radius) :
    (completedZeroImaginaryNeighborhood height radius).Finite :=
  Set.Finite.subset
    (finite_completedZeroCoordinate_imaginaryBand (|height| + radius))
    (completedZeroImaginaryNeighborhood_subset_imaginaryBand
      height radius hradius)

/-- The finite completed-zero coordinate set in an ordinate neighborhood. -/
noncomputable def completedZeroImaginaryNeighborhoodFinset
    (height radius : ℝ)
    (hradius : 0 ≤ radius) : Finset ZetaCompletedZeroCoordinate :=
  (finite_completedZeroImaginaryNeighborhood height radius hradius).toFinset

/-- Membership in the finite ordinate neighborhood has its defining form. -/
theorem mem_completedZeroImaginaryNeighborhoodFinset_iff
    (height radius : ℝ)
    (hradius : 0 ≤ radius)
    (rho : ZetaCompletedZeroCoordinate) :
    rho ∈ completedZeroImaginaryNeighborhoodFinset height radius hradius ↔
      |(rho : ℂ).im - height| ≤ radius := by
  have hfiniteMembership :
      rho ∈
          (finite_completedZeroImaginaryNeighborhood
            height radius hradius).toFinset ↔
        rho ∈ completedZeroImaginaryNeighborhood height radius :=
    (finite_completedZeroImaginaryNeighborhood height radius hradius).mem_toFinset
  have hneighborhoodMembership :
      rho ∈ completedZeroImaginaryNeighborhood height radius ↔
        |(rho : ℂ).im - height| ≤ radius :=
    Iff.rfl
  exact Iff.trans hfiniteMembership hneighborhoodMembership

/-- The exact imaginary fiber is contained in every nonnegative-radius
neighborhood at the same ordinate. -/
theorem completedZeroImaginaryFiber_subset_neighborhoodFinset
    (height radius : ℝ)
    (hradius : 0 ≤ radius) :
    completedZeroImaginaryFiber height ⊆
      (completedZeroImaginaryNeighborhoodFinset
        height radius hradius : Set ZetaCompletedZeroCoordinate) := by
  intro rho hrho
  have hdifferenceZero : (rho : ℂ).im - height = 0 :=
    sub_eq_zero.mpr hrho
  have habsoluteZero : |(rho : ℂ).im - height| = 0 :=
    Eq.trans (congrArg abs hdifferenceZero) abs_zero
  exact
    (mem_completedZeroImaginaryNeighborhoodFinset_iff
      height radius hradius rho).mpr
      (Eq.subst
        (motive := fun value : ℝ => value ≤ radius)
        habsoluteZero.symm
        hradius)

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
