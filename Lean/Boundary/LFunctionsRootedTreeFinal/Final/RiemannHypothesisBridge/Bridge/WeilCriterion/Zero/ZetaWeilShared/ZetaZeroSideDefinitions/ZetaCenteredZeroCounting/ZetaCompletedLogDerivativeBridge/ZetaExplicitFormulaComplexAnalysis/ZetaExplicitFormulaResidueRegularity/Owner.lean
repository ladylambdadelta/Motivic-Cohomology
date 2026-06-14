import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaAnalyticPackage.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaContour.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaGeometry.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroSideContribution.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.Owner

/-!
# Boundary explicit-formula residue regularity

This file owns the analytic regularity input for the residue stage of the
completed-zeta contour argument.  The singular set includes the poles at `0`
and `1` and the zeros of the completed zeta factor; away from that set the
full contour integrand, including `completedZetaNegLogDeriv`, is differentiable.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The full completed-zeta contour-integrand singular set used in the residue argument. -/
def completedZetaContourIntegrandSingularSet : Set ℂ :=
  {z : ℂ | z = 0 ∨ z = 1 ∨ (z ≠ 0 ∧ z ≠ 1 ∧ completedRiemannZeta z = 0)}

/-- The named singular-set definition unfolds to the completed-zeta singular-set predicate. -/
theorem completedZetaContourIntegrandSingularSet_eq :
    completedZetaContourIntegrandSingularSet =
      ({z : ℂ | z = 0 ∨ z = 1 ∨
        (z ≠ 0 ∧ z ≠ 1 ∧ completedRiemannZeta z = 0)} : Set ℂ) :=
  rfl

/-- The full completed-zeta contour-integrand singular set is countable. -/
theorem completedZetaContourIntegrandSingularSet_countable :
    completedZetaContourIntegrandSingularSet.Countable :=
  contourIntegrand_singularSet_countable

/-- Outside the full completed-zeta contour-integrand singular set, the integrand is
complex differentiable. -/
theorem completedZetaContourIntegrand_differentiableAt_off_singularSet
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    {z : ℂ} (hz : z ∉ completedZetaContourIntegrandSingularSet) :
    DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z :=
  contourIntegrand_differentiableAt_off_countable hPhi hz

/-- Outside the full completed-zeta contour-integrand singular set, the integrand is
continuous. -/
theorem completedZetaContourIntegrand_continuousAt_off_singularSet
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    {z : ℂ} (hz : z ∉ completedZetaContourIntegrandSingularSet) :
    ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z :=
  (completedZetaContourIntegrand_differentiableAt_off_singularSet hPhi hz).continuousAt

/-- The package-level residue regularity theorem for the full completed-zeta contour integrand. -/
theorem completedZetaContourIntegrand_regularAt_off_singularSet
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    {z : ℂ} (hz : z ∉ completedZetaContourIntegrandSingularSet) :
    ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
      DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z :=
  And.intro
    (completedZetaContourIntegrand_continuousAt_off_singularSet h.phi_control hz)
    (completedZetaContourIntegrand_differentiableAt_off_singularSet h.phi_control hz)

/-- The residue-argument singular set for the rectangle formula is countable. -/
theorem completedZeta_rectangleResidueFormula_singularSet_countable
    {f : ZetaAdmissibleFunction} (_h : ExplicitFormulaAnalyticPackage f) :
    ({z : ℂ | z = 0 ∨ z = 1 ∨ (z ≠ 0 ∧ z ≠ 1 ∧ completedRiemannZeta z = 0)} :
      Set ℂ).Countable :=
  completedZetaContourIntegrandSingularSet_countable

/-- Away from the completed-zeta singular set, the full contour integrand is continuous. -/
theorem completedZeta_rectangleResidueFormula_continuousOn
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    {z : ℂ}
    (hz : z ∉ ({w : ℂ | w = 0 ∨ w = 1 ∨
      (w ≠ 0 ∧ w ≠ 1 ∧ completedRiemannZeta w = 0)} : Set ℂ)) :
    ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z :=
  completedZetaContourIntegrand_continuousAt_off_singularSet h.phi_control hz

/-- Away from the completed-zeta singular set, the full contour integrand is differentiable. -/
theorem completedZeta_rectangleResidueFormula_differentiableAt
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    {z : ℂ}
    (hz : z ∉ ({w : ℂ | w = 0 ∨ w = 1 ∨
      (w ≠ 0 ∧ w ≠ 1 ∧ completedRiemannZeta w = 0)} : Set ℂ)) :
    DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z :=
  completedZetaContourIntegrand_differentiableAt_off_singularSet h.phi_control hz

/-- The package exposes the owner-level countable-singular-set regularity theorem. -/
theorem completedZeta_rectangleResidueFormula_regular_off_countable
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    {z : ℂ}
    (hz : z ∉ ({w : ℂ | w = 0 ∨ w = 1 ∨
      (w ≠ 0 ∧ w ≠ 1 ∧ completedRiemannZeta w = 0)} : Set ℂ)) :
    ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
      DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z :=
  And.intro
    (completedZeta_rectangleResidueFormula_continuousOn h hz)
    (completedZeta_rectangleResidueFormula_differentiableAt h hz)

/-- The residue-regularity singular set is contained in the contour-family singular
predicate used by the scheduled boundary-avoidance certificate. -/
theorem completedZetaContourIntegrandSingularSet_subset_contourSingularPoint :
    completedZetaContourIntegrandSingularSet ⊆
      {z : ℂ | explicitFormulaContourSingularPoint z} := by
  intro z hz
  unfold completedZetaContourIntegrandSingularSet at hz
  unfold explicitFormulaContourSingularPoint
  rcases hz with hz0 | hz1 | hzeta
  · exact Or.inl hz0
  · exact Or.inr (Or.inl hz1)
  · exact Or.inr (Or.inr (Or.inr (Or.inr hzeta)))

/-- Boundary avoidance for the scheduled contour excludes the completed contour-integrand
singular set on that rectangle boundary. -/
theorem completedZetaContourIntegrand_not_mem_singularSet_of_avoidsBoundary
    (F : ExplicitFormulaContourFamily) (T : ℝ) {z : ℂ}
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T)
    (hboundary : z ∈ explicitFormulaContourFamilyBoundary F T) :
    z ∉ completedZetaContourIntegrandSingularSet := by
  intro hz
  exact havoid z
    (completedZetaContourIntegrandSingularSet_subset_contourSingularPoint hz)
    hboundary

/-- The completed contour integrand is regular at every avoided rectangle-boundary point.

This is the boundary-regularity input for the finite rectangle residue theorem: the schedule
does not hide a contour choice; its `havoid` certificate is used pointwise to put the
integrand in the regular domain on the chosen boundary. -/
theorem completedZetaContourIntegrand_regularAt_boundary_of_avoidsBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (T : ℝ) {z : ℂ}
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T)
    (hboundary : z ∈ explicitFormulaContourFamilyBoundary F T) :
    ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
      DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z := by
  have hoff :
      z ∉ completedZetaContourIntegrandSingularSet :=
    completedZetaContourIntegrand_not_mem_singularSet_of_avoidsBoundary
      F T havoid hboundary
  exact And.intro
    (completedZetaContourIntegrand_continuousAt_off_singularSet h.phi_control hoff)
    (completedZetaContourIntegrand_differentiableAt_off_singularSet h.phi_control hoff)

/-- Every boundary point of an avoided rectangle is regular for the completed contour
integrand. This is the pointwise boundary-avoidance sink used by the finite residue theorem. -/
theorem completedZetaContourIntegrand_regularAt_all_boundary_points_of_avoidsBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    ∀ z : ℂ,
      z ∈ explicitFormulaContourFamilyBoundary F T →
        ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
          DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z :=
  fun z hz => completedZetaContourIntegrand_regularAt_boundary_of_avoidsBoundary f F h T havoid hz

/-- The completed contour integrand is continuous on every avoided rectangle boundary.

This is the set-level packaging of the pointwise boundary regularity sink used by the
finite rectangle residue theorem. -/
theorem completedZetaContourIntegrand_continuousOn_boundary_of_avoidsBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    ContinuousOn (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w)
      (explicitFormulaContourFamilyBoundary F T) := by
  intro z hz
  exact
    (completedZetaContourIntegrand_regularAt_all_boundary_points_of_avoidsBoundary
      f F h T havoid z hz).1

/-- The explicit-formula residue datum attached to a completed zero.  The zero coordinate
is the same coordinate used by the completed-zero side, so the residue summand evaluates
`Φ_f` at `ρ - 1 / 2`, matching `zetaCenteredZero ρ`. -/
noncomputable def explicitFormulaZeroDataOfCompletedZero
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) : ExplicitFormulaZeroData :=
  { zero := (ρ : ℂ)
    multiplicity := zetaZeroMultiplicity (ρ : ℂ) }

/-- The explicit-formula residue attached to a completed zero is the existing zero-side
contribution.  This is bookkeeping: both sides are the same multiplicity-weighted spectral
evaluation at the centered zero coordinate. -/
theorem explicitFormulaZeroResidue_ofCompletedZero_eq_zeroSideContribution
    (f : ZetaAdmissibleFunction) (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ) =
      zetaZeroSideContribution (ρ : ℂ) f := by
  unfold explicitFormulaZeroResidue
  unfold explicitFormulaZeroDataOfCompletedZero
  unfold zetaZeroSideContribution
  unfold zetaCenteredZero
  rfl

/-- The finite completed-zero height window used by the residue-side contour approximation. -/
noncomputable def explicitFormulaCompletedZeroHeightWindow
    (T : ℝ) : Finset {ρ : ℂ // ZetaCompletedZero ρ} :=
  (finite_completedZerosInCenteredHeightBall T).toFinset

/-- Membership in the finite completed-zero residue window is membership in the underlying
centered-height ball. -/
theorem mem_explicitFormulaCompletedZeroHeightWindow_iff
    (T : ℝ) (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
      ρ ∈ completedZerosInCenteredHeightBall T := by
  unfold explicitFormulaCompletedZeroHeightWindow
  exact Set.Finite.mem_toFinset (finite_completedZerosInCenteredHeightBall T)

/-- Completed-zero height windows are monotone in the height cutoff. -/
theorem explicitFormulaCompletedZeroHeightWindow_mono
    {S T : ℝ} (hST : S ≤ T) :
    explicitFormulaCompletedZeroHeightWindow S ⊆
      explicitFormulaCompletedZeroHeightWindow T := by
  intro ρ hρ
  have hρS :
      ρ ∈ completedZerosInCenteredHeightBall S :=
    (mem_explicitFormulaCompletedZeroHeightWindow_iff S ρ).1 hρ
  have hρT :
      ρ ∈ completedZerosInCenteredHeightBall T := by
    unfold completedZerosInCenteredHeightBall at hρS
    unfold completedZerosInCenteredHeightBall
    exact le_trans hρS hST
  exact (mem_explicitFormulaCompletedZeroHeightWindow_iff T ρ).2 hρT

/-- The finite completed-zero height windows exhaust the completed-zero subtype. -/
theorem explicitFormulaCompletedZeroHeightWindow_tendsto_atTop :
    Tendsto explicitFormulaCompletedZeroHeightWindow atTop atTop := by
  exact Monotone.tendsto_atTop_finset
    (fun S T hST => explicitFormulaCompletedZeroHeightWindow_mono hST)
    (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
      ⟨zetaCompletedZeroCenteredHeight ρ, by
        exact (mem_explicitFormulaCompletedZeroHeightWindow_iff
          (zetaCompletedZeroCenteredHeight ρ) ρ).2
          (by
            unfold completedZerosInCenteredHeightBall
            exact le_refl (zetaCompletedZeroCenteredHeight ρ))⟩)

/-- The finite residue sum over the completed-zero height window. -/
noncomputable def explicitFormulaCompletedZeroHeightWindowResidueSum
    (f : ZetaAdmissibleFunction) (T : ℝ) : ℂ :=
  ∑ ρ in explicitFormulaCompletedZeroHeightWindow T,
    explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ)

/-- The same finite residue window expressed in zero-side contribution notation. -/
noncomputable def explicitFormulaCompletedZeroHeightWindowZeroSideSum
    (f : ZetaAdmissibleFunction) (T : ℝ) : ℂ :=
  ∑ ρ in explicitFormulaCompletedZeroHeightWindow T,
    zetaZeroSideContribution (ρ : ℂ) f

/-- The residue-window presentation and the zero-side presentation are the same finite sum. -/
theorem explicitFormulaCompletedZeroHeightWindowResidueSum_eq_zeroSideSum
    (f : ZetaAdmissibleFunction) (T : ℝ) :
    explicitFormulaCompletedZeroHeightWindowResidueSum f T =
      explicitFormulaCompletedZeroHeightWindowZeroSideSum f T := by
  unfold explicitFormulaCompletedZeroHeightWindowResidueSum
  unfold explicitFormulaCompletedZeroHeightWindowZeroSideSum
  exact Finset.sum_congr
    rfl
    (fun ρ _hρ =>
      explicitFormulaZeroResidue_ofCompletedZero_eq_zeroSideContribution f ρ)

/-- The zero-side presentation of the finite completed-zero height windows converges to the
completed zero-side complex `tsum`. -/
theorem explicitFormulaCompletedZeroHeightWindowZeroSideSum_tendsto_tsum
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun T : ℝ => explicitFormulaCompletedZeroHeightWindowZeroSideSum f T)
      atTop
      (𝓝
        (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          zetaZeroSideContribution (ρ : ℂ) f)) := by
  have hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaZeroSideContribution (ρ : ℂ) f) :=
    summable_zetaZeroSideContribution f
  have hwindow :
      Tendsto
        (fun T : ℝ =>
          ∑ ρ in explicitFormulaCompletedZeroHeightWindow T,
            zetaZeroSideContribution (ρ : ℂ) f)
        atTop
        (𝓝
          (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
            zetaZeroSideContribution (ρ : ℂ) f)) :=
    hsum.hasSum.comp explicitFormulaCompletedZeroHeightWindow_tendsto_atTop
  have hpointwise :
      (fun T : ℝ => explicitFormulaCompletedZeroHeightWindowZeroSideSum f T) =
        (fun T : ℝ =>
          ∑ ρ in explicitFormulaCompletedZeroHeightWindow T,
            zetaZeroSideContribution (ρ : ℂ) f) := by
    funext T
    rfl
  exact Eq.subst
    (motive := fun u : ℝ → ℂ =>
      Tendsto u atTop
        (𝓝
          (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
            zetaZeroSideContribution (ρ : ℂ) f)))
    hpointwise.symm
    hwindow

/-- The residue presentation of the finite completed-zero height windows converges to the
completed zero-side complex `tsum`. -/
theorem explicitFormulaCompletedZeroHeightWindowResidueSum_tendsto_zeroSideTsum
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun T : ℝ => explicitFormulaCompletedZeroHeightWindowResidueSum f T)
      atTop
      (𝓝
        (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          zetaZeroSideContribution (ρ : ℂ) f)) := by
  have hzeroSide :
      Tendsto
        (fun T : ℝ => explicitFormulaCompletedZeroHeightWindowZeroSideSum f T)
        atTop
        (𝓝
          (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
            zetaZeroSideContribution (ρ : ℂ) f)) :=
    explicitFormulaCompletedZeroHeightWindowZeroSideSum_tendsto_tsum f
  have hpointwise :
      (fun T : ℝ => explicitFormulaCompletedZeroHeightWindowResidueSum f T) =
        (fun T : ℝ => explicitFormulaCompletedZeroHeightWindowZeroSideSum f T) := by
    funext T
    exact explicitFormulaCompletedZeroHeightWindowResidueSum_eq_zeroSideSum f T
  exact Eq.subst
    (motive := fun u : ℝ → ℂ =>
      Tendsto u atTop
        (𝓝
          (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
            zetaZeroSideContribution (ρ : ℂ) f)))
    hpointwise.symm
    hzeroSide

/-- Finite rectangle Cauchy-residue computation with the chosen boundary avoiding the
completed-zeta singular set.

This is the acyclic owner theorem for the finite rectangle residue equality.  Downstream
files consume this theorem; they do not reconstruct a second finite residue calculation. -/
theorem zetaCompletedExplicitFormulaRectangleContourIntegral_eq_heightWindowResidueSum_of_avoidsBoundary_ownerCauchyResidueComputation
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) =
      explicitFormulaCompletedZeroHeightWindowResidueSum f T := by
  exact
    explicitFormulaRectangleContourIntegral_eq_heightWindowResidueSum_of_avoidsBoundary_ownerFiniteRectangleResidueTheorem
      f F h T havoid

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
