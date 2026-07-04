import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part04
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.CorrectionPoleBoundaryPrimitives

/-!
# Explicit-formula finite rectangle residues

This owner layer contains finite-rectangle residue equalities, scheduled avoidance, and residue-window error transport.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Adding a half after subtracting a half returns the original complex coordinate. -/
theorem explicitFormulaRectangle_half_add_sub_half (z : ℂ) :
    (1 / 2 : ℂ) + (z - (1 / 2 : ℂ)) = z := by
  calc
    (1 / 2 : ℂ) + (z - (1 / 2 : ℂ)) =
        (1 / 2 : ℂ) + (z + -(1 / 2 : ℂ)) := by
      exact congrArg (fun w : ℂ => (1 / 2 : ℂ) + w)
        (sub_eq_add_neg z (1 / 2 : ℂ))
    _ = ((1 / 2 : ℂ) + z) + -(1 / 2 : ℂ) := by
      exact (add_assoc (1 / 2 : ℂ) z (-(1 / 2 : ℂ))).symm
    _ = (z + (1 / 2 : ℂ)) + -(1 / 2 : ℂ) := by
      exact congrArg (fun w : ℂ => w + -(1 / 2 : ℂ)) (add_comm (1 / 2 : ℂ) z)
    _ = z + ((1 / 2 : ℂ) + -(1 / 2 : ℂ)) := by
      exact add_assoc z (1 / 2 : ℂ) (-(1 / 2 : ℂ))
    _ = z + 0 := by
      exact congrArg (fun w : ℂ => z + w) (add_neg_cancel (1 / 2 : ℂ))
    _ = z := by
      exact add_zero z

/-- Compatibility sink for consumers that still state the completed-zero residue with the
named zero-side summand. -/
theorem explicitFormulaRectangle_completedZero_localResidue_zeroSideCoordinateCompatibility_ownerGap
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hnormalize :
      explicitFormulaZeroResidue f (explicitFormulaContourZeroDataOfCompletedZero ρ) =
        explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ)) :
    Tendsto
      (fun z : ℂ =>
        (z - completedZeroResidueCoordinate ρ) * zetaCompletedExplicitFormulaContourIntegrand f z)
      (𝓝[≠] (completedZeroResidueCoordinate ρ))
      (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ))) := by
  exact
    explicitFormulaRectangle_completedZero_localResidue_zeroSideCoordinateCompatibility_from_uncentered_ownerGap
      f ρ hnormalize
      (explicitFormulaRectangle_completedZero_localResidue_tendsto_contourSummand f hPhi ρ)

/-- Off the completed contour-integrand singular set, the finite-rectangle integrand is
regular at an interior point.  This is the interior counterpart to the boundary-regularity
input used by the finite Cauchy residue theorem. -/
theorem explicitFormulaRectangleContourIntegrand_regularAt_interior_of_not_singular
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (T : ℝ) {z : ℂ}
    (_hinterior : z ∈ explicitFormulaContourFamilyInterior F T)
    (hz : z ∉ completedZetaContourIntegrandSingularSet) :
    ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
      DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z := by
  exact And.intro
    (completedZetaContourIntegrand_continuousAt_off_singularSet h.phi_control hz)
    (completedZetaContourIntegrand_differentiableAt_off_singularSet h.phi_control hz)

/-- If a local deleted-disk coefficient stays in the contour interior and avoids all
singularities away from its center, then the coefficient function is continuous on the
deleted disk and differentiable away from any chosen countable exceptional set.  This is the
analytic regularity transport used after the finite radius has been chosen geometrically. -/
theorem explicitFormulaRectangle_localResidueCoefficient_regularOn_of_deletedDisk_avoids_singular
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (T : ℝ) (a : ℂ)
    (R : Set ℂ) (s : Set ℂ)
    (hinterior :
      ∀ z : ℂ, z ∈ R → z ∈ explicitFormulaContourFamilyInterior F T)
    (havoid :
      ∀ z : ℂ, z ∈ R → z ∉ completedZetaContourIntegrandSingularSet) :
    ContinuousOn
        (fun z : ℂ => (z - a) * zetaCompletedExplicitFormulaContourIntegrand f z)
        R ∧
      (∀ z : ℂ,
        z ∈ R \ s →
          DifferentiableAt ℂ
            (fun w : ℂ => (w - a) * zetaCompletedExplicitFormulaContourIntegrand f w)
            z) := by
  have hcontinuous :
      ContinuousOn
        (fun z : ℂ => (z - a) * zetaCompletedExplicitFormulaContourIntegrand f z)
        R :=
    fun z hz =>
      have hregular :
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z :=
        explicitFormulaRectangleContourIntegrand_regularAt_interior_of_not_singular
          f F h T (hinterior z hz) (havoid z hz)
      have hsub :
          ContinuousAt (fun w : ℂ => w - a) z :=
        continuousAt_id.sub continuousAt_const
      (hsub.mul hregular.1).continuousWithinAt
  have hdifferentiable :
      ∀ z : ℂ,
        z ∈ R \ s →
          DifferentiableAt ℂ
            (fun w : ℂ => (w - a) * zetaCompletedExplicitFormulaContourIntegrand f w)
            z :=
    fun z hz =>
      have hzR : z ∈ R := hz.1
      have hregular :
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z :=
        explicitFormulaRectangleContourIntegrand_regularAt_interior_of_not_singular
          f F h T (hinterior z hzR) (havoid z hzR)
      have hsub :
          DifferentiableAt ℂ (fun w : ℂ => w - a) z :=
        differentiableAt_id'.sub_const a
      hsub.mul hregular.2
  exact And.intro hcontinuous hdifferentiable

/-- A finite-rectangle interior singularity of the completed contour integrand is either
one of the two completed-zeta pole coordinates or a genuine completed-zeta zero away from
those poles. -/
theorem explicitFormulaRectangleContourIntegrand_interiorSingular_cases
    (F : ExplicitFormulaContourFamily) (T : ℝ) {z : ℂ}
    (_hinterior : z ∈ explicitFormulaContourFamilyInterior F T)
    (hz : z ∈ completedZetaContourIntegrandSingularSet) :
    z = 0 ∨ z = 1 ∨ (z ≠ 0 ∧ z ≠ 1 ∧ completedRiemannZeta z = 0) := by
  exact hz

/-- If an interior singularity is not one of the completed-zeta pole coordinates, then
it is a completed-zeta zero in the singular-set sense. -/
theorem explicitFormulaRectangleContourIntegrand_interiorSingular_zeroCase
    (F : ExplicitFormulaContourFamily) (T : ℝ) {z : ℂ}
    (hinterior : z ∈ explicitFormulaContourFamilyInterior F T)
    (hz : z ∈ completedZetaContourIntegrandSingularSet)
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    completedRiemannZeta z = 0 := by
  match explicitFormulaRectangleContourIntegrand_interiorSingular_cases
      F T hinterior hz with
  | Or.inl hzero => exact False.elim (hz0 hzero)
  | Or.inr (Or.inl hone) => exact False.elim (hz1 hone)
  | Or.inr (Or.inr hzeroData) => exact hzeroData.2.2

/-- The supplied interior-pole classification sends every completed-zero window entry to
an interior singularity of the finite rectangle. -/
theorem explicitFormulaRectangle_completedZeroWindow_coordinate_mem_interiorSingular
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    {ρ : {ρ : ℂ // ZetaCompletedZero ρ}}
    (hρ : ρ ∈ explicitFormulaCompletedZeroHeightWindow T) :
    completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
      completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet := by
  exact (hinterior ρ).mp hρ

/-- The supplied local-residue data specializes to each finite completed-zero window
coordinate. -/
theorem explicitFormulaRectangle_completedZeroWindow_coordinate_localResidue
    (f : ZetaAdmissibleFunction) (T : ℝ)
    (hlocal :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T →
          Tendsto
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate ρ) * zetaCompletedExplicitFormulaContourIntegrand f z)
            (𝓝[≠] (completedZeroResidueCoordinate ρ))
            (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ))))
    {ρ : {ρ : ℂ // ZetaCompletedZero ρ}}
    (hρ : ρ ∈ explicitFormulaCompletedZeroHeightWindow T) :
    Tendsto
      (fun z : ℂ =>
        (z - completedZeroResidueCoordinate ρ) * zetaCompletedExplicitFormulaContourIntegrand f z)
      (𝓝[≠] (completedZeroResidueCoordinate ρ))
      (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ))) := by
  exact hlocal ρ hρ

/-- A completed-zeta zero away from the two completed-zeta pole coordinates determines
the centered completed-zero coordinate used by the finite residue window. -/
def explicitFormulaCompletedZeroOfContourZero
    (z : ℂ) (hz0 : z ≠ 0) (hz1 : z ≠ 1)
    (hzeta : completedRiemannZeta z = 0) :
    {ρ : ℂ // ZetaCompletedZero ρ} :=
  ⟨z - (1 / 2 : ℂ),
    zetaCompletedZero_mk
      (by
        intro hneg
        have hz_eq_zero : z = 0 := by
          calc
            z = (z - (1 / 2 : ℂ)) + (1 / 2 : ℂ) := by
              exact (sub_add_cancel z (1 / 2 : ℂ)).symm
            _ = -(1 / 2 : ℂ) + (1 / 2 : ℂ) := by
              exact congrArg (fun w : ℂ => w + (1 / 2 : ℂ)) hneg
            _ = 0 := by
              exact neg_add_cancel (1 / 2 : ℂ)
        exact hz0 hz_eq_zero)
      (by
        intro hpos
        have hz_eq_one : z = 1 := by
          calc
            z = (z - (1 / 2 : ℂ)) + (1 / 2 : ℂ) := by
              exact (sub_add_cancel z (1 / 2 : ℂ)).symm
            _ = (1 / 2 : ℂ) + (1 / 2 : ℂ) := by
              exact congrArg (fun w : ℂ => w + (1 / 2 : ℂ)) hpos
            _ = 1 := by
              exact add_halves (1 : ℂ)
        exact hz1 hz_eq_one)
      (by
        calc
          centeredCompletedRiemannZetaFunction (z - (1 / 2 : ℂ)) =
              centeredCompletedRiemannZeta (z - (1 / 2 : ℂ)) := by
            exact centeredCompletedRiemannZetaFunction_eq (z - (1 / 2 : ℂ))
          _ = completedRiemannZeta ((1 / 2 : ℂ) + (z - (1 / 2 : ℂ))) := by
            exact centeredCompletedRiemannZeta_eq_completedRiemannZeta_shift
              (z - (1 / 2 : ℂ))
          _ = completedRiemannZeta z := by
            exact congrArg completedRiemannZeta
              (explicitFormulaRectangle_half_add_sub_half z)
          _ = 0 := hzeta)⟩

/-- The contour-zero constructor has the expected uncentered residue coordinate. -/
theorem explicitFormulaCompletedZeroOfContourZero_residueCoordinate
    (z : ℂ) (hz0 : z ≠ 0) (hz1 : z ≠ 1)
    (hzeta : completedRiemannZeta z = 0) :
    completedZeroResidueCoordinate
        (explicitFormulaCompletedZeroOfContourZero z hz0 hz1 hzeta) = z := by
  calc
    completedZeroResidueCoordinate
        (explicitFormulaCompletedZeroOfContourZero z hz0 hz1 hzeta) =
        (1 / 2 : ℂ) + (z - (1 / 2 : ℂ)) := by
      rfl
    _ = z := by
      exact explicitFormulaRectangle_half_add_sub_half z

/-- A non-pole interior singular point is represented by a completed-zero residue
coordinate. -/
theorem explicitFormulaRectangle_interiorSingular_nonPole_exists_completedZeroCoordinate
    (F : ExplicitFormulaContourFamily) (T : ℝ) {z : ℂ}
    (hinterior : z ∈ explicitFormulaContourFamilyInterior F T)
    (hz : z ∈ completedZetaContourIntegrandSingularSet)
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    ∃ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
      completedZeroResidueCoordinate ρ = z := by
  let hzeta : completedRiemannZeta z = 0 :=
    explicitFormulaRectangleContourIntegrand_interiorSingular_zeroCase
      F T hinterior hz hz0 hz1
  exact
    ⟨explicitFormulaCompletedZeroOfContourZero z hz0 hz1 hzeta,
      explicitFormulaCompletedZeroOfContourZero_residueCoordinate z hz0 hz1 hzeta⟩

/-- Under the supplied finite-window classification, a non-pole interior singular point
is represented by a completed-zero entry in the rectangle height window. -/
theorem explicitFormulaRectangle_interiorSingular_nonPole_completedZero_mem_window
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hclass :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    {z : ℂ}
    (hinterior : z ∈ explicitFormulaContourFamilyInterior F T)
    (hz : z ∈ completedZetaContourIntegrandSingularSet)
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    explicitFormulaCompletedZeroOfContourZero z hz0 hz1
        (explicitFormulaRectangleContourIntegrand_interiorSingular_zeroCase
          F T hinterior hz hz0 hz1)
      ∈ explicitFormulaCompletedZeroHeightWindow T := by
  let hzeta : completedRiemannZeta z = 0 :=
    explicitFormulaRectangleContourIntegrand_interiorSingular_zeroCase
      F T hinterior hz hz0 hz1
  let ρ : {ρ : ℂ // ZetaCompletedZero ρ} :=
    explicitFormulaCompletedZeroOfContourZero z hz0 hz1 hzeta
  have hcoord : completedZeroResidueCoordinate ρ = z :=
    explicitFormulaCompletedZeroOfContourZero_residueCoordinate z hz0 hz1 hzeta
  have hcoordInterior :
      completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T :=
    Eq.subst
      (motive := fun w : ℂ => w ∈ explicitFormulaContourFamilyInterior F T)
      hcoord.symm
      hinterior
  have hcoordSingular :
      completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet :=
    Eq.subst
      (motive := fun w : ℂ => w ∈ completedZetaContourIntegrandSingularSet)
      hcoord.symm
      hz
  exact (hclass ρ).mpr (And.intro hcoordInterior hcoordSingular)

/-- The finite-window classification normalizes every interior singularity of the
completed contour integrand to one of the two completed-zeta pole coordinates or to a
completed-zero residue coordinate in the height window. -/
theorem explicitFormulaRectangle_interiorSingular_pole_or_completedZeroWindow
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hclass :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    {z : ℂ}
    (hinterior : z ∈ explicitFormulaContourFamilyInterior F T)
    (hz : z ∈ completedZetaContourIntegrandSingularSet) :
    z = 0 ∨ z = 1 ∨
      ∃ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ∧
          completedZeroResidueCoordinate ρ = z := by
  match explicitFormulaRectangleContourIntegrand_interiorSingular_cases
      F T hinterior hz with
  | Or.inl hzero => exact Or.inl hzero
  | Or.inr (Or.inl hone) => exact Or.inr (Or.inl hone)
  | Or.inr (Or.inr hzeroData) =>
      let hz0 : z ≠ 0 := hzeroData.1
      let hz1 : z ≠ 1 := hzeroData.2.1
      let hzeta : completedRiemannZeta z = 0 := hzeroData.2.2
      let ρ : {ρ : ℂ // ZetaCompletedZero ρ} :=
        explicitFormulaCompletedZeroOfContourZero z hz0 hz1 hzeta
      have hcoord : completedZeroResidueCoordinate ρ = z :=
        explicitFormulaCompletedZeroOfContourZero_residueCoordinate z hz0 hz1 hzeta
      have hcoordInterior :
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T :=
        Eq.subst
          (motive := fun w : ℂ => w ∈ explicitFormulaContourFamilyInterior F T)
          hcoord.symm
          hinterior
      have hcoordSingular :
          completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet :=
        Eq.subst
          (motive := fun w : ℂ => w ∈ completedZetaContourIntegrandSingularSet)
          hcoord.symm
          hz
      have hρWindow : ρ ∈ explicitFormulaCompletedZeroHeightWindow T :=
        (hclass ρ).mpr (And.intro hcoordInterior hcoordSingular)
      exact Or.inr (Or.inr ⟨ρ, And.intro hρWindow hcoord⟩)

/-- At positive height, the completed-zeta pole coordinate `0` lies in the open rectangle
interior of every pole-enclosing contour family. -/
theorem explicitFormulaRectangle_zeroPole_mem_interior_of_pos_height
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T) :
    (0 : ℂ) ∈ explicitFormulaContourFamilyInterior F T := by
  exact
    And.intro
      F.zero_mem_horizontal_uIoo
      (And.intro (neg_neg_of_pos hT) hT)

/-- At positive height, the completed-zeta pole coordinate `1` lies in the open rectangle
interior of every pole-enclosing contour family. -/
theorem explicitFormulaRectangle_onePole_mem_interior_of_pos_height
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T) :
    (1 : ℂ) ∈ explicitFormulaContourFamilyInterior F T := by
  exact
    And.intro
      F.one_mem_horizontal_uIoo
      (And.intro (neg_neg_of_pos hT) hT)

/-- The completed-zeta pole coordinate `0` is a singular point of the raw completed contour
integrand. -/
theorem explicitFormulaRectangle_zeroPole_mem_singularSet :
    (0 : ℂ) ∈ completedZetaContourIntegrandSingularSet := by
  exact Or.inl rfl

/-- The completed-zeta pole coordinate `1` is a singular point of the raw completed contour
integrand. -/
theorem explicitFormulaRectangle_onePole_mem_singularSet :
    (1 : ℂ) ∈ completedZetaContourIntegrandSingularSet := by
  exact Or.inr (Or.inl rfl)

/-- At positive height, the raw completed contour integrand has the `0` pole as an
interior singularity of the finite rectangle. -/
theorem explicitFormulaRectangle_zeroPole_mem_interiorSingular_of_pos_height
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T) :
    (0 : ℂ) ∈ explicitFormulaContourFamilyInterior F T ∧
      (0 : ℂ) ∈ completedZetaContourIntegrandSingularSet := by
  exact
    And.intro
      (explicitFormulaRectangle_zeroPole_mem_interior_of_pos_height F hT)
      explicitFormulaRectangle_zeroPole_mem_singularSet

/-- At positive height, the raw completed contour integrand has the `1` pole as an
interior singularity of the finite rectangle. -/
theorem explicitFormulaRectangle_onePole_mem_interiorSingular_of_pos_height
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T) :
    (1 : ℂ) ∈ explicitFormulaContourFamilyInterior F T ∧
      (1 : ℂ) ∈ completedZetaContourIntegrandSingularSet := by
  exact
    And.intro
      (explicitFormulaRectangle_onePole_mem_interior_of_pos_height F hT)
      explicitFormulaRectangle_onePole_mem_singularSet

/-- The finite completed-zero window never represents the completed-zeta pole coordinate
`0`. -/
theorem explicitFormulaRectangle_zeroPole_not_completedZeroWindowCoordinate
    (T : ℝ) (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (_hρ : ρ ∈ explicitFormulaCompletedZeroHeightWindow T) :
    completedZeroResidueCoordinate ρ ≠ 0 := by
  exact completedZeroResidueCoordinate_ne_zero ρ

/-- The finite completed-zero window never represents the completed-zeta pole coordinate
`1`. -/
theorem explicitFormulaRectangle_onePole_not_completedZeroWindowCoordinate
    (T : ℝ) (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (_hρ : ρ ∈ explicitFormulaCompletedZeroHeightWindow T) :
    completedZeroResidueCoordinate ρ ≠ 1 := by
  exact completedZeroResidueCoordinate_ne_one ρ

/-- The two completed-zeta pole-coordinate residues which are present in a pole-enclosing
finite rectangle but absent from the completed-zero height window. -/
noncomputable def explicitFormulaRectangle_completedPoleResidueSum
    (f : ZetaAdmissibleFunction) : ℂ :=
  explicitFormulaRectangle_zeroPoleResidue f +
    explicitFormulaRectangle_onePoleResidue f

/-- The pole-corrected finite residue target for the raw completed contour integrand. -/
noncomputable def explicitFormulaRectangle_poleCorrectedResidueSum
    (f : ZetaAdmissibleFunction) (T : ℝ) : ℂ :=
  explicitFormulaCompletedZeroHeightWindowResidueSum f T +
    explicitFormulaRectangle_completedPoleResidueSum f

/-- The pole-corrected finite residue target unfolds to the completed-zero window plus the
two pole-coordinate residues. -/
theorem explicitFormulaRectangle_poleCorrectedResidueSum_eq
    (f : ZetaAdmissibleFunction) (T : ℝ) :
    explicitFormulaRectangle_poleCorrectedResidueSum f T =
      explicitFormulaCompletedZeroHeightWindowResidueSum f T +
        explicitFormulaRectangle_completedPoleResidueSum f := by
  rfl

/-- The two-pole residue sum unfolds to the `0` and `1` pole-coordinate residues. -/
theorem explicitFormulaRectangle_completedPoleResidueSum_eq
    (f : ZetaAdmissibleFunction) :
    explicitFormulaRectangle_completedPoleResidueSum f =
      explicitFormulaRectangle_zeroPoleResidue f +
        explicitFormulaRectangle_onePoleResidue f := by
  rfl

/-- The `s = 0` pole residue unfolds to the centered value `-1 / 2` of the test
transform. -/
theorem explicitFormulaRectangle_zeroPoleResidue_eq
    (f : ZetaAdmissibleFunction) :
    explicitFormulaRectangle_zeroPoleResidue f =
      zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)) := by
  rfl

/-- The `s = 1` pole residue unfolds to the centered value `1 / 2` of the test transform. -/
theorem explicitFormulaRectangle_onePoleResidue_eq
    (f : ZetaAdmissibleFunction) :
    explicitFormulaRectangle_onePoleResidue f =
      zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ) := by
  rfl

/-- Removing the two pole-coordinate residues from the pole-corrected residue target
recovers the completed-zero height window. -/
theorem explicitFormulaRectangle_heightWindowResidueSum_eq_poleCorrected_sub_poles
    (f : ZetaAdmissibleFunction) (T : ℝ) :
    explicitFormulaCompletedZeroHeightWindowResidueSum f T =
      explicitFormulaRectangle_poleCorrectedResidueSum f T -
        explicitFormulaRectangle_completedPoleResidueSum f := by
  let Z : ℂ := explicitFormulaCompletedZeroHeightWindowResidueSum f T
  let P : ℂ := explicitFormulaRectangle_completedPoleResidueSum f
  calc
    explicitFormulaCompletedZeroHeightWindowResidueSum f T = Z := by
      rfl
    _ = (Z + P) - P := by
      exact (add_sub_cancel_right Z P).symm
    _ = explicitFormulaRectangle_poleCorrectedResidueSum f T -
        explicitFormulaRectangle_completedPoleResidueSum f := by
      rfl

/-- The isolated correction kernel at `s = 0` has the negative of the raw completed-contour
pole residue named in this owner file. -/
theorem explicitFormulaRectangle_zeroPole_localResidue_tendsto
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f) :
    Tendsto
      (fun z : ℂ =>
        z *
          ((-1 / z) *
            zetaCompletedExplicitFormulaPhi f (z - 1 / 2)))
      (𝓝[≠] (0 : ℂ))
      (𝓝 (-explicitFormulaRectangle_zeroPoleResidue f)) := by
  have hraw :
      Tendsto
        (fun z : ℂ =>
          z *
            ((-1 / z) *
              zetaCompletedExplicitFormulaPhi f (z - 1 / 2)))
        (𝓝[≠] (0 : ℂ))
        (𝓝 (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))) :=
    zetaCompletedExplicitFormulaCorrectionZeroPole_localResidue_tendsto f hPhi
  exact
    Eq.subst
      (motive := fun w : ℂ =>
        Tendsto
          (fun z : ℂ =>
            z *
              ((-1 / z) *
                zetaCompletedExplicitFormulaPhi f (z - 1 / 2)))
          (𝓝[≠] (0 : ℂ))
          (𝓝 w))
      (congrArg Neg.neg (explicitFormulaRectangle_zeroPoleResidue_eq f)).symm
      hraw

/-- The isolated correction kernel at `s = 1` has the negative of the raw completed-contour
pole residue named in this owner file. -/
theorem explicitFormulaRectangle_onePole_localResidue_tendsto
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f) :
    Tendsto
      (fun z : ℂ =>
        (z - 1) *
          ((-1 / (z - 1)) *
            zetaCompletedExplicitFormulaPhi f (z - 1 / 2)))
      (𝓝[≠] (1 : ℂ))
      (𝓝 (-explicitFormulaRectangle_onePoleResidue f)) := by
  have hraw :
      Tendsto
        (fun z : ℂ =>
          (z - 1) *
            ((-1 / (z - 1)) *
              zetaCompletedExplicitFormulaPhi f (z - 1 / 2)))
        (𝓝[≠] (1 : ℂ))
        (𝓝 (-zetaCompletedExplicitFormulaPhi f (1 / 2))) :=
    zetaCompletedExplicitFormulaCorrectionOnePole_localResidue_tendsto f hPhi
  exact
    Eq.subst
      (motive := fun w : ℂ =>
        Tendsto
          (fun z : ℂ =>
            (z - 1) *
              ((-1 / (z - 1)) *
                zetaCompletedExplicitFormulaPhi f (z - 1 / 2)))
          (𝓝[≠] (1 : ℂ))
          (𝓝 w))
      (congrArg Neg.neg (explicitFormulaRectangle_onePoleResidue_eq f)).symm
      hraw

/-- The isolated `s = 0` pole local residue transports along any punctured
parametrization approaching the pole coordinate. -/
theorem explicitFormulaRectangle_zeroPole_localResidue_along_puncturedParam
    {ι : Type*} [TopologicalSpace ι] {l : Filter ι}
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (γ : ι → ℂ)
    (hγ : Tendsto γ l (𝓝[≠] (0 : ℂ))) :
    Tendsto
      (fun i : ι =>
        γ i *
          ((-1 / γ i) *
            zetaCompletedExplicitFormulaPhi f (γ i - 1 / 2)))
      l
      (𝓝 (-explicitFormulaRectangle_zeroPoleResidue f)) := by
  exact
    (explicitFormulaRectangle_zeroPole_localResidue_tendsto f hPhi).comp hγ

/-- The isolated `s = 1` pole local residue transports along any punctured
parametrization approaching the pole coordinate. -/
theorem explicitFormulaRectangle_onePole_localResidue_along_puncturedParam
    {ι : Type*} [TopologicalSpace ι] {l : Filter ι}
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (γ : ι → ℂ)
    (hγ : Tendsto γ l (𝓝[≠] (1 : ℂ))) :
    Tendsto
      (fun i : ι =>
        (γ i - 1) *
          ((-1 / (γ i - 1)) *
            zetaCompletedExplicitFormulaPhi f (γ i - 1 / 2)))
      l
      (𝓝 (-explicitFormulaRectangle_onePoleResidue f)) := by
  exact
    (explicitFormulaRectangle_onePole_localResidue_tendsto f hPhi).comp hγ

/-- The centered completed-zero residue coordinate is injective. -/
theorem completedZeroResidueCoordinate_injective :
    Function.Injective
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        completedZeroResidueCoordinate ρ) := by
  intro ρ σ hcoord
  apply Subtype.ext
  calc
    (ρ : ℂ) = completedZeroResidueCoordinate ρ - (1 / 2 : ℂ) := by
      unfold completedZeroResidueCoordinate
      exact (add_sub_cancel_left (1 / 2 : ℂ) (ρ : ℂ)).symm
    _ = completedZeroResidueCoordinate σ - (1 / 2 : ℂ) := by
      exact congrArg (fun z : ℂ => z - (1 / 2 : ℂ)) hcoord
    _ = (σ : ℂ) := by
      unfold completedZeroResidueCoordinate
      exact add_sub_cancel_left (1 / 2 : ℂ) (σ : ℂ)

/-- The non-tangent finite-rectangle boundary contribution of the two completed-zeta pole
principal parts in the explicit-formula side convention. -/
noncomputable def explicitFormulaRectangle_completedPoleBoundaryContribution
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral f F T +
    zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral f F T

/-- The tangent-weighted finite-rectangle boundary contribution of the two completed-zeta
pole principal parts.  This is the contour normalization to which Cauchy residue calculus
directly applies. -/
noncomputable def explicitFormulaRectangle_completedPoleTangentBoundaryContribution
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral f F T +
    zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral f F T

/-- The tangent-weighted completed explicit-formula rectangle contour.  The vertical sides
carry the tangent factor `I`, matching the boundary orientation in Cauchy-Goursat. -/
noncomputable def zetaCompletedExplicitFormulaTangentContourIntegral
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) : ℂ :=
  zetaCompletedExplicitFormulaRightLineIntegral f r * Complex.I -
    zetaCompletedExplicitFormulaLeftLineIntegral f r * Complex.I +
    zetaCompletedExplicitFormulaTopLineIntegral f r -
    zetaCompletedExplicitFormulaBottomLineIntegral f r

/-- The defect between the tangent-weighted pole boundary contribution and the
non-tangent explicit-formula side convention. -/
noncomputable def explicitFormulaRectangle_completedPoleBoundaryTangentDefect
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  explicitFormulaRectangle_completedPoleTangentBoundaryContribution f F T -
    explicitFormulaRectangle_completedPoleBoundaryContribution f F T

/-- The raw completed contour integral with the two completed-zeta pole principal parts
removed in the explicit-formula side convention. -/
noncomputable def explicitFormulaRectangle_poleCorrectedContourIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) -
    explicitFormulaRectangle_completedPoleBoundaryContribution f F T

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
