import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part34

/-!
# Narrow complement subdivision wrappers

This file peels the complement-grid subdivision surface away from the full
analytic-package argument.  The subdivision itself is combinatorial once the
side-integrability inputs and closed-radius controls have been supplied.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Package-free local residue limit at a raw singular coordinate.  The only analytic
input needed for the limit itself is the test-transform control. -/
theorem explicitFormulaRectangleRawSingular_residueLimit_of_phiControl
    (f : ZetaAdmissibleFunction) (phiControl : ZetaPhiAnalyticControl f) {T : ℝ}
    (a : ℂ) (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    ∃ residue : ℂ,
      Tendsto (fun z : ℂ => (z - a) * zetaCompletedExplicitFormulaContourIntegrand f z)
        (𝓝[≠] a) (𝓝 residue) := by
  match explicitFormulaRectangleRawSingularCoordinates_cases T ha with
  | Or.inl hzero =>
      let P : ℂ → Prop := fun a0 : ℂ =>
        ∃ residue : ℂ,
          Tendsto
            (fun z : ℂ => (z - a0) * zetaCompletedExplicitFormulaContourIntegrand f z)
            (𝓝[≠] a0) (𝓝 residue)
      have hzeroCoeff :
          (fun z : ℂ => (z - (0 : ℂ)) * zetaCompletedExplicitFormulaContourIntegrand f z) =
            fun z : ℂ => z * zetaCompletedExplicitFormulaContourIntegrand f z := by
        funext z
        exact congrArg
          (fun w : ℂ => w * zetaCompletedExplicitFormulaContourIntegrand f z)
          (sub_zero z)
      have hzeroLimit :
          P (0 : ℂ) :=
        ⟨explicitFormulaRectangle_zeroPoleResidue f,
          Eq.subst
            (motive := fun phi : ℂ → ℂ =>
              Tendsto phi (𝓝[≠] (0 : ℂ)) (𝓝 (explicitFormulaRectangle_zeroPoleResidue f)))
            hzeroCoeff.symm
            (explicitFormulaRectangle_zeroPole_localResidue_tendsto_rawCompleted f
              phiControl)⟩
      exact Eq.subst (motive := P) hzero.symm hzeroLimit
  | Or.inr (Or.inl hone) =>
      let P : ℂ → Prop := fun a0 : ℂ =>
        ∃ residue : ℂ,
          Tendsto
            (fun z : ℂ => (z - a0) * zetaCompletedExplicitFormulaContourIntegrand f z)
            (𝓝[≠] a0) (𝓝 residue)
      have honeLimit :
          P (1 : ℂ) :=
        ⟨explicitFormulaRectangle_onePoleResidue f,
          explicitFormulaRectangle_onePole_localResidue_tendsto_rawCompleted f phiControl⟩
      exact Eq.subst (motive := P) hone.symm honeLimit
  | Or.inr (Or.inr hcompleted) =>
      match hcompleted with
      | ⟨rho, hrho, hcoord⟩ =>
          let P : ℂ → Prop := fun a0 : ℂ =>
            ∃ residue : ℂ,
              Tendsto
                (fun z : ℂ => (z - a0) * zetaCompletedExplicitFormulaContourIntegrand f z)
                (𝓝[≠] a0) (𝓝 residue)
          have hrhoLimit :
              P (completedZeroResidueCoordinate rho) :=
            ⟨explicitFormulaZeroResidue f (explicitFormulaContourZeroDataOfCompletedZero rho),
              explicitFormulaRectangle_completedZero_localResidue_tendsto_contourSummand
                f phiControl rho⟩
          exact Eq.subst (motive := P) hcoord hrhoLimit

/-- Off the singular set, the completed contour integrand is regular from the
test-transform analytic control alone. -/
theorem explicitFormulaRectangleContourIntegrand_regularAt_interior_of_not_singular_phiControl
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (phiControl : ZetaPhiAnalyticControl f) (T : ℝ) {z : ℂ}
    (_hinterior : z ∈ explicitFormulaContourFamilyInterior F T)
    (hz : z ∉ completedZetaContourIntegrandSingularSet) :
    ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
      DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z := by
  exact And.intro
    (completedZetaContourIntegrand_continuousAt_off_singularSet phiControl hz)
    (completedZetaContourIntegrand_differentiableAt_off_singularSet phiControl hz)

/-- Local residue coefficient regularity on a supplied deleted region, with the
full analytic package replaced by explicit test-transform control. -/
theorem explicitFormulaRectangle_localResidueCoefficient_regularOn_of_deletedDisk_avoids_singular_phiControl
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (phiControl : ZetaPhiAnalyticControl f) (T : ℝ) (a : ℂ)
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
    fun z hz => by
      have hregular :
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z :=
        explicitFormulaRectangleContourIntegrand_regularAt_interior_of_not_singular_phiControl
          f F phiControl T (hinterior z hz) (havoid z hz)
      have hsub :
          ContinuousAt (fun w : ℂ => w - a) z :=
        continuousAt_id.sub continuousAt_const
      exact (hsub.mul hregular.1).continuousWithinAt
  have hdifferentiable :
      ∀ z : ℂ,
        z ∈ R \ s →
          DifferentiableAt ℂ
            (fun w : ℂ => (w - a) * zetaCompletedExplicitFormulaContourIntegrand f w)
            z :=
    fun z hz => by
      have hzR : z ∈ R := hz.1
      have hregular :
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z :=
        explicitFormulaRectangleContourIntegrand_regularAt_interior_of_not_singular_phiControl
          f F phiControl T (hinterior z hzR) (havoid z hzR)
      have hsub :
          DifferentiableAt ℂ (fun w : ℂ => w - a) z :=
        differentiableAt_id'.sub_const a
      exact hsub.mul hregular.2
  exact And.intro hcontinuous hdifferentiable

/-- Closed-deleted-ball coefficient regularity from explicit test-transform control and
closed-radius singular-set geometry. -/
theorem explicitFormulaRectangle_rawDeletedClosedBall_localResidueCoefficient_regular_phiControl
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (phiControl : ZetaPhiAnalyticControl f)
    {T epsilon : ℝ} (hT : 0 < T) (hepsilon : 0 < epsilon)
    (hinterior :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate rho ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate rho ∈ completedZetaContourIntegrandSingularSet)
    (hclosedBall :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a epsilon ⊆ explicitFormulaContourFamilyInterior F T)
    (hclosedDisjoint :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b →
                Disjoint (Metric.closedBall a epsilon) (Metric.closedBall b epsilon))
    (a : ℂ) (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (s : Set ℂ) :
    ContinuousOn
        (fun z : ℂ => (z - a) * zetaCompletedExplicitFormulaContourIntegrand f z)
        (Metric.closedBall a epsilon \ {a}) ∧
      (∀ z : ℂ,
        z ∈ (Metric.ball a epsilon \ {a}) \ s →
          DifferentiableAt ℂ
            (fun w : ℂ => (w - a) * zetaCompletedExplicitFormulaContourIntegrand f w)
            z) := by
  have hregular :
      ContinuousOn
          (fun z : ℂ => (z - a) * zetaCompletedExplicitFormulaContourIntegrand f z)
          (Metric.closedBall a epsilon \ {a}) ∧
        (∀ z : ℂ,
          z ∈ (Metric.closedBall a epsilon \ {a}) \ s →
            DifferentiableAt ℂ
              (fun w : ℂ => (w - a) * zetaCompletedExplicitFormulaContourIntegrand f w)
              z) :=
    explicitFormulaRectangle_localResidueCoefficient_regularOn_of_deletedDisk_avoids_singular_phiControl
      f F phiControl T a
      (Metric.closedBall a epsilon \ {a})
      s
      (fun z hz => hclosedBall a ha hz.1)
      (fun z hz =>
        explicitFormulaRectangle_deletedClosedBall_not_mem_singularSet_of_rawClosedDisjoint
          F hT hepsilon hinterior hclosedBall hclosedDisjoint ha hz)
  exact And.intro
    hregular.1
    (fun z hz =>
      hregular.2 z
        (And.intro
          (And.intro
            (Metric.ball_subset_closedBall hz.1.1)
            hz.1.2)
          hz.2))

/-- Raw-singular coefficient regularity from `ZetaPhiAnalyticControl` and the selected
closed-radius geometry. -/
theorem explicitFormulaRectangleRawSingular_coefficientRegularity_of_phiControl
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (phiControl : ZetaPhiAnalyticControl f) {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate rho ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate rho ∈ completedZetaContourIntegrandSingularSet)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a epsilon ⊆ explicitFormulaContourFamilyInterior F T)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → epsilon + epsilon < dist a b)
    (a : ℂ) (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    ContinuousOn (fun z : ℂ => (z - a) * zetaCompletedExplicitFormulaContourIntegrand f z)
        (Metric.closedBall a (epsilon / 2) \ {a}) ∧
      (∀ z : ℂ,
        z ∈ (Metric.ball a (epsilon / 2) \ {a}) \ (∅ : Set ℂ) →
          DifferentiableAt ℂ
            (fun w : ℂ => (w - a) * zetaCompletedExplicitFormulaContourIntegrand f w) z) ∧
      ContinuousOn (fun z : ℂ => (z - a) * zetaCompletedExplicitFormulaContourIntegrand f z)
          ((Set.uIcc (a.re - (epsilon / 2) / 2) (a.re + (epsilon / 2) / 2) ×ℂ
            Set.uIcc (a.im - (epsilon / 2) / 2) (a.im + (epsilon / 2) / 2)) \ {a}) ∧
        (∀ z : ℂ,
          z ∈ ((Set.Ioo (a.re - (epsilon / 2) / 2) (a.re + (epsilon / 2) / 2) ×ℂ
              Set.Ioo (a.im - (epsilon / 2) / 2) (a.im + (epsilon / 2) / 2)) \ {a}) \
              (∅ : Set ℂ) →
            DifferentiableAt ℂ
              (fun w : ℂ => (w - a) * zetaCompletedExplicitFormulaContourIntegrand f w) z) := by
  have hepsilonHalf : 0 < epsilon / 2 :=
    finiteRectangle_halfRadius_pos hepsilon
  have hclosedHalf :
      ∀ b : ℂ,
        b ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall b (epsilon / 2) ⊆ explicitFormulaContourFamilyInterior F T := by
    intro b hb
    exact Set.Subset.trans
      (finiteRectangle_closedBall_subset_of_radius_le
        (finiteRectangle_halfRadius_le_self hepsilon))
      (hclosed b hb)
  have hdisjointHalf :
      ∀ b : ℂ,
        b ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ d : ℂ,
            d ∈ explicitFormulaRectangleRawSingularCoordinates T →
              b ≠ d →
                Disjoint (Metric.closedBall b (epsilon / 2)) (Metric.closedBall d (epsilon / 2)) := by
    intro b hb d hd hbd
    have hhalfSum :
        epsilon / 2 + epsilon / 2 < dist b d := by
      calc
        epsilon / 2 + epsilon / 2 = epsilon := by
          exact add_halves epsilon
        _ < epsilon + epsilon := by
          exact lt_add_of_pos_right epsilon hepsilon
        _ < dist b d := by
          exact hsep b hb d hd hbd
    exact Metric.closedBall_disjoint_closedBall hhalfSum
  have hdisk :
      ContinuousOn (fun z : ℂ => (z - a) * zetaCompletedExplicitFormulaContourIntegrand f z)
          (Metric.closedBall a (epsilon / 2) \ {a}) ∧
        (∀ z : ℂ,
          z ∈ (Metric.ball a (epsilon / 2) \ {a}) \ (∅ : Set ℂ) →
            DifferentiableAt ℂ
              (fun w : ℂ => (w - a) * zetaCompletedExplicitFormulaContourIntegrand f w) z) :=
    explicitFormulaRectangle_rawDeletedClosedBall_localResidueCoefficient_regular_phiControl
      f F phiControl hT hepsilonHalf hinterior hclosedHalf hdisjointHalf a ha (∅ : Set ℂ)
  have hsquareSubsetClosedBall :
      ((Set.uIcc (a.re - (epsilon / 2) / 2) (a.re + (epsilon / 2) / 2) ×ℂ
          Set.uIcc (a.im - (epsilon / 2) / 2) (a.im + (epsilon / 2) / 2)) \ {a}) ⊆
        Metric.closedBall a (epsilon / 2) \ {a} := by
    intro z hz
    have hzcell :
        z ∈ explicitFormulaRectangleRawInscribedSquareClosedCell (epsilon / 2) a := by
      have hre :
          z.re ∈
            Set.uIcc (explicitFormulaRectangleRawInscribedSquareLowerCorner (epsilon / 2) a).re
              (explicitFormulaRectangleRawInscribedSquareUpperCorner (epsilon / 2) a).re :=
        finiteRectangle_mem_uIcc_congr_endpoints
          (explicitFormulaRectangleRawInscribedSquareLowerCorner_re (epsilon / 2) a).symm
          (explicitFormulaRectangleRawInscribedSquareUpperCorner_re (epsilon / 2) a).symm
          hz.1.1
      have him :
          z.im ∈
            Set.uIcc (explicitFormulaRectangleRawInscribedSquareLowerCorner (epsilon / 2) a).im
              (explicitFormulaRectangleRawInscribedSquareUpperCorner (epsilon / 2) a).im :=
        finiteRectangle_mem_uIcc_congr_endpoints
          (explicitFormulaRectangleRawInscribedSquareLowerCorner_im (epsilon / 2) a).symm
          (explicitFormulaRectangleRawInscribedSquareUpperCorner_im (epsilon / 2) a).symm
          hz.1.2
      exact And.intro hre him
    exact And.intro
      (explicitFormulaRectangleRawInscribedSquareClosedCell_subset_closedBall
        (finiteRectangle_halfRadius_nonneg hepsilon) a hzcell)
      hz.2
  have hcontSquare :
      ContinuousOn (fun z : ℂ => (z - a) * zetaCompletedExplicitFormulaContourIntegrand f z)
        ((Set.uIcc (a.re - (epsilon / 2) / 2) (a.re + (epsilon / 2) / 2) ×ℂ
          Set.uIcc (a.im - (epsilon / 2) / 2) (a.im + (epsilon / 2) / 2)) \ {a}) :=
    hdisk.1.mono hsquareSubsetClosedBall
  have hopenSquareSubsetClosedBall :
      ((Set.Ioo (a.re - (epsilon / 2) / 2) (a.re + (epsilon / 2) / 2) ×ℂ
          Set.Ioo (a.im - (epsilon / 2) / 2) (a.im + (epsilon / 2) / 2)) \ {a}) ⊆
        Metric.closedBall a (epsilon / 2) \ {a} := by
    intro z hz
    have hclosedMem :
        z ∈ (Set.uIcc (a.re - (epsilon / 2) / 2) (a.re + (epsilon / 2) / 2) ×ℂ
          Set.uIcc (a.im - (epsilon / 2) / 2) (a.im + (epsilon / 2) / 2)) := by
      have hre :
          z.re ∈ Set.uIcc (a.re - (epsilon / 2) / 2) (a.re + (epsilon / 2) / 2) := by
        exact Set.Icc_subset_uIcc (Set.Ioo_subset_Icc_self hz.1.1)
      have him :
          z.im ∈ Set.uIcc (a.im - (epsilon / 2) / 2) (a.im + (epsilon / 2) / 2) := by
        exact Set.Icc_subset_uIcc (Set.Ioo_subset_Icc_self hz.1.2)
      exact And.intro hre him
    exact hsquareSubsetClosedBall (And.intro hclosedMem hz.2)
  have hregularOpen :
      ContinuousOn
          (fun z : ℂ => (z - a) * zetaCompletedExplicitFormulaContourIntegrand f z)
          ((Set.Ioo (a.re - (epsilon / 2) / 2) (a.re + (epsilon / 2) / 2) ×ℂ
              Set.Ioo (a.im - (epsilon / 2) / 2) (a.im + (epsilon / 2) / 2)) \ {a}) ∧
        (∀ z : ℂ,
          z ∈ ((Set.Ioo (a.re - (epsilon / 2) / 2) (a.re + (epsilon / 2) / 2) ×ℂ
              Set.Ioo (a.im - (epsilon / 2) / 2) (a.im + (epsilon / 2) / 2)) \ {a}) \
              (∅ : Set ℂ) →
            DifferentiableAt ℂ
              (fun w : ℂ => (w - a) * zetaCompletedExplicitFormulaContourIntegrand f w) z) :=
    explicitFormulaRectangle_localResidueCoefficient_regularOn_of_deletedDisk_avoids_singular_phiControl
      f F phiControl T a
      ((Set.Ioo (a.re - (epsilon / 2) / 2) (a.re + (epsilon / 2) / 2) ×ℂ
          Set.Ioo (a.im - (epsilon / 2) / 2) (a.im + (epsilon / 2) / 2)) \ {a})
      (∅ : Set ℂ)
      (fun z hz => hclosedHalf a ha (hopenSquareSubsetClosedBall hz).1)
      (fun z hz =>
        explicitFormulaRectangle_deletedClosedBall_not_mem_singularSet_of_rawClosedDisjoint
          F hT hepsilonHalf hinterior hclosedHalf hdisjointHalf ha
          (hopenSquareSubsetClosedBall hz))
  exact And.intro hdisk.1
    (And.intro hdisk.2
      (And.intro hcontSquare hregularOpen.2))

/-- Punctured residue regularity assembled from an explicit coefficient-regularity
statement and the package-free residue-limit theorem. -/
theorem explicitFormulaRectangleRawSingular_puncturedResidueRegularity_of_coefficientRegularity
    (f : ZetaAdmissibleFunction) (phiControl : ZetaPhiAnalyticControl f)
    {T epsilon : ℝ} (a : ℂ)
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (hcoefficient :
      ContinuousOn (fun z : ℂ => (z - a) * zetaCompletedExplicitFormulaContourIntegrand f z)
          (Metric.closedBall a (epsilon / 2) \ {a}) ∧
        (∀ z : ℂ,
          z ∈ (Metric.ball a (epsilon / 2) \ {a}) \ (∅ : Set ℂ) →
            DifferentiableAt ℂ
              (fun w : ℂ => (w - a) * zetaCompletedExplicitFormulaContourIntegrand f w) z) ∧
        ContinuousOn (fun z : ℂ => (z - a) * zetaCompletedExplicitFormulaContourIntegrand f z)
            ((Set.uIcc (a.re - (epsilon / 2) / 2) (a.re + (epsilon / 2) / 2) ×ℂ
              Set.uIcc (a.im - (epsilon / 2) / 2) (a.im + (epsilon / 2) / 2)) \ {a}) ∧
          (∀ z : ℂ,
            z ∈ ((Set.Ioo (a.re - (epsilon / 2) / 2) (a.re + (epsilon / 2) / 2) ×ℂ
                Set.Ioo (a.im - (epsilon / 2) / 2) (a.im + (epsilon / 2) / 2)) \ {a}) \
                (∅ : Set ℂ) →
              DifferentiableAt ℂ
                (fun w : ℂ => (w - a) * zetaCompletedExplicitFormulaContourIntegrand f w) z)) :
    ∃ residue : ℂ,
      ContinuousOn (fun z : ℂ => (z - a) * zetaCompletedExplicitFormulaContourIntegrand f z)
          (Metric.closedBall a (epsilon / 2) \ {a}) ∧
        (∀ z : ℂ,
          z ∈ (Metric.ball a (epsilon / 2) \ {a}) \ (∅ : Set ℂ) →
            DifferentiableAt ℂ
              (fun w : ℂ => (w - a) * zetaCompletedExplicitFormulaContourIntegrand f w) z) ∧
        ContinuousOn (fun z : ℂ => (z - a) * zetaCompletedExplicitFormulaContourIntegrand f z)
            ((Set.uIcc (a.re - (epsilon / 2) / 2) (a.re + (epsilon / 2) / 2) ×ℂ
              Set.uIcc (a.im - (epsilon / 2) / 2) (a.im + (epsilon / 2) / 2)) \ {a}) ∧
          (∀ z : ℂ,
            z ∈ ((Set.Ioo (a.re - (epsilon / 2) / 2) (a.re + (epsilon / 2) / 2) ×ℂ
                Set.Ioo (a.im - (epsilon / 2) / 2) (a.im + (epsilon / 2) / 2)) \ {a}) \
                (∅ : Set ℂ) →
              DifferentiableAt ℂ
                (fun w : ℂ => (w - a) * zetaCompletedExplicitFormulaContourIntegrand f w) z) ∧
            Tendsto (fun z : ℂ => (z - a) * zetaCompletedExplicitFormulaContourIntegrand f z)
              (𝓝[≠] a) (𝓝 residue) := by
  match explicitFormulaRectangleRawSingular_residueLimit_of_phiControl f phiControl a ha with
  | ⟨residue, hlimit⟩ =>
      match hcoefficient with
      | ⟨hcontDisk, hdiffDisk, hcontSquare, hdiffSquare⟩ =>
          exact ⟨residue, hcontDisk, hdiffDisk, hcontSquare, hdiffSquare, hlimit⟩

/-- Package-free circle-to-deleted-square deformation from supplied local
punctured-residue regularity. -/
theorem explicitFormulaRectangleComplement_circleEqDeletedSquare_of_puncturedResidueRegularity
    (f : ZetaAdmissibleFunction) (T epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hregularity :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∃ residue : ℂ,
            ContinuousOn
              (fun z : ℂ => (z - a) * zetaCompletedExplicitFormulaContourIntegrand f z)
              (Metric.closedBall a (epsilon / 2) \ {a}) ∧
            (∀ z : ℂ,
              z ∈ (Metric.ball a (epsilon / 2) \ {a}) \ (∅ : Set ℂ) →
                DifferentiableAt ℂ
                  (fun w : ℂ =>
                    (w - a) * zetaCompletedExplicitFormulaContourIntegrand f w) z) ∧
            ContinuousOn
              (fun z : ℂ => (z - a) * zetaCompletedExplicitFormulaContourIntegrand f z)
              ((Set.uIcc (a.re - (epsilon / 2) / 2) (a.re + (epsilon / 2) / 2) ×ℂ
                Set.uIcc (a.im - (epsilon / 2) / 2) (a.im + (epsilon / 2) / 2)) \ {a}) ∧
              (∀ z : ℂ,
                z ∈ ((Set.Ioo (a.re - (epsilon / 2) / 2)
                      (a.re + (epsilon / 2) / 2) ×ℂ
                    Set.Ioo (a.im - (epsilon / 2) / 2)
                      (a.im + (epsilon / 2) / 2)) \ {a}) \ (∅ : Set ℂ) →
                  DifferentiableAt ℂ
                    (fun w : ℂ =>
                      (w - a) * zetaCompletedExplicitFormulaContourIntegrand f w) z) ∧
                Tendsto
                  (fun z : ℂ =>
                    (z - a) * zetaCompletedExplicitFormulaContourIntegrand f z)
                  (𝓝[≠] a) (𝓝 residue)) :
    ∀ a : ℂ,
      a ∈ explicitFormulaRectangleRawSingularCoordinates T →
        explicitFormulaRectangleRawDeletedCircleBoundary f (epsilon / 2) a =
          explicitFormulaRectangleRawDeletedSquareBoundary f ((epsilon / 2) / 2) a := by
  intro a ha
  match hregularity a ha with
  | ⟨residue, hcontCircle, hdiffCircle, hcontSquare, hdiffSquare, hlim⟩ =>
      have hhalf : (0 : ℝ) < epsilon / 2 :=
        half_pos hepsilon
      have hquarter : (0 : ℝ) < (epsilon / 2) / 2 :=
        half_pos hhalf
      have hcircle :
          explicitFormulaRectangleRawDeletedCircleBoundary f (epsilon / 2) a =
            (2 * ↑Real.pi * Complex.I : ℂ) • residue :=
        finiteRectangle_deletedCircleIntegral_eq_twoPiI_smul_residue
          (c := a) (R := epsilon / 2) hhalf
          (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
          residue (∅ : Set ℂ) Set.countable_empty hcontCircle hdiffCircle hlim
      have hsquare :
          explicitFormulaRectangleRawDeletedSquareBoundary f ((epsilon / 2) / 2) a =
            (2 * ↑Real.pi * Complex.I : ℂ) • residue :=
        finiteRectangleSquareBoundaryIntegral_eq_twoPiI_smul_residue
          a hquarter
          (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
          residue (∅ : Set ℂ) Set.countable_empty hcontSquare hdiffSquare hlim
      exact Eq.trans hcircle hsquare.symm

/-- Package-free circle-to-inscribed-square deletion agreement from supplied local
punctured-residue regularity. -/
theorem explicitFormulaRectangleComplement_circleEqSquare_of_puncturedResidueRegularity
    (f : ZetaAdmissibleFunction) (T epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hregularity :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∃ residue : ℂ,
            ContinuousOn
              (fun z : ℂ => (z - a) * zetaCompletedExplicitFormulaContourIntegrand f z)
              (Metric.closedBall a (epsilon / 2) \ {a}) ∧
            (∀ z : ℂ,
              z ∈ (Metric.ball a (epsilon / 2) \ {a}) \ (∅ : Set ℂ) →
                DifferentiableAt ℂ
                  (fun w : ℂ =>
                    (w - a) * zetaCompletedExplicitFormulaContourIntegrand f w) z) ∧
            ContinuousOn
              (fun z : ℂ => (z - a) * zetaCompletedExplicitFormulaContourIntegrand f z)
              ((Set.uIcc (a.re - (epsilon / 2) / 2) (a.re + (epsilon / 2) / 2) ×ℂ
                Set.uIcc (a.im - (epsilon / 2) / 2) (a.im + (epsilon / 2) / 2)) \ {a}) ∧
              (∀ z : ℂ,
                z ∈ ((Set.Ioo (a.re - (epsilon / 2) / 2)
                      (a.re + (epsilon / 2) / 2) ×ℂ
                    Set.Ioo (a.im - (epsilon / 2) / 2)
                      (a.im + (epsilon / 2) / 2)) \ {a}) \ (∅ : Set ℂ) →
                  DifferentiableAt ℂ
                    (fun w : ℂ =>
                      (w - a) * zetaCompletedExplicitFormulaContourIntegrand f w) z) ∧
                Tendsto
                  (fun z : ℂ =>
                    (z - a) * zetaCompletedExplicitFormulaContourIntegrand f z)
                  (𝓝[≠] a) (𝓝 residue)) :
    ∀ a : ℂ,
      a ∈ explicitFormulaRectangleRawSingularCoordinates T →
        explicitFormulaRectangleRawDeletedCircleBoundary f (epsilon / 2) a =
          explicitFormulaRectangleRawInscribedSquareBoundary f (epsilon / 2) a :=
  explicitFormulaRectangleRawDeletedCircleBoundary_half_eq_rawInscribedSquareBoundary_half_on_of_rawDeletedSquare_quarter_on
    f T epsilon
    (explicitFormulaRectangleComplement_circleEqDeletedSquare_of_puncturedResidueRegularity
      f T epsilon hepsilon hregularity)

/-- Package-free endpoint-data complement subdivision identity. -/
theorem explicitFormulaRectangleComplement_endpointDataSubdivision_noPackage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T : ℝ} (hT : 0 < T) :
    ∀ epsilon : ℝ,
      0 < epsilon →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            Metric.closedBall a epsilon ⊆ explicitFormulaContourFamilyInterior F T) →
        explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (epsilon / 2) (-T) →
        explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (epsilon / 2) T →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (epsilon / 2)
              (explicitFormulaRectangleRawInscribedSquareLowerCorner (epsilon / 2) a).im) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (epsilon / 2)
              (explicitFormulaRectangleRawInscribedSquareUpperCorner (epsilon / 2) a).im) →
        explicitFormulaRectangleSortedYVerticalSideIntegrable f T (epsilon / 2) F.c →
        explicitFormulaRectangleSortedYVerticalSideIntegrable f T (epsilon / 2) (1 - F.c) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            explicitFormulaRectangleSortedYVerticalSideIntegrable f T (epsilon / 2)
              (explicitFormulaRectangleRawInscribedSquareUpperCorner (epsilon / 2) a).re) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            explicitFormulaRectangleSortedYVerticalSideIntegrable f T (epsilon / 2)
              (explicitFormulaRectangleRawInscribedSquareLowerCorner (epsilon / 2) a).re) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            ∀ b : ℂ,
              b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a ≠ b → epsilon + epsilon < dist a b) →
          ∃ data : List
              (ExplicitFormulaRectangleRegularGridCellEndpointData F T (epsilon / 2)),
            zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
                ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
                  finiteRectangleSubdivisionCellBoundaryIntegral
                    (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
                    (explicitFormulaRectangleRawInscribedSquareLowerCorner (epsilon / 2) a)
                    (explicitFormulaRectangleRawInscribedSquareUpperCorner (epsilon / 2) a) =
              explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data := by
  intro epsilon hepsilon hclosed hbottom htop hbottomHole htopHole hright hleft
    hrightHole hleftHole hsep
  have hTNonneg : 0 ≤ T :=
    le_of_lt hT
  let data : List
      (ExplicitFormulaRectangleRegularGridCellEndpointData F T (epsilon / 2)) :=
    explicitFormulaRectangleRawHoleSelectedEndpointData F T (epsilon / 2)
      (finiteRectangle_halfRadius_pos hepsilon)
  have hedges :
      explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data +
            (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data) =
        zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
          ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
            finiteRectangleSubdivisionCellBoundaryIntegral
              (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
              (explicitFormulaRectangleRawInscribedSquareLowerCorner (epsilon / 2) a)
              (explicitFormulaRectangleRawInscribedSquareUpperCorner (epsilon / 2) a) :=
    explicitFormulaRectangleRawHoleSelectedEndpointData_edgeAccounting_closedRadiusControls
      f F hTNonneg hepsilon hclosed hbottom htop hbottomHole htopHole hright hleft
      hrightHole hleftHole hsep
  have hendpoint :
      zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
          ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
            finiteRectangleSubdivisionCellBoundaryIntegral
              (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
              (explicitFormulaRectangleRawInscribedSquareLowerCorner (epsilon / 2) a)
              (explicitFormulaRectangleRawInscribedSquareUpperCorner (epsilon / 2) a) =
        explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data :=
    explicitFormulaRectangle_tangentContour_sub_rawInscribedSquareCellBoundarySum_eq_endpointDataBoundarySum_of_edgeSums
      f data hedges
  exact ⟨data, hendpoint⟩

/-- Package-free regular-grid subdivision hypothesis for finite-hole Cauchy. -/
theorem explicitFormulaRectangleComplement_hgrid_noPackage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T : ℝ} (hT : 0 < T) :
    ∀ epsilon : ℝ,
      0 < epsilon →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            Metric.closedBall a epsilon ⊆ explicitFormulaContourFamilyInterior F T) →
        explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (epsilon / 2) (-T) →
        explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (epsilon / 2) T →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (epsilon / 2)
              (explicitFormulaRectangleRawInscribedSquareLowerCorner (epsilon / 2) a).im) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (epsilon / 2)
              (explicitFormulaRectangleRawInscribedSquareUpperCorner (epsilon / 2) a).im) →
        explicitFormulaRectangleSortedYVerticalSideIntegrable f T (epsilon / 2) F.c →
        explicitFormulaRectangleSortedYVerticalSideIntegrable f T (epsilon / 2) (1 - F.c) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            explicitFormulaRectangleSortedYVerticalSideIntegrable f T (epsilon / 2)
              (explicitFormulaRectangleRawInscribedSquareUpperCorner (epsilon / 2) a).re) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            explicitFormulaRectangleSortedYVerticalSideIntegrable f T (epsilon / 2)
              (explicitFormulaRectangleRawInscribedSquareLowerCorner (epsilon / 2) a).re) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            ∀ b : ℂ,
              b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a ≠ b → epsilon + epsilon < dist a b) →
          ∃ data : List
              (ExplicitFormulaRectangleRegularGridCellEndpointData F T (epsilon / 2)),
            zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
                ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
                  finiteRectangleSubdivisionCellBoundaryIntegral
                    (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
                    (explicitFormulaRectangleRawInscribedSquareLowerCorner (epsilon / 2) a)
                    (explicitFormulaRectangleRawInscribedSquareUpperCorner (epsilon / 2) a) =
              explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data :=
  explicitFormulaRectangleComplement_endpointDataSubdivision_noPackage f F hT

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
