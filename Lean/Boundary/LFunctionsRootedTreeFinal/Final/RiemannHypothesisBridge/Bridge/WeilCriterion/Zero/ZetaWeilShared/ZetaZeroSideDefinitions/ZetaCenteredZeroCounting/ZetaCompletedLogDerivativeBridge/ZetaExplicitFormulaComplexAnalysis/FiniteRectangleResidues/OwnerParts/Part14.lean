import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part13

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

/-- Deleted-circle residue theorem at the completed-zeta pole coordinate `0` for the
actual completed explicit-formula contour integrand.  The remaining analytic input is the
true full-contour local coefficient limit at `0`. -/
theorem explicitFormulaRectangle_zeroPole_deletedCircleIntegral_eq_twoPiI_smul_residue
    (f : ZetaAdmissibleFunction)
    {R : ℝ} (hR : 0 < R)
    (s : Set ℂ) (hs : s.Countable)
    (hcontinuous :
      ContinuousOn
        (fun z : ℂ => (z - 0) * zetaCompletedExplicitFormulaContourIntegrand f z)
        (Metric.closedBall (0 : ℂ) R \ {(0 : ℂ)}))
    (hdifferentiable :
      ∀ z : ℂ,
        z ∈ (Metric.ball (0 : ℂ) R \ {(0 : ℂ)}) \ s →
          DifferentiableAt ℂ
            (fun w : ℂ => (w - 0) * zetaCompletedExplicitFormulaContourIntegrand f w)
            z)
    (hlocal :
      Tendsto
        (fun z : ℂ => (z - 0) * zetaCompletedExplicitFormulaContourIntegrand f z)
        (𝓝[≠] (0 : ℂ))
        (𝓝 (explicitFormulaRectangle_zeroPoleResidue f))) :
    (∮ z in C((0 : ℂ), R),
        zetaCompletedExplicitFormulaContourIntegrand f z) =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaRectangle_zeroPoleResidue f := by
  exact
    finiteRectangle_deletedCircleIntegral_eq_twoPiI_smul_residue
      hR
      (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
      (explicitFormulaRectangle_zeroPoleResidue f)
      s
      hs
      hcontinuous
      hdifferentiable
      hlocal

/-- Deleted-circle residue theorem at the completed-zeta pole coordinate `1` for the
actual completed explicit-formula contour integrand.  The remaining analytic input is the
true full-contour local coefficient limit at `1`. -/
theorem explicitFormulaRectangle_onePole_deletedCircleIntegral_eq_twoPiI_smul_residue
    (f : ZetaAdmissibleFunction)
    {R : ℝ} (hR : 0 < R)
    (s : Set ℂ) (hs : s.Countable)
    (hcontinuous :
      ContinuousOn
        (fun z : ℂ => (z - 1) * zetaCompletedExplicitFormulaContourIntegrand f z)
        (Metric.closedBall (1 : ℂ) R \ {(1 : ℂ)}))
    (hdifferentiable :
      ∀ z : ℂ,
        z ∈ (Metric.ball (1 : ℂ) R \ {(1 : ℂ)}) \ s →
          DifferentiableAt ℂ
            (fun w : ℂ => (w - 1) * zetaCompletedExplicitFormulaContourIntegrand f w)
            z)
    (hlocal :
      Tendsto
        (fun z : ℂ => (z - 1) * zetaCompletedExplicitFormulaContourIntegrand f z)
        (𝓝[≠] (1 : ℂ))
        (𝓝 (explicitFormulaRectangle_onePoleResidue f))) :
    (∮ z in C((1 : ℂ), R),
        zetaCompletedExplicitFormulaContourIntegrand f z) =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaRectangle_onePoleResidue f := by
  exact
    finiteRectangle_deletedCircleIntegral_eq_twoPiI_smul_residue
      hR
      (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
      (explicitFormulaRectangle_onePoleResidue f)
      s
      hs
      hcontinuous
      hdifferentiable
      hlocal

/-- A base-domain point avoiding each listed deleted disk lies in the punctured rectangle. -/
theorem finiteRectanglePuncturedDomain_mem_of_mem_base_of_forall_not_mem_ball
    (R : Set ℂ) (S : Finset ℂ) (ε : ℝ) {z : ℂ}
    (hR : z ∈ R) (havoid : ∀ a : ℂ, a ∈ S → z ∉ Metric.ball a ε) :
    z ∈ finiteRectanglePuncturedDomain R S ε :=
  And.intro hR
    (fun hdeleted =>
      Exists.elim hdeleted
        (fun a ha_deleted =>
          (havoid a ha_deleted.left) ha_deleted.right))

/-- A set contained in the base rectangle and avoiding every deleted disk is contained in
the finite punctured rectangle. -/
theorem finiteRectanglePuncturedDomain_subset_of_subset_base_of_forall_not_mem_ball
    (R U : Set ℂ) (S : Finset ℂ) (ε : ℝ)
    (hR : U ⊆ R)
    (havoid : ∀ z : ℂ, z ∈ U → ∀ a : ℂ, a ∈ S → z ∉ Metric.ball a ε) :
    U ⊆ finiteRectanglePuncturedDomain R S ε :=
  fun z hz =>
    finiteRectanglePuncturedDomain_mem_of_mem_base_of_forall_not_mem_ball
      R S ε
      (hR hz)
      (havoid z hz)

/-- A closed rectangular cell is contained in the finite punctured rectangle once its
closed cell lies in the base rectangle and avoids every deleted disk. -/
theorem finiteRectangleClosedCell_subset_puncturedDomain_of_subset_base_of_forall_not_mem_ball
    (R : Set ℂ) (S : Finset ℂ) (ε : ℝ) (z w : ℂ)
    (hR : (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) ⊆ R)
    (havoid :
      ∀ x : ℂ,
        x ∈ (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) →
          ∀ a : ℂ, a ∈ S → x ∉ Metric.ball a ε) :
    (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) ⊆
      finiteRectanglePuncturedDomain R S ε :=
  finiteRectanglePuncturedDomain_subset_of_subset_base_of_forall_not_mem_ball
    R
    (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im)
    S ε hR havoid

/-- Under closed-radius containment and strict pairwise separation, every point on a
deleted circle belongs to the punctured rectangle domain: it is on the boundary of its
own deleted disk, outside every other deleted disk, and still inside the rectangle
interior. -/
theorem finiteRectanglePuncturedDomain_mem_of_mem_sphere_of_closedBall_subset_pairwise
    (R : Set ℂ) (S : Finset ℂ) (ε : ℝ) {a z : ℂ}
    (ha : a ∈ S) (hz : z ∈ Metric.sphere a ε)
    (hclosed : ∀ b : ℂ, b ∈ S → Metric.closedBall b ε ⊆ R)
    (hsep :
      ∀ b : ℂ,
        b ∈ S →
          ∀ c : ℂ,
            c ∈ S →
              b ≠ c → ε + ε < dist b c) :
    z ∈ finiteRectanglePuncturedDomain R S ε :=
  finiteRectanglePuncturedDomain_mem_of_mem_base_of_forall_not_mem_ball
    R S ε
    (hclosed a ha (Metric.mem_closedBall.mpr (le_of_eq (Metric.mem_sphere.mp hz))))
    (fun b hb hball =>
      match eq_or_ne b a with
      | Or.inl hba =>
          have hz_dist : dist z a = ε :=
            Metric.mem_sphere.mp hz
          have hball_a : z ∈ Metric.ball a ε :=
            Eq.subst
              (motive := fun w : ℂ => z ∈ Metric.ball w ε)
              hba
              hball
          have hlt : dist z a < ε :=
            Metric.mem_ball.mp hball_a
          (not_lt_of_ge (le_of_eq hz_dist.symm)) hlt
      | Or.inr hba_ne =>
          have hza : dist z a = ε :=
            Metric.mem_sphere.mp hz
          have haz : dist a z = ε := by
            calc
              dist a z = dist z a := by
                exact dist_comm a z
              _ = ε := hza
          have hzb_lt : dist z b < ε :=
            Metric.mem_ball.mp hball
          have hab_lt : dist a b < ε + ε := by
            exact
              lt_of_le_of_lt
                (dist_triangle a z b)
                (by
                  calc
                    dist a z + dist z b = ε + dist z b := by
                      exact congrArg (fun x : ℝ => x + dist z b) haz
                    _ < ε + ε := by
                      exact add_lt_add_left hzb_lt ε)
          have hsep_ab : ε + ε < dist a b :=
            hsep a ha b hb hba_ne.symm
          lt_asymm hab_lt hsep_ab)

/-- The actual deleted-circle parametrization for one raw singular coordinate lies in
the finite-radius punctured rectangle whenever the chosen radius has the closed-disk
containment and strict pairwise-separation controls. -/
theorem explicitFormulaRectangleRawCircleMap_mem_puncturedDomain_of_closedRadiusControls
    (F : ExplicitFormulaContourFamily) (T ε θ : ℝ) {a : ℂ}
    (hε : 0 < ε)
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (hclosed :
      ∀ b : ℂ,
        b ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall b ε ⊆ explicitFormulaContourFamilyInterior F T)
    (hsep :
      ∀ b : ℂ,
        b ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ c : ℂ,
            c ∈ explicitFormulaRectangleRawSingularCoordinates T →
              b ≠ c → ε + ε < dist b c) :
    circleMap a ε θ ∈
      finiteRectanglePuncturedDomain
        (explicitFormulaContourFamilyInterior F T)
        (explicitFormulaRectangleRawSingularCoordinates T)
        ε :=
  finiteRectanglePuncturedDomain_mem_of_mem_sphere_of_closedBall_subset_pairwise
    (explicitFormulaContourFamilyInterior F T)
    (explicitFormulaRectangleRawSingularCoordinates T)
    ε
    ha
    (circleMap_mem_sphere a hε.le θ)
    hclosed
    hsep

/-- The deleted-circle parametrization for a raw singular coordinate remains in the
contour-family interior under the selected closed-radius controls. -/
theorem explicitFormulaRectangleRawCircleMap_mem_interior_of_closedRadiusControls
    (F : ExplicitFormulaContourFamily) (T ε θ : ℝ) {a : ℂ}
    (hε : 0 < ε)
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (hclosed :
      ∀ b : ℂ,
        b ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall b ε ⊆ explicitFormulaContourFamilyInterior F T)
    (hsep :
      ∀ b : ℂ,
        b ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ c : ℂ,
            c ∈ explicitFormulaRectangleRawSingularCoordinates T →
              b ≠ c → ε + ε < dist b c) :
    circleMap a ε θ ∈ explicitFormulaContourFamilyInterior F T :=
  finiteRectanglePuncturedDomain_mem_base
    (explicitFormulaContourFamilyInterior F T)
    (explicitFormulaRectangleRawSingularCoordinates T)
    ε
    (explicitFormulaRectangleRawCircleMap_mem_puncturedDomain_of_closedRadiusControls
      F T ε θ hε ha hclosed hsep)

/-- The deleted-circle parametrization for one raw singular coordinate avoids every raw
deleted disk under the selected closed-radius controls. -/
theorem explicitFormulaRectangleRawCircleMap_not_mem_deletedBall_of_closedRadiusControls
    (F : ExplicitFormulaContourFamily) (T ε θ : ℝ) {a b : ℂ}
    (hε : 0 < ε)
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (hb : b ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (hclosed :
      ∀ c : ℂ,
        c ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall c ε ⊆ explicitFormulaContourFamilyInterior F T)
    (hsep :
      ∀ c : ℂ,
        c ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ d : ℂ,
            d ∈ explicitFormulaRectangleRawSingularCoordinates T →
              c ≠ d → ε + ε < dist c d) :
    circleMap a ε θ ∉ Metric.ball b ε :=
  finiteRectanglePuncturedDomain_not_mem_deletedBall
    (explicitFormulaContourFamilyInterior F T)
    (explicitFormulaRectangleRawSingularCoordinates T)
    ε
    (explicitFormulaRectangleRawCircleMap_mem_puncturedDomain_of_closedRadiusControls
      F T ε θ hε ha hclosed hsep)
    hb

/-- The full range of the actual deleted-circle parametrization around a raw singular
coordinate lies in the finite-radius punctured rectangle under the selected closed-radius
controls. -/
theorem explicitFormulaRectangleRawCircleMap_range_subset_puncturedDomain_of_closedRadiusControls
    (F : ExplicitFormulaContourFamily) (T ε : ℝ) {a : ℂ}
    (hε : 0 < ε)
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (hclosed :
      ∀ b : ℂ,
        b ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall b ε ⊆ explicitFormulaContourFamilyInterior F T)
    (hsep :
      ∀ b : ℂ,
        b ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ c : ℂ,
            c ∈ explicitFormulaRectangleRawSingularCoordinates T →
              b ≠ c → ε + ε < dist b c) :
    Set.range (circleMap a ε) ⊆
      finiteRectanglePuncturedDomain
        (explicitFormulaContourFamilyInterior F T)
        (explicitFormulaRectangleRawSingularCoordinates T)
        ε :=
  fun _ hz =>
    Exists.elim hz
      (fun θ hθ =>
        Eq.subst
          (motive := fun w : ℂ =>
            w ∈
              finiteRectanglePuncturedDomain
                (explicitFormulaContourFamilyInterior F T)
                (explicitFormulaRectangleRawSingularCoordinates T)
                ε)
          hθ
          (explicitFormulaRectangleRawCircleMap_mem_puncturedDomain_of_closedRadiusControls
            F T ε θ hε ha hclosed hsep))

/-- The full range of the deleted-circle parametrization around a raw singular coordinate
lies in the contour-family interior under the selected closed-radius controls. -/
theorem explicitFormulaRectangleRawCircleMap_range_subset_interior_of_closedRadiusControls
    (F : ExplicitFormulaContourFamily) (T ε : ℝ) {a : ℂ}
    (hε : 0 < ε)
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (hclosed :
      ∀ b : ℂ,
        b ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall b ε ⊆ explicitFormulaContourFamilyInterior F T)
    (hsep :
      ∀ b : ℂ,
        b ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ c : ℂ,
            c ∈ explicitFormulaRectangleRawSingularCoordinates T →
              b ≠ c → ε + ε < dist b c) :
    Set.range (circleMap a ε) ⊆ explicitFormulaContourFamilyInterior F T :=
  fun _ hz =>
    finiteRectanglePuncturedDomain_mem_base
      (explicitFormulaContourFamilyInterior F T)
      (explicitFormulaRectangleRawSingularCoordinates T)
      ε
      (explicitFormulaRectangleRawCircleMap_range_subset_puncturedDomain_of_closedRadiusControls
        F T ε hε ha hclosed hsep hz)

/-- The completed contour integrand is continuous on every actual raw deleted-circle
range selected by the closed-radius controls. -/
theorem explicitFormulaRectangleRawCircleMap_range_continuousOn_of_closedRadiusControls
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    {a : ℂ}
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (hclosed :
      ∀ b : ℂ,
        b ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall b ε ⊆ explicitFormulaContourFamilyInterior F T)
    (hsep :
      ∀ b : ℂ,
        b ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ c : ℂ,
            c ∈ explicitFormulaRectangleRawSingularCoordinates T →
              b ≠ c → ε + ε < dist b c) :
    ContinuousOn
      (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
      (Set.range (circleMap a ε)) :=
  (explicitFormulaRectangleRawPuncturedInterior_continuousOn
    f F h hT hε hinterior).mono
    (explicitFormulaRectangleRawCircleMap_range_subset_puncturedDomain_of_closedRadiusControls
      F T ε hε ha hclosed hsep)

/-- The completed contour integrand is differentiable at every point of every actual raw
deleted-circle range selected by the closed-radius controls. -/
theorem explicitFormulaRectangleRawCircleMap_range_differentiableAt_of_closedRadiusControls
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    {a z : ℂ}
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (hz : z ∈ Set.range (circleMap a ε))
    (hclosed :
      ∀ b : ℂ,
        b ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall b ε ⊆ explicitFormulaContourFamilyInterior F T)
    (hsep :
      ∀ b : ℂ,
        b ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ c : ℂ,
            c ∈ explicitFormulaRectangleRawSingularCoordinates T →
              b ≠ c → ε + ε < dist b c) :
    DifferentiableAt ℂ
      (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z :=
  explicitFormulaRectangleRawPuncturedInterior_differentiableAt
    f F h hT hε hinterior
    (explicitFormulaRectangleRawCircleMap_range_subset_puncturedDomain_of_closedRadiusControls
      F T ε hε ha hclosed hsep hz)

/-- A base-domain point avoiding each indexed deleted disk lies in the indexed punctured
rectangle. -/
theorem finiteRectangleIndexedPuncturedDomain_mem_of_mem_base_of_forall_not_mem_ball
    {α : Type*} (R : Set ℂ) (S : Finset α) (center : α → ℂ) (ε : ℝ) {z : ℂ}
    (hR : z ∈ R) (havoid : ∀ a : α, a ∈ S → z ∉ Metric.ball (center a) ε) :
    z ∈ finiteRectangleIndexedPuncturedDomain R S center ε :=
  And.intro hR
    (fun hdeleted =>
      Exists.elim hdeleted
        (fun a ha_deleted =>
          (havoid a ha_deleted.left) ha_deleted.right))

/-- A point in the completed-zero-window punctured interior lies in the original contour
interior. -/
theorem explicitFormulaCompletedZeroWindowPuncturedInterior_mem_interior
    (F : ExplicitFormulaContourFamily) (T ε : ℝ) {z : ℂ}
    (hz : z ∈ explicitFormulaCompletedZeroWindowPuncturedInterior F T ε) :
    z ∈ explicitFormulaContourFamilyInterior F T :=
  finiteRectangleIndexedPuncturedDomain_mem_base
    (explicitFormulaContourFamilyInterior F T)
    (explicitFormulaCompletedZeroHeightWindow T)
    (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} => completedZeroResidueCoordinate ρ)
    ε
    hz

/-- A point in the completed-zero-window punctured interior avoids the deleted disk around
each completed zero in the height window. -/
theorem explicitFormulaCompletedZeroWindowPuncturedInterior_not_mem_zeroDisk
    (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    {ρ : {ρ : ℂ // ZetaCompletedZero ρ}} {z : ℂ}
    (hz : z ∈ explicitFormulaCompletedZeroWindowPuncturedInterior F T ε)
    (hρ : ρ ∈ explicitFormulaCompletedZeroHeightWindow T) :
    z ∉ Metric.ball (completedZeroResidueCoordinate ρ) ε :=
  finiteRectangleIndexedPuncturedDomain_not_mem_deletedBall
    (explicitFormulaContourFamilyInterior F T)
    (explicitFormulaCompletedZeroHeightWindow T)
    (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} => completedZeroResidueCoordinate ρ)
    ε
    hz
    hρ

/-- A contour-interior point avoiding each completed-zero deleted disk belongs to the
completed-zero-window punctured interior. -/
theorem explicitFormulaCompletedZeroWindowPuncturedInterior_mem_of_mem_interior_of_avoids
    (F : ExplicitFormulaContourFamily) (T ε : ℝ) {z : ℂ}
    (hinterior : z ∈ explicitFormulaContourFamilyInterior F T)
    (havoid :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T →
          z ∉ Metric.ball (completedZeroResidueCoordinate ρ) ε) :
    z ∈ explicitFormulaCompletedZeroWindowPuncturedInterior F T ε :=
  finiteRectangleIndexedPuncturedDomain_mem_of_mem_base_of_forall_not_mem_ball
    (explicitFormulaContourFamilyInterior F T)
    (explicitFormulaCompletedZeroHeightWindow T)
    (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} => completedZeroResidueCoordinate ρ)
    ε
    hinterior
    havoid

/-- Finite deleted-circle limits assemble into the finite residue sum. -/
theorem finiteRectangleDeletedBoundary_tendsto_sum_of_local
    {ι α : Type*} [TopologicalSpace ι] [DecidableEq α] {l : Filter ι}
    (S : Finset α) (deleted : ι → α → ℂ) (residue : α → ℂ) :
    (∀ a : α, a ∈ S → Tendsto (fun i : ι => deleted i a) l (𝓝 (residue a))) →
      Tendsto
        (fun i : ι => ∑ a in S, deleted i a)
        l
        (𝓝 (∑ a in S, residue a)) := by
  exact
    Finset.cons_induction_on S
      (fun _hlocal => tendsto_const_nhds)
      (fun a S ha ih hlocal =>
        let hlocal_a : Tendsto (fun i : ι => deleted i a) l (𝓝 (residue a)) :=
          hlocal a (Finset.mem_cons_self a S)
        let hlocal_S :
            ∀ b : α, b ∈ S → Tendsto (fun i : ι => deleted i b) l (𝓝 (residue b)) :=
          fun b hb => hlocal b (Finset.mem_cons_of_mem hb)
        let hsum_S :
            Tendsto
              (fun i : ι => ∑ b in S, deleted i b)
              l
              (𝓝 (∑ b in S, residue b)) :=
          ih hlocal_S
        let hsum_cons :
            Tendsto
              (fun i : ι => deleted i a + ∑ b in S, deleted i b)
              l
              (𝓝 (residue a + ∑ b in S, residue b)) :=
          hlocal_a.add hsum_S
        let hsource :
            (fun i : ι => deleted i a + ∑ b in S, deleted i b) =
              (fun i : ι => ∑ b in S.cons a ha, deleted i b) := by
          funext i
          exact (Finset.sum_cons ha).symm
        let htarget :
            residue a + ∑ b in S, residue b =
              ∑ b in S.cons a ha, residue b :=
          (Finset.sum_cons ha).symm
        htarget ▸
          (hsum_cons.congr' (Filter.Eventually.of_forall (fun i => congrFun hsource i))))

/-- The deleted-circle limits over the completed-zero height window assemble to the exact
finite residue window used by the explicit formula. -/
theorem explicitFormulaRectangle_completedZeroDeletedBoundary_tendsto_residueWindowSum
    {ι : Type*} [TopologicalSpace ι] {l : Filter ι}
    (f : ZetaAdmissibleFunction) (T : ℝ)
    (deleted : ι → {ρ : ℂ // ZetaCompletedZero ρ} → ℂ) :
    (∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
      ρ ∈ explicitFormulaCompletedZeroHeightWindow T →
        Tendsto
          (fun i : ι => deleted i ρ)
          l
          (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ)))) →
      Tendsto
        (fun i : ι =>
          ∑ ρ in explicitFormulaCompletedZeroHeightWindow T, deleted i ρ)
        l
        (𝓝
          (∑ ρ in explicitFormulaCompletedZeroHeightWindow T,
            explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ))) := by
  exact
    finiteRectangleDeletedBoundary_tendsto_sum_of_local
      (explicitFormulaCompletedZeroHeightWindow T)
      deleted
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ))

/-- The honest residue-calculus reconstruction with tangent normalization: once the
tangent-corrected contour has the zero-window residue sum and the tangent pole contour has
the pole residue sum, the raw contour has the pole-corrected residue target. -/
theorem zetaCompletedExplicitFormulaContourIntegral_eq_poleCorrectedResidueSum_of_tangentCorrectedContour
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hcorrected :
      explicitFormulaRectangle_tangentPoleCorrectedContourIntegral f F T =
        explicitFormulaCompletedZeroHeightWindowResidueSum f T)
    (hpoles :
      explicitFormulaRectangle_completedPoleTangentBoundaryContribution f F T =
        explicitFormulaRectangle_completedPoleResidueSum f) :
    zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) =
      explicitFormulaRectangle_poleCorrectedResidueSum f T := by
  calc
    zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) =
        explicitFormulaRectangle_tangentPoleCorrectedContourIntegral f F T +
          explicitFormulaRectangle_completedPoleTangentBoundaryContribution f F T := by
      exact zetaCompletedExplicitFormulaContourIntegral_eq_tangentPoleCorrected_add_tangentPoles f F T
    _ = explicitFormulaCompletedZeroHeightWindowResidueSum f T +
          explicitFormulaRectangle_completedPoleTangentBoundaryContribution f F T := by
      exact congrArg
        (fun z : ℂ => z + explicitFormulaRectangle_completedPoleTangentBoundaryContribution f F T)
        hcorrected
    _ = explicitFormulaCompletedZeroHeightWindowResidueSum f T +
          explicitFormulaRectangle_completedPoleResidueSum f := by
      exact congrArg
        (fun z : ℂ => explicitFormulaCompletedZeroHeightWindowResidueSum f T + z)
        hpoles
    _ = explicitFormulaRectangle_poleCorrectedResidueSum f T := by
      exact (explicitFormulaRectangle_poleCorrectedResidueSum_eq f T).symm

/-- Full tangent contour residue accounting: once the tangent outer rectangle contour has
the completed-zero plus pole residue sum, and the tangent pole boundary contributes exactly
the pole residue sum, the full tangent pole-corrected contour has the completed-zero
residue window. -/
theorem explicitFormulaRectangle_fullTangentPoleCorrectedContourIntegral_eq_heightWindowResidueSum_of_tangentContour_poleCorrectedResidueSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hcontour :
      zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) =
        explicitFormulaRectangle_poleCorrectedResidueSum f T)
    (hpoles :
      explicitFormulaRectangle_completedPoleTangentBoundaryContribution f F T =
        explicitFormulaRectangle_completedPoleResidueSum f) :
    explicitFormulaRectangle_fullTangentPoleCorrectedContourIntegral f F T =
      explicitFormulaCompletedZeroHeightWindowResidueSum f T := by
  let C : ℂ := zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T)
  let P : ℂ := explicitFormulaRectangle_completedPoleTangentBoundaryContribution f F T
  let Z : ℂ := explicitFormulaCompletedZeroHeightWindowResidueSum f T
  let R : ℂ := explicitFormulaRectangle_completedPoleResidueSum f
  have hsum : explicitFormulaRectangle_poleCorrectedResidueSum f T = Z + R := by
    exact explicitFormulaRectangle_poleCorrectedResidueSum_eq f T
  calc
    explicitFormulaRectangle_fullTangentPoleCorrectedContourIntegral f F T = C - P := by
      rfl
    _ = explicitFormulaRectangle_poleCorrectedResidueSum f T - P := by
      exact congrArg (fun x : ℂ => x - P) hcontour
    _ = (Z + R) - P := by
      exact congrArg (fun x : ℂ => x - P) hsum
    _ = (Z + R) - R := by
      exact congrArg (fun x : ℂ => (Z + R) - x) hpoles
    _ = Z := by
      exact add_sub_cancel_right Z R

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
