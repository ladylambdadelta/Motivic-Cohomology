import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part07

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

/-- The indexed zero-window deleted disks are the same finite union as the coordinate
carrier deleted disks. -/
theorem explicitFormulaCompletedZeroWindowDeletedDisks_eq_coordinateDeletedDisks
    (T ε : ℝ) :
    explicitFormulaCompletedZeroWindowDeletedDisks T ε =
      finiteRectangleDeletedDisks (explicitFormulaCompletedZeroWindowCoordinates T) ε := by
  apply Set.ext
  intro z
  apply Iff.intro
  · intro hz
    exact
      Exists.elim hz
        (fun ρ hρ =>
          finiteRectangleDeletedDisks_mem_of_mem_ball
            (explicitFormulaCompletedZeroWindowCoordinates T)
            ε
            (explicitFormulaCompletedZeroWindowCoordinates_mem_of_mem_window T hρ.left)
            hρ.right)
  · intro hz
    exact
      Exists.elim hz
        (fun a ha =>
          Exists.elim
            (explicitFormulaCompletedZeroWindowCoordinates_exists_window_of_mem T ha.left)
            (fun ρ hρ =>
              Exists.intro ρ
                (And.intro hρ.left
                  (Eq.subst
                    (motive := fun w : ℂ => z ∈ Metric.ball w ε)
                    hρ.right.symm
                    ha.right))))

/-- A point in the punctured rectangle lies in the original rectangle domain. -/
theorem finiteRectanglePuncturedDomain_mem_base
    (R : Set ℂ) (S : Finset ℂ) (ε : ℝ) {z : ℂ}
    (hz : z ∈ finiteRectanglePuncturedDomain R S ε) :
    z ∈ R :=
  hz.left

/-- A point in the punctured rectangle lies outside the finite deleted-disk union. -/
theorem finiteRectanglePuncturedDomain_not_mem_deletedDisks
    (R : Set ℂ) (S : Finset ℂ) (ε : ℝ) {z : ℂ}
    (hz : z ∈ finiteRectanglePuncturedDomain R S ε) :
    z ∉ finiteRectangleDeletedDisks S ε :=
  hz.right

/-- A point in the punctured rectangle avoids every deleted disk centered at a listed
singular coordinate. -/
theorem finiteRectanglePuncturedDomain_not_mem_deletedBall
    (R : Set ℂ) (S : Finset ℂ) (ε : ℝ) {a z : ℂ}
    (hz : z ∈ finiteRectanglePuncturedDomain R S ε) (ha : a ∈ S) :
    z ∉ Metric.ball a ε :=
  fun hball =>
    finiteRectanglePuncturedDomain_not_mem_deletedDisks R S ε hz
      (finiteRectangleDeletedDisks_mem_of_mem_ball S ε ha hball)

/-- A point in the indexed punctured rectangle lies in the original rectangle domain. -/
theorem finiteRectangleIndexedPuncturedDomain_mem_base
    {α : Type*} (R : Set ℂ) (S : Finset α) (center : α → ℂ) (ε : ℝ) {z : ℂ}
    (hz : z ∈ finiteRectangleIndexedPuncturedDomain R S center ε) :
    z ∈ R :=
  hz.left

/-- A point in the indexed punctured rectangle lies outside the indexed finite deleted-disk
union. -/
theorem finiteRectangleIndexedPuncturedDomain_not_mem_deletedDisks
    {α : Type*} (R : Set ℂ) (S : Finset α) (center : α → ℂ) (ε : ℝ) {z : ℂ}
    (hz : z ∈ finiteRectangleIndexedPuncturedDomain R S center ε) :
    z ∉ finiteRectangleIndexedDeletedDisks S center ε :=
  hz.right

/-- A point in the indexed punctured rectangle avoids every indexed deleted disk centered
at a listed singular coordinate. -/
theorem finiteRectangleIndexedPuncturedDomain_not_mem_deletedBall
    {α : Type*} (R : Set ℂ) (S : Finset α) (center : α → ℂ) (ε : ℝ)
    {a : α} {z : ℂ}
    (hz : z ∈ finiteRectangleIndexedPuncturedDomain R S center ε) (ha : a ∈ S) :
    z ∉ Metric.ball (center a) ε :=
  fun hball =>
    finiteRectangleIndexedPuncturedDomain_not_mem_deletedDisks R S center ε hz
      (finiteRectangleIndexedDeletedDisks_mem_of_mem_ball S center ε ha hball)

/-- The completed-zero-window punctured interior can be read either from the indexed
zero-window carrier or from the finite coordinate carrier. -/
theorem explicitFormulaCompletedZeroWindowPuncturedInterior_eq_coordinatePuncturedDomain
    (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    explicitFormulaCompletedZeroWindowPuncturedInterior F T ε =
      finiteRectanglePuncturedDomain
        (explicitFormulaContourFamilyInterior F T)
        (explicitFormulaCompletedZeroWindowCoordinates T)
        ε := by
  apply Set.ext
  intro z
  apply Iff.intro
  · intro hz
    exact
      And.intro hz.left
        (fun hdeleted =>
          hz.right
            (Eq.subst
              (motive := fun S : Set ℂ => z ∈ S)
              (explicitFormulaCompletedZeroWindowDeletedDisks_eq_coordinateDeletedDisks T ε).symm
              hdeleted))
  · intro hz
    exact
      And.intro hz.left
        (fun hdeleted =>
          hz.right
            (Eq.subst
              (motive := fun S : Set ℂ => z ∈ S)
              (explicitFormulaCompletedZeroWindowDeletedDisks_eq_coordinateDeletedDisks T ε)
              hdeleted))

/-- Each coordinate in the finite completed-zero carrier is an interior singular coordinate
under the zero-window/interior-singular identification hypothesis. -/
theorem explicitFormulaCompletedZeroWindowCoordinates_mem_interiorSingular_of_hinterior
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    {z : ℂ}
    (hz : z ∈ explicitFormulaCompletedZeroWindowCoordinates T) :
    z ∈ explicitFormulaContourFamilyInterior F T ∧
      z ∈ completedZetaContourIntegrandSingularSet := by
  exact
    Exists.elim
      (explicitFormulaCompletedZeroWindowCoordinates_exists_window_of_mem T hz)
      (fun ρ hρ =>
        Eq.subst
          (motive := fun w : ℂ =>
            w ∈ explicitFormulaContourFamilyInterior F T ∧
              w ∈ completedZetaContourIntegrandSingularSet)
          hρ.right
          ((hinterior ρ).mp hρ.left))

/-- A non-pole interior singular coordinate belongs to the finite completed-zero coordinate
carrier.  The two completed-zeta pole coordinates remain separate from this carrier. -/
theorem explicitFormulaCompletedZeroWindowCoordinates_mem_of_interiorSingular_nonPole
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    {z : ℂ}
    (hzInterior : z ∈ explicitFormulaContourFamilyInterior F T)
    (hzSingular : z ∈ completedZetaContourIntegrandSingularSet)
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    z ∈ explicitFormulaCompletedZeroWindowCoordinates T := by
  let hzeta : completedRiemannZeta z = 0 :=
    explicitFormulaRectangleContourIntegrand_interiorSingular_zeroCase
      F T hzInterior hzSingular hz0 hz1
  let ρ : {ρ : ℂ // ZetaCompletedZero ρ} :=
    explicitFormulaCompletedZeroOfContourZero z hz0 hz1 hzeta
  have hρWindow :
      ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T :=
    explicitFormulaRectangle_interiorSingular_nonPole_completedZero_mem_window
      F T hinterior hzInterior hzSingular hz0 hz1
  have hcoord : completedZeroResidueCoordinate ρ = z :=
    explicitFormulaCompletedZeroOfContourZero_residueCoordinate z hz0 hz1 hzeta
  exact
    Eq.subst
      (motive := fun w : ℂ => w ∈ explicitFormulaCompletedZeroWindowCoordinates T)
      hcoord
      (explicitFormulaCompletedZeroWindowCoordinates_mem_of_mem_window T hρWindow)

/-- Every interior singular coordinate of the raw completed contour integrand belongs to
the finite raw singular-coordinate carrier. -/
theorem explicitFormulaRectangleRawSingularCoordinates_mem_of_interiorSingular
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    {z : ℂ}
    (hzInterior : z ∈ explicitFormulaContourFamilyInterior F T)
    (hzSingular : z ∈ completedZetaContourIntegrandSingularSet) :
    z ∈ explicitFormulaRectangleRawSingularCoordinates T := by
  match explicitFormulaRectangleContourIntegrand_interiorSingular_cases
      F T hzInterior hzSingular with
  | Or.inl hzero =>
      exact
        Eq.subst
          (motive := fun w : ℂ => w ∈ explicitFormulaRectangleRawSingularCoordinates T)
          hzero.symm
          (explicitFormulaRectangleRawSingularCoordinates_zero_mem T)
  | Or.inr (Or.inl hone) =>
      exact
        Eq.subst
          (motive := fun w : ℂ => w ∈ explicitFormulaRectangleRawSingularCoordinates T)
          hone.symm
          (explicitFormulaRectangleRawSingularCoordinates_one_mem T)
  | Or.inr (Or.inr hzeroData) =>
      exact
        Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem
            (explicitFormulaCompletedZeroWindowCoordinates_mem_of_interiorSingular_nonPole
              F T hinterior hzInterior hzSingular hzeroData.1 hzeroData.2.1))

/-- At positive height, every point of the raw singular-coordinate carrier is an interior
singular coordinate of the raw completed contour integrand. -/
theorem explicitFormulaRectangleRawSingularCoordinates_mem_interiorSingular_of_mem
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    {z : ℂ}
    (hz : z ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    z ∈ explicitFormulaContourFamilyInterior F T ∧
      z ∈ completedZetaContourIntegrandSingularSet := by
  match Finset.mem_insert.mp hz with
  | Or.inl hzero =>
      exact
        Eq.subst
          (motive := fun w : ℂ =>
            w ∈ explicitFormulaContourFamilyInterior F T ∧
              w ∈ completedZetaContourIntegrandSingularSet)
          hzero.symm
          (And.intro
            (explicitFormulaRectangle_zeroPole_mem_interior_of_pos_height F hT)
            explicitFormulaRectangle_zeroPole_mem_singularSet)
  | Or.inr hrest =>
      match Finset.mem_insert.mp hrest with
      | Or.inl hone =>
          exact
            Eq.subst
              (motive := fun w : ℂ =>
                w ∈ explicitFormulaContourFamilyInterior F T ∧
                  w ∈ completedZetaContourIntegrandSingularSet)
              hone.symm
              (And.intro
                (explicitFormulaRectangle_onePole_mem_interior_of_pos_height F hT)
                explicitFormulaRectangle_onePole_mem_singularSet)
      | Or.inr hzeroCoord =>
          exact
            explicitFormulaCompletedZeroWindowCoordinates_mem_interiorSingular_of_hinterior
              F T hinterior hzeroCoord

/-- At positive height, the raw singular-coordinate carrier is exactly the finite interior
singular set of the raw completed contour integrand. -/
theorem explicitFormulaRectangleRawSingularCoordinates_mem_iff_interiorSingular
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    {z : ℂ} :
    z ∈ explicitFormulaRectangleRawSingularCoordinates T ↔
      z ∈ explicitFormulaContourFamilyInterior F T ∧
        z ∈ completedZetaContourIntegrandSingularSet :=
  Iff.intro
    (fun hz =>
      explicitFormulaRectangleRawSingularCoordinates_mem_interiorSingular_of_mem
        F hT hinterior hz)
    (fun hz =>
      explicitFormulaRectangleRawSingularCoordinates_mem_of_interiorSingular
        F T hinterior hz.left hz.right)

/-- At positive height, every raw singular coordinate has a small ball contained in the
open contour-family interior. -/
theorem explicitFormulaRectangleRawSingularCoordinates_localInterior_ball
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    {z : ℂ}
    (hz : z ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball z r ⊆ explicitFormulaContourFamilyInterior F T := by
  exact
    explicitFormulaContourFamilyInterior_exists_ball_subset
      F T
      ((explicitFormulaRectangleRawSingularCoordinates_mem_iff_interiorSingular
        F hT hinterior).mp hz).left

/-- An interior point that is not in the raw finite singular-coordinate carrier is not a
completed contour-integrand singularity. -/
theorem explicitFormulaRectangleInterior_not_mem_singularSet_of_not_mem_rawSingularCoordinates
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    {z : ℂ}
    (hzInterior : z ∈ explicitFormulaContourFamilyInterior F T)
    (hzRaw : z ∉ explicitFormulaRectangleRawSingularCoordinates T) :
    z ∉ completedZetaContourIntegrandSingularSet := by
  intro hzSingular
  exact hzRaw
    ((explicitFormulaRectangleRawSingularCoordinates_mem_iff_interiorSingular
      F hT hinterior).mpr
      (And.intro hzInterior hzSingular))

/-- A point of the raw finite-singularity punctured interior is off the completed contour
integrand singular set. -/
theorem explicitFormulaRectangleRawPuncturedInterior_not_mem_singularSet
    (F : ExplicitFormulaContourFamily) {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    {z : ℂ}
    (hz :
      z ∈ finiteRectanglePuncturedDomain
        (explicitFormulaContourFamilyInterior F T)
        (explicitFormulaRectangleRawSingularCoordinates T)
        ε) :
    z ∉ completedZetaContourIntegrandSingularSet := by
  intro hzSingular
  have hzCarrier :
      z ∈ explicitFormulaRectangleRawSingularCoordinates T :=
    (explicitFormulaRectangleRawSingularCoordinates_mem_iff_interiorSingular
      F hT hinterior).mpr
      (And.intro
        (finiteRectanglePuncturedDomain_mem_base
          (explicitFormulaContourFamilyInterior F T)
          (explicitFormulaRectangleRawSingularCoordinates T)
          ε
          hz)
        hzSingular)
  have hzBall : z ∈ Metric.ball z ε :=
    Metric.mem_ball_self hε
  exact
    finiteRectanglePuncturedDomain_not_mem_deletedBall
      (explicitFormulaContourFamilyInterior F T)
      (explicitFormulaRectangleRawSingularCoordinates T)
      ε
      hz
      hzCarrier
      hzBall

/-- On a deleted disk around one raw singular coordinate, pairwise disjoint raw deleted
disks exclude every other raw singularity.  Since the raw carrier is exactly the interior
singular set at positive height, every off-center point in that disk is regular for the raw
completed contour integrand. -/
theorem explicitFormulaRectangle_deletedBall_not_mem_singularSet_of_rawDisjoint
    (F : ExplicitFormulaContourFamily) {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hball :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.ball a ε ⊆ explicitFormulaContourFamilyInterior F T)
    (hdisjoint :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b →
                Disjoint (Metric.ball a ε) (Metric.ball b ε))
    {a z : ℂ}
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (hz : z ∈ Metric.ball a ε \ {a}) :
    z ∉ completedZetaContourIntegrandSingularSet := by
  intro hzSingular
  have hzInterior : z ∈ explicitFormulaContourFamilyInterior F T :=
    hball a ha hz.1
  have hzCarrier : z ∈ explicitFormulaRectangleRawSingularCoordinates T :=
    (explicitFormulaRectangleRawSingularCoordinates_mem_iff_interiorSingular
      F hT hinterior).mpr (And.intro hzInterior hzSingular)
  have hza : z ≠ a := by
    intro hza_eq
    exact hz.2 hza_eq
  have haz : a ≠ z := fun haz_eq => hza haz_eq.symm
  have hzSelf : z ∈ Metric.ball z ε :=
    Metric.mem_ball_self hε
  exact
    Set.disjoint_left.mp
      (hdisjoint a ha z hzCarrier haz)
      hz.1
      hzSelf

/-- On a closed deleted disk around one raw singular coordinate, strict pairwise closed-disk
separation excludes every other raw singularity.  This is the closed-radius analogue needed
for deleted-circle coefficient continuity. -/
theorem explicitFormulaRectangle_deletedClosedBall_not_mem_singularSet_of_rawClosedDisjoint
    (F : ExplicitFormulaContourFamily) {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hclosedBall :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    (hclosedDisjoint :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b →
                Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
    {a z : ℂ}
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (hz : z ∈ Metric.closedBall a ε \ {a}) :
    z ∉ completedZetaContourIntegrandSingularSet := by
  intro hzSingular
  have hzInterior : z ∈ explicitFormulaContourFamilyInterior F T :=
    hclosedBall a ha hz.1
  have hzCarrier : z ∈ explicitFormulaRectangleRawSingularCoordinates T :=
    (explicitFormulaRectangleRawSingularCoordinates_mem_iff_interiorSingular
      F hT hinterior).mpr (And.intro hzInterior hzSingular)
  have hza : z ≠ a := by
    intro hza_eq
    exact hz.2 hza_eq
  have haz : a ≠ z := fun haz_eq => hza haz_eq.symm
  have hzSelf : z ∈ Metric.closedBall z ε :=
    Metric.mem_closedBall_self hε.le
  exact
    Set.disjoint_left.mp
      (hclosedDisjoint a ha z hzCarrier haz)
      hz.1
      hzSelf

/-- Under closed-radius controls for the raw singular carrier, the local residue coefficient
at a listed raw singular coordinate is continuous on the closed deleted disk and
differentiable on the open deleted disk away from any chosen countable exceptional set. -/
theorem explicitFormulaRectangle_rawDeletedClosedBall_localResidueCoefficient_regular
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hclosedBall :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    (hclosedDisjoint :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b →
                Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
    (a : ℂ) (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (s : Set ℂ) :
    ContinuousOn
        (fun z : ℂ => (z - a) * zetaCompletedExplicitFormulaContourIntegrand f z)
        (Metric.closedBall a ε \ {a}) ∧
      (∀ z : ℂ,
        z ∈ (Metric.ball a ε \ {a}) \ s →
          DifferentiableAt ℂ
            (fun w : ℂ => (w - a) * zetaCompletedExplicitFormulaContourIntegrand f w)
            z) := by
  have hregular :
      ContinuousOn
          (fun z : ℂ => (z - a) * zetaCompletedExplicitFormulaContourIntegrand f z)
          (Metric.closedBall a ε \ {a}) ∧
        (∀ z : ℂ,
          z ∈ (Metric.closedBall a ε \ {a}) \ s →
            DifferentiableAt ℂ
              (fun w : ℂ => (w - a) * zetaCompletedExplicitFormulaContourIntegrand f w)
              z) :=
    explicitFormulaRectangle_localResidueCoefficient_regularOn_of_deletedDisk_avoids_singular
      f F h T a
      (Metric.closedBall a ε \ {a})
      s
      (fun z hz => hclosedBall a ha hz.1)
      (fun z hz =>
        explicitFormulaRectangle_deletedClosedBall_not_mem_singularSet_of_rawClosedDisjoint
          F hT hε hinterior hclosedBall hclosedDisjoint ha hz)
  exact And.intro
    hregular.1
    (fun z hz =>
      hregular.2 z
        (And.intro
          (And.intro
            (Metric.ball_subset_closedBall hz.1.1)
            hz.1.2)
          hz.2))

/-- Closed-radius regularity input for the deleted-circle theorem at the completed-zeta pole
coordinate `0`. -/
theorem explicitFormulaRectangle_zeroPole_rawDeletedCircle_regular_of_closedRadiusGeometry
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hgeometry :
      (∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) ∧
      (∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b →
                Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε)))
    (s : Set ℂ) :
    ContinuousOn
        (fun z : ℂ => z * zetaCompletedExplicitFormulaContourIntegrand f z)
        (Metric.closedBall (0 : ℂ) ε \ {(0 : ℂ)}) ∧
      (∀ z : ℂ,
        z ∈ (Metric.ball (0 : ℂ) ε \ {(0 : ℂ)}) \ s →
          DifferentiableAt ℂ
            (fun w : ℂ => w * zetaCompletedExplicitFormulaContourIntegrand f w)
            z) := by
  have hraw :
      ContinuousOn
          (fun z : ℂ => (z - (0 : ℂ)) * zetaCompletedExplicitFormulaContourIntegrand f z)
          (Metric.closedBall (0 : ℂ) ε \ {(0 : ℂ)}) ∧
        (∀ z : ℂ,
          z ∈ (Metric.ball (0 : ℂ) ε \ {(0 : ℂ)}) \ s →
            DifferentiableAt ℂ
              (fun w : ℂ => (w - (0 : ℂ)) *
                zetaCompletedExplicitFormulaContourIntegrand f w)
              z) :=
    explicitFormulaRectangle_rawDeletedClosedBall_localResidueCoefficient_regular
      f F h hT hε hinterior hgeometry.1 hgeometry.2
      (0 : ℂ) (explicitFormulaRectangleRawSingularCoordinates_zero_mem T) s
  have hcoeff :
      (fun z : ℂ => (z - (0 : ℂ)) * zetaCompletedExplicitFormulaContourIntegrand f z) =
        fun z : ℂ => z * zetaCompletedExplicitFormulaContourIntegrand f z := by
    funext z
    exact congrArg
      (fun x : ℂ => x * zetaCompletedExplicitFormulaContourIntegrand f z)
      (sub_zero z)
  exact And.intro
    (Eq.subst
      (motive := fun φ : ℂ → ℂ =>
        ContinuousOn φ (Metric.closedBall (0 : ℂ) ε \ {(0 : ℂ)}))
      hcoeff
      hraw.1)
    (fun z hz =>
      Eq.subst
        (motive := fun φ : ℂ → ℂ => DifferentiableAt ℂ φ z)
        hcoeff
        (hraw.2 z hz))

/-- Closed-radius regularity input for the deleted-circle theorem at the completed-zeta pole
coordinate `1`. -/
theorem explicitFormulaRectangle_onePole_rawDeletedCircle_regular_of_closedRadiusGeometry
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hgeometry :
      (∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) ∧
      (∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b →
                Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε)))
    (s : Set ℂ) :
    ContinuousOn
        (fun z : ℂ => (z - 1) * zetaCompletedExplicitFormulaContourIntegrand f z)
        (Metric.closedBall (1 : ℂ) ε \ {(1 : ℂ)}) ∧
      (∀ z : ℂ,
        z ∈ (Metric.ball (1 : ℂ) ε \ {(1 : ℂ)}) \ s →
          DifferentiableAt ℂ
            (fun w : ℂ => (w - 1) * zetaCompletedExplicitFormulaContourIntegrand f w)
            z) :=
  explicitFormulaRectangle_rawDeletedClosedBall_localResidueCoefficient_regular
    f F h hT hε hinterior hgeometry.1 hgeometry.2
    (1 : ℂ) (explicitFormulaRectangleRawSingularCoordinates_one_mem T) s

/-- Closed-radius regularity input for the deleted-circle theorem at a completed-zero
coordinate in the finite height window. -/
theorem explicitFormulaRectangle_completedZero_rawDeletedCircle_regular_of_closedRadiusGeometry
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hgeometry :
      (∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) ∧
      (∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b →
                Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε)))
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hρ : ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T)
    (s : Set ℂ) :
    ContinuousOn
        (fun z : ℂ =>
          (z - completedZeroResidueCoordinate ρ) *
            zetaCompletedExplicitFormulaContourIntegrand f z)
        (Metric.closedBall (completedZeroResidueCoordinate ρ) ε \
          {completedZeroResidueCoordinate ρ}) ∧
      (∀ z : ℂ,
        z ∈ (Metric.ball (completedZeroResidueCoordinate ρ) ε \
            {completedZeroResidueCoordinate ρ}) \ s →
          DifferentiableAt ℂ
            (fun w : ℂ =>
              (w - completedZeroResidueCoordinate ρ) *
                zetaCompletedExplicitFormulaContourIntegrand f w)
            z) :=
  explicitFormulaRectangle_rawDeletedClosedBall_localResidueCoefficient_regular
    f F h hT hε hinterior hgeometry.1 hgeometry.2
    (completedZeroResidueCoordinate ρ)
    (explicitFormulaRectangleRawSingularCoordinates_completedZero_mem T hρ)
    s

/-- The completed contour integrand is differentiable at every point of the raw
finite-singularity punctured interior. -/
theorem explicitFormulaRectangleRawPuncturedInterior_differentiableAt
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    {z : ℂ}
    (hz :
      z ∈ finiteRectanglePuncturedDomain
        (explicitFormulaContourFamilyInterior F T)
        (explicitFormulaRectangleRawSingularCoordinates T)
        ε) :
    DifferentiableAt ℂ
      (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z := by
  exact
    completedZetaContourIntegrand_differentiableAt_off_singularSet
      (f := f)
      h.phi_control
      (explicitFormulaRectangleRawPuncturedInterior_not_mem_singularSet
        F hT hε hinterior hz)

/-- The completed contour integrand is continuous at every point of the raw
finite-singularity punctured interior. -/
theorem explicitFormulaRectangleRawPuncturedInterior_continuousAt
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    {z : ℂ}
    (hz :
      z ∈ finiteRectanglePuncturedDomain
        (explicitFormulaContourFamilyInterior F T)
        (explicitFormulaRectangleRawSingularCoordinates T)
        ε) :
    ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z := by
  exact
    completedZetaContourIntegrand_continuousAt_off_singularSet
      h.phi_control
      (explicitFormulaRectangleRawPuncturedInterior_not_mem_singularSet
        F hT hε hinterior hz)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
