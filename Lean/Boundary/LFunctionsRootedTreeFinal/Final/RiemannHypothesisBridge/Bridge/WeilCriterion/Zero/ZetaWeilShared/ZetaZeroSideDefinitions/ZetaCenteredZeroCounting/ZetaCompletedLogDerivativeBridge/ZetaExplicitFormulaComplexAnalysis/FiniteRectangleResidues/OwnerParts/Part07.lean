import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part06

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

/-- The contour-family interior with disks around the completed-zero height-window
coordinates deleted. -/
def explicitFormulaCompletedZeroWindowPuncturedInterior
    (F : ExplicitFormulaContourFamily) (T ε : ℝ) : Set ℂ :=
  finiteRectangleIndexedPuncturedDomain
    (explicitFormulaContourFamilyInterior F T)
    (explicitFormulaCompletedZeroHeightWindow T)
    (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} => completedZeroResidueCoordinate ρ)
    ε

/-- Membership in one deleted disk gives membership in the finite deleted-disk union. -/
theorem finiteRectangleDeletedDisks_mem_of_mem_ball
    (S : Finset ℂ) (ε : ℝ) {a z : ℂ}
    (ha : a ∈ S) (hz : z ∈ Metric.ball a ε) :
    z ∈ finiteRectangleDeletedDisks S ε :=
  Exists.intro a (And.intro ha hz)

/-- A deleted disk centered at a listed singular coordinate is contained in the finite
deleted-disk union. -/
theorem finiteRectangleDeletedDisks_ball_subset
    (S : Finset ℂ) (ε : ℝ) {a : ℂ} (ha : a ∈ S) :
    Metric.ball a ε ⊆ finiteRectangleDeletedDisks S ε :=
  fun _z hz => finiteRectangleDeletedDisks_mem_of_mem_ball S ε ha hz

/-- If every deleted disk around a finite singular coordinate lies in a base domain, then
the whole finite deleted-disk union lies in that domain. -/
theorem finiteRectangleDeletedDisks_subset_of_forall_ball_subset
    (R : Set ℂ) (S : Finset ℂ) (ε : ℝ)
    (hball : ∀ a : ℂ, a ∈ S → Metric.ball a ε ⊆ R) :
    finiteRectangleDeletedDisks S ε ⊆ R :=
  fun _z hz =>
    Exists.elim hz
      (fun a ha => hball a ha.left ha.right)

/-- A finite set of points with individual positive ball neighborhoods inside a domain has
one positive radius working for every point in the set. -/
theorem finiteRectangle_exists_uniform_ball_subset_of_finite
    (R : Set ℂ) (S : Finset ℂ)
    (hlocal :
      ∀ a : ℂ, a ∈ S → ∃ r : ℝ, 0 < r ∧ Metric.ball a r ⊆ R) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a : ℂ, a ∈ S → Metric.ball a ε ⊆ R := by
  exact
    Finset.induction_on S
      (fun _hlocal_empty =>
        Exists.intro (1 : ℝ)
          (And.intro zero_lt_one
            (fun a ha => False.elim (Finset.not_mem_empty a ha))))
      (fun a S ha ih hlocal_insert =>
        have hlocal_a : ∃ r : ℝ, 0 < r ∧ Metric.ball a r ⊆ R :=
          hlocal_insert a (Finset.mem_insert_self a S)
        have hlocal_S :
            ∀ b : ℂ, b ∈ S → ∃ r : ℝ, 0 < r ∧ Metric.ball b r ⊆ R :=
          fun b hb => hlocal_insert b (Finset.mem_insert_of_mem hb)
        match hlocal_a with
        | ⟨ra, hra_pos, hra_subset⟩ =>
            match ih hlocal_S with
            | ⟨εS, hεS_pos, hεS_subset⟩ =>
                let ε : ℝ := min ra εS
                have hε_pos : 0 < ε :=
                  lt_min hra_pos hεS_pos
                have hε_le_ra : ε ≤ ra :=
                  min_le_left ra εS
                have hε_le_εS : ε ≤ εS :=
                  min_le_right ra εS
                Exists.intro ε
                  (And.intro hε_pos
                    (fun b hb =>
                      match Finset.mem_insert.mp hb with
                      | Or.inl hba =>
                          Eq.subst
                            (motive := fun x : ℂ => Metric.ball x ε ⊆ R)
                            hba.symm
                            (Set.Subset.trans (Metric.ball_subset_ball hε_le_ra) hra_subset)
                      | Or.inr hbS =>
                          Set.Subset.trans
                            (Metric.ball_subset_ball hε_le_εS)
                            (hεS_subset b hbS))))
      hlocal

/-- If a positive radius is at most half the distance between any two distinct points in a
finite carrier, then the corresponding open balls are pairwise disjoint. -/
theorem finiteRectangle_pairwiseDisjoint_balls_of_two_mul_le_dist
    (S : Finset ℂ) (ε : ℝ)
    (hsep :
      ∀ a : ℂ, a ∈ S → ∀ b : ℂ, b ∈ S → a ≠ b →
        ε + ε ≤ dist a b) :
    ∀ a : ℂ, a ∈ S → ∀ b : ℂ, b ∈ S → a ≠ b →
      Disjoint (Metric.ball a ε) (Metric.ball b ε) := by
  intro a ha b hb hab
  exact Metric.ball_disjoint_ball (hsep a ha b hb hab)

/-- If a positive radius has strict doubled margin below the distance between
any two distinct carrier points, then the corresponding closed balls are
pairwise disjoint. -/
theorem finiteRectangle_pairwiseDisjoint_closedBalls_of_two_mul_lt_dist
    (S : Finset ℂ) (ε : ℝ)
    (hsep :
      ∀ a : ℂ, a ∈ S → ∀ b : ℂ, b ∈ S → a ≠ b →
        ε + ε < dist a b) :
    ∀ a : ℂ, a ∈ S → ∀ b : ℂ, b ∈ S → a ≠ b →
      Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε) := by
  intro a ha b hb hab
  exact Metric.closedBall_disjoint_closedBall (hsep a ha b hb hab)

/-- A finite family of positive real bounds admits one positive number smaller
than all of them. -/
theorem finiteRectangle_exists_uniform_pos_lt_of_finite
    {α : Type*} [DecidableEq α] (S : Finset α) (d : α → ℝ)
    (hpos : ∀ a : α, a ∈ S → 0 < d a) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a : α, a ∈ S → ε < d a := by
  exact
    Finset.induction_on S
      (fun _hpos_empty =>
        Exists.intro (1 : ℝ)
          (And.intro zero_lt_one
            (fun a ha => False.elim (Finset.not_mem_empty a ha))))
      (fun a S ha ih hpos_insert =>
        have ha_pos : 0 < d a :=
          hpos_insert a (Finset.mem_insert_self a S)
        have hS_pos : ∀ b : α, b ∈ S → 0 < d b :=
          fun b hb => hpos_insert b (Finset.mem_insert_of_mem hb)
        match ih hS_pos with
        | ⟨δ, hδ_pos, hδ_lt⟩ =>
            let ε : ℝ := min (d a / 2) δ
            have hhalf_pos : 0 < d a / 2 :=
              half_pos ha_pos
            have hε_pos : 0 < ε :=
              lt_min hhalf_pos hδ_pos
            have hε_lt_da : ε < d a := by
              have hε_le_half : ε ≤ d a / 2 :=
                min_le_left (d a / 2) δ
              have hhalf_lt : d a / 2 < d a := by
                calc
                  d a / 2 < d a / 1 := by
                    exact div_lt_div_of_pos_left ha_pos zero_lt_one one_lt_two
                  _ = d a := by
                    exact div_one (d a)
              exact lt_of_le_of_lt hε_le_half hhalf_lt
            have hε_le_δ : ε ≤ δ :=
              min_le_right (d a / 2) δ
            Exists.intro ε
              (And.intro hε_pos
                (fun b hb =>
                  match Finset.mem_insert.mp hb with
                  | Or.inl hba =>
                      Eq.subst
                        (motive := fun x : α => ε < d x)
                        hba.symm
                        hε_lt_da
                  | Or.inr hbS =>
                      lt_of_le_of_lt hε_le_δ (hδ_lt b hbS))))
      hpos

/-- Every finite set of complex points admits one positive radius whose doubled
radius is strictly smaller than the distance between any two distinct listed
points. -/
theorem finiteRectangle_exists_uniform_strict_pairwise_radius
    (S : Finset ℂ) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ a : ℂ, a ∈ S → ∀ b : ℂ, b ∈ S → a ≠ b →
        ε + ε < dist a b := by
  let P : Finset (ℂ × ℂ) := S.product S
  let d : ℂ × ℂ → ℝ := fun p : ℂ × ℂ =>
    if p.1 = p.2 then (1 : ℝ) else dist p.1 p.2 / 2
  have hd_pos : ∀ p : ℂ × ℂ, p ∈ P → 0 < d p := by
    intro p _hp
    by_cases hp_eq : p.1 = p.2
    · exact Eq.subst
        (motive := fun r : ℝ => 0 < r)
        (if_pos hp_eq).symm
        zero_lt_one
    · have hdist_pos : 0 < dist p.1 p.2 :=
        dist_pos.mpr hp_eq
      exact Eq.subst
        (motive := fun r : ℝ => 0 < r)
        (if_neg hp_eq).symm
        (half_pos hdist_pos)
  match finiteRectangle_exists_uniform_pos_lt_of_finite P d hd_pos with
  | ⟨ε, hε_pos, hε_lt⟩ =>
      exact Exists.intro ε
        (And.intro hε_pos
          (fun a ha b hb hab =>
            let p : ℂ × ℂ := (a, b)
            have hp : p ∈ P :=
              Finset.mem_product.mpr (And.intro ha hb)
            have hp_ne : p.1 ≠ p.2 :=
              hab
            have hε_lt_half : ε < dist a b / 2 := by
              have hraw : ε < d p :=
                hε_lt p hp
              exact Eq.subst
                (motive := fun r : ℝ => ε < r)
                (if_neg hp_ne)
                hraw
            calc
              ε + ε < dist a b / 2 + dist a b / 2 :=
                add_lt_add hε_lt_half hε_lt_half
              _ = dist a b := by
                calc
                  dist a b / 2 + dist a b / 2 =
                      ((1 / 2 : ℝ) + (1 / 2 : ℝ)) * dist a b := by
                    have hleft : dist a b / 2 = (1 / 2 : ℝ) * dist a b := by
                      calc
                        dist a b / 2 = dist a b * (2 : ℝ)⁻¹ := by
                          exact div_eq_mul_inv (dist a b) 2
                        _ = (2 : ℝ)⁻¹ * dist a b := by
                          exact mul_comm (dist a b) (2 : ℝ)⁻¹
                        _ = (1 / 2 : ℝ) * dist a b := by
                          exact congrArg (fun r : ℝ => r * dist a b) (one_div 2).symm
                    calc
                      dist a b / 2 + dist a b / 2 =
                          (1 / 2 : ℝ) * dist a b + (1 / 2 : ℝ) * dist a b := by
                        exact congrArg₂ Add.add hleft hleft
                      _ = ((1 / 2 : ℝ) + (1 / 2 : ℝ)) * dist a b := by
                        exact (add_mul (1 / 2 : ℝ) (1 / 2 : ℝ) (dist a b)).symm
                  _ = 1 * dist a b := by
                    exact congrArg (fun r : ℝ => r * dist a b)
                      (show (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 by
                        exact add_halves 1)
                  _ = dist a b := by
                    exact one_mul (dist a b)))

/-- The raw deleted disks lie in the contour-family interior once each raw singular
coordinate has its deleted disk contained in that interior. -/
theorem explicitFormulaRectangleRawDeletedDisks_subset_interior_of_forall_ball_subset
    (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (hball :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.ball a ε ⊆ explicitFormulaContourFamilyInterior F T) :
    finiteRectangleDeletedDisks
        (explicitFormulaRectangleRawSingularCoordinates T) ε ⊆
      explicitFormulaContourFamilyInterior F T := by
  exact
    finiteRectangleDeletedDisks_subset_of_forall_ball_subset
      (explicitFormulaContourFamilyInterior F T)
      (explicitFormulaRectangleRawSingularCoordinates T)
      ε
      hball

/-- A finite raw singular-coordinate carrier admits one positive radius whose disks all lie
in the rectangle interior, once each raw singular coordinate has some local interior disk.
This is the finite-selection part of the punctured-rectangle radius construction. -/
theorem explicitFormulaRectangleRawSingularCoordinates_exists_uniform_ball_subset_interior
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hlocal :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∃ r : ℝ, 0 < r ∧ Metric.ball a r ⊆ explicitFormulaContourFamilyInterior F T) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            Metric.ball a ε ⊆ explicitFormulaContourFamilyInterior F T := by
  exact
    finiteRectangle_exists_uniform_ball_subset_of_finite
      (explicitFormulaContourFamilyInterior F T)
      (explicitFormulaRectangleRawSingularCoordinates T)
      hlocal

/-- A strictly smaller closed metric ball is contained in the larger open ball
with the same center. -/
theorem finiteRectangle_closedBall_subset_ball_of_lt
    {a : ℂ} {ε r : ℝ}
    (hεr : ε < r) :
    Metric.closedBall a ε ⊆ Metric.ball a r := by
  intro z hz
  exact lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hεr

/-- A finite set of points with individual positive open neighborhoods inside a
domain has one positive radius whose closed balls all lie in that domain. -/
theorem finiteRectangle_exists_uniform_closedBall_subset_of_finite
    (R : Set ℂ) (S : Finset ℂ)
    (hlocal :
      ∀ a : ℂ, a ∈ S → ∃ r : ℝ, 0 < r ∧ Metric.ball a r ⊆ R) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a : ℂ, a ∈ S → Metric.closedBall a ε ⊆ R := by
  match finiteRectangle_exists_uniform_ball_subset_of_finite R S hlocal with
  | ⟨δ, hδ_pos, hδ_subset⟩ =>
      let ε : ℝ := δ / 2
      have hε_pos : 0 < ε :=
        half_pos hδ_pos
      have hε_lt_δ : ε < δ := by
        calc
          δ / 2 < δ / 1 := by
            exact div_lt_div_of_pos_left hδ_pos zero_lt_one one_lt_two
          _ = δ := by
            exact div_one δ
      exact Exists.intro ε
        (And.intro hε_pos
          (fun a ha =>
            Set.Subset.trans
              (finiteRectangle_closedBall_subset_ball_of_lt hε_lt_δ)
              (hδ_subset a ha)))

/-- The raw singular-coordinate carrier admits one positive radius whose
closed disks all lie in the rectangle interior.  This is the closed-radius
selection needed by deleted-circle residue continuity. -/
theorem explicitFormulaRectangleRawSingularCoordinates_exists_uniform_closedBall_subset_interior
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hlocal :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∃ r : ℝ, 0 < r ∧ Metric.ball a r ⊆ explicitFormulaContourFamilyInterior F T) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T := by
  exact
    finiteRectangle_exists_uniform_closedBall_subset_of_finite
      (explicitFormulaContourFamilyInterior F T)
      (explicitFormulaRectangleRawSingularCoordinates T)
      hlocal

/-- Closed-radius containment is preserved when the radius is shrunk. -/
theorem finiteRectangle_closedBall_subset_of_radius_le
    {a : ℂ} {ε δ : ℝ}
    (hεδ : ε ≤ δ) :
    Metric.closedBall a ε ⊆ Metric.closedBall a δ :=
  Metric.closedBall_subset_closedBall hεδ

/-- A positive radius has nonnegative half-radius. -/
theorem finiteRectangle_halfRadius_nonneg {ε : ℝ} (hε : 0 < ε) :
    0 ≤ ε / 2 :=
  div_nonneg (le_of_lt hε) zero_le_two

/-- A positive radius has positive half-radius. -/
theorem finiteRectangle_halfRadius_pos {ε : ℝ} (hε : 0 < ε) :
    0 < ε / 2 :=
  half_pos hε

/-- A positive radius dominates its half-radius. -/
theorem finiteRectangle_halfRadius_le_self {ε : ℝ} (hε : 0 < ε) :
    ε / 2 ≤ ε := by
  calc
    ε / 2 ≤ ε / 1 := by
      exact div_le_div_of_nonneg_left (le_of_lt hε) zero_lt_one one_le_two
    _ = ε := by
      exact div_one ε

/-- A positive radius has positive quarter-width, written as half of the half-radius. -/
theorem finiteRectangle_quarterRadius_pos {ε : ℝ} (hε : 0 < ε) :
    0 < (ε / 2) / 2 :=
  half_pos (finiteRectangle_halfRadius_pos hε)

/-- A positive radius dominates its quarter-width, written as half of the half-radius. -/
theorem finiteRectangle_quarterRadius_le_self {ε : ℝ} (hε : 0 < ε) :
    (ε / 2) / 2 ≤ ε := by
  exact le_trans
    (finiteRectangle_halfRadius_le_self (finiteRectangle_halfRadius_pos hε))
    (finiteRectangle_halfRadius_le_self hε)

/-- Closed-radius containment passes to the quarter-width used by the half-radius
inscribed-square deleted boundary. -/
theorem explicitFormulaRectangleRawSingularCoordinates_quarterRadius_closedBall_subset_interior
    (F : ExplicitFormulaContourFamily) {T ε : ℝ} (hε : 0 < ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) :
    ∀ a : ℂ,
      a ∈ explicitFormulaRectangleRawSingularCoordinates T →
        Metric.closedBall a ((ε / 2) / 2) ⊆ explicitFormulaContourFamilyInterior F T := by
  intro a ha
  exact Set.Subset.trans
    (finiteRectangle_closedBall_subset_of_radius_le
      (finiteRectangle_quarterRadius_le_self hε))
    (hclosed a ha)

/-- Closed-radius containment passes to the half-radius used by the inscribed-square
construction. -/
theorem explicitFormulaRectangleRawSingularCoordinates_halfRadius_closedBall_subset_interior
    (F : ExplicitFormulaContourFamily) {T ε : ℝ} (hε : 0 < ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) :
    ∀ a : ℂ,
      a ∈ explicitFormulaRectangleRawSingularCoordinates T →
        Metric.closedBall a (ε / 2) ⊆ explicitFormulaContourFamilyInterior F T :=
  fun a ha =>
    Set.Subset.trans
      (finiteRectangle_closedBall_subset_of_radius_le
        (finiteRectangle_halfRadius_le_self hε))
      (hclosed a ha)

/-- Combine a closed-ball containment radius and a strict pairwise-separation
radius by taking their minimum. -/
theorem explicitFormulaRectangleRawSingularCoordinates_closedRadiusControls_of_two_radii
    (F : ExplicitFormulaContourFamily) (T δ η : ℝ)
    (hδ_pos : 0 < δ)
    (hη_pos : 0 < η)
    (hclosedδ :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a δ ⊆ explicitFormulaContourFamilyInterior F T)
    (hsepη :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → η + η < dist a b) :
    ∃ ε : ℝ,
      0 < ε ∧
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) ∧
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            ∀ b : ℂ,
              b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a ≠ b → ε + ε < dist a b) := by
  let ε : ℝ := min δ η
  have hε_pos : 0 < ε :=
    lt_min hδ_pos hη_pos
  have hεδ : ε ≤ δ :=
    min_le_left δ η
  have hεη : ε ≤ η :=
    min_le_right δ η
  have hclosedε :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T := by
    intro a ha
    exact Set.Subset.trans
      (finiteRectangle_closedBall_subset_of_radius_le hεδ)
      (hclosedδ a ha)
  have hsepε :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ε + ε < dist a b := by
    intro a ha b hb hab
    have hsum_le : ε + ε ≤ η + η :=
      add_le_add hεη hεη
    exact lt_of_le_of_lt hsum_le (hsepη a ha b hb hab)
  exact Exists.intro ε
    (And.intro hε_pos
      (And.intro hclosedε hsepε))

/-- The raw singular-coordinate carrier admits one positive radius satisfying both
closed-disk containment in the rectangle interior and strict pairwise closed-disk separation,
once every listed raw singular coordinate has a local interior ball. -/
theorem explicitFormulaRectangleRawSingularCoordinates_exists_closedRadiusControls
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hlocal :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∃ r : ℝ, 0 < r ∧ Metric.ball a r ⊆ explicitFormulaContourFamilyInterior F T) :
    ∃ ε : ℝ,
      0 < ε ∧
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) ∧
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            ∀ b : ℂ,
              b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a ≠ b → ε + ε < dist a b) := by
  match explicitFormulaRectangleRawSingularCoordinates_exists_uniform_closedBall_subset_interior
      F T hlocal with
  | ⟨δ, hδ_pos, hclosedδ⟩ =>
      match finiteRectangle_exists_uniform_strict_pairwise_radius
          (explicitFormulaRectangleRawSingularCoordinates T) with
      | ⟨η, hη_pos, hsepη⟩ =>
          exact
            explicitFormulaRectangleRawSingularCoordinates_closedRadiusControls_of_two_radii
              F T δ η hδ_pos hη_pos hclosedδ hsepη

/-- The concrete deleted-disk geometry needed for finite-hole rectangle subdivision:
deleted disks around the raw finite singular carrier lie in the rectangle interior and are
pairwise disjoint. -/
theorem explicitFormulaRectangleRawDeletedDisks_geometry_of_radius_controls
    (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (hball :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.ball a ε ⊆ explicitFormulaContourFamilyInterior F T)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ε + ε ≤ dist a b) :
    finiteRectangleDeletedDisks
        (explicitFormulaRectangleRawSingularCoordinates T) ε ⊆
        explicitFormulaContourFamilyInterior F T ∧
      (∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b →
                Disjoint (Metric.ball a ε) (Metric.ball b ε)) := by
  exact
    And.intro
      (explicitFormulaRectangleRawDeletedDisks_subset_interior_of_forall_ball_subset
        F T ε hball)
      (finiteRectangle_pairwiseDisjoint_balls_of_two_mul_le_dist
        (explicitFormulaRectangleRawSingularCoordinates T) ε hsep)

/-- Closed-disk version of the raw singular-coordinate geometry used by
deleted-circle residue inputs: all closed disks lie in the rectangle interior
and distinct closed disks are pairwise disjoint. -/
theorem explicitFormulaRectangleRawClosedDisks_geometry_of_radius_controls
    (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ε + ε < dist a b) :
    (∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) ∧
      (∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b →
                Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε)) := by
  exact
    And.intro
      hclosed
      (finiteRectangle_pairwiseDisjoint_closedBalls_of_two_mul_lt_dist
        (explicitFormulaRectangleRawSingularCoordinates T) ε hsep)

/-- Membership in one indexed deleted disk gives membership in the indexed finite
deleted-disk union. -/
theorem finiteRectangleIndexedDeletedDisks_mem_of_mem_ball
    {α : Type*} (S : Finset α) (center : α → ℂ) (ε : ℝ) {a : α} {z : ℂ}
    (ha : a ∈ S) (hz : z ∈ Metric.ball (center a) ε) :
    z ∈ finiteRectangleIndexedDeletedDisks S center ε :=
  Exists.intro a (And.intro ha hz)

/-- An indexed deleted disk centered at a listed singular coordinate is contained in the
indexed finite deleted-disk union. -/
theorem finiteRectangleIndexedDeletedDisks_ball_subset
    {α : Type*} (S : Finset α) (center : α → ℂ) (ε : ℝ) {a : α}
    (ha : a ∈ S) :
    Metric.ball (center a) ε ⊆ finiteRectangleIndexedDeletedDisks S center ε :=
  fun _z hz => finiteRectangleIndexedDeletedDisks_mem_of_mem_ball S center ε ha hz

/-- If every indexed deleted disk lies in a base domain, then the indexed finite
deleted-disk union lies in that domain. -/
theorem finiteRectangleIndexedDeletedDisks_subset_of_forall_ball_subset
    {α : Type*} (R : Set ℂ) (S : Finset α) (center : α → ℂ) (ε : ℝ)
    (hball : ∀ a : α, a ∈ S → Metric.ball (center a) ε ⊆ R) :
    finiteRectangleIndexedDeletedDisks S center ε ⊆ R :=
  fun _z hz =>
    Exists.elim hz
      (fun a ha => hball a ha.left ha.right)

/-- A completed zero in the height window contributes its contour coordinate to the
finite coordinate carrier. -/
theorem explicitFormulaCompletedZeroWindowCoordinates_mem_of_mem_window
    (T : ℝ) {ρ : {ρ : ℂ // ZetaCompletedZero ρ}}
    (hρ : ρ ∈ explicitFormulaCompletedZeroHeightWindow T) :
    completedZeroResidueCoordinate ρ ∈ explicitFormulaCompletedZeroWindowCoordinates T :=
  Finset.mem_image.mpr (Exists.intro ρ (And.intro hρ rfl))

/-- The pole coordinate `0` belongs to the raw singular-coordinate carrier. -/
theorem explicitFormulaRectangleRawSingularCoordinates_zero_mem
    (T : ℝ) :
    (0 : ℂ) ∈ explicitFormulaRectangleRawSingularCoordinates T :=
  Finset.mem_insert_self (0 : ℂ) (insert (1 : ℂ) (explicitFormulaCompletedZeroWindowCoordinates T))

/-- The pole coordinate `1` belongs to the raw singular-coordinate carrier. -/
theorem explicitFormulaRectangleRawSingularCoordinates_one_mem
    (T : ℝ) :
    (1 : ℂ) ∈ explicitFormulaRectangleRawSingularCoordinates T :=
  Finset.mem_insert_of_mem
    (Finset.mem_insert_self (1 : ℂ) (explicitFormulaCompletedZeroWindowCoordinates T))

/-- Every completed-zero coordinate in the finite window belongs to the raw
singular-coordinate carrier. -/
theorem explicitFormulaRectangleRawSingularCoordinates_completedZero_mem
    (T : ℝ) {ρ : {ρ : ℂ // ZetaCompletedZero ρ}}
    (hρ : ρ ∈ explicitFormulaCompletedZeroHeightWindow T) :
    completedZeroResidueCoordinate ρ ∈ explicitFormulaRectangleRawSingularCoordinates T :=
  Finset.mem_insert_of_mem
    (Finset.mem_insert_of_mem
      (explicitFormulaCompletedZeroWindowCoordinates_mem_of_mem_window T hρ))

/-- Every raw singular coordinate is either one of the two completed-zeta pole coordinates
or the residue coordinate of a completed zero in the finite height window. -/
theorem explicitFormulaRectangleRawSingularCoordinates_cases
    (T : ℝ) {a : ℂ}
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    a = 0 ∨ a = 1 ∨
      ∃ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ∧
          completedZeroResidueCoordinate ρ = a := by
  match Finset.mem_insert.mp ha with
  | Or.inl hzero =>
      exact Or.inl hzero
  | Or.inr hrest =>
      match Finset.mem_insert.mp hrest with
      | Or.inl hone =>
          exact Or.inr (Or.inl hone)
      | Or.inr hcompleted =>
          exact Or.inr
            (Or.inr
              (explicitFormulaCompletedZeroWindowCoordinates_exists_window_of_mem
                T hcompleted))

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
