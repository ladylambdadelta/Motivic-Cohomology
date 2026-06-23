import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part15

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

/-- A rectangular subdivision cell disjoint from every removed raw inscribed square avoids
the raw singular carrier. -/
theorem explicitFormulaRectangleSubdivisionCell_not_mem_rawSingularCoordinates_of_disjoint_inscribedSquares
    (T ε : ℝ) (hε : 0 ≤ ε) (lower upper : ℂ)
    (hdisjoint :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Disjoint
            ([[ lower.re, upper.re ]] ×ℂ [[ lower.im, upper.im ]])
            (explicitFormulaRectangleRawInscribedSquareClosedCell ε a))
    {z : ℂ}
    (hz : z ∈ ([[ lower.re, upper.re ]] ×ℂ [[ lower.im, upper.im ]])) :
    z ∉ explicitFormulaRectangleRawSingularCoordinates T :=
  explicitFormulaRectangleRawSingularCoordinates_not_mem_of_disjoint_inscribedSquares
    T ε hε
    ([[ lower.re, upper.re ]] ×ℂ [[ lower.im, upper.im ]])
    hdisjoint
    hz

/-- The annulus between half of a selected closed radius and the selected radius remains in
the contour-family interior. -/
theorem explicitFormulaRectangleRawSingularHalfAnnulus_subset_interior_of_closedRadiusControls
    (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    (a : ℂ)
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    Metric.closedBall a ε \ Metric.ball a (ε / 2) ⊆
      explicitFormulaContourFamilyInterior F T := by
  intro z hz
  exact hclosed a ha hz.1

/-- The annulus between half of a selected closed radius and the selected radius contains
no raw singular coordinate. -/
theorem explicitFormulaRectangleRawSingularHalfAnnulus_offRaw_of_closedRadiusControls
    (T ε : ℝ) (hε : 0 < ε)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ε + ε < dist a b)
    (a : ℂ)
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    ∀ z : ℂ,
      z ∈ Metric.closedBall a ε \ Metric.ball a (ε / 2) →
        z ∉ explicitFormulaRectangleRawSingularCoordinates T := by
  intro z hz hzRaw
  have hhalf_pos : 0 < ε / 2 :=
    half_pos hε
  have hz_ne_a : z ≠ a := by
    intro hza
    have ha_ball : a ∈ Metric.ball a (ε / 2) :=
      Metric.mem_ball_self hhalf_pos
    have hz_ball : z ∈ Metric.ball a (ε / 2) :=
      Eq.subst
        (motive := fun w : ℂ => w ∈ Metric.ball a (ε / 2))
        hza.symm
        ha_ball
    exact hz.2 hz_ball
  have ha_ne_z : a ≠ z :=
    fun haz => hz_ne_a haz.symm
  have hdist_za_le : dist z a ≤ ε :=
    Metric.mem_closedBall.mp hz.1
  have hdist_az_le : dist a z ≤ ε :=
    Eq.subst
      (motive := fun x : ℝ => x ≤ ε)
      (dist_comm z a)
      hdist_za_le
  have hε_le_two : ε ≤ ε + ε :=
    le_add_of_nonneg_right (le_of_lt hε)
  have hdist_az_le_two : dist a z ≤ ε + ε :=
    le_trans hdist_az_le hε_le_two
  exact
    (not_lt_of_ge hdist_az_le_two)
      (hsep a ha z hzRaw ha_ne_z)

/-- The completed contour integrand is continuous on the half-radius annulus around a raw
singular coordinate under the selected closed-radius controls. -/
theorem explicitFormulaRectangleRawSingularHalfAnnulus_continuousOn_of_closedRadiusControls
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ε + ε < dist a b)
    (a : ℂ)
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    ContinuousOn
      (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
      (Metric.closedBall a ε \ Metric.ball a (ε / 2)) :=
  explicitFormulaRectangleInteriorOffRawSingular_continuousOn
    f F h hT hinterior
    (Metric.closedBall a ε \ Metric.ball a (ε / 2))
    (explicitFormulaRectangleRawSingularHalfAnnulus_subset_interior_of_closedRadiusControls
      F T ε hclosed a ha)
    (explicitFormulaRectangleRawSingularHalfAnnulus_offRaw_of_closedRadiusControls
      T ε hε hsep a ha)

/-- The completed contour integrand is differentiable on the open half-radius annulus
around a raw singular coordinate under the selected closed-radius controls. -/
theorem explicitFormulaRectangleRawSingularHalfAnnulus_differentiableAt_of_closedRadiusControls
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ε + ε < dist a b)
    (a : ℂ)
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (z : ℂ)
    (hz : z ∈ Metric.ball a ε \ Metric.closedBall a (ε / 2)) :
    DifferentiableAt ℂ
      (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z := by
  have hzClosed : z ∈ Metric.closedBall a ε :=
    Metric.mem_closedBall.mpr
      (le_of_lt (Metric.mem_ball.mp hz.1))
  have hzNotBall : z ∉ Metric.ball a (ε / 2) := by
    intro hzBall
    exact hz.2
      (Metric.mem_closedBall.mpr
        (le_of_lt (Metric.mem_ball.mp hzBall)))
  have hzAnnulus :
      z ∈ Metric.closedBall a ε \ Metric.ball a (ε / 2) :=
    And.intro hzClosed hzNotBall
  exact
    explicitFormulaRectangleInteriorOffRawSingular_differentiableAt
      f F h hT hinterior
      (Metric.closedBall a ε \ Metric.ball a (ε / 2))
      (explicitFormulaRectangleRawSingularHalfAnnulus_subset_interior_of_closedRadiusControls
        F T ε hclosed a ha)
      (explicitFormulaRectangleRawSingularHalfAnnulus_offRaw_of_closedRadiusControls
        T ε hε hsep a ha)
      hzAnnulus

/-- A point in a rectangular cell can equal a center only if both center coordinates lie in
the corresponding coordinate intervals. -/
theorem finiteRectangleSubdivisionCell_ne_center_of_coordinate_omission
    (lower upper a z : ℂ)
    (hz : z ∈ ([[ lower.re, upper.re ]] ×ℂ [[ lower.im, upper.im ]]))
    (homit :
      a.re ∉ [[ lower.re, upper.re ]] ∨
        a.im ∉ [[ lower.im, upper.im ]]) :
    z ≠ a := by
  intro hza
  match homit with
  | Or.inl hre_omit =>
      have hre_mem : a.re ∈ [[ lower.re, upper.re ]] :=
        Eq.subst
          (motive := fun w : ℂ => w.re ∈ [[ lower.re, upper.re ]])
          hza
          hz.1
      exact hre_omit hre_mem
  | Or.inr him_omit =>
      have him_mem : a.im ∈ [[ lower.im, upper.im ]] :=
        Eq.subst
          (motive := fun w : ℂ => w.im ∈ [[ lower.im, upper.im ]])
          hza
          hz.2
      exact him_omit him_mem

/-- A rectangular subdivision cell avoids the raw finite singular-coordinate carrier when
each raw center is omitted by at least one coordinate interval. -/
theorem explicitFormulaRectangleSubdivisionCell_not_mem_rawSingularCoordinates_of_coordinate_omission
    (T : ℝ) (lower upper : ℂ)
    (homit :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          a.re ∉ [[ lower.re, upper.re ]] ∨
            a.im ∉ [[ lower.im, upper.im ]])
    {z : ℂ}
    (hz : z ∈ ([[ lower.re, upper.re ]] ×ℂ [[ lower.im, upper.im ]])) :
    z ∉ explicitFormulaRectangleRawSingularCoordinates T := by
  intro hzRaw
  exact
    finiteRectangleSubdivisionCell_ne_center_of_coordinate_omission
      lower upper z z hz (homit z hzRaw) rfl

/-- Lower-left corner of the outer explicit-formula rectangle at height `T`. -/
def explicitFormulaRectangleOuterLowerCorner
    (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  (F.c : ℂ) + (-T : ℂ) * Complex.I

/-- Upper-right corner of the outer explicit-formula rectangle at height `T`. -/
def explicitFormulaRectangleOuterUpperCorner
    (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  ((1 - F.c : ℝ) : ℂ) + (T : ℂ) * Complex.I

/-- The closed cell of the outer explicit-formula rectangle. -/
def explicitFormulaRectangleOuterClosedCell
    (F : ExplicitFormulaContourFamily) (T : ℝ) : Set ℂ :=
  [[ (explicitFormulaRectangleOuterLowerCorner F T).re,
      (explicitFormulaRectangleOuterUpperCorner F T).re ]] ×ℂ
    [[ (explicitFormulaRectangleOuterLowerCorner F T).im,
      (explicitFormulaRectangleOuterUpperCorner F T).im ]]

/-- Real coordinate of the lower-left outer rectangle corner. -/
theorem explicitFormulaRectangleOuterLowerCorner_re
    (F : ExplicitFormulaContourFamily) (T : ℝ) :
    (explicitFormulaRectangleOuterLowerCorner F T).re = F.c :=
  ofReal_add_mul_I_re F.c (-T)

/-- Imaginary coordinate of the lower-left outer rectangle corner. -/
theorem explicitFormulaRectangleOuterLowerCorner_im
    (F : ExplicitFormulaContourFamily) (T : ℝ) :
    (explicitFormulaRectangleOuterLowerCorner F T).im = -T :=
  ofReal_add_mul_I_im F.c (-T)

/-- Real coordinate of the upper-right outer rectangle corner. -/
theorem explicitFormulaRectangleOuterUpperCorner_re
    (F : ExplicitFormulaContourFamily) (T : ℝ) :
    (explicitFormulaRectangleOuterUpperCorner F T).re = 1 - F.c :=
  ofReal_add_mul_I_re (1 - F.c) T

/-- Imaginary coordinate of the upper-right outer rectangle corner. -/
theorem explicitFormulaRectangleOuterUpperCorner_im
    (F : ExplicitFormulaContourFamily) (T : ℝ) :
    (explicitFormulaRectangleOuterUpperCorner F T).im = T :=
  ofReal_add_mul_I_im (1 - F.c) T

/-- The outer rectangle boundary in the Cauchy-Goursat cell orientation used by
`finiteRectangleSubdivisionCellBoundaryIntegral`: bottom minus top, plus the tangent
vertical side contribution. -/
noncomputable def explicitFormulaRectangleOuterCauchyCellBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  finiteRectangleSubdivisionCellBoundaryIntegral
    (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
    (explicitFormulaRectangleOuterLowerCorner F T)
    (explicitFormulaRectangleOuterUpperCorner F T)

/-- The named outer Cauchy boundary is the rectangular subdivision-cell boundary between
the named outer corners. -/
theorem explicitFormulaRectangleOuterCauchyCellBoundary_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaRectangleOuterCauchyCellBoundary f F T =
      finiteRectangleSubdivisionCellBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
        (explicitFormulaRectangleOuterLowerCorner F T)
        (explicitFormulaRectangleOuterUpperCorner F T) := by
  rfl

/-- Horizontal endpoints used by the finite inscribed-square complement subdivision:
the two outer vertical sides and the two vertical sides of each square hole. -/
noncomputable def explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints
    (F : ExplicitFormulaContourFamily) (T ε : ℝ) : Finset ℝ :=
  insert F.c <|
    insert (1 - F.c) <|
      (explicitFormulaRectangleRawSingularCoordinates T).bind
        (fun a : ℂ =>
          { (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).re,
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).re })

/-- Vertical endpoints used by the finite inscribed-square complement subdivision:
the two outer horizontal sides and the two horizontal sides of each square hole. -/
noncomputable def explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints
    (T ε : ℝ) : Finset ℝ :=
  insert (-T) <|
    insert T <|
      (explicitFormulaRectangleRawSingularCoordinates T).bind
        (fun a : ℂ =>
          { (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).im,
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).im })

/-- The lower outer vertical endpoint belongs to the horizontal subdivision endpoint
carrier. -/
theorem explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints_mem_left
    (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    F.c ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε :=
  Finset.mem_insert_self F.c _

/-- The upper outer vertical endpoint belongs to the horizontal subdivision endpoint
carrier. -/
theorem explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints_mem_right
    (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    1 - F.c ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε :=
  Finset.mem_insert_of_mem (Finset.mem_insert_self (1 - F.c) _)

/-- The lower outer horizontal endpoint belongs to the vertical subdivision endpoint
carrier. -/
theorem explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints_mem_lower
    (T ε : ℝ) :
    -T ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε :=
  Finset.mem_insert_self (-T) _

/-- The upper outer horizontal endpoint belongs to the vertical subdivision endpoint
carrier. -/
theorem explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints_mem_upper
    (T ε : ℝ) :
    T ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε :=
  Finset.mem_insert_of_mem (Finset.mem_insert_self T _)

/-- The left side of each inscribed square hole is recorded in the horizontal subdivision
endpoint carrier. -/
theorem explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints_mem_holeLeft
    (F : ExplicitFormulaContourFamily) (T ε : ℝ) {a : ℂ}
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).re ∈
      explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε :=
  Finset.mem_insert_of_mem <|
    Finset.mem_insert_of_mem <|
      Finset.mem_bind.mpr
        ⟨a, ha, Finset.mem_insert_self
          (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).re _⟩

/-- The right side of each inscribed square hole is recorded in the horizontal subdivision
endpoint carrier. -/
theorem explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints_mem_holeRight
    (F : ExplicitFormulaContourFamily) (T ε : ℝ) {a : ℂ}
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).re ∈
      explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε :=
  Finset.mem_insert_of_mem <|
    Finset.mem_insert_of_mem <|
      Finset.mem_bind.mpr
        ⟨a, ha, Finset.mem_insert_of_mem
          (Finset.mem_insert_self
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).re _)⟩

/-- The bottom side of each inscribed square hole is recorded in the vertical subdivision
endpoint carrier. -/
theorem explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints_mem_holeBottom
    (T ε : ℝ) {a : ℂ}
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).im ∈
      explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε :=
  Finset.mem_insert_of_mem <|
    Finset.mem_insert_of_mem <|
      Finset.mem_bind.mpr
        ⟨a, ha, Finset.mem_insert_self
          (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).im _⟩

/-- The top side of each inscribed square hole is recorded in the vertical subdivision
endpoint carrier. -/
theorem explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints_mem_holeTop
    (T ε : ℝ) {a : ℂ}
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).im ∈
      explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε :=
  Finset.mem_insert_of_mem <|
    Finset.mem_insert_of_mem <|
      Finset.mem_bind.mpr
        ⟨a, ha, Finset.mem_insert_of_mem
          (Finset.mem_insert_self
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).im _)⟩

/-- Closed-radius controls put every lower-square horizontal endpoint strictly inside the
outer horizontal span. -/
theorem explicitFormulaRectangleInscribedSquareLowerCorner_re_mem_horizontal_uIoo_of_closedRadiusControls
    (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (hε : 0 ≤ ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    {a : ℂ}
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).re ∈
      Set.uIoo F.c (1 - F.c) :=
  (explicitFormulaRectangleRawInscribedSquareLowerCorner_mem_interior_of_closedRadiusControls
    F T ε hε hclosed a ha).1

/-- Closed-radius controls put every upper-square horizontal endpoint strictly inside the
outer horizontal span. -/
theorem explicitFormulaRectangleInscribedSquareUpperCorner_re_mem_horizontal_uIoo_of_closedRadiusControls
    (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (hε : 0 ≤ ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    {a : ℂ}
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).re ∈
      Set.uIoo F.c (1 - F.c) :=
  (explicitFormulaRectangleRawInscribedSquareUpperCorner_mem_interior_of_closedRadiusControls
    F T ε hε hclosed a ha).1

/-- Closed-radius controls put every lower-square vertical endpoint strictly inside the
height interval. -/
theorem explicitFormulaRectangleInscribedSquareLowerCorner_im_mem_vertical_Ioo_of_closedRadiusControls
    (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (hε : 0 ≤ ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    {a : ℂ}
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).im ∈
      Set.Ioo (-T) T :=
  (explicitFormulaRectangleRawInscribedSquareLowerCorner_mem_interior_of_closedRadiusControls
    F T ε hε hclosed a ha).2

/-- Closed-radius controls put every upper-square vertical endpoint strictly inside the
height interval. -/
theorem explicitFormulaRectangleInscribedSquareUpperCorner_im_mem_vertical_Ioo_of_closedRadiusControls
    (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (hε : 0 ≤ ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    {a : ℂ}
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).im ∈
      Set.Ioo (-T) T :=
  (explicitFormulaRectangleRawInscribedSquareUpperCorner_mem_interior_of_closedRadiusControls
    F T ε hε hclosed a ha).2

/-- Every horizontal endpoint of the inscribed-square subdivision lies in the closed outer
horizontal span, once the deleted-square sides are controlled by closed-radius geometry. -/
theorem explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints_mem_horizontal_uIcc_of_closedRadiusControls
    (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (hε : 0 ≤ ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    {x : ℝ}
    (hx : x ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε) :
    x ∈ [[F.c, 1 - F.c]] := by
  match Finset.mem_insert.mp hx with
  | Or.inl hx_left =>
      exact
        Eq.subst
          (motive := fun y : ℝ => y ∈ [[F.c, 1 - F.c]])
          hx_left.symm
          Set.left_mem_uIcc
  | Or.inr hx_not_left =>
      match Finset.mem_insert.mp hx_not_left with
      | Or.inl hx_right =>
          exact
            Eq.subst
              (motive := fun y : ℝ => y ∈ [[F.c, 1 - F.c]])
              hx_right.symm
              Set.right_mem_uIcc
      | Or.inr hx_hole =>
          match Finset.mem_bind.mp hx_hole with
          | ⟨a, ha, hx_side⟩ =>
              match Finset.mem_insert.mp hx_side with
              | Or.inl hx_lower =>
                  have hstrict :
                      (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).re ∈
                        Set.uIoo F.c (1 - F.c) :=
                    explicitFormulaRectangleInscribedSquareLowerCorner_re_mem_horizontal_uIoo_of_closedRadiusControls
                      F T ε hε hclosed ha
                  have hclosed_span :
                      (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).re ∈
                        [[F.c, 1 - F.c]] :=
                    Set.uIoo_subset_uIcc F.c (1 - F.c) hstrict
                  exact
                    Eq.subst
                      (motive := fun y : ℝ => y ∈ [[F.c, 1 - F.c]])
                      hx_lower.symm
                      hclosed_span
              | Or.inr hx_upper =>
                  have hstrict :
                      (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).re ∈
                        Set.uIoo F.c (1 - F.c) :=
                    explicitFormulaRectangleInscribedSquareUpperCorner_re_mem_horizontal_uIoo_of_closedRadiusControls
                      F T ε hε hclosed ha
                  have hclosed_span :
                      (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).re ∈
                        [[F.c, 1 - F.c]] :=
                    Set.uIoo_subset_uIcc F.c (1 - F.c) hstrict
                  exact
                    Eq.subst
                      (motive := fun y : ℝ => y ∈ [[F.c, 1 - F.c]])
                      hx_upper.symm
                      hclosed_span

/-- Every vertical endpoint of the inscribed-square subdivision lies in the closed height
interval, once the deleted-square sides are controlled by closed-radius geometry. -/
theorem explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints_mem_vertical_Icc_of_closedRadiusControls
    (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (hT_nonneg : 0 ≤ T)
    (hε : 0 ≤ ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    {y : ℝ}
    (hy : y ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε) :
    y ∈ Set.Icc (-T) T := by
  have hnegT_le_T : -T ≤ T :=
    le_trans (neg_nonpos.mpr hT_nonneg) hT_nonneg
  match Finset.mem_insert.mp hy with
  | Or.inl hy_bottom =>
      exact
        Eq.subst
          (motive := fun u : ℝ => u ∈ Set.Icc (-T) T)
          hy_bottom.symm
          (Set.left_mem_Icc.mpr hnegT_le_T)
  | Or.inr hy_not_bottom =>
      match Finset.mem_insert.mp hy_not_bottom with
      | Or.inl hy_top =>
          exact
            Eq.subst
              (motive := fun u : ℝ => u ∈ Set.Icc (-T) T)
              hy_top.symm
              (Set.right_mem_Icc.mpr hnegT_le_T)
      | Or.inr hy_hole =>
          match Finset.mem_bind.mp hy_hole with
          | ⟨a, ha, hy_side⟩ =>
              match Finset.mem_insert.mp hy_side with
              | Or.inl hy_lower =>
                  have hstrict :
                      (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).im ∈
                        Set.Ioo (-T) T :=
                    explicitFormulaRectangleInscribedSquareLowerCorner_im_mem_vertical_Ioo_of_closedRadiusControls
                      F T ε hε hclosed ha
                  have hclosed_height :
                      (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).im ∈
                        Set.Icc (-T) T :=
                    Set.Ioo_subset_Icc_self hstrict
                  exact
                    Eq.subst
                      (motive := fun u : ℝ => u ∈ Set.Icc (-T) T)
                      hy_lower.symm
                      hclosed_height
              | Or.inr hy_upper =>
                  have hstrict :
                      (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).im ∈
                        Set.Ioo (-T) T :=
                    explicitFormulaRectangleInscribedSquareUpperCorner_im_mem_vertical_Ioo_of_closedRadiusControls
                      F T ε hε hclosed ha
                  have hclosed_height :
                      (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).im ∈
                        Set.Icc (-T) T :=
                    Set.Ioo_subset_Icc_self hstrict
                  exact
                    Eq.subst
                      (motive := fun u : ℝ => u ∈ Set.Icc (-T) T)
                      hy_upper.symm
                      hclosed_height

/-- A rectangular grid cell index is a pair of horizontal endpoints and a pair of vertical
endpoints.  The complement-cell subdivision will select ordered, non-hole cells from this
finite carrier. -/
abbrev ExplicitFormulaRectangleGridCellIndex : Type :=
  (ℝ × ℝ) × (ℝ × ℝ)

/-- Lower-left corner associated to a grid cell index. -/
def explicitFormulaRectangleGridCellLower
    (c : ExplicitFormulaRectangleGridCellIndex) : ℂ :=
  (c.1.1 : ℂ) + (c.2.1 : ℂ) * Complex.I

/-- Upper-right corner associated to a grid cell index. -/
def explicitFormulaRectangleGridCellUpper
    (c : ExplicitFormulaRectangleGridCellIndex) : ℂ :=
  (c.1.2 : ℂ) + (c.2.2 : ℂ) * Complex.I

/-- Real coordinate of the lower-left corner associated to a grid cell index. -/
theorem explicitFormulaRectangleGridCellLower_re
    (c : ExplicitFormulaRectangleGridCellIndex) :
    (explicitFormulaRectangleGridCellLower c).re = c.1.1 :=
  ofReal_add_mul_I_re c.1.1 c.2.1

/-- Imaginary coordinate of the lower-left corner associated to a grid cell index. -/
theorem explicitFormulaRectangleGridCellLower_im
    (c : ExplicitFormulaRectangleGridCellIndex) :
    (explicitFormulaRectangleGridCellLower c).im = c.2.1 :=
  ofReal_add_mul_I_im c.1.1 c.2.1

/-- Real coordinate of the upper-right corner associated to a grid cell index. -/
theorem explicitFormulaRectangleGridCellUpper_re
    (c : ExplicitFormulaRectangleGridCellIndex) :
    (explicitFormulaRectangleGridCellUpper c).re = c.1.2 :=
  ofReal_add_mul_I_re c.1.2 c.2.2

/-- Imaginary coordinate of the upper-right corner associated to a grid cell index. -/
theorem explicitFormulaRectangleGridCellUpper_im
    (c : ExplicitFormulaRectangleGridCellIndex) :
    (explicitFormulaRectangleGridCellUpper c).im = c.2.2 :=
  ofReal_add_mul_I_im c.1.2 c.2.2

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
