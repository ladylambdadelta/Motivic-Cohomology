import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part14

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

/-- Full tangent contour residue accounting in the reverse direction: a full tangent
pole-corrected contour residue identity plus the tangent pole residue identity reconstructs
the completed-zero plus pole residue sum on the tangent outer boundary. -/
theorem zetaCompletedExplicitFormulaTangentContourIntegral_eq_poleCorrectedResidueSum_of_fullTangentCorrectedContour
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hcorrected :
      explicitFormulaRectangle_fullTangentPoleCorrectedContourIntegral f F T =
        explicitFormulaCompletedZeroHeightWindowResidueSum f T)
    (hpoles :
      explicitFormulaRectangle_completedPoleTangentBoundaryContribution f F T =
        explicitFormulaRectangle_completedPoleResidueSum f) :
    zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) =
      explicitFormulaRectangle_poleCorrectedResidueSum f T := by
  calc
    zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) =
        explicitFormulaRectangle_fullTangentPoleCorrectedContourIntegral f F T +
          explicitFormulaRectangle_completedPoleTangentBoundaryContribution f F T := by
      exact
        zetaCompletedExplicitFormulaTangentContourIntegral_eq_fullTangentPoleCorrected_add_tangentPoles
          f F T
    _ = explicitFormulaCompletedZeroHeightWindowResidueSum f T +
          explicitFormulaRectangle_completedPoleTangentBoundaryContribution f F T := by
      exact congrArg
        (fun x : ℂ => x + explicitFormulaRectangle_completedPoleTangentBoundaryContribution f F T)
        hcorrected
    _ = explicitFormulaCompletedZeroHeightWindowResidueSum f T +
          explicitFormulaRectangle_completedPoleResidueSum f := by
      exact congrArg
        (fun x : ℂ => explicitFormulaCompletedZeroHeightWindowResidueSum f T + x)
        hpoles
    _ = explicitFormulaRectangle_poleCorrectedResidueSum f T := by
      exact (explicitFormulaRectangle_poleCorrectedResidueSum_eq f T).symm

/-- Generic finite-rectangle residue accounting assembly.

This is the owner-level limit algebra used after punctured-rectangle Cauchy-Goursat and
shrinking-circle local residue limits have been proved: if the punctured rectangle
boundary differs from the deleted-boundary contribution by a term tending to zero, and the
deleted-boundary contribution tends to the finite residue sum, then the punctured
rectangle boundary tends to that finite residue sum. -/
theorem finiteRectangleResidueAccounting_tendsto_of_puncturedCauchy_and_deletedBoundary
    {ι : Type*} [TopologicalSpace ι] {l : Filter ι}
    (outer deleted : ι → ℂ) (residueSum : ℂ)
    (hcauchy : Tendsto (fun i : ι => outer i - deleted i) l (𝓝 0))
    (hdeleted : Tendsto deleted l (𝓝 residueSum)) :
    Tendsto outer l (𝓝 residueSum) := by
  have hsum :
      Tendsto
        (fun i : ι => (outer i - deleted i) + deleted i)
        l
        (𝓝 (0 + residueSum)) :=
    hcauchy.add hdeleted
  have hpoint :
      (fun i : ι => (outer i - deleted i) + deleted i) =ᶠ[l]
        outer := by
    exact
      Filter.Eventually.of_forall
        (fun i => sub_add_cancel (outer i) (deleted i))
  have htarget : 0 + residueSum = residueSum :=
    zero_add residueSum
  exact (htarget ▸ hsum).congr' hpoint

/-- Finite deleted-circle boundary contributions are recorded with positive residue
orientation.  The punctured rectangle boundary therefore appears as outer boundary minus
this deleted-circle sum. -/
noncomputable def finiteRectangleDeletedCircleBoundarySum
    (S : Finset ℂ) (deletedCircle : ℂ → ℂ) : ℂ :=
  ∑ a in S, deletedCircle a

/-- The positive-orientation deleted-circle boundary contribution of the completed
explicit-formula integrand around a singular coordinate. -/
noncomputable def explicitFormulaRectangleRawDeletedCircleBoundary
    (f : ZetaAdmissibleFunction) (ε : ℝ) (a : ℂ) : ℂ :=
  ∮ z in C(a, ε), zetaCompletedExplicitFormulaContourIntegrand f z

/-- The positive-orientation square deleted-boundary contribution of the completed
explicit-formula integrand around a singular coordinate.  This is the rectangular
replacement boundary used by the finite square-hole subdivision before transport back to
the public circular deleted-boundary normalization. -/
noncomputable def explicitFormulaRectangleRawDeletedSquareBoundary
    (f : ZetaAdmissibleFunction) (ε : ℝ) (a : ℂ) : ℂ :=
  finiteRectangleSquareBoundaryIntegral
    (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z) a ε

/-- The positive-orientation inscribed-square deleted-boundary contribution of the
completed explicit-formula integrand around a singular coordinate.  The square half-width
is `ε / 2`, so this boundary is the square-hole replacement compatible with radius-`ε`
closed-disk controls. -/
noncomputable def explicitFormulaRectangleRawInscribedSquareBoundary
    (f : ZetaAdmissibleFunction) (ε : ℝ) (a : ℂ) : ℂ :=
  finiteRectangleSquareBoundaryIntegral
    (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z) a (ε / 2)

/-- The raw deleted-circle boundary is unchanged when the radius is transported across a
regular annulus about the same raw coordinate. -/
theorem explicitFormulaRectangleRawDeletedCircleBoundary_eq_of_annulus_regular
    (f : ZetaAdmissibleFunction) {a : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R)
    (s : Set ℂ) (hs : s.Countable)
    (hcontinuous :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
        (Metric.closedBall a R \ Metric.ball a r))
    (hdifferentiable :
      ∀ z : ℂ,
        z ∈ (Metric.ball a R \ Metric.closedBall a r) \ s →
          DifferentiableAt ℂ
            (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z) :
    explicitFormulaRectangleRawDeletedCircleBoundary f R a =
      explicitFormulaRectangleRawDeletedCircleBoundary f r a :=
  finiteRectangle_deletedCircleIntegral_eq_of_annulus_regular
    hr hrR
    (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
    s hs hcontinuous hdifferentiable

/-- Lower-left corner of the inscribed square of circular radius `ε` around a raw
singular coordinate. -/
def explicitFormulaRectangleRawInscribedSquareLowerCorner (ε : ℝ) (a : ℂ) : ℂ :=
  finiteRectangleSquareLowerCorner a (ε / 2)

/-- Upper-right corner of the inscribed square of circular radius `ε` around a raw
singular coordinate. -/
def explicitFormulaRectangleRawInscribedSquareUpperCorner (ε : ℝ) (a : ℂ) : ℂ :=
  finiteRectangleSquareUpperCorner a (ε / 2)

/-- The lower-left corner of the raw inscribed square is the lower-left corner of the
ordinary deleted square at half-width `ε / 2`. -/
theorem explicitFormulaRectangleRawInscribedSquareLowerCorner_eq_squareLowerCorner_half
    (ε : ℝ) (a : ℂ) :
    explicitFormulaRectangleRawInscribedSquareLowerCorner ε a =
      finiteRectangleSquareLowerCorner a (ε / 2) := by
  rfl

/-- The upper-right corner of the raw inscribed square is the upper-right corner of the
ordinary deleted square at half-width `ε / 2`. -/
theorem explicitFormulaRectangleRawInscribedSquareUpperCorner_eq_squareUpperCorner_half
    (ε : ℝ) (a : ℂ) :
    explicitFormulaRectangleRawInscribedSquareUpperCorner ε a =
      finiteRectangleSquareUpperCorner a (ε / 2) := by
  rfl

/-- Closed cell of the inscribed square of circular radius `ε` around a raw singular
coordinate. -/
def explicitFormulaRectangleRawInscribedSquareClosedCell (ε : ℝ) (a : ℂ) : Set ℂ :=
  [[ (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).re,
      (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).re ]] ×ℂ
    [[ (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).im,
      (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).im ]]

/-- The named inscribed-square closed cell is the closed rectangle between the named
lower-left and upper-right corners. -/
theorem explicitFormulaRectangleRawInscribedSquareClosedCell_eq
    (ε : ℝ) (a : ℂ) :
    explicitFormulaRectangleRawInscribedSquareClosedCell ε a =
      ([[ (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).re,
          (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).re ]] ×ℂ
        [[ (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).im,
          (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).im ]]) := by
  rfl

/-- A point in the named inscribed-square closed cell has its real coordinate in the
cell's closed real interval. -/
theorem explicitFormulaRectangleRawInscribedSquareClosedCell_re_mem
    (ε : ℝ) (a z : ℂ)
    (hz : z ∈ explicitFormulaRectangleRawInscribedSquareClosedCell ε a) :
    z.re ∈
      [[ (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).re,
        (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).re ]] :=
  hz.1

/-- A point in the named inscribed-square closed cell has its imaginary coordinate in the
cell's closed imaginary interval. -/
theorem explicitFormulaRectangleRawInscribedSquareClosedCell_im_mem
    (ε : ℝ) (a z : ℂ)
    (hz : z ∈ explicitFormulaRectangleRawInscribedSquareClosedCell ε a) :
    z.im ∈
      [[ (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).im,
        (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).im ]] :=
  hz.2

/-- Membership in the named inscribed-square closed cell is equivalent to the two
coordinate interval memberships. -/
theorem explicitFormulaRectangleRawInscribedSquareClosedCell_mem_iff
    (ε : ℝ) (a z : ℂ) :
    z ∈ explicitFormulaRectangleRawInscribedSquareClosedCell ε a ↔
      z.re ∈
        [[ (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).re,
          (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).re ]] ∧
        z.im ∈
          [[ (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).im,
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).im ]] := by
  exact Iff.rfl

/-- Transport membership in an unordered closed interval across endpoint equalities. -/
theorem finiteRectangle_mem_uIcc_congr_endpoints
    {x a b c d : ℝ} (ha : a = c) (hb : b = d)
    (hx : x ∈ [[a, b]]) :
    x ∈ [[c, d]] :=
  match ha, hb with
  | rfl, rfl => hx

/-- Membership in the closed interval `[c - r, c + r]` bounds displacement from `c`. -/
theorem finiteRectangle_mem_uIcc_sub_add_abs_sub_le
    {c r x : ℝ} (hr : 0 ≤ r)
    (hx : x ∈ [[c - r, c + r]]) :
    |x - c| ≤ r := by
  have hleft : c - r ≤ c :=
    sub_le_self c hr
  have hright : c ≤ c + r :=
    le_add_of_nonneg_right hr
  have hordered : c - r ≤ c + r :=
    le_trans hleft hright
  have hxIcc : x ∈ Set.Icc (c - r) (c + r) :=
    Eq.subst
      (motive := fun s : Set ℝ => x ∈ s)
      (Set.uIcc_of_le hordered)
      hx
  have hx_lower : c - r ≤ x :=
    hxIcc.1
  have hx_upper : x ≤ c + r :=
    hxIcc.2
  have hupper : x - c ≤ r :=
    sub_le_iff_le_add'.2 hx_upper
  have hlower : c - x ≤ r :=
    sub_le_comm.1 hx_lower
  exact abs_sub_le_iff.2 (And.intro hupper hlower)

/-- Real coordinate of the lower-left corner of a raw inscribed square. -/
theorem explicitFormulaRectangleRawInscribedSquareLowerCorner_re
    (ε : ℝ) (a : ℂ) :
    (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).re =
      a.re - ε / 2 :=
  finiteRectangleSquareLowerCorner_re a (ε / 2)

/-- The real coordinate of the raw inscribed-square lower-left corner is the real
coordinate of the deleted-square lower-left corner at half-width `ε / 2`. -/
theorem explicitFormulaRectangleRawInscribedSquareLowerCorner_re_eq_squareLowerCorner_half_re
    (ε : ℝ) (a : ℂ) :
    (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).re =
      (finiteRectangleSquareLowerCorner a (ε / 2)).re := by
  exact congrArg Complex.re
    (explicitFormulaRectangleRawInscribedSquareLowerCorner_eq_squareLowerCorner_half ε a)

/-- Imaginary coordinate of the lower-left corner of a raw inscribed square. -/
theorem explicitFormulaRectangleRawInscribedSquareLowerCorner_im
    (ε : ℝ) (a : ℂ) :
    (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).im =
      a.im - ε / 2 :=
  finiteRectangleSquareLowerCorner_im a (ε / 2)

/-- The imaginary coordinate of the raw inscribed-square lower-left corner is the imaginary
coordinate of the deleted-square lower-left corner at half-width `ε / 2`. -/
theorem explicitFormulaRectangleRawInscribedSquareLowerCorner_im_eq_squareLowerCorner_half_im
    (ε : ℝ) (a : ℂ) :
    (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).im =
      (finiteRectangleSquareLowerCorner a (ε / 2)).im := by
  exact congrArg Complex.im
    (explicitFormulaRectangleRawInscribedSquareLowerCorner_eq_squareLowerCorner_half ε a)

/-- Real coordinate of the upper-right corner of a raw inscribed square. -/
theorem explicitFormulaRectangleRawInscribedSquareUpperCorner_re
    (ε : ℝ) (a : ℂ) :
    (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).re =
      a.re + ε / 2 :=
  finiteRectangleSquareUpperCorner_re a (ε / 2)

/-- The real coordinate of the raw inscribed-square upper-right corner is the real
coordinate of the deleted-square upper-right corner at half-width `ε / 2`. -/
theorem explicitFormulaRectangleRawInscribedSquareUpperCorner_re_eq_squareUpperCorner_half_re
    (ε : ℝ) (a : ℂ) :
    (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).re =
      (finiteRectangleSquareUpperCorner a (ε / 2)).re := by
  exact congrArg Complex.re
    (explicitFormulaRectangleRawInscribedSquareUpperCorner_eq_squareUpperCorner_half ε a)

/-- Imaginary coordinate of the upper-right corner of a raw inscribed square. -/
theorem explicitFormulaRectangleRawInscribedSquareUpperCorner_im
    (ε : ℝ) (a : ℂ) :
    (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).im =
      a.im + ε / 2 :=
  finiteRectangleSquareUpperCorner_im a (ε / 2)

/-- The imaginary coordinate of the raw inscribed-square upper-right corner is the
imaginary coordinate of the deleted-square upper-right corner at half-width `ε / 2`. -/
theorem explicitFormulaRectangleRawInscribedSquareUpperCorner_im_eq_squareUpperCorner_half_im
    (ε : ℝ) (a : ℂ) :
    (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).im =
      (finiteRectangleSquareUpperCorner a (ε / 2)).im := by
  exact congrArg Complex.im
    (explicitFormulaRectangleRawInscribedSquareUpperCorner_eq_squareUpperCorner_half ε a)

/-- The lower-left corner of a raw inscribed square is strictly left of its upper-right
corner for positive circular radius. -/
theorem explicitFormulaRectangleRawInscribedSquareLowerCorner_re_lt_upperCorner_re
    {ε : ℝ} (hε : 0 < ε) (a : ℂ) :
    (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).re <
      (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).re :=
  finiteRectangleSquareLowerCorner_re_lt_upperCorner_re a (half_pos hε)

/-- The lower-left corner of a raw inscribed square is strictly below its upper-right
corner for positive circular radius. -/
theorem explicitFormulaRectangleRawInscribedSquareLowerCorner_im_lt_upperCorner_im
    {ε : ℝ} (hε : 0 < ε) (a : ℂ) :
    (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).im <
      (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).im :=
  finiteRectangleSquareLowerCorner_im_lt_upperCorner_im a (half_pos hε)

/-- A point in a raw inscribed square has real-coordinate displacement at most
`ε / 2` from the square center. -/
theorem explicitFormulaRectangleRawInscribedSquareClosedCell_re_abs_sub_le_half
    {ε : ℝ} (hε : 0 ≤ ε) (a z : ℂ)
    (hz : z ∈ explicitFormulaRectangleRawInscribedSquareClosedCell ε a) :
    |z.re - a.re| ≤ ε / 2 := by
  have hmem :
      z.re ∈
        [[ (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).re,
          (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).re ]] :=
    explicitFormulaRectangleRawInscribedSquareClosedCell_re_mem ε a z hz
  have hmem_center :
      z.re ∈ [[a.re - ε / 2, a.re + ε / 2]] :=
    finiteRectangle_mem_uIcc_congr_endpoints
      (explicitFormulaRectangleRawInscribedSquareLowerCorner_re ε a)
      (explicitFormulaRectangleRawInscribedSquareUpperCorner_re ε a)
      hmem
  exact
    finiteRectangle_mem_uIcc_sub_add_abs_sub_le
      (half_nonneg hε)
      hmem_center

/-- A point in a raw inscribed square has imaginary-coordinate displacement at most
`ε / 2` from the square center. -/
theorem explicitFormulaRectangleRawInscribedSquareClosedCell_im_abs_sub_le_half
    {ε : ℝ} (hε : 0 ≤ ε) (a z : ℂ)
    (hz : z ∈ explicitFormulaRectangleRawInscribedSquareClosedCell ε a) :
    |z.im - a.im| ≤ ε / 2 := by
  have hmem :
      z.im ∈
        [[ (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).im,
          (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).im ]] :=
    explicitFormulaRectangleRawInscribedSquareClosedCell_im_mem ε a z hz
  have hmem_center :
      z.im ∈ [[a.im - ε / 2, a.im + ε / 2]] :=
    finiteRectangle_mem_uIcc_congr_endpoints
      (explicitFormulaRectangleRawInscribedSquareLowerCorner_im ε a)
      (explicitFormulaRectangleRawInscribedSquareUpperCorner_im ε a)
      hmem
  exact
    finiteRectangle_mem_uIcc_sub_add_abs_sub_le
      (half_nonneg hε)
      hmem_center

/-- A point in a raw inscribed square is within circular radius `ε` of the square
center. -/
theorem explicitFormulaRectangleRawInscribedSquareClosedCell_abs_sub_le
    {ε : ℝ} (hε : 0 ≤ ε) (a z : ℂ)
    (hz : z ∈ explicitFormulaRectangleRawInscribedSquareClosedCell ε a) :
    Complex.abs (z - a) ≤ ε := by
  have hre_center :
      |z.re - a.re| ≤ ε / 2 :=
    explicitFormulaRectangleRawInscribedSquareClosedCell_re_abs_sub_le_half
      hε a z hz
  have him_center :
      |z.im - a.im| ≤ ε / 2 :=
    explicitFormulaRectangleRawInscribedSquareClosedCell_im_abs_sub_le_half
      hε a z hz
  have hre :
      |(z - a).re| ≤ ε / 2 :=
    Eq.subst
      (motive := fun x : ℝ => |x| ≤ ε / 2)
      (Complex.sub_re z a).symm
      hre_center
  have him :
      |(z - a).im| ≤ ε / 2 :=
    Eq.subst
      (motive := fun x : ℝ => |x| ≤ ε / 2)
      (Complex.sub_im z a).symm
      him_center
  have hsum :
      |(z - a).re| + |(z - a).im| ≤ ε / 2 + ε / 2 :=
    add_le_add hre him
  calc
    Complex.abs (z - a) ≤ |(z - a).re| + |(z - a).im| := by
      exact Complex.abs_le_abs_re_add_abs_im (z - a)
    _ ≤ ε / 2 + ε / 2 := by
      exact hsum
    _ = ε := by
      exact add_halves ε

/-- The raw inscribed-square closed cell is contained in the closed metric ball of its
circular radius. -/
theorem explicitFormulaRectangleRawInscribedSquareClosedCell_subset_closedBall
    {ε : ℝ} (hε : 0 ≤ ε) (a : ℂ) :
    explicitFormulaRectangleRawInscribedSquareClosedCell ε a ⊆
      Metric.closedBall a ε := by
  intro z hz
  have habs :
      Complex.abs (z - a) ≤ ε :=
    explicitFormulaRectangleRawInscribedSquareClosedCell_abs_sub_le hε a z hz
  have hnorm :
      ‖z - a‖ ≤ ε :=
    Eq.subst
      (motive := fun x : ℝ => x ≤ ε)
      (Complex.norm_eq_abs (z - a)).symm
      habs
  have hdist :
      dist z a ≤ ε := by
    calc
      dist z a = ‖z - a‖ := by
        exact dist_eq_norm z a
      _ ≤ ε := by
        exact hnorm
  exact Metric.mem_closedBall.mpr hdist

/-- The half-radius raw inscribed-square closed cell, whose square half-width is
`(ε / 2) / 2`, is contained in the selected closed ball of radius `ε`. -/
theorem explicitFormulaRectangleRawInscribedSquareClosedCell_half_subset_closedBall
    {ε : ℝ} (hε : 0 < ε) (a : ℂ) :
    explicitFormulaRectangleRawInscribedSquareClosedCell (ε / 2) a ⊆
      Metric.closedBall a ε := by
  exact Set.Subset.trans
    (explicitFormulaRectangleRawInscribedSquareClosedCell_subset_closedBall
      (finiteRectangle_halfRadius_nonneg hε) a)
    (finiteRectangle_closedBall_subset_of_radius_le
      (finiteRectangle_halfRadius_le_self hε))

/-- Under closed-radius controls, the half-radius raw inscribed-square closed cell lies in
the contour-family interior. -/
theorem explicitFormulaRectangleRawInscribedSquareClosedCell_half_subset_interior_of_closedRadiusControls
    (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (hε : 0 < ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    (a : ℂ)
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    explicitFormulaRectangleRawInscribedSquareClosedCell (ε / 2) a ⊆
      explicitFormulaContourFamilyInterior F T :=
  Set.Subset.trans
    (explicitFormulaRectangleRawInscribedSquareClosedCell_half_subset_closedBall hε a)
    (hclosed a ha)

/-- Under closed-radius controls, each raw inscribed-square closed cell lies in the
contour-family interior. -/
theorem explicitFormulaRectangleRawInscribedSquareClosedCell_subset_interior_of_closedRadiusControls
    (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (hε : 0 ≤ ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    (a : ℂ)
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    explicitFormulaRectangleRawInscribedSquareClosedCell ε a ⊆
      explicitFormulaContourFamilyInterior F T := by
  exact Set.Subset.trans
    (explicitFormulaRectangleRawInscribedSquareClosedCell_subset_closedBall hε a)
    (hclosed a ha)

/-- Under closed-radius controls, distinct raw inscribed-square closed cells are
pairwise disjoint. -/
theorem explicitFormulaRectangleRawInscribedSquareClosedCell_pairwiseDisjoint_of_closedRadiusControls
    (T ε : ℝ)
    (hε : 0 ≤ ε)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b →
                Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
    (a : ℂ)
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (b : ℂ)
    (hb : b ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (hab : a ≠ b) :
    Disjoint
      (explicitFormulaRectangleRawInscribedSquareClosedCell ε a)
      (explicitFormulaRectangleRawInscribedSquareClosedCell ε b) := by
  exact Set.disjoint_of_subset
    (explicitFormulaRectangleRawInscribedSquareClosedCell_subset_closedBall hε a)
    (explicitFormulaRectangleRawInscribedSquareClosedCell_subset_closedBall hε b)
    (hsep a ha b hb hab)

/-- The center of a raw inscribed square belongs to its named closed cell. -/
theorem explicitFormulaRectangleRawSingular_mem_own_inscribedSquareClosedCell
    {ε : ℝ} (hε : 0 ≤ ε) (a : ℂ) :
    a ∈ explicitFormulaRectangleRawInscribedSquareClosedCell ε a := by
  have hhalf_nonneg : 0 ≤ ε / 2 :=
    half_nonneg hε
  have hre_left : a.re - ε / 2 ≤ a.re :=
    sub_le_self a.re hhalf_nonneg
  have hre_right : a.re ≤ a.re + ε / 2 :=
    le_add_of_nonneg_right hhalf_nonneg
  have him_left : a.im - ε / 2 ≤ a.im :=
    sub_le_self a.im hhalf_nonneg
  have him_right : a.im ≤ a.im + ε / 2 :=
    le_add_of_nonneg_right hhalf_nonneg
  have hre_center :
      a.re ∈ [[a.re - ε / 2, a.re + ε / 2]] :=
    Set.mem_uIcc.mpr (Or.inl (And.intro hre_left hre_right))
  have him_center :
      a.im ∈ [[a.im - ε / 2, a.im + ε / 2]] :=
    Set.mem_uIcc.mpr (Or.inl (And.intro him_left him_right))
  have hre :
      a.re ∈
        [[ (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).re,
          (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).re ]] :=
    finiteRectangle_mem_uIcc_congr_endpoints
      (explicitFormulaRectangleRawInscribedSquareLowerCorner_re ε a).symm
      (explicitFormulaRectangleRawInscribedSquareUpperCorner_re ε a).symm
      hre_center
  have him :
      a.im ∈
        [[ (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).im,
          (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).im ]] :=
    finiteRectangle_mem_uIcc_congr_endpoints
      (explicitFormulaRectangleRawInscribedSquareLowerCorner_im ε a).symm
      (explicitFormulaRectangleRawInscribedSquareUpperCorner_im ε a).symm
      him_center
  exact And.intro hre him

/-- The lower-left corner of a raw inscribed square belongs to its named closed cell. -/
theorem explicitFormulaRectangleRawInscribedSquareLowerCorner_mem_closedCell
    (ε : ℝ) (a : ℂ) :
    explicitFormulaRectangleRawInscribedSquareLowerCorner ε a ∈
      explicitFormulaRectangleRawInscribedSquareClosedCell ε a := by
  have hre :
      (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).re ∈
        [[ (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).re,
          (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).re ]] :=
    Set.left_mem_uIcc
  have him :
      (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).im ∈
        [[ (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).im,
          (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).im ]] :=
    Set.left_mem_uIcc
  exact And.intro hre him

/-- The upper-right corner of a raw inscribed square belongs to its named closed cell. -/
theorem explicitFormulaRectangleRawInscribedSquareUpperCorner_mem_closedCell
    (ε : ℝ) (a : ℂ) :
    explicitFormulaRectangleRawInscribedSquareUpperCorner ε a ∈
      explicitFormulaRectangleRawInscribedSquareClosedCell ε a := by
  have hre :
      (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).re ∈
        [[ (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).re,
          (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).re ]] :=
    Set.right_mem_uIcc
  have him :
      (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).im ∈
        [[ (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).im,
          (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).im ]] :=
    Set.right_mem_uIcc
  exact And.intro hre him

/-- Under closed-radius controls, the lower-left corner of every raw inscribed square lies
in the contour-family interior. -/
theorem explicitFormulaRectangleRawInscribedSquareLowerCorner_mem_interior_of_closedRadiusControls
    (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (hε : 0 ≤ ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    (a : ℂ)
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    explicitFormulaRectangleRawInscribedSquareLowerCorner ε a ∈
      explicitFormulaContourFamilyInterior F T :=
  explicitFormulaRectangleRawInscribedSquareClosedCell_subset_interior_of_closedRadiusControls
    F T ε hε hclosed a ha
    (explicitFormulaRectangleRawInscribedSquareLowerCorner_mem_closedCell ε a)

/-- Under closed-radius controls, the upper-right corner of every raw inscribed square lies
in the contour-family interior. -/
theorem explicitFormulaRectangleRawInscribedSquareUpperCorner_mem_interior_of_closedRadiusControls
    (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (hε : 0 ≤ ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    (a : ℂ)
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    explicitFormulaRectangleRawInscribedSquareUpperCorner ε a ∈
      explicitFormulaContourFamilyInterior F T :=
  explicitFormulaRectangleRawInscribedSquareClosedCell_subset_interior_of_closedRadiusControls
    F T ε hε hclosed a ha
    (explicitFormulaRectangleRawInscribedSquareUpperCorner_mem_closedCell ε a)

/-- A set disjoint from every removed raw inscribed square avoids the raw singular carrier.
This is the point-exclusion step used by complement-cell subdivisions. -/
theorem explicitFormulaRectangleRawSingularCoordinates_not_mem_of_disjoint_inscribedSquares
    (T ε : ℝ) (hε : 0 ≤ ε) (R : Set ℂ)
    (hdisjoint :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Disjoint R (explicitFormulaRectangleRawInscribedSquareClosedCell ε a))
    {z : ℂ}
    (hz : z ∈ R) :
    z ∉ explicitFormulaRectangleRawSingularCoordinates T := by
  intro hzRaw
  have hzOwn :
      z ∈ explicitFormulaRectangleRawInscribedSquareClosedCell ε z :=
    explicitFormulaRectangleRawSingular_mem_own_inscribedSquareClosedCell hε z
  exact
    (Set.disjoint_left.mp (hdisjoint z hzRaw)) hz hzOwn

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
