import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicircleCoreCauchy

/-!
# Finite-hole subdivision for the Abel-Plana punctured rectangle

This file owns the generic punctured-collar boundary, vertical strip and
horizontal subdivision vocabulary, and the finite-hole boundary identification
used before the endpoint/interior cap-collar Cauchy balances.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology


/-- Unnormalized oriented boundary of a horizontal punctured rectangular
collar.

The convention is the same as mathlib's rectangle Cauchy theorem: bottom minus
top plus `I` times the right side minus `I` times the left side.  The final
term is the clockwise inner boundary, written as minus the standard
counterclockwise `circleIntegral`. -/
noncomputable def Complex.finiteAbelPlanaLogPuncturedRectangularCollarBoundary
    (w : ℂ)
    (x₀ x₁ : ℝ)
    (T : ℝ)
    (c : ℂ)
    (ρ : ℝ) : ℂ :=
  (∫ x : ℝ in x₀..x₁,
      Complex.finiteAbelPlanaLogRectangleIntegrand w
        ((x : ℂ) - Complex.I * (T : ℂ))) -
    (∫ x : ℝ in x₀..x₁,
      Complex.finiteAbelPlanaLogRectangleIntegrand w
        ((x : ℂ) + Complex.I * (T : ℂ))) +
      Complex.I *
        (∫ y : ℝ in (-T)..T,
          Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((x₁ : ℂ) + Complex.I * (y : ℂ))) -
        Complex.I *
          (∫ y : ℝ in (-T)..T,
            Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((x₀ : ℂ) + Complex.I * (y : ℂ))) -
          circleIntegral
            (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
            c
            ρ

/-- Unfolding of the punctured rectangular collar boundary into its four
straight sides and clockwise circular inner boundary. -/
theorem Complex.finiteAbelPlana_log_puncturedRectangularCollarBoundary_unfold
    (w : ℂ)
    (x₀ x₁ : ℝ)
    (T : ℝ)
    (c : ℂ)
    (ρ : ℝ) :
    Complex.finiteAbelPlanaLogPuncturedRectangularCollarBoundary w x₀ x₁ T c ρ =
      (∫ x : ℝ in x₀..x₁,
          Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((x : ℂ) - Complex.I * (T : ℂ))) -
        (∫ x : ℝ in x₀..x₁,
          Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((x : ℂ) + Complex.I * (T : ℂ))) +
          Complex.I *
            (∫ y : ℝ in (-T)..T,
              Complex.finiteAbelPlanaLogRectangleIntegrand w
                ((x₁ : ℂ) + Complex.I * (y : ℂ))) -
            Complex.I *
              (∫ y : ℝ in (-T)..T,
                Complex.finiteAbelPlanaLogRectangleIntegrand w
                  ((x₀ : ℂ) + Complex.I * (y : ℂ))) -
              circleIntegral
                (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
                c
                ρ := by
  rfl

/-- The Abel-Plana punctured rectangular collar boundary is the generic
punctured rectangular collar boundary specialized to the logarithmic cotangent
rectangle integrand. -/
theorem Complex.finiteAbelPlana_log_puncturedRectangularCollarBoundary_eq_generic
    (w : ℂ)
    (x₀ x₁ T : ℝ)
    (c : ℂ)
    (ρ : ℝ) :
    Complex.finiteAbelPlanaLogPuncturedRectangularCollarBoundary w x₀ x₁ T c ρ =
      Complex.puncturedRectangularCollarBoundaryIntegral
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        x₀ x₁ T c ρ := by
  rfl

/-- Annular Cauchy-Goursat reduction for the curved boundary component of a
punctured rectangular collar.

This is the canonical mathlib reduction for the round part of the collar: on
any annulus contained in the punctured rectangle, the two circular contour
integrals agree.  It is deliberately stated with `DifferentiableAt` on the
open annulus, matching mathlib's annulus API. -/
theorem Complex.finiteAbelPlana_log_annulusCircleIntegral_eq_of_subset_puncturedRectangle
    {w c : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ r R : ℝ}
    (hr : 0 < r)
    (hrR : r ≤ R)
    (hclosed :
      (Metric.closedBall c R \ Metric.ball c r) ⊆
        Complex.finiteAbelPlanaPuncturedRectangle N T ρ)
    (hopen :
      (Metric.ball c R \ Metric.closedBall c r) ⊆
        Complex.finiteAbelPlanaPuncturedRectangle N T ρ)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      ∀ z ∈ Complex.finiteAbelPlanaPuncturedRectangle N T ρ,
        DifferentiableAt ℂ
          (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z) z) :
    circleIntegral
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        c
        R =
      circleIntegral
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        c
        r := by
  exact
    Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
      hr
      hrR
      Set.countable_empty
      (hcont.mono hclosed)
      (fun z hz => hdiff z (hopen ⟨hz.1.1, hz.1.2⟩))

/-- A finite family of ordinary subrectangles contained in the punctured
Abel-Plana rectangle contributes zero total boundary integral before internal
edge cancellation is performed. -/
theorem Complex.finiteAbelPlana_log_sum_rectangleBoundaryIntegral_eq_zero_of_subset_puncturedRectangle_of_holomorphic
    {ι : Type}
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (s : Finset ι)
    (z₀ z₁ : ι → ℂ)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hclosed :
      ∀ i ∈ s,
        ([[((z₀ i).re), ((z₁ i).re)]] ×ℂ
          [[((z₀ i).im), ((z₁ i).im)]]) ⊆
          Complex.finiteAbelPlanaPuncturedRectangle N T ρ)
    (hopen :
      ∀ i ∈ s,
        (Set.Ioo (min (z₀ i).re (z₁ i).re) (max (z₀ i).re (z₁ i).re) ×ℂ
          Set.Ioo (min (z₀ i).im (z₁ i).im) (max (z₀ i).im (z₁ i).im)) ⊆
          Complex.finiteAbelPlanaPuncturedRectangle N T ρ) :
    (∑ i in s,
      Complex.finiteAbelPlanaLogRectangleBoundaryIntegral w (z₀ i) (z₁ i)) =
      0 := by
  exact
    Finset.sum_eq_zero
      (fun i hi =>
        Complex.finiteAbelPlana_log_rectangleBoundaryIntegral_eq_zero_of_subset_puncturedRectangle_of_holomorphic
          N T (z₀ i) (z₁ i) hcont hdiff (hclosed i hi) (hopen i hi))

/-- Lower-left corner of the puncture-free vertical strip between the integer
centers `n` and `n + 1`, after deleting radius `ρ`. -/
noncomputable def Complex.finiteAbelPlanaVerticalStripLowerLeftCorner
    (n : ℕ)
    (T ρ : ℝ) : ℂ :=
  (((n : ℝ) + ρ : ℝ) : ℂ) - (T : ℂ) * Complex.I

/-- Upper-right corner of the puncture-free vertical strip between the integer
centers `n` and `n + 1`, after deleting radius `ρ`. -/
noncomputable def Complex.finiteAbelPlanaVerticalStripUpperRightCorner
    (n : ℕ)
    (T ρ : ℝ) : ℂ :=
  (((n + 1 : ℕ) : ℝ) - ρ : ℝ) + (T : ℂ) * Complex.I

/-- Cauchy-Goursat for one puncture-free vertical strip in the finite
Abel-Plana rectangle.

The two inclusion hypotheses are the honest geometry obligations for this
strip: the closed strip must avoid the deleted disks, and its open interior
must lie in the punctured rectangle.  The analytic step is then exactly the
ordinary rectangle Cauchy theorem above. -/
theorem Complex.finiteAbelPlana_log_verticalStripBoundaryIntegral_eq_zero_of_subset_puncturedRectangle
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (n : ℕ)
    (hclosed :
      ([[(Complex.finiteAbelPlanaVerticalStripLowerLeftCorner n T ρ).re,
          (Complex.finiteAbelPlanaVerticalStripUpperRightCorner n T ρ).re]] ×ℂ
        [[(Complex.finiteAbelPlanaVerticalStripLowerLeftCorner n T ρ).im,
          (Complex.finiteAbelPlanaVerticalStripUpperRightCorner n T ρ).im]]) ⊆
        Complex.finiteAbelPlanaPuncturedRectangle N T ρ)
    (hopen :
      (Set.Ioo
          (min
            (Complex.finiteAbelPlanaVerticalStripLowerLeftCorner n T ρ).re
            (Complex.finiteAbelPlanaVerticalStripUpperRightCorner n T ρ).re)
          (max
            (Complex.finiteAbelPlanaVerticalStripLowerLeftCorner n T ρ).re
            (Complex.finiteAbelPlanaVerticalStripUpperRightCorner n T ρ).re) ×ℂ
        Set.Ioo
          (min
            (Complex.finiteAbelPlanaVerticalStripLowerLeftCorner n T ρ).im
            (Complex.finiteAbelPlanaVerticalStripUpperRightCorner n T ρ).im)
          (max
            (Complex.finiteAbelPlanaVerticalStripLowerLeftCorner n T ρ).im
            (Complex.finiteAbelPlanaVerticalStripUpperRightCorner n T ρ).im)) ⊆
        Complex.finiteAbelPlanaPuncturedRectangle N T ρ) :
    Complex.finiteAbelPlanaLogRectangleBoundaryIntegral w
      (Complex.finiteAbelPlanaVerticalStripLowerLeftCorner n T ρ)
      (Complex.finiteAbelPlanaVerticalStripUpperRightCorner n T ρ) = 0 := by
  exact
    Complex.finiteAbelPlana_log_rectangleBoundaryIntegral_eq_zero_of_subset_puncturedRectangle
      hw N T hρ
      (Complex.finiteAbelPlanaVerticalStripLowerLeftCorner n T ρ)
      (Complex.finiteAbelPlanaVerticalStripUpperRightCorner n T ρ)
      hclosed hopen

/-- The finite strip indices for the vertical gaps between consecutive deleted
integer disks.  Index `k` denotes the gap between the deleted disks centered at
`k` and `k + 1`; hence there are `N + 1` such strips. -/
def Complex.finiteAbelPlanaVerticalStripIndexSet
    (N : ℕ) : Finset ℕ :=
  Finset.range (N + 1)

/-- The same finite strip indexing data as a list, for consumers that need an
ordered subdivision rather than a finite sum. -/
def Complex.finiteAbelPlanaVerticalStripList
    (N : ℕ) : List ℕ :=
  (Complex.finiteAbelPlanaVerticalStripIndexSet N).toList

/-- Left real coordinate of the vertical gap strip between the deleted disks
centered at `k` and `k + 1`. -/
def Complex.finiteAbelPlanaVerticalStripLeft
    (k : ℕ)
    (ρ : ℝ) : ℝ :=
  (k : ℝ) + ρ

/-- Right real coordinate of the vertical gap strip between the deleted disks
centered at `k` and `k + 1`. -/
def Complex.finiteAbelPlanaVerticalStripRight
    (k : ℕ)
    (ρ : ℝ) : ℝ :=
  ((k + 1 : ℕ) : ℝ) - ρ

/-- The closed vertical gap strip between the deleted disks centered at `k`
and `k + 1`, cut off at finite height `T`. -/
def Complex.finiteAbelPlanaVerticalStrip
    (k : ℕ)
    (T ρ : ℝ) : Set ℂ :=
  [[Complex.finiteAbelPlanaVerticalStripLeft k ρ,
    Complex.finiteAbelPlanaVerticalStripRight k ρ]] ×ℂ [[-T, T]]

/-- The finite union of the vertical gap strips in the Abel-Plana punctured
rectangle decomposition. -/
def Complex.finiteAbelPlanaVerticalStripUnion
    (N : ℕ)
    (T ρ : ℝ) : Set ℂ :=
  ⋃ k ∈ Complex.finiteAbelPlanaVerticalStripIndexSet N,
    Complex.finiteAbelPlanaVerticalStrip k T ρ

/-- Unfolding of the finite vertical strip index set. -/
theorem Complex.finiteAbelPlana_verticalStripIndexSet_unfold
    (N : ℕ) :
    Complex.finiteAbelPlanaVerticalStripIndexSet N = Finset.range (N + 1) := by
  rfl

/-- Membership in the finite vertical strip index set. -/
theorem Complex.mem_finiteAbelPlanaVerticalStripIndexSet_iff
    {N k : ℕ} :
    k ∈ Complex.finiteAbelPlanaVerticalStripIndexSet N ↔ k < N + 1 := by
  exact Finset.mem_range

/-- Unfolding of the left coordinate of a vertical gap strip. -/
theorem Complex.finiteAbelPlana_verticalStripLeft_unfold
    (k : ℕ)
    (ρ : ℝ) :
    Complex.finiteAbelPlanaVerticalStripLeft k ρ = (k : ℝ) + ρ := by
  rfl

/-- Unfolding of the right coordinate of a vertical gap strip. -/
theorem Complex.finiteAbelPlana_verticalStripRight_unfold
    (k : ℕ)
    (ρ : ℝ) :
    Complex.finiteAbelPlanaVerticalStripRight k ρ =
      ((k + 1 : ℕ) : ℝ) - ρ := by
  rfl

/-- Unfolding of a finite vertical gap strip. -/
theorem Complex.finiteAbelPlana_verticalStrip_unfold
    (k : ℕ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaVerticalStrip k T ρ =
      [[Complex.finiteAbelPlanaVerticalStripLeft k ρ,
        Complex.finiteAbelPlanaVerticalStripRight k ρ]] ×ℂ [[-T, T]] := by
  rfl

/-- Unfolding of the finite union of vertical gap strips. -/
theorem Complex.finiteAbelPlana_verticalStripUnion_unfold
    (N : ℕ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaVerticalStripUnion N T ρ =
      ⋃ k ∈ Complex.finiteAbelPlanaVerticalStripIndexSet N,
        Complex.finiteAbelPlanaVerticalStrip k T ρ := by
  rfl

/-- Lower horizontal side of one finite vertical gap strip. -/
noncomputable def Complex.finiteAbelPlanaLogVerticalStripLowerSide
    (k : ℕ)
    (w : ℂ)
    (T ρ : ℝ) : ℂ :=
  ∫ x : ℝ in
      (Complex.finiteAbelPlanaVerticalStripLeft k ρ)..
        (Complex.finiteAbelPlanaVerticalStripRight k ρ),
    Complex.finiteAbelPlanaLogRectangleIntegrand w
      ((x : ℂ) - Complex.I * (T : ℂ))

/-- Upper horizontal side of one finite vertical gap strip. -/
noncomputable def Complex.finiteAbelPlanaLogVerticalStripUpperSide
    (k : ℕ)
    (w : ℂ)
    (T ρ : ℝ) : ℂ :=
  ∫ x : ℝ in
      (Complex.finiteAbelPlanaVerticalStripLeft k ρ)..
        (Complex.finiteAbelPlanaVerticalStripRight k ρ),
    Complex.finiteAbelPlanaLogRectangleIntegrand w
      ((x : ℂ) + Complex.I * (T : ℂ))

/-- Left vertical side of one finite vertical gap strip. -/
noncomputable def Complex.finiteAbelPlanaLogVerticalStripLeftSide
    (k : ℕ)
    (w : ℂ)
    (T ρ : ℝ) : ℂ :=
  ∫ y : ℝ in (-T)..T,
    Complex.finiteAbelPlanaLogRectangleIntegrand w
      ((Complex.finiteAbelPlanaVerticalStripLeft k ρ : ℂ) +
        Complex.I * (y : ℂ))

/-- Right vertical side of one finite vertical gap strip. -/
noncomputable def Complex.finiteAbelPlanaLogVerticalStripRightSide
    (k : ℕ)
    (w : ℂ)
    (T ρ : ℝ) : ℂ :=
  ∫ y : ℝ in (-T)..T,
    Complex.finiteAbelPlanaLogRectangleIntegrand w
      ((Complex.finiteAbelPlanaVerticalStripRight k ρ : ℂ) +
        Complex.I * (y : ℂ))

/-- Normalized oriented boundary integral of one vertical gap strip in the same
side convention as the finite Abel-Plana rectangle. -/
noncomputable def Complex.finiteAbelPlanaLogVerticalStripBoundaryIntegral
    (k : ℕ)
    (w : ℂ)
    (T ρ : ℝ) : ℂ :=
  ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
    (Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ -
      Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ +
        Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide k w T ρ -
          Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide k w T ρ)

/-- One concrete vertical gap strip is the normalized version of the abstract
oriented vertical-strip side expression. -/
theorem Complex.finiteAbelPlana_log_verticalStripBoundaryIntegral_eq_normalized_sideExpression
    (k : ℕ)
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogVerticalStripBoundaryIntegral k w T ρ =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        Complex.finiteAbelPlanaLogVerticalStripSideExpression
          w
          (Complex.finiteAbelPlanaVerticalStripLeft k ρ)
          (Complex.finiteAbelPlanaVerticalStripRight k ρ)
          (-T)
          T := by
  dsimp [Complex.finiteAbelPlanaLogVerticalStripBoundaryIntegral,
    Complex.finiteAbelPlanaLogVerticalStripSideExpression,
    Complex.finiteAbelPlanaLogVerticalStripLowerSide,
    Complex.finiteAbelPlanaLogVerticalStripUpperSide,
    Complex.finiteAbelPlanaLogVerticalStripLeftSide,
    Complex.finiteAbelPlanaLogVerticalStripRightSide,
    Complex.finiteAbelPlanaLogVerticalStripLowerEdge,
    Complex.finiteAbelPlanaLogVerticalStripUpperEdge,
    Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution,
    Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution,
    Complex.finiteAbelPlanaLogVerticalSubdivisionEdge]
  ring

/-- Sum of the normalized oriented boundary integrals of all finite vertical
gap strips. -/
noncomputable def Complex.finiteAbelPlanaLogVerticalStripBoundarySum
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) : ℂ :=
  ∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
    Complex.finiteAbelPlanaLogVerticalStripBoundaryIntegral k w T ρ

/-- Boundary expression after the strip subdivision has cancelled internal
vertical cuts and attached the deleted arcs with punctured-domain orientation.
The deleted arcs are stored in the positive parametrization used elsewhere, so
they enter here with a minus sign. -/
noncomputable def Complex.finiteAbelPlanaLogStripBoundaryWithDeletedArcs
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) : ℂ :=
  Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ -
    Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ

/-- Unfolding of the finite vertical strip boundary sum. -/
theorem Complex.finiteAbelPlana_log_verticalStripBoundarySum_unfold
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ =
      ∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
        Complex.finiteAbelPlanaLogVerticalStripBoundaryIntegral k w T ρ := by
  rfl

/-- The concrete vertical-strip boundary sum is the normalized sum of the
abstract oriented strip side expressions. -/
theorem Complex.finiteAbelPlana_log_verticalStripBoundarySum_eq_normalized_sideExpression_sum
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ =
      ∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          Complex.finiteAbelPlanaLogVerticalStripSideExpression
            w
            (Complex.finiteAbelPlanaVerticalStripLeft k ρ)
            (Complex.finiteAbelPlanaVerticalStripRight k ρ)
            (-T)
            T := by
  calc
    Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ =
        ∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
          Complex.finiteAbelPlanaLogVerticalStripBoundaryIntegral k w T ρ := by
      exact
        Complex.finiteAbelPlana_log_verticalStripBoundarySum_unfold
          N w T ρ
    _ =
        ∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
          ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
            Complex.finiteAbelPlanaLogVerticalStripSideExpression
              w
              (Complex.finiteAbelPlanaVerticalStripLeft k ρ)
              (Complex.finiteAbelPlanaVerticalStripRight k ρ)
              (-T)
              T := by
      exact
        Finset.sum_congr rfl
          (fun k _hk =>
            Complex.finiteAbelPlana_log_verticalStripBoundaryIntegral_eq_normalized_sideExpression
              k w T ρ)

/-- Unfolding of the strip-boundary expression after deleted arcs have been
attached with punctured-domain orientation. -/
theorem Complex.finiteAbelPlana_log_stripBoundaryWithDeletedArcs_unfold
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogStripBoundaryWithDeletedArcs N w T ρ =
      Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ -
        Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ := by
  rfl

/-- Lower horizontal collar adjacent to the left endpoint deleted disk. -/
noncomputable def Complex.finiteAbelPlanaLogLeftEndpointLowerCollar
    (w : ℂ)
    (T ρ : ℝ) : ℂ :=
  ∫ x : ℝ in (0 : ℝ)..ρ,
    Complex.finiteAbelPlanaLogRectangleIntegrand w
      ((x : ℂ) - Complex.I * (T : ℂ))

/-- Upper horizontal collar adjacent to the left endpoint deleted disk. -/
noncomputable def Complex.finiteAbelPlanaLogLeftEndpointUpperCollar
    (w : ℂ)
    (T ρ : ℝ) : ℂ :=
  ∫ x : ℝ in (0 : ℝ)..ρ,
    Complex.finiteAbelPlanaLogRectangleIntegrand w
      ((x : ℂ) + Complex.I * (T : ℂ))

/-- Lower horizontal collar adjacent to the right endpoint deleted disk. -/
noncomputable def Complex.finiteAbelPlanaLogRightEndpointLowerCollar
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) : ℂ :=
  let M : ℕ := N + 1
  ∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ),
    Complex.finiteAbelPlanaLogRectangleIntegrand w
      ((x : ℂ) - Complex.I * (T : ℂ))

/-- Upper horizontal collar adjacent to the right endpoint deleted disk. -/
noncomputable def Complex.finiteAbelPlanaLogRightEndpointUpperCollar
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) : ℂ :=
  let M : ℕ := N + 1
  ∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ),
    Complex.finiteAbelPlanaLogRectangleIntegrand w
      ((x : ℂ) + Complex.I * (T : ℂ))

/-- Lower horizontal collar across the deleted disk centered at the interior
integer `n + 1`. -/
noncomputable def Complex.finiteAbelPlanaLogInteriorLowerCollar
    (n : ℕ)
    (w : ℂ)
    (T ρ : ℝ) : ℂ :=
  let c : ℝ := (n + 1 : ℕ)
  ∫ x : ℝ in (c - ρ)..(c + ρ),
    Complex.finiteAbelPlanaLogRectangleIntegrand w
      ((x : ℂ) - Complex.I * (T : ℂ))

/-- Upper horizontal collar across the deleted disk centered at the interior
integer `n + 1`. -/
noncomputable def Complex.finiteAbelPlanaLogInteriorUpperCollar
    (n : ℕ)
    (w : ℂ)
    (T ρ : ℝ) : ℂ :=
  let c : ℝ := (n + 1 : ℕ)
  ∫ x : ℝ in (c - ρ)..(c + ρ),
    Complex.finiteAbelPlanaLogRectangleIntegrand w
      ((x : ℂ) + Complex.I * (T : ℂ))

/-- Boundary contribution of the left endpoint cap/collar rectangle, with the
deleted endpoint semicircle itself kept out as a separate deleted-boundary
term. -/
noncomputable def Complex.finiteAbelPlanaLogLeftEndpointCapCollarBoundary
    (w : ℂ)
    (T ρ : ℝ) : ℂ :=
  ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
    (Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ -
      Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
        Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ -
          Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ)

/-- Boundary contribution of the right endpoint cap/collar rectangle, with the
deleted endpoint semicircle itself kept out as a separate deleted-boundary
term. -/
noncomputable def Complex.finiteAbelPlanaLogRightEndpointCapCollarBoundary
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) : ℂ :=
  ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
    (Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
      Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
        Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
          Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ)

/-- Boundary contribution of the cap/collar rectangle around the deleted disk
centered at the interior integer `n + 1`, with the deleted circle itself kept
out as a separate deleted-boundary term. -/
noncomputable def Complex.finiteAbelPlanaLogInteriorCapCollarBoundary
    (n : ℕ)
    (w : ℂ)
    (T ρ : ℝ) : ℂ :=
  ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
    (Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ -
      Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ +
        Complex.I *
          Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ -
          Complex.I *
            Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ)

/-- Concrete endpoint cap/collar boundary contribution: the two endpoint
collars adjacent to the principal-value vertical sides. -/
noncomputable def Complex.finiteAbelPlanaLogEndpointCapCollarBoundaryContribution
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) : ℂ :=
  Complex.finiteAbelPlanaLogLeftEndpointCapCollarBoundary w T ρ +
    Complex.finiteAbelPlanaLogRightEndpointCapCollarBoundary N w T ρ

/-- Concrete interior cap/collar boundary contribution: one collar around each
interior deleted integer disk. -/
noncomputable def Complex.finiteAbelPlanaLogInteriorCapCollarBoundaryContribution
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) : ℂ :=
  ∑ n in Finset.range N,
    Complex.finiteAbelPlanaLogInteriorCapCollarBoundary n w T ρ

/-- Concrete cap/collar boundary contribution obtained by adding the endpoint
and interior collar rectangles. -/
noncomputable def Complex.finiteAbelPlanaLogConcreteCapCollarBoundaryContribution
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) : ℂ :=
  Complex.finiteAbelPlanaLogEndpointCapCollarBoundaryContribution N w T ρ +
    Complex.finiteAbelPlanaLogInteriorCapCollarBoundaryContribution N w T ρ

/-- Unfolding of the left endpoint cap/collar boundary. -/
theorem Complex.finiteAbelPlana_log_leftEndpointCapCollarBoundary_unfold
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarBoundary w T ρ =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ -
          Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ) := by
  rfl

/-- Unfolding of the right endpoint cap/collar boundary. -/
theorem Complex.finiteAbelPlana_log_rightEndpointCapCollarBoundary_unfold
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogRightEndpointCapCollarBoundary N w T ρ =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
          Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ) := by
  rfl

/-- Unfolding of one interior cap/collar boundary. -/
theorem Complex.finiteAbelPlana_log_interiorCapCollarBoundary_unfold
    (n : ℕ)
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogInteriorCapCollarBoundary n w T ρ =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ -
          Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ +
            Complex.I *
              Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ -
              Complex.I *
                Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ) := by
  rfl

/-- Unfolding of the endpoint cap/collar contribution. -/
theorem Complex.finiteAbelPlana_log_endpointCapCollarBoundaryContribution_unfold
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogEndpointCapCollarBoundaryContribution N w T ρ =
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarBoundary w T ρ +
        Complex.finiteAbelPlanaLogRightEndpointCapCollarBoundary N w T ρ := by
  rfl

/-- Unfolding of the interior cap/collar contribution. -/
theorem Complex.finiteAbelPlana_log_interiorCapCollarBoundaryContribution_unfold
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogInteriorCapCollarBoundaryContribution N w T ρ =
      ∑ n in Finset.range N,
        Complex.finiteAbelPlanaLogInteriorCapCollarBoundary n w T ρ := by
  rfl

/-- Unfolding of the concrete cap/collar contribution. -/
theorem Complex.finiteAbelPlana_log_concreteCapCollarBoundaryContribution_unfold
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogConcreteCapCollarBoundaryContribution N w T ρ =
      Complex.finiteAbelPlanaLogEndpointCapCollarBoundaryContribution N w T ρ +
        Complex.finiteAbelPlanaLogInteriorCapCollarBoundaryContribution N w T ρ := by
  rfl

/-- A radius bounded by the Abel-Plana quarter-gap is bounded by one. -/
theorem Real.lt_one_of_lt_one_div_four
    {ρ : ℝ}
    (hρquarter : ρ < (1 : ℝ) / 4) :
    ρ < 1 := by
  have hquarter_one : (1 : ℝ) / 4 < 1 := by norm_num
  exact lt_trans hρquarter hquarter_one

/-- A positive radius below the Abel-Plana quarter-gap leaves a nonempty safe
interval between two adjacent collars. -/
theorem Real.rho_lt_one_sub_rho_of_lt_one_div_four
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hρquarter : ρ < (1 : ℝ) / 4) :
    ρ < 1 - ρ := by
  have hρ_lt_half : ρ < (1 : ℝ) / 2 := by
    have hquarter_half : (1 : ℝ) / 4 < (1 : ℝ) / 2 := by norm_num
    exact lt_trans hρquarter hquarter_half
  have htwoρ_lt_one : ρ + ρ < 1 := by
    calc
      ρ + ρ < (1 : ℝ) / 2 + (1 : ℝ) / 2 := add_lt_add hρ_lt_half hρ_lt_half
      _ = 1 := by norm_num
  exact lt_sub_iff_add_lt'.mpr htwoρ_lt_one

/-- Interval integrability descends to a subinterval whose endpoints both lie
in the original unordered interval. -/
theorem Complex.intervalIntegrable_of_mem_uIcc
    {F : ℝ → ℂ}
    {a b c d : ℝ}
    (hF : IntervalIntegrable F volume a b)
    (hc : c ∈ [[a, b]])
    (hd : d ∈ [[a, b]]) :
    IntervalIntegrable F volume c d := by
  exact hF.mono_set (uIcc_subset_uIcc hc hd)

/-- Reusable finite real-line partition identity for an arbitrary adjacent
endpoint chain.

This is the owner-level interval-integral step behind the horizontal
Abel-Plana subdivision: once the concrete endpoint chain is supplied, the
integral over the whole side is the sum of the adjacent subinterval integrals. -/
theorem Complex.integral_eq_sum_adjacent_intervals_of_endpoint_chain
    (F : ℝ → ℂ)
    (a : ℕ → ℝ)
    (m : ℕ)
    (A B : ℝ)
    (hA : a 0 = A)
    (hB : a m = B)
    (hint : ∀ k < m, IntervalIntegrable F volume (a k) (a (k + 1))) :
    (∫ x : ℝ in A..B, F x) =
      ∑ k in Finset.range m, ∫ x : ℝ in (a k)..(a (k + 1)), F x := by
  calc
    (∫ x : ℝ in A..B, F x) =
        ∫ x : ℝ in (a 0)..(a m), F x := by
      rw [hA, hB]
    _ =
        ∑ k in Finset.range m, ∫ x : ℝ in (a k)..(a (k + 1)), F x := by
      exact (intervalIntegral.sum_integral_adjacent_intervals hint).symm

/-- Endpoint chain for the finite Abel-Plana horizontal subdivision.

The adjacent intervals are, in order,
`[0, ρ]`, `[ρ, 1 - ρ]`, `[1 - ρ, 1 + ρ]`, ...,
`[N + ρ, N + 1 - ρ]`, `[N + 1 - ρ, N + 1]`. -/
noncomputable def Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint
    (N : ℕ)
    (ρ : ℝ)
    (i : ℕ) : ℝ :=
  if i = 0 then
    0
  else if i = 2 * N + 3 then
    ((N + 1 : ℕ) : ℝ)
  else
    let j : ℕ := i - 1
    if j % 2 = 0 then
      ((j / 2 : ℕ) : ℝ) + ρ
    else
      (((j + 1) / 2 : ℕ) : ℝ) - ρ

/-- Unfolding of the finite Abel-Plana horizontal subdivision endpoint chain. -/
theorem Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_unfold
    (N : ℕ)
    (ρ : ℝ)
    (i : ℕ) :
    Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i =
      if i = 0 then
        0
      else if i = 2 * N + 3 then
        ((N + 1 : ℕ) : ℝ)
      else
        let j : ℕ := i - 1
        if j % 2 = 0 then
          ((j / 2 : ℕ) : ℝ) + ρ
        else
          (((j + 1) / 2 : ℕ) : ℝ) - ρ := by
  rfl

/-- The finite Abel-Plana horizontal chain starts at the left endpoint. -/
theorem Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_start
    (N : ℕ)
    (ρ : ℝ) :
    Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ 0 = 0 := by
  rfl

/-- The finite Abel-Plana horizontal chain ends at the right endpoint. -/
theorem Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_end
    (N : ℕ)
    (ρ : ℝ) :
    Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (2 * N + 3) =
      ((N + 1 : ℕ) : ℝ) := by
  have hne : 2 * N + 3 ≠ 0 := by
    exact Nat.succ_ne_zero (2 * N + 2)
  dsimp [Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint]
  rw [if_neg hne, if_pos rfl]

/-- Odd subdivision nodes are exactly the left endpoints of the safe vertical
strips. -/
theorem Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_safe_left
    (N k : ℕ)
    (ρ : ℝ)
    (hk : k ≤ N) :
    Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (2 * k + 1) =
      (k : ℝ) + ρ := by
  have hzero : 2 * k + 1 ≠ 0 := by omega
  have hlast : 2 * k + 1 ≠ 2 * N + 3 := by omega
  have hsub : 2 * k + 1 - 1 = 2 * k := by omega
  have hmod : (2 * k) % 2 = 0 := by
    rw [Nat.mul_comm]
    exact Nat.mul_mod_right k 2
  have hdiv : (2 * k) / 2 = k := by
    rw [Nat.mul_comm]
    exact Nat.mul_div_cancel k (by norm_num : 0 < 2)
  dsimp [Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint]
  rw [if_neg hzero, if_neg hlast]
  simp [hsub, hmod, hdiv]

/-- Even successor subdivision nodes are exactly the right endpoints of the
safe vertical strips. -/
theorem Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_safe_right
    (N k : ℕ)
    (ρ : ℝ)
    (hk : k ≤ N) :
    Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (2 * k + 2) =
      ((k + 1 : ℕ) : ℝ) - ρ := by
  have hzero : 2 * k + 2 ≠ 0 := by omega
  have hlast : 2 * k + 2 ≠ 2 * N + 3 := by omega
  have hsub : 2 * k + 2 - 1 = 2 * k + 1 := by omega
  have hmod : (2 * k + 1) % 2 = 1 := by
    rw [show 2 * k + 1 = k * 2 + 1 by omega]
    exact Nat.mul_add_mod_of_lt (by norm_num : 1 < 2)
  have hdiv : (2 * k + 1 + 1) / 2 = k + 1 := by
    rw [show 2 * k + 1 + 1 = (k + 1) * 2 by omega]
    exact Nat.mul_div_cancel (k + 1) (by norm_num : 0 < 2)
  dsimp [Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint]
  rw [if_neg hzero, if_neg hlast]
  simp [hsub, hmod, hdiv]

/-- The left endpoint of the collar around the interior pole `n + 1`. -/
theorem Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_interior_left
    (N n : ℕ)
    (ρ : ℝ)
    (hn : n ∈ Finset.range N) :
    Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (2 * (n + 1)) =
      ((n + 1 : ℕ) : ℝ) - ρ := by
  exact
    Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_safe_right
      N n ρ (Nat.le_of_lt_succ (Finset.mem_range.mp hn))

/-- The right endpoint of the collar around the interior pole `n + 1`. -/
theorem Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_interior_right
    (N n : ℕ)
    (ρ : ℝ)
    (hn : n ∈ Finset.range N) :
    Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (2 * (n + 1) + 1) =
      ((n + 1 : ℕ) : ℝ) + ρ := by
  have hnlt : n < N := Finset.mem_range.mp hn
  have hsucc_le : n + 1 ≤ N := Nat.succ_le_iff.mpr hnlt
  exact
    Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_safe_left
      N (n + 1) ρ hsucc_le

/-- Algebraic reindexing of the corrected adjacent interval chain into odd
safe intervals, the two endpoint collars, and the positive even interior
collars. -/
theorem Complex.sum_range_horizontalSubdivision_adjacent_reindex
    (N : ℕ)
    (G : ℕ → ℂ) :
    (∑ i in Finset.range (2 * N + 3), G i) =
      (∑ k in Finset.range (N + 1), G (2 * k + 1)) +
        (G 0 + G (2 * N + 2) +
          ∑ n in Finset.range N, G (2 * (n + 1))) := by
  induction N with
  | zero =>
      simp
      ring
  | succ N ih =>
      rw [show 2 * (N + 1) + 3 = (2 * N + 3) + 2 by omega]
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      rw [ih]
      rw [Finset.sum_range_succ (f := fun k => G (2 * k + 1))]
      rw [Finset.sum_range_succ (f := fun n => G (2 * (n + 1)))]
      ring

/-- Lower-horizontal adjacent intervals for the corrected endpoint chain
reindex to the safe strips plus endpoint and interior collars. -/
theorem Complex.finiteAbelPlana_log_lowerHorizontalSubdivision_sum_eq_verticalStrips_add_capCollars
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) :
    (∑ i in Finset.range (2 * N + 3),
      ∫ x : ℝ in
        (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i)..
          (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)),
        Complex.finiteAbelPlanaLogRectangleIntegrand w
          ((x : ℂ) - Complex.I * (T : ℂ))) =
      (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
        Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ) +
        (Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ +
          Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ +
            ∑ n in Finset.range N,
              Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ) := by
  let G : ℕ → ℂ := fun i =>
    ∫ x : ℝ in
      (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i)..
        (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)),
      Complex.finiteAbelPlanaLogRectangleIntegrand w
        ((x : ℂ) - Complex.I * (T : ℂ))
  have hsafe :
      (∑ k in Finset.range (N + 1), G (2 * k + 1)) =
        ∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
          Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ := by
    dsimp [Complex.finiteAbelPlanaVerticalStripIndexSet]
    exact Finset.sum_congr rfl
      (fun k hk => by
        have hk_le : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        dsimp [G, Complex.finiteAbelPlanaLogVerticalStripLowerSide,
          Complex.finiteAbelPlanaVerticalStripLeft,
          Complex.finiteAbelPlanaVerticalStripRight]
        rw [Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_safe_left
            N k ρ hk_le,
          Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_safe_right
            N k ρ hk_le])
  have hleft :
      G 0 = Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ := by
    dsimp [G, Complex.finiteAbelPlanaLogLeftEndpointLowerCollar]
    rw [Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_start]
    rw [Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_safe_left
      N 0 ρ (Nat.zero_le N)]
  have hright :
      G (2 * N + 2) =
        Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ := by
    dsimp [G, Complex.finiteAbelPlanaLogRightEndpointLowerCollar]
    rw [Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_safe_right
        N N ρ le_rfl,
      show 2 * N + 2 + 1 = 2 * N + 3 by omega,
      Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_end]
  have hinterior :
      (∑ n in Finset.range N, G (2 * (n + 1))) =
        ∑ n in Finset.range N,
          Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ := by
    exact Finset.sum_congr rfl
      (fun n hn => by
        dsimp [G, Complex.finiteAbelPlanaLogInteriorLowerCollar]
        rw [Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_interior_left
            N n ρ hn,
          Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_interior_right
            N n ρ hn])
  calc
    (∑ i in Finset.range (2 * N + 3), G i) =
        (∑ k in Finset.range (N + 1), G (2 * k + 1)) +
          (G 0 + G (2 * N + 2) +
            ∑ n in Finset.range N, G (2 * (n + 1))) := by
      exact Complex.sum_range_horizontalSubdivision_adjacent_reindex N G
    _ =
        (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
          Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ) +
          (Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ +
            Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ +
              ∑ n in Finset.range N,
                Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ) := by
      rw [hsafe, hleft, hright, hinterior]

/-- Upper-horizontal adjacent intervals for the corrected endpoint chain
reindex to the safe strips plus endpoint and interior collars. -/
theorem Complex.finiteAbelPlana_log_upperHorizontalSubdivision_sum_eq_verticalStrips_add_capCollars
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) :
    (∑ i in Finset.range (2 * N + 3),
      ∫ x : ℝ in
        (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i)..
          (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)),
        Complex.finiteAbelPlanaLogRectangleIntegrand w
          ((x : ℂ) + Complex.I * (T : ℂ))) =
      (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
        Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ) +
        (Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
          Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
            ∑ n in Finset.range N,
              Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ) := by
  let G : ℕ → ℂ := fun i =>
    ∫ x : ℝ in
      (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i)..
        (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)),
      Complex.finiteAbelPlanaLogRectangleIntegrand w
        ((x : ℂ) + Complex.I * (T : ℂ))
  have hsafe :
      (∑ k in Finset.range (N + 1), G (2 * k + 1)) =
        ∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
          Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ := by
    dsimp [Complex.finiteAbelPlanaVerticalStripIndexSet]
    exact Finset.sum_congr rfl
      (fun k hk => by
        have hk_le : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        dsimp [G, Complex.finiteAbelPlanaLogVerticalStripUpperSide,
          Complex.finiteAbelPlanaVerticalStripLeft,
          Complex.finiteAbelPlanaVerticalStripRight]
        rw [Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_safe_left
            N k ρ hk_le,
          Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_safe_right
            N k ρ hk_le])
  have hleft :
      G 0 = Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ := by
    dsimp [G, Complex.finiteAbelPlanaLogLeftEndpointUpperCollar]
    rw [Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_start]
    rw [Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_safe_left
      N 0 ρ (Nat.zero_le N)]
  have hright :
      G (2 * N + 2) =
        Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ := by
    dsimp [G, Complex.finiteAbelPlanaLogRightEndpointUpperCollar]
    rw [Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_safe_right
        N N ρ le_rfl,
      show 2 * N + 2 + 1 = 2 * N + 3 by omega,
      Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_end]
  have hinterior :
      (∑ n in Finset.range N, G (2 * (n + 1))) =
        ∑ n in Finset.range N,
          Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ := by
    exact Finset.sum_congr rfl
      (fun n hn => by
        dsimp [G, Complex.finiteAbelPlanaLogInteriorUpperCollar]
        rw [Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_interior_left
            N n ρ hn,
          Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_interior_right
            N n ρ hn])
  calc
    (∑ i in Finset.range (2 * N + 3), G i) =
        (∑ k in Finset.range (N + 1), G (2 * k + 1)) +
          (G 0 + G (2 * N + 2) +
            ∑ n in Finset.range N, G (2 * (n + 1))) := by
      exact Complex.sum_range_horizontalSubdivision_adjacent_reindex N G
    _ =
        (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
          Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ) +
          (Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
            Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
              ∑ n in Finset.range N,
                Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ) := by
      rw [hsafe, hleft, hright, hinterior]

/-- Every endpoint of the finite horizontal subdivision lies on the real
projection of the closed Abel-Plana rectangle. -/
theorem Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_mem_closedInterval
    (N : ℕ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hρquarter : ρ < (1 : ℝ) / 4)
    {i : ℕ}
    (hi : i ≤ 2 * N + 3) :
    Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i ∈
      [[(0 : ℝ), ((N + 1 : ℕ) : ℝ)]] := by
  have hρ_lt_one : ρ < 1 :=
    Real.lt_one_of_lt_one_div_four hρquarter
  have hzero_le_right : (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.zero_le (N + 1)
  by_cases hzero : i = 0
  · rw [hzero, Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_start]
    rw [Set.uIcc_of_le hzero_le_right]
    exact ⟨le_rfl, hzero_le_right⟩
  by_cases hlast : i = 2 * N + 3
  · rw [hlast, Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_end]
    rw [Set.uIcc_of_le hzero_le_right]
    exact ⟨hzero_le_right, le_rfl⟩
  have hilt : i < 2 * N + 3 :=
    lt_of_le_of_ne hi hlast
  let j : ℕ := i - 1
  have hj_le : j ≤ 2 * N + 1 := by
    dsimp [j]
    omega
  dsimp [Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint]
  rw [if_neg hzero, if_neg hlast]
  by_cases hmod : j % 2 = 0
  · rw [if_pos hmod]
    have hjdiv_le : j / 2 ≤ N := by
      omega
    rw [Set.uIcc_of_le hzero_le_right]
    constructor
    · have hnonneg : (0 : ℝ) ≤ ((j / 2 : ℕ) : ℝ) := by
        exact_mod_cast Nat.zero_le (j / 2)
      exact add_nonneg hnonneg (le_of_lt hρ)
    · have hjdiv_real : (((j / 2 : ℕ) : ℝ) : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast hjdiv_le
      have hN_le : (N : ℝ) + 1 = ((N + 1 : ℕ) : ℝ) := by
        norm_num
      calc
        ((j / 2 : ℕ) : ℝ) + ρ ≤ (N : ℝ) + ρ := by
          exact add_le_add_right hjdiv_real ρ
        _ ≤ (N : ℝ) + 1 := by
          exact add_le_add_left (le_of_lt hρ_lt_one) (N : ℝ)
        _ = ((N + 1 : ℕ) : ℝ) := hN_le
  · rw [if_neg hmod]
    have hj_pos : 0 < j := by
      dsimp [j]
      omega
    have hjdiv_pos : 1 ≤ (j + 1) / 2 := by
      omega
    have hjdiv_le : (j + 1) / 2 ≤ N + 1 := by
      omega
    rw [Set.uIcc_of_le hzero_le_right]
    constructor
    · have hleft : ρ ≤ (((j + 1) / 2 : ℕ) : ℝ) := by
        calc
          ρ < 1 := hρ_lt_one
          _ ≤ (((j + 1) / 2 : ℕ) : ℝ) := by
            exact_mod_cast hjdiv_pos
      exact sub_nonneg.mpr hleft
    · have hright : (((j + 1) / 2 : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
        exact_mod_cast hjdiv_le
      exact (sub_le_self _ (le_of_lt hρ)).trans hright

/-- A horizontal top or bottom edge point of the finite Abel-Plana rectangle
avoids every deleted integer disk under the deleted-geometry hypotheses. -/
theorem Complex.finiteAbelPlana_horizontalEdgePoint_not_mem_deletedDisk
    {N m : ℕ}
    {T ρ x : ℝ}
    (hx : x ∈ [[(0 : ℝ), ((N + 1 : ℕ) : ℝ)]])
    (hρ : 0 < ρ)
    (hTρ : ρ < |T| / 2)
    (hm : m ∈ Finset.range (N + 2)) :
    ((x : ℂ) + Complex.I * (T : ℂ)) ∉ Metric.ball (m : ℂ) ρ ∧
      ((x : ℂ) - Complex.I * (T : ℂ)) ∉ Metric.ball (m : ℂ) ρ := by
  have hTpos : 0 < |T| := by
    have hhalf_pos : 0 < |T| / 2 := lt_trans hρ hTρ
    linarith
  have hρ_lt_absT : ρ < |T| := by
    have hhalf_lt_abs : |T| / 2 < |T| := by linarith
    exact lt_trans hTρ hhalf_lt_abs
  constructor
  · intro hball
    have hdist_lt :
        dist ((x : ℂ) + Complex.I * (T : ℂ)) (m : ℂ) < ρ :=
      Metric.mem_ball.mp hball
    have him_le_norm :
        |T| ≤ ‖((x : ℂ) + Complex.I * (T : ℂ)) - (m : ℂ)‖ := by
      have him :
          (((x : ℂ) + Complex.I * (T : ℂ)) - (m : ℂ)).im = T := by
        simp
      calc
        |T| = |(((x : ℂ) + Complex.I * (T : ℂ)) - (m : ℂ)).im| := by
          rw [him]
        _ ≤ ‖((x : ℂ) + Complex.I * (T : ℂ)) - (m : ℂ)‖ :=
          Complex.abs_im_le_abs _
    have hnorm_lt :
        ‖((x : ℂ) + Complex.I * (T : ℂ)) - (m : ℂ)‖ < ρ := by
      simpa [dist_eq_norm] using hdist_lt
    exact (not_lt_of_ge (le_of_lt hρ_lt_absT)) (him_le_norm.trans_lt hnorm_lt)
  · intro hball
    have hdist_lt :
        dist ((x : ℂ) - Complex.I * (T : ℂ)) (m : ℂ) < ρ :=
      Metric.mem_ball.mp hball
    have him_le_norm :
        |T| ≤ ‖((x : ℂ) - Complex.I * (T : ℂ)) - (m : ℂ)‖ := by
      have him :
          (((x : ℂ) - Complex.I * (T : ℂ)) - (m : ℂ)).im = -T := by
        simp
      calc
        |T| = |(((x : ℂ) - Complex.I * (T : ℂ)) - (m : ℂ)).im| := by
          rw [him, abs_neg]
        _ ≤ ‖((x : ℂ) - Complex.I * (T : ℂ)) - (m : ℂ)‖ :=
          Complex.abs_im_le_abs _
    have hnorm_lt :
        ‖((x : ℂ) - Complex.I * (T : ℂ)) - (m : ℂ)‖ < ρ := by
      simpa [dist_eq_norm] using hdist_lt
    exact (not_lt_of_ge (le_of_lt hρ_lt_absT)) (him_le_norm.trans_lt hnorm_lt)

/-- Horizontal edge segments in the finite subdivision are contained in the
punctured Abel-Plana rectangle. -/
theorem Complex.finiteAbelPlana_horizontalSubdivision_segment_subset_puncturedRectangle
    {w : ℂ}
    {N : ℕ}
    {T ρ : ℝ}
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    {i : ℕ}
    (hi : i < 2 * N + 3) :
    (∀ x ∈ [[Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i,
        Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)]],
      ((x : ℂ) + Complex.I * (T : ℂ)) ∈
        Complex.finiteAbelPlanaPuncturedRectangle N T ρ) ∧
    (∀ x ∈ [[Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i,
        Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)]],
      ((x : ℂ) - Complex.I * (T : ℂ)) ∈
        Complex.finiteAbelPlanaPuncturedRectangle N T ρ) := by
  have hi_le : i ≤ 2 * N + 3 := le_of_lt hi
  have hisucc_le : i + 1 ≤ 2 * N + 3 := by omega
  have hend₀ :
      Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i ∈
        [[(0 : ℝ), ((N + 1 : ℕ) : ℝ)]] :=
    Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_mem_closedInterval
      N hρ hdeleted_geometry.1 hi_le
  have hend₁ :
      Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1) ∈
        [[(0 : ℝ), ((N + 1 : ℕ) : ℝ)]] :=
    Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_mem_closedInterval
      N hρ hdeleted_geometry.1 hisucc_le
  have hsegment_subset :
      [[Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i,
        Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)]] ⊆
        [[(0 : ℝ), ((N + 1 : ℕ) : ℝ)]] :=
    uIcc_subset_uIcc hend₀ hend₁
  constructor
  · intro x hx
    have hxglobal :
        x ∈ [[(0 : ℝ), ((N + 1 : ℕ) : ℝ)]] :=
      hsegment_subset hx
    have him : (((x : ℂ) + Complex.I * (T : ℂ)).im) ∈ [[-T, T]] := by
      simpa using (right_mem_uIcc : T ∈ [[-T, T]])
    have havoid :
        ∀ m ∈ Finset.range (N + 2),
          ((x : ℂ) + Complex.I * (T : ℂ)) ∉ Metric.ball (m : ℂ) ρ := by
      intro m hm
      exact
        (Complex.finiteAbelPlana_horizontalEdgePoint_not_mem_deletedDisk
          hxglobal hρ hdeleted_geometry.2.1 hm).1
    exact
      Complex.mem_finiteAbelPlanaPuncturedRectangle_iff.mpr
        ⟨Complex.mem_reProdIm.mpr ⟨by simpa using hxglobal, him⟩, havoid⟩
  · intro x hx
    have hxglobal :
        x ∈ [[(0 : ℝ), ((N + 1 : ℕ) : ℝ)]] :=
      hsegment_subset hx
    have him : (((x : ℂ) - Complex.I * (T : ℂ)).im) ∈ [[-T, T]] := by
      simpa using (left_mem_uIcc : (-T) ∈ [[-T, T]])
    have havoid :
        ∀ m ∈ Finset.range (N + 2),
          ((x : ℂ) - Complex.I * (T : ℂ)) ∉ Metric.ball (m : ℂ) ρ := by
      intro m hm
      exact
        (Complex.finiteAbelPlana_horizontalEdgePoint_not_mem_deletedDisk
          hxglobal hρ hdeleted_geometry.2.1 hm).2
    exact
      Complex.mem_finiteAbelPlanaPuncturedRectangle_iff.mpr
        ⟨Complex.mem_reProdIm.mpr ⟨by simpa using hxglobal, him⟩, havoid⟩

/-- Interval-integrability of every adjacent interval in a horizontal
subdivision chain.

This is the only analytic hygiene input needed by the finite real-line
partition theorem: each closed horizontal subinterval lies in the punctured
rectangle, so continuity of the contour integrand there gives interval
integrability. -/
theorem Complex.finiteAbelPlana_log_horizontalSubdivision_intervalIntegrable
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    (∀ i < 2 * N + 3,
      IntervalIntegrable
        (fun x : ℝ =>
          Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((x : ℂ) - Complex.I * (T : ℂ)))
        volume
        (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i)
        (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1))) ∧
    (∀ i < 2 * N + 3,
      IntervalIntegrable
        (fun x : ℝ =>
          Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((x : ℂ) + Complex.I * (T : ℂ)))
        volume
        (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i)
        (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1))) := by
  constructor
  · intro i hi
    have hseg :
        ∀ x ∈ [[Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i,
            Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)]],
          ((x : ℂ) - Complex.I * (T : ℂ)) ∈
            Complex.finiteAbelPlanaPuncturedRectangle N T ρ :=
      (Complex.finiteAbelPlana_horizontalSubdivision_segment_subset_puncturedRectangle
        hρ hdeleted_geometry hi).2
    have hparam_cont :
        ContinuousOn
          (fun x : ℝ => ((x : ℂ) - Complex.I * (T : ℂ)))
          [[Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i,
            Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)]] :=
      (Complex.continuous_ofReal.sub continuous_const).continuousOn
    have hcont_segment :
        ContinuousOn
          (fun x : ℝ =>
            Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((x : ℂ) - Complex.I * (T : ℂ)))
          [[Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i,
            Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)]] :=
      hcont.comp_continuousOn hparam_cont hseg
    exact hcont_segment.intervalIntegrable
  · intro i hi
    have hseg :
        ∀ x ∈ [[Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i,
            Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)]],
          ((x : ℂ) + Complex.I * (T : ℂ)) ∈
            Complex.finiteAbelPlanaPuncturedRectangle N T ρ :=
      (Complex.finiteAbelPlana_horizontalSubdivision_segment_subset_puncturedRectangle
        hρ hdeleted_geometry hi).1
    have hparam_cont :
        ContinuousOn
          (fun x : ℝ => ((x : ℂ) + Complex.I * (T : ℂ)))
          [[Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i,
            Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)]] :=
      (Complex.continuous_ofReal.add continuous_const).continuousOn
    have hcont_segment :
        ContinuousOn
          (fun x : ℝ =>
            Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((x : ℂ) + Complex.I * (T : ℂ)))
          [[Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i,
            Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)]] :=
      hcont.comp_continuousOn hparam_cont hseg
    exact hcont_segment.intervalIntegrable

/-- Lower horizontal accounting for the finite-hole subdivision.

The full lower horizontal side is the sum of the safe vertical-strip lower
edges plus the endpoint and interior lower collars around the deleted disks. -/
theorem Complex.finiteAbelPlana_log_lowerHorizontalSide_eq_verticalStrips_add_capCollars
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogFiniteHeightLowerSide N w T =
      (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
        Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ) +
        (Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ +
          Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ +
            ∑ n in Finset.range N,
              Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ) := by
  let F : ℝ → ℂ := fun x : ℝ =>
    Complex.finiteAbelPlanaLogRectangleIntegrand w
      ((x : ℂ) - Complex.I * (T : ℂ))
  have hchain :
      (∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ), F x) =
        ∑ i in Finset.range (2 * N + 3),
          ∫ x : ℝ in
            (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i)..
              (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)),
            F x := by
    exact
      Complex.integral_eq_sum_adjacent_intervals_of_endpoint_chain
        F
        (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ)
        (2 * N + 3)
        0
        ((N + 1 : ℕ) : ℝ)
        (Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_start N ρ)
        (Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_end N ρ)
        (Complex.finiteAbelPlana_log_horizontalSubdivision_intervalIntegrable
          N T hρ hdeleted_geometry hcont).1
  have hreindex :
      (∑ i in Finset.range (2 * N + 3),
        ∫ x : ℝ in
          (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i)..
            (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)),
          F x) =
        (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
          Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ) +
          (Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ +
            Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ +
              ∑ n in Finset.range N,
                Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ) := by
    exact
      Complex.finiteAbelPlana_log_lowerHorizontalSubdivision_sum_eq_verticalStrips_add_capCollars
        N w T ρ
  calc
    Complex.finiteAbelPlanaLogFiniteHeightLowerSide N w T =
        ∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ), F x := by
      rfl
    _ =
        ∑ i in Finset.range (2 * N + 3),
          ∫ x : ℝ in
            (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i)..
              (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)),
            F x := hchain
    _ =
        (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
          Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ) +
          (Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ +
            Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ +
              ∑ n in Finset.range N,
                Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ) := hreindex

/-- Upper horizontal accounting for the finite-hole subdivision.

The full upper horizontal side is the sum of the safe vertical-strip upper
edges plus the endpoint and interior upper collars around the deleted disks. -/
theorem Complex.finiteAbelPlana_log_upperHorizontalSide_eq_verticalStrips_add_capCollars
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogFiniteHeightUpperSide N w T =
      (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
        Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ) +
        (Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
          Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
            ∑ n in Finset.range N,
              Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ) := by
  let F : ℝ → ℂ := fun x : ℝ =>
    Complex.finiteAbelPlanaLogRectangleIntegrand w
      ((x : ℂ) + Complex.I * (T : ℂ))
  have hchain :
      (∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ), F x) =
        ∑ i in Finset.range (2 * N + 3),
          ∫ x : ℝ in
            (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i)..
              (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)),
            F x := by
    exact
      Complex.integral_eq_sum_adjacent_intervals_of_endpoint_chain
        F
        (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ)
        (2 * N + 3)
        0
        ((N + 1 : ℕ) : ℝ)
        (Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_start N ρ)
        (Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_end N ρ)
        (Complex.finiteAbelPlana_log_horizontalSubdivision_intervalIntegrable
          N T hρ hdeleted_geometry hcont).2
  have hreindex :
      (∑ i in Finset.range (2 * N + 3),
        ∫ x : ℝ in
          (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i)..
            (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)),
          F x) =
        (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
          Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ) +
          (Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
            Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
              ∑ n in Finset.range N,
                Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ) := by
    exact
      Complex.finiteAbelPlana_log_upperHorizontalSubdivision_sum_eq_verticalStrips_add_capCollars
        N w T ρ
  calc
    Complex.finiteAbelPlanaLogFiniteHeightUpperSide N w T =
        ∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ), F x := by
      rfl
    _ =
        ∑ i in Finset.range (2 * N + 3),
          ∫ x : ℝ in
            (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i)..
              (Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)),
            F x := hchain
    _ =
        (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
          Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ) +
          (Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
            Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
              ∑ n in Finset.range N,
                Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ) := hreindex

/-- Vertical-side telescoping for the finite-hole subdivision.

Subtracting the safe-strip vertical sides from the principal-value endpoint
vertical sides leaves exactly the endpoint collars and the interior collar
vertical sides. -/
theorem Complex.finiteAbelPlana_log_verticalPVSide_sub_verticalStrips_eq_capCollars
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) :
    (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
        Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ) -
      (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
        (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide k w T ρ -
          Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide k w T ρ)) =
      (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ -
          Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ) +
        (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
          Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ) +
          ∑ n in Finset.range N,
            (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ) := by
  induction N with
  | zero =>
      dsimp [Complex.finiteAbelPlanaVerticalStripIndexSet]
      rw [Finset.sum_range_one, Finset.sum_range_zero]
      ring
  | succ N ih =>
      dsimp [Complex.finiteAbelPlanaVerticalStripIndexSet] at ih ⊢
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      rw [← ih]
      ring

/-- Raw cap/collar accounting before applying the residue normalization.

This is the assembly of the lower-horizontal partition, upper-horizontal
partition, and vertical-side telescoping theorem. -/
theorem Complex.finiteAbelPlana_log_concreteCapCollarBoundaryContribution_eq_pvNormalized_sub_verticalStripBoundarySum
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogConcreteCapCollarBoundaryContribution N w T ρ =
      Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ -
        Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ := by
  have hlower :
      Complex.finiteAbelPlanaLogFiniteHeightLowerSide N w T =
        (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
          Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ) +
          (Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ +
            Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ +
              ∑ n in Finset.range N,
                Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ) :=
    Complex.finiteAbelPlana_log_lowerHorizontalSide_eq_verticalStrips_add_capCollars
      N T hρ hdeleted_geometry hcont
  have hupper :
      Complex.finiteAbelPlanaLogFiniteHeightUpperSide N w T =
        (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
          Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ) +
          (Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
            Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
              ∑ n in Finset.range N,
                Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ) :=
    Complex.finiteAbelPlana_log_upperHorizontalSide_eq_verticalStrips_add_capCollars
      N T hρ hdeleted_geometry hcont
  have hvertical :
      (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
          Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ) -
        (∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
          (Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide k w T ρ -
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide k w T ρ)) =
        (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ -
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ) +
          (Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ) +
            ∑ n in Finset.range N,
              (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ -
                Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ) :=
    Complex.finiteAbelPlana_log_verticalPVSide_sub_verticalStrips_eq_capCollars
      N w T ρ
  dsimp [Complex.finiteAbelPlanaLogConcreteCapCollarBoundaryContribution,
    Complex.finiteAbelPlanaLogEndpointCapCollarBoundaryContribution,
    Complex.finiteAbelPlanaLogInteriorCapCollarBoundaryContribution,
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarBoundary,
    Complex.finiteAbelPlanaLogRightEndpointCapCollarBoundary,
    Complex.finiteAbelPlanaLogInteriorCapCollarBoundary,
    Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized,
    Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPV,
    Complex.finiteAbelPlanaLogFiniteHeightHorizontalSideExpression,
    Complex.finiteAbelPlanaLogFiniteHeightRawVerticalSideExpressionPV,
    Complex.finiteAbelPlanaLogVerticalStripBoundarySum,
    Complex.finiteAbelPlanaLogVerticalStripBoundaryIntegral]
  rw [hlower, hupper, hvertical]
  ring

/-- Boundary contribution of the cap/collar subdomains omitted by the vertical
gap strips.

The vertical safe strips alone do not cover the finite punctured rectangle.
This term records the ordinary cap/collar subdomain boundaries around the
deleted disks.  With this term included, the subdivision has the same outer
boundary as the named principal-value punctured rectangle. -/
noncomputable def Complex.finiteAbelPlanaLogCapCollarBoundaryContribution
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) : ℂ :=
  Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ -
    Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ

/-- The concrete endpoint and interior cap/collar rectangles assemble to the
abstract cap/collar correction.

This is the remaining collar-accounting theorem: split the lower and upper
outer horizontal sides into safe-strip intervals and deleted-disk collar
intervals, telescope the adjacent vertical strip sides, and identify the
surviving endpoint principal-value vertical pieces. -/
theorem Complex.finiteAbelPlana_log_concreteCapCollarBoundaryContribution_eq_capCollarBoundaryContribution
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogConcreteCapCollarBoundaryContribution N w T ρ =
      Complex.finiteAbelPlanaLogCapCollarBoundaryContribution N w T ρ := by
  calc
    Complex.finiteAbelPlanaLogConcreteCapCollarBoundaryContribution N w T ρ =
        Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ -
          Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ := by
      exact
        Complex.finiteAbelPlana_log_concreteCapCollarBoundaryContribution_eq_pvNormalized_sub_verticalStripBoundarySum
          N T hρ hdeleted_geometry hcont
    _ =
        Complex.finiteAbelPlanaLogCapCollarBoundaryContribution N w T ρ := by
      rfl

/-- Full finite-hole subdivision boundary: vertical gap strips, cap/collar
subdomains, and deleted arcs with punctured-domain orientation. -/
noncomputable def Complex.finiteAbelPlanaLogFiniteHoleSubdivisionBoundary
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) : ℂ :=
  Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ +
      Complex.finiteAbelPlanaLogCapCollarBoundaryContribution N w T ρ -
    Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ

/-- Concrete finite-hole subdivision boundary, before the concrete cap/collar
sum is identified with the abstract cap/collar correction. -/
noncomputable def Complex.finiteAbelPlanaLogConcreteFiniteHoleSubdivisionBoundary
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) : ℂ :=
  Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ +
      Complex.finiteAbelPlanaLogConcreteCapCollarBoundaryContribution N w T ρ -
    Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ

/-- Unfolding of the full finite-hole subdivision boundary. -/
theorem Complex.finiteAbelPlana_log_finiteHoleSubdivisionBoundary_unfold
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogFiniteHoleSubdivisionBoundary N w T ρ =
      Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ +
          Complex.finiteAbelPlanaLogCapCollarBoundaryContribution N w T ρ -
        Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ := by
  rfl

/-- Unfolding of the concrete finite-hole subdivision boundary. -/
theorem Complex.finiteAbelPlana_log_concreteFiniteHoleSubdivisionBoundary_unfold
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogConcreteFiniteHoleSubdivisionBoundary N w T ρ =
      Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ +
          Complex.finiteAbelPlanaLogConcreteCapCollarBoundaryContribution N w T ρ -
        Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ := by
  rfl

/-- Replacing the concrete cap/collar sum by the abstract cap/collar
correction transports the concrete finite-hole boundary to the public
finite-hole subdivision boundary. -/
theorem Complex.finiteAbelPlana_log_concreteFiniteHoleSubdivisionBoundary_eq_finiteHoleSubdivisionBoundary
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogConcreteFiniteHoleSubdivisionBoundary N w T ρ =
      Complex.finiteAbelPlanaLogFiniteHoleSubdivisionBoundary N w T ρ := by
  calc
    Complex.finiteAbelPlanaLogConcreteFiniteHoleSubdivisionBoundary N w T ρ =
        Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ +
            Complex.finiteAbelPlanaLogConcreteCapCollarBoundaryContribution N w T ρ -
          Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ := by
      exact
        Complex.finiteAbelPlana_log_concreteFiniteHoleSubdivisionBoundary_unfold
          N w T ρ
    _ =
        Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ +
            Complex.finiteAbelPlanaLogCapCollarBoundaryContribution N w T ρ -
          Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ := by
      rw [
        Complex.finiteAbelPlana_log_concreteCapCollarBoundaryContribution_eq_capCollarBoundaryContribution
          N T hρ hdeleted_geometry hcont]
    _ =
        Complex.finiteAbelPlanaLogFiniteHoleSubdivisionBoundary N w T ρ := by
      exact
        (Complex.finiteAbelPlana_log_finiteHoleSubdivisionBoundary_unfold
          N w T ρ).symm

/-- The full finite-hole subdivision boundary is the named finite-radius
punctured boundary. -/
theorem Complex.finiteAbelPlana_log_finiteHoleSubdivisionBoundary_eq_finiteRadiusPuncturedBoundary
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogFiniteHoleSubdivisionBoundary N w T ρ =
      Complex.finiteAbelPlanaLogFiniteRadiusPuncturedBoundaryIntegral N w T ρ := by
  calc
    Complex.finiteAbelPlanaLogFiniteHoleSubdivisionBoundary N w T ρ =
        Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ +
            (Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ -
              Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ) -
          Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ := by
      rfl
    _ =
        Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ -
          Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ := by
      ring
    _ =
        Complex.finiteAbelPlanaLogFiniteRadiusPuncturedBoundaryIntegral N w T ρ := by
      exact
        (Complex.finiteAbelPlana_log_finiteRadiusPuncturedBoundaryIntegral_eq_pvNormalized_sub_deleted
          N w T ρ).symm

/-- The remaining outer-boundary accounting defect after the deleted-boundary
terms have been put on both sides.

This is the precise geometric object that must vanish after the cap/collar
subdomains near the deleted disks are included in the finite-hole strip
decomposition.  The vertical safe strips alone do not definitionally contain
those cap pieces. -/
noncomputable def Complex.finiteAbelPlanaLogStripOuterBoundaryDefect
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) : ℂ :=
  Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ -
    Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ

/-- The strip-boundary/deleted-arc equality is exactly the vanishing of the
outer-boundary defect. -/
theorem Complex.finiteAbelPlana_log_stripBoundaryWithDeletedArcs_eq_finiteRadiusPuncturedBoundary_iff_outerBoundaryDefect_zero
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogStripBoundaryWithDeletedArcs N w T ρ =
        Complex.finiteAbelPlanaLogFiniteRadiusPuncturedBoundaryIntegral N w T ρ ↔
      Complex.finiteAbelPlanaLogStripOuterBoundaryDefect N w T ρ = 0 := by
  constructor
  · intro hboundary
    dsimp [Complex.finiteAbelPlanaLogStripOuterBoundaryDefect]
    have hstrip :
        Complex.finiteAbelPlanaLogStripBoundaryWithDeletedArcs N w T ρ =
          Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ -
            Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ := by
      exact
        Complex.finiteAbelPlana_log_stripBoundaryWithDeletedArcs_unfold
          N w T ρ
    have hpunctured :
        Complex.finiteAbelPlanaLogFiniteRadiusPuncturedBoundaryIntegral N w T ρ =
          Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ -
            Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ := by
      exact
        Complex.finiteAbelPlana_log_finiteRadiusPuncturedBoundaryIntegral_eq_pvNormalized_sub_deleted
          N w T ρ
    have houter :
        Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ -
            Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ =
          Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ -
            Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ := by
      exact hstrip.symm.trans (hboundary.trans hpunctured)
    exact sub_right_cancel houter
  · intro hdefect
    have houter :
        Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ =
          Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ := by
      dsimp [Complex.finiteAbelPlanaLogStripOuterBoundaryDefect] at hdefect
      exact sub_eq_zero.mp hdefect
    calc
      Complex.finiteAbelPlanaLogStripBoundaryWithDeletedArcs N w T ρ =
          Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ -
            Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ := by
        exact
          Complex.finiteAbelPlana_log_stripBoundaryWithDeletedArcs_unfold
            N w T ρ
      _ =
          Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ -
            Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ := by
        rw [houter]
      _ =
          Complex.finiteAbelPlanaLogFiniteRadiusPuncturedBoundaryIntegral N w T ρ := by
        exact
          (Complex.finiteAbelPlana_log_finiteRadiusPuncturedBoundaryIntegral_eq_pvNormalized_sub_deleted
            N w T ρ).symm

/-- Vanishing of the outer-boundary defect gives the boundary-identification
half of the finite-hole decomposition. -/
theorem Complex.finiteAbelPlana_log_stripBoundaryWithDeletedArcs_eq_finiteRadiusPuncturedBoundary_of_outerBoundaryDefect_zero
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ)
    (hdefect :
      Complex.finiteAbelPlanaLogStripOuterBoundaryDefect N w T ρ = 0) :
    Complex.finiteAbelPlanaLogStripBoundaryWithDeletedArcs N w T ρ =
      Complex.finiteAbelPlanaLogFiniteRadiusPuncturedBoundaryIntegral N w T ρ :=
  (Complex.finiteAbelPlana_log_stripBoundaryWithDeletedArcs_eq_finiteRadiusPuncturedBoundary_iff_outerBoundaryDefect_zero
    N w T ρ).2 hdefect

/-- The full finite-hole subdivision boundary is the named finite-radius
punctured boundary. -/
theorem Complex.finiteAbelPlana_log_finiteHoleSubdivisionBoundary_eq_finiteRadiusPuncturedBoundary_owner
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogFiniteHoleSubdivisionBoundary N w T ρ =
      Complex.finiteAbelPlanaLogFiniteRadiusPuncturedBoundaryIntegral N w T ρ := by
  exact
    Complex.finiteAbelPlana_log_finiteHoleSubdivisionBoundary_eq_finiteRadiusPuncturedBoundary
      N w T ρ


end

end LFunctions
end Boundary
