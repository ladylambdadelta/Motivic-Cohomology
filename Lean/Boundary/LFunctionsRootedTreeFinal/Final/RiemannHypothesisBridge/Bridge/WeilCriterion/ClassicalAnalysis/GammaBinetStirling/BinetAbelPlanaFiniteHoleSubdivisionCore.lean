import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Nat.Digits
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicircleCoreCauchy

/-!
# Finite-hole subdivision core vocabulary

This file owns the low-level arithmetic, strip, cap/collar, and expansion lemmas
used by the finite-hole Abel-Plana subdivision.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped Topology Interval

theorem Real.finiteAbelPlana_one_lt_four : (1 : ℝ) < 4 := by
  calc
    (1 : ℝ) < 1 + 1 :=
      lt_add_of_pos_right (1 : ℝ) zero_lt_one
    _ = 2 := one_add_one_eq_two
    _ < 2 + 1 :=
      lt_add_of_pos_right (2 : ℝ) zero_lt_one
    _ = 3 := two_add_one_eq_three
    _ < 3 + 1 :=
      lt_add_of_pos_right (3 : ℝ) zero_lt_one
    _ = 4 := three_add_one_eq_four

/-- The numerical inequality `2 < 4`, isolated for the Abel-Plana quarter gap. -/
theorem Real.finiteAbelPlana_two_lt_four : (2 : ℝ) < 4 := by
  calc
    (2 : ℝ) < 2 + 1 :=
      lt_add_of_pos_right (2 : ℝ) zero_lt_one
    _ = 3 := two_add_one_eq_three
    _ < 3 + 1 :=
      lt_add_of_pos_right (3 : ℝ) zero_lt_one
    _ = 4 := three_add_one_eq_four

/-- The Abel-Plana quarter gap is strictly smaller than one. -/
theorem Real.finiteAbelPlana_one_div_four_lt_one :
    (1 : ℝ) / 4 < 1 := by
  calc
    (1 : ℝ) / 4 < (1 : ℝ) / 1 :=
      one_div_lt_one_div_of_lt zero_lt_one Real.finiteAbelPlana_one_lt_four
    _ = 1 := div_one (1 : ℝ)

/-- The Abel-Plana quarter gap is strictly smaller than one half. -/
theorem Real.finiteAbelPlana_one_div_four_lt_one_div_two :
    (1 : ℝ) / 4 < (1 : ℝ) / 2 :=
  one_div_lt_one_div_of_lt zero_lt_two Real.finiteAbelPlana_two_lt_four

/-- Two half units add to one. -/
theorem Real.finiteAbelPlana_half_add_half :
    (1 : ℝ) / 2 + (1 : ℝ) / 2 = 1 :=
  add_halves (1 : ℝ)

/-- Three-term additive rotation used by finite subdivision base cases. -/
theorem Complex.finiteAbelPlana_add_rotate_middle
    (a b c : ℂ) :
    (a + b) + c = b + (a + c) := by
  calc
    (a + b) + c = a + (b + c) :=
      add_assoc a b c
    _ = b + (a + c) :=
      add_left_comm a b c

/-- Boundary-sum cancellation in the form `V + (P - V) = P`. -/
theorem Complex.finiteAbelPlana_add_sub_cancel_boundary
    (V P : ℂ) :
    V + (P - V) = P := by
  calc
    V + (P - V) = V + (P + (-V)) := by
      exact congrArg (fun z : ℂ => V + z) (sub_eq_add_neg P V)
    _ = P + (V + (-V)) := by
      exact add_left_comm V P (-V)
    _ = P + 0 := by
      exact congrArg (fun z : ℂ => P + z) (add_neg_cancel V)
    _ = P :=
      add_zero P

/-- Reassociate a boundary sum after cancelling an intermediate strip sum. -/
theorem Complex.finiteAbelPlana_boundary_sum_cancel_then_sub
    (V P D : ℂ) :
    V + (P - V) - D = P - D := by
  calc
    V + (P - V) - D =
        (V + (P - V)) - D := rfl
    _ = P - D := by
      exact congrArg (fun z : ℂ => z - D)
        (Complex.finiteAbelPlana_add_sub_cancel_boundary V P)

/-- The Nat inequality `1 < 3`, used by the finite subdivision indexing. -/
theorem Nat.finiteAbelPlana_one_lt_three : 1 < 3 :=
  Nat.succ_lt_succ (Nat.zero_lt_succ 1)

/-- Odd safe-strip nodes occur before the final endpoint node. -/
theorem Nat.finiteAbelPlana_odd_node_lt_last
    {k N : ℕ}
    (hk : k ≤ N) :
    2 * k + 1 < 2 * N + 3 := by
  have hmul : 2 * k ≤ 2 * N :=
    Nat.mul_le_mul_left 2 hk
  have hle : 2 * k + 1 ≤ 2 * N + 1 :=
    Nat.add_le_add_right hmul 1
  have htail : 2 * N + 1 < 2 * N + 3 :=
    Nat.add_lt_add_left Nat.finiteAbelPlana_one_lt_three (2 * N)
  exact lt_of_le_of_lt hle htail

/-- Even safe-strip successor nodes occur before the final endpoint node. -/
theorem Nat.finiteAbelPlana_even_succ_node_lt_last
    {k N : ℕ}
    (hk : k ≤ N) :
    2 * k + 2 < 2 * N + 3 := by
  have hmul : 2 * k ≤ 2 * N :=
    Nat.mul_le_mul_left 2 hk
  have hle : 2 * k + 2 ≤ 2 * N + 2 :=
    Nat.add_le_add_right hmul 2
  have htail : 2 * N + 2 < 2 * N + 3 :=
    Nat.lt_succ_self (2 * N + 2)
  exact lt_of_le_of_lt hle htail

/-- Odd endpoint arithmetic in the horizontal subdivision chain. -/
theorem Nat.finiteAbelPlana_two_mul_add_one_comm
    (k : ℕ) :
    2 * k + 1 = k * 2 + 1 :=
  congrArg (fun x : ℕ => x + 1) (Nat.mul_comm 2 k)

/-- The successor of an odd endpoint index is the next doubled successor. -/
theorem Nat.finiteAbelPlana_two_mul_add_one_add_one_eq_succ_mul_two
    (k : ℕ) :
    2 * k + 1 + 1 = (k + 1) * 2 := by
  calc
    2 * k + 1 + 1 = 2 * k + (1 + 1) :=
      Eq.symm (Nat.add_assoc (2 * k) 1 1)
    _ = 2 * k + 2 := rfl
    _ = k * 2 + 2 := by
      exact congrArg (fun x : ℕ => x + 2) (Nat.mul_comm 2 k)
    _ = k * 2 + 1 * 2 := rfl
    _ = (k + 1) * 2 := by
      exact Eq.symm (Nat.add_mul k 1 2)

/-- The final successor step in the horizontal subdivision chain. -/
theorem Nat.finiteAbelPlana_last_index_succ_succ
    (N : ℕ) :
    2 * (N + 1) + 3 = (2 * N + 3) + 2 := by
  calc
    2 * (N + 1) + 3 = (2 * N + 2 * 1) + 3 := by
      exact congrArg (fun x : ℕ => x + 3) (Nat.mul_add 2 N 1)
    _ = (2 * N + 2) + 3 := rfl
    _ = 2 * N + (2 + 3) :=
      Nat.add_assoc (2 * N) 2 3
    _ = 2 * N + (3 + 2) := by
      exact congrArg (fun x : ℕ => 2 * N + x) (Nat.add_comm 2 3)
    _ = (2 * N + 3) + 2 :=
      Eq.symm (Nat.add_assoc (2 * N) 3 2)

/-- The final predecessor plus one is the final endpoint index. -/
theorem Nat.finiteAbelPlana_last_predecessor_add_one
    (N : ℕ) :
    2 * N + 2 + 1 = 2 * N + 3 := by
  calc
    2 * N + 2 + 1 = 2 * N + (2 + 1) :=
      Eq.symm (Nat.add_assoc (2 * N) 2 1)
    _ = 2 * N + 3 := rfl

/-- The predecessor of a non-final subdivision index is bounded by the last
interior predecessor. -/
theorem Nat.finiteAbelPlana_pred_le_last_interior_of_lt_last
    {N i : ℕ}
    (hi : i < 2 * N + 3) :
    i - 1 ≤ 2 * N + 1 := by
  have hi_le : i ≤ 2 * N + 2 :=
    Nat.lt_succ_iff.mp hi
  exact Nat.pred_le_iff.mpr hi_le

/-- The half of the last odd interior predecessor is the last strip index. -/
theorem Nat.finiteAbelPlana_two_mul_add_one_div_two
    (N : ℕ) :
    (2 * N + 1) / 2 = N := by
  calc
    (2 * N + 1) / 2 = (1 + 2 * N) / 2 := by
      exact
        congrArg (fun x : ℕ => x / 2)
          (Nat.add_comm (2 * N) 1)
    _ = 1 / 2 + N := Nat.add_mul_div_left 1 N Nat.two_pos
    _ = 0 + N := by
      exact congrArg (fun x : ℕ => x + N) (Nat.div_eq_of_lt one_lt_two)
    _ = N := Nat.zero_add N

/-- A number below the last interior predecessor has half bounded by `N`. -/
theorem Nat.finiteAbelPlana_div_two_le_of_le_last_interior
    {N j : ℕ}
    (hj : j ≤ 2 * N + 1) :
    j / 2 ≤ N := by
  have hdiv : j / 2 ≤ (2 * N + 1) / 2 :=
    Nat.div_le_div_right hj
  exact
    le_trans hdiv
      (le_of_eq (Nat.finiteAbelPlana_two_mul_add_one_div_two N))

/-- A positive odd branch index gives a nonzero half-successor. -/
theorem Nat.finiteAbelPlana_one_le_succ_div_two_of_pos
    {j : ℕ}
    (hj : 0 < j) :
    1 ≤ (j + 1) / 2 := by
  have hone_le_j : 1 ≤ j := hj
  have htwo_le_succ : 2 ≤ j + 1 :=
    Nat.succ_le_succ hone_le_j
  exact (Nat.one_le_div_iff Nat.two_pos).mpr htwo_le_succ

/-- A successor below the doubled final endpoint has half bounded by `N+1`. -/
theorem Nat.finiteAbelPlana_succ_div_two_le_succ_of_le_last_interior
    {N j : ℕ}
    (hj : j ≤ 2 * N + 1) :
    (j + 1) / 2 ≤ N + 1 := by
  have hsucc : j + 1 ≤ 2 * N + 2 :=
    Nat.succ_le_succ hj
  have htarget : j + 1 ≤ 2 * (N + 1) := by
    calc
      j + 1 ≤ 2 * N + 2 := hsucc
      _ = 2 * (N + 1) := by
        exact Eq.symm (Nat.mul_add 2 N 1)
  exact Nat.div_le_of_le_mul' htarget

/-- The concrete vertical-strip orientation `right - left` is the same as the
abstract side-expression convention with the left edge stored as a negative
contribution. -/
theorem Complex.finiteAbelPlana_verticalStrip_orientedSide_sub_left_eq_add_leftContribution
    (lower upper right left : ℂ) :
    lower - upper + Complex.I * right - Complex.I * left =
      lower - upper + Complex.I * right + (-Complex.I * left) := by
  calc
    lower - upper + Complex.I * right - Complex.I * left =
        lower - upper + Complex.I * right + (-(Complex.I * left)) := by
      exact sub_eq_add_neg
        (lower - upper + Complex.I * right)
        (Complex.I * left)
    _ = lower - upper + Complex.I * right + (-Complex.I * left) := by
      exact congrArg
        (fun z : ℂ => lower - upper + Complex.I * right + z)
        (Eq.symm (neg_mul Complex.I left))

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
    (hT : 0 < T)
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

/-- The lower horizontal finite strip parametrization can be written in the
vertical-strip owner convention with height `-T`. -/
theorem Complex.finiteAbelPlana_lowerHorizontal_sub_eq_add_neg_height
    (x T : ℝ) :
    (x : ℂ) - Complex.I * (T : ℂ) =
      (x : ℂ) + Complex.I * ((-T : ℝ) : ℂ) := by
  calc
    (x : ℂ) - Complex.I * (T : ℂ) =
        (x : ℂ) + (-(Complex.I * (T : ℂ))) := by
      exact sub_eq_add_neg (x : ℂ) (Complex.I * (T : ℂ))
    _ = (x : ℂ) + Complex.I * ((-T : ℝ) : ℂ) := by
      exact congrArg
        (fun z : ℂ => (x : ℂ) + z)
        (Eq.trans
          (Eq.symm (mul_neg Complex.I (T : ℂ)))
          (congrArg (fun z : ℂ => Complex.I * z)
            (Eq.symm (map_neg Complex.ofRealCLM T))))

/-- The local lower side agrees with the imported vertical-strip lower edge. -/
theorem Complex.finiteAbelPlana_log_verticalStripLowerSide_eq_lowerEdge
    (k : ℕ)
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ =
      Complex.finiteAbelPlanaLogVerticalStripLowerEdge
        w
        (Complex.finiteAbelPlanaVerticalStripLeft k ρ)
        (Complex.finiteAbelPlanaVerticalStripRight k ρ)
        (-T) := by
  exact
    intervalIntegral.integral_congr
      (fun x _hx =>
        congrArg
          (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
          (Complex.finiteAbelPlana_lowerHorizontal_sub_eq_add_neg_height x T))

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
  have hlower :
      Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ =
        Complex.finiteAbelPlanaLogVerticalStripLowerEdge
          w
          (Complex.finiteAbelPlanaVerticalStripLeft k ρ)
          (Complex.finiteAbelPlanaVerticalStripRight k ρ)
          (-T) :=
    Complex.finiteAbelPlana_log_verticalStripLowerSide_eq_lowerEdge k w T ρ
  have hright :
      Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide k w T ρ =
        Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution
          w
          (Complex.finiteAbelPlanaVerticalStripRight k ρ)
          (-T)
          T :=
    Eq.symm
      (Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution_unfold
        w
        (Complex.finiteAbelPlanaVerticalStripRight k ρ)
        (-T)
        T)
  have hleft :
      -(Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide k w T ρ) =
        Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution
          w
          (Complex.finiteAbelPlanaVerticalStripLeft k ρ)
          (-T)
          T := by
    exact
      Eq.trans
        (Eq.symm
          (neg_mul Complex.I
            (Complex.finiteAbelPlanaLogVerticalStripLeftSide k w T ρ)))
        (Eq.symm
          (Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution_unfold
            w
            (Complex.finiteAbelPlanaVerticalStripLeft k ρ)
            (-T)
            T))
  have hbody :
      Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ -
          Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide k w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide k w T ρ =
        Complex.finiteAbelPlanaLogVerticalStripSideExpression
          w
          (Complex.finiteAbelPlanaVerticalStripLeft k ρ)
          (Complex.finiteAbelPlanaVerticalStripRight k ρ)
          (-T)
          T := by
    calc
      Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ -
          Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide k w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide k w T ρ =
        Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ -
          Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide k w T ρ +
              (-(Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide k w T ρ)) := by
        exact sub_eq_add_neg
          (Complex.finiteAbelPlanaLogVerticalStripLowerSide k w T ρ -
            Complex.finiteAbelPlanaLogVerticalStripUpperSide k w T ρ +
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide k w T ρ)
          (Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide k w T ρ)
      _ =
        Complex.finiteAbelPlanaLogVerticalStripLowerEdge
          w
          (Complex.finiteAbelPlanaVerticalStripLeft k ρ)
          (Complex.finiteAbelPlanaVerticalStripRight k ρ)
          (-T) -
          Complex.finiteAbelPlanaLogVerticalStripUpperEdge
            w
            (Complex.finiteAbelPlanaVerticalStripLeft k ρ)
            (Complex.finiteAbelPlanaVerticalStripRight k ρ)
            T +
          Complex.finiteAbelPlanaLogVerticalSubdivisionRightContribution
            w
            (Complex.finiteAbelPlanaVerticalStripRight k ρ)
            (-T)
            T +
          Complex.finiteAbelPlanaLogVerticalSubdivisionLeftContribution
            w
            (Complex.finiteAbelPlanaVerticalStripLeft k ρ)
            (-T)
            T := by
        exact congrArg₂
          HAdd.hAdd
          (congrArg₂
            HAdd.hAdd
            (congrArg₂ HSub.hSub hlower rfl)
            hright)
          hleft
      _ =
        Complex.finiteAbelPlanaLogVerticalStripSideExpression
          w
          (Complex.finiteAbelPlanaVerticalStripLeft k ρ)
          (Complex.finiteAbelPlanaVerticalStripRight k ρ)
          (-T)
          T := by
        exact Eq.symm
          (Complex.finiteAbelPlana_log_verticalStripSideExpression_unfold
            w
            (Complex.finiteAbelPlanaVerticalStripLeft k ρ)
            (Complex.finiteAbelPlanaVerticalStripRight k ρ)
            (-T)
            T)
  exact congrArg
    (fun z : ℂ => ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ * z)
    hbody

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
  exact lt_trans hρquarter Real.finiteAbelPlana_one_div_four_lt_one

/-- A positive radius below the Abel-Plana quarter-gap leaves a nonempty safe
interval between two adjacent collars. -/
theorem Real.rho_lt_one_sub_rho_of_lt_one_div_four
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hρquarter : ρ < (1 : ℝ) / 4) :
    ρ < 1 - ρ := by
  have hρ_lt_half : ρ < (1 : ℝ) / 2 := by
    exact
      lt_trans hρquarter
        Real.finiteAbelPlana_one_div_four_lt_one_div_two
  have htwoρ_lt_one : ρ + ρ < 1 := by
    calc
      ρ + ρ < (1 : ℝ) / 2 + (1 : ℝ) / 2 := add_lt_add hρ_lt_half hρ_lt_half
      _ = 1 := Real.finiteAbelPlana_half_add_half
  exact lt_sub_iff_add_lt'.mpr htwoρ_lt_one

/-- Four named substitutions assemble the horizontal subdivision sum with its
safe-strip, endpoint-collar, and interior-collar pieces. -/
theorem Complex.add_triple_congr
    {a b c d a' b' c' d' : ℂ}
    (ha : a = a')
    (hb : b = b')
    (hc : c = c')
    (hd : d = d') :
    a + (b + c + d) = a' + (b' + c' + d') := by
  calc
    a + (b + c + d) = a' + (b + c + d) :=
      congrArg (fun z : ℂ => z + (b + c + d)) ha
    _ = a' + (b' + c + d) :=
      congrArg (fun z : ℂ => a' + (z + c + d)) hb
    _ = a' + (b' + c' + d) :=
      congrArg (fun z : ℂ => a' + (b' + z + d)) hc
    _ = a' + (b' + c' + d') :=
      congrArg (fun z : ℂ => a' + (b' + c' + z)) hd

/-- Base-case additive rearrangement for the horizontal subdivision reindexing. -/
theorem Complex.finiteAbelPlana_horizontalSubdivision_base_algebra
    (a b c : ℂ) :
    a + b + c = b + (a + c + 0) := by
  calc
    a + b + c = b + (a + c) :=
      Complex.finiteAbelPlana_add_rotate_middle a b c
    _ = b + (a + c + 0) := by
      exact congrArg (fun z : ℂ => b + z) (Eq.symm (add_zero (a + c)))

/-- Two-step expansion of a range sum. -/
theorem Finset.sum_range_add_two_complex
    (G : ℕ → ℂ)
    (m : ℕ) :
    (∑ i in Finset.range (m + 2), G i) =
      (∑ i in Finset.range m, G i) + G m + G (m + 1) := by
  have hlast :
      (∑ i in Finset.range (m + 2), G i) =
        (∑ i in Finset.range (m + 1), G i) + G (m + 1) :=
    Finset.sum_range_succ (f := G) (n := m + 1)
  have hprev :
      (∑ i in Finset.range (m + 1), G i) =
        (∑ i in Finset.range m, G i) + G m :=
    Finset.sum_range_succ (f := G) (n := m)
  exact
    Eq.trans hlast
      (congrArg
        (fun z : ℂ => z + G (m + 1))
        hprev)

/-- Successor-step additive rearrangement for the horizontal subdivision
reindexing induction. -/
theorem Complex.finiteAbelPlana_horizontalSubdivision_succ_algebra
    (A B C D E F : ℂ) :
    A + (B + C + D) + E + F =
      A + E + (B + F + (D + C)) := by
  have htail :
      (B + C + D) + F = B + F + (D + C) := by
    calc
      (B + C + D) + F = B + (C + D) + F := by
        exact congrArg (fun z : ℂ => z + F) (add_assoc B C D)
      _ = B + ((C + D) + F) :=
        add_assoc B (C + D) F
      _ = B + (F + (C + D)) := by
        exact congrArg (fun z : ℂ => B + z) (add_comm (C + D) F)
      _ = B + (F + (D + C)) := by
        exact congrArg (fun z : ℂ => B + (F + z)) (add_comm C D)
      _ = B + F + (D + C) :=
        Eq.symm (add_assoc B F (D + C))
  calc
    A + (B + C + D) + E + F =
        A + E + ((B + C + D) + F) := by
      calc
        A + (B + C + D) + E + F =
            (A + (B + C + D) + E) + F := rfl
        _ = ((B + C + D) + (A + E)) + F := by
          exact congrArg
            (fun z : ℂ => z + F)
            (Complex.finiteAbelPlana_add_rotate_middle A (B + C + D) E)
        _ = (A + E) + ((B + C + D) + F) := by
          calc
            ((B + C + D) + (A + E)) + F =
                (B + C + D) + ((A + E) + F) :=
              add_assoc (B + C + D) (A + E) F
            _ = ((A + E) + F) + (B + C + D) :=
              add_comm (B + C + D) ((A + E) + F)
            _ = (A + E) + (F + (B + C + D)) :=
              add_assoc (A + E) F (B + C + D)
            _ = (A + E) + ((B + C + D) + F) := by
              exact congrArg
                (fun z : ℂ => (A + E) + z)
                (add_comm F (B + C + D))
    _ = A + E + (B + F + (D + C)) := by

      exact congrArg (fun z : ℂ => A + E + z) htail

end

end LFunctions
end Boundary
