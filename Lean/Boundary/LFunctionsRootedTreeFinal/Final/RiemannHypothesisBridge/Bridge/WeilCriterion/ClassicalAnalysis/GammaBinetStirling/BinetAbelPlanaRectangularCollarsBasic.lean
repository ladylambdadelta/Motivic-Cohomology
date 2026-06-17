import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaVerticalStrips

/-!
# Rectangular collar geometry for finite-height Abel-Plana

This file owns the basic punctured rectangular collar and half-collar geometry
used by the endpoint indentation argument.  The right-semicircle staircase and
endpoint residue-limit layers live downstream.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open Filter MeasureTheory

/-- A nonnegative radius orders its symmetric interval. -/
theorem Real.binet_neg_radius_le_radius {ρ : ℝ}
    (hρ : 0 ≤ ρ) :
    -ρ ≤ ρ := by
  exact (neg_nonpos.mpr hρ).trans hρ

/-- A nonnegative radius has nonpositive negative endpoint. -/
theorem Real.binet_neg_radius_le_zero {ρ : ℝ}
    (hρ : 0 ≤ ρ) :
    -ρ ≤ (0 : ℝ) := by
  exact neg_nonpos.mpr hρ

/-- Adding a nonnegative radius moves a real number to the right. -/
theorem Real.binet_le_add_radius (x ρ : ℝ)
    (hρ : 0 ≤ ρ) :
    x ≤ x + ρ := by
  exact le_add_of_nonneg_right hρ

/-- Subtracting a nonnegative radius moves a real number to the left. -/
theorem Real.binet_sub_radius_le (x ρ : ℝ)
    (hρ : 0 ≤ ρ) :
    x - ρ ≤ x := by
  exact sub_le_self x hρ

/-- A symmetric interval of nonnegative radius is ordered after translating by
its center. -/
theorem Real.binet_sub_radius_le_add_radius (x ρ : ℝ)
    (hρ : 0 ≤ ρ) :
    x - ρ ≤ x + ρ := by
  exact (Real.binet_sub_radius_le x ρ hρ).trans
    (Real.binet_le_add_radius x ρ hρ)

/-- Translating a lower endpoint inequality gives a nonnegative displacement. -/
theorem Real.binet_nonneg_sub_of_le {x y : ℝ}
    (h : x ≤ y) :
    0 ≤ y - x := by
  exact sub_nonneg.mpr h

/-- Translating an upper endpoint inequality gives a radius bound on the
displacement. -/
theorem Real.binet_sub_le_radius_of_le_add {x y ρ : ℝ}
    (h : y ≤ x + ρ) :
    y - x ≤ ρ := by
  have hcomm : y ≤ ρ + x := h.trans_eq (add_comm x ρ)
  exact sub_le_iff_le_add.mpr hcomm

/-- Translating a lower symmetric endpoint inequality gives a lower radius
bound on the displacement. -/
theorem Real.binet_neg_radius_le_sub_of_sub_le {x y ρ : ℝ}
    (h : x - ρ ≤ y) :
    -ρ ≤ y - x := by
  have hcomm : -ρ + x ≤ y := by
    calc
      -ρ + x = x - ρ := by
        calc
          -ρ + x = x + -ρ := add_comm (-ρ) x
          _ = x - ρ := (sub_eq_add_neg x ρ).symm
      _ ≤ y := h
  exact le_sub_iff_add_le.mpr hcomm

/-- Translating an upper endpoint inequality against the center gives a
nonpositive displacement. -/
theorem Real.binet_sub_nonpos_of_le {x y : ℝ}
    (h : y ≤ x) :
    y - x ≤ 0 := by
  exact sub_nonpos.mpr h

/-- Bounds in the ordered interval give membership in the corresponding
unordered interval. -/
theorem Real.mem_uIcc_of_bounds
    {a b x : ℝ}
    (horder : a ≤ b)
    (h : a ≤ x ∧ x ≤ b) :
    x ∈ Set.uIcc a b :=
  Eq.mpr
    (congrArg (fun S : Set ℝ => x ∈ S) (Set.uIcc_of_le horder))
    h

/-- Membership in an unordered interval with ordered endpoints gives ordinary
closed-interval bounds. -/
theorem Real.bounds_of_mem_uIcc
    {a b x : ℝ}
    (horder : a ≤ b)
    (h : x ∈ Set.uIcc a b) :
    a ≤ x ∧ x ≤ b :=
  Eq.mp
    (congrArg (fun S : Set ℝ => x ∈ S) (Set.uIcc_of_le horder))
    h

/-- If `b = -a`, then `a = -b`. -/
theorem Complex.eq_neg_of_eq_neg
    {a b : ℂ}
    (h : b = -a) :
    a = -b := by
  calc
    a = -(-a) := (neg_neg a).symm
    _ = -b := by
      exact congrArg Neg.neg h.symm

/-- A point in `[c, c + ρ]` is within `ρ` of `c`. -/
theorem Real.abs_center_sub_le_radius_of_mem_right_interval
    {c x ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (h : c ≤ x ∧ x ≤ c + ρ) :
    |c - x| ≤ ρ := by
  have hleft : c - ρ ≤ x :=
    (Real.binet_sub_radius_le c ρ hρ).trans h.1
  have hx_sub_le :
      |x - c| ≤ ρ :=
    abs_le.mpr
      ⟨Real.binet_neg_radius_le_sub_of_sub_le hleft,
        Real.binet_sub_le_radius_of_le_add h.2⟩
  calc
    |c - x| = |x - c| := abs_sub_comm c x
    _ ≤ ρ := hx_sub_le

/-- A point in `[c - ρ, c + ρ]` is within `ρ` of `c`. -/
theorem Real.abs_center_sub_le_radius_of_mem_center_interval
    {c x ρ : ℝ}
    (h : c - ρ ≤ x ∧ x ≤ c + ρ) :
    |c - x| ≤ ρ := by
  have hx_sub_le :
      |x - c| ≤ ρ :=
    abs_le.mpr
      ⟨Real.binet_neg_radius_le_sub_of_sub_le h.1,
        Real.binet_sub_le_radius_of_le_add h.2⟩
  calc
    |c - x| = |x - c| := abs_sub_comm c x
    _ ≤ ρ := hx_sub_le

/-- The sum of two coordinate squares bounded by `ρ²` is bounded by
`(2ρ)²`, the coarse estimate used for compact rectangular collars. -/
theorem Real.two_square_radius_dominates_two_coordinate_squares
    {x y ρ : ℝ}
    (hx : x ^ 2 ≤ ρ ^ 2)
    (hy : y ^ 2 ≤ ρ ^ 2) :
    x ^ 2 + y ^ 2 ≤ (2 * ρ) ^ 2 := by
  have hsum : x ^ 2 + y ^ 2 ≤ ρ ^ 2 + ρ ^ 2 :=
    add_le_add hx hy
  have htwo_le_four : (2 : ℝ) ≤ 4 :=
    Nat.cast_le.mpr
      (show (2 : ℕ) ≤ 4 from
        Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le 2)))
  have hρsq_nonneg : 0 ≤ ρ ^ 2 :=
    sq_nonneg ρ
  have htwice : ρ ^ 2 + ρ ^ 2 ≤ (2 * ρ) ^ 2 := by
    calc
      ρ ^ 2 + ρ ^ 2 = 2 * ρ ^ 2 :=
        (two_mul (ρ ^ 2)).symm
      _ ≤ 4 * ρ ^ 2 :=
        mul_le_mul_of_nonneg_right htwo_le_four hρsq_nonneg
      _ = (2 * ρ) ^ 2 := by
        have hfour : (4 : ℝ) = (2 : ℝ) ^ 2 := by
          calc
            (4 : ℝ) = ((4 : ℕ) : ℝ) := rfl
            _ = ((2 * 2 : ℕ) : ℝ) := by
              exact congrArg Nat.cast (show (4 : ℕ) = 2 * 2 from rfl)
            _ = (2 : ℝ) * 2 :=
              Nat.cast_mul 2 2
            _ = (2 : ℝ) ^ 2 := (pow_two (2 : ℝ)).symm
        calc
          4 * ρ ^ 2 = (2 ^ 2 : ℝ) * ρ ^ 2 :=
            congrArg (fun t : ℝ => t * ρ ^ 2) hfour
          _ = (2 * ρ) ^ 2 :=
            (mul_pow 2 ρ 2).symm
  exact hsum.trans htwice

/-- Moving the `y²` term across the inequality in the circle graph equation. -/
theorem Real.circle_square_le_iff_sub_square_le
    {x y ρ : ℝ} :
    ρ ^ 2 ≤ x ^ 2 + y ^ 2 ↔ ρ ^ 2 - y ^ 2 ≤ x ^ 2 := by
  constructor
  · intro h
    exact sub_le_iff_le_add.mpr h
  · intro h
    exact sub_le_iff_le_add.mp h

/-- Reflection through `c` carries `[c, c + a]` into `[c - a, c]`. -/
theorem Real.mem_reflected_right_interval
    {c x a : ℝ}
    (h : c ≤ x ∧ x ≤ c + a) :
    2 * c - x ∈ Set.Icc (c - a) c := by
  have hlow : c - a ≤ 2 * c - x := by
    have hraw : 2 * c - (c + a) ≤ 2 * c - x :=
      sub_le_sub_left h.2 (2 * c)
    have hendpoint : 2 * c - (c + a) = c - a := by
      calc
        2 * c - (c + a) = (c + c) - (c + a) := by
          exact congrArg (fun t : ℝ => t - (c + a)) (two_mul c)
        _ = c - a :=
          add_sub_add_left_eq_sub c a c
    exact hendpoint ▸ hraw
  have hhigh : 2 * c - x ≤ c := by
    have hraw : 2 * c - x ≤ 2 * c - c :=
      sub_le_sub_left h.1 (2 * c)
    have hendpoint : 2 * c - c = c := by
      calc
        2 * c - c = (c + c) - c := by
          exact congrArg (fun t : ℝ => t - c) (two_mul c)
        _ = c :=
          add_sub_cancel_left c c
    exact hraw.trans_eq hendpoint
  exact ⟨hlow, hhigh⟩

/-- Reflection through `c` preserves the symmetric interval `[c - ρ, c + ρ]`. -/
theorem Real.mem_reflected_center_interval
    {c x ρ : ℝ}
    (h : c - ρ ≤ x ∧ x ≤ c + ρ) :
    2 * c - x ∈ Set.Icc (c - ρ) (c + ρ) := by
  have hlow : c - ρ ≤ 2 * c - x := by
    have hraw : 2 * c - (c + ρ) ≤ 2 * c - x :=
      sub_le_sub_left h.2 (2 * c)
    have hendpoint : 2 * c - (c + ρ) = c - ρ := by
      calc
        2 * c - (c + ρ) = (c + c) - (c + ρ) := by
          exact congrArg (fun t : ℝ => t - (c + ρ)) (two_mul c)
        _ = c - ρ :=
          add_sub_add_left_eq_sub c ρ c
    exact hendpoint ▸ hraw
  have hhigh : 2 * c - x ≤ c + ρ := by
    have hraw : 2 * c - x ≤ 2 * c - (c - ρ) :=
      sub_le_sub_left h.1 (2 * c)
    have hendpoint : 2 * c - (c - ρ) = c + ρ := by
      have hsub_neg : c - (-ρ) = c + ρ := by
        exact sub_neg_eq_add c ρ
      calc
        2 * c - (c - ρ) = (c + c) - (c - ρ) := by
          exact congrArg (fun t : ℝ => t - (c - ρ)) (two_mul c)
        _ = (c + c) - (c + (-ρ)) := by
          exact congrArg (fun t : ℝ => (c + c) - t) (sub_eq_add_neg c ρ)
        _ = c - (-ρ) :=
          add_sub_add_left_eq_sub c (-ρ) c
        _ = c + ρ :=
          hsub_neg
    exact hraw.trans_eq hendpoint
  exact ⟨hlow, hhigh⟩

/-- Closed rectangular collar with one round puncture removed.

This is the owner-level geometric object for the cap/collar pieces omitted by
the safe vertical strips.  Endpoint collars use semicircular variants of the
same pattern; interior collars use this full-disk version directly. -/
def Complex.finiteAbelPlanaLogPuncturedRectangularCollar
    (x₀ x₁ : ℝ)
    (T : ℝ)
    (c : ℂ)
    (ρ : ℝ) : Set ℂ :=
  ({z : ℂ | z.re ∈ Set.uIcc x₀ x₁ ∧ z.im ∈ Set.uIcc (-T) T} : Set ℂ) \
    Metric.ball c ρ

/-- Membership in a punctured rectangular collar is coordinatewise rectangle
membership plus avoidance of the deleted disk. -/
theorem Complex.mem_finiteAbelPlanaLogPuncturedRectangularCollar_iff
    {x₀ x₁ T ρ : ℝ}
    {c z : ℂ} :
    z ∈ Complex.finiteAbelPlanaLogPuncturedRectangularCollar x₀ x₁ T c ρ ↔
      z.re ∈ Set.uIcc x₀ x₁ ∧ z.im ∈ Set.uIcc (-T) T ∧
        z ∉ Metric.ball c ρ := by
  show
    ((z.re ∈ Set.uIcc x₀ x₁ ∧ z.im ∈ Set.uIcc (-T) T) ∧
        z ∉ Metric.ball c ρ) ↔
      z.re ∈ Set.uIcc x₀ x₁ ∧ z.im ∈ Set.uIcc (-T) T ∧
        z ∉ Metric.ball c ρ
  constructor
  · intro hz
    exact ⟨hz.1.1, hz.1.2, hz.2⟩
  · intro hz
    exact ⟨⟨hz.1, hz.2.1⟩, hz.2.2⟩

/-- Set-normalization lemma for feeding collar geometry into the finite
punctured rectangle.

The two hypotheses are the actual geometric obligations: the closed collar
rectangle lies in the ambient finite rectangle, and points of the punctured
collar avoid every deleted pole disk. -/
theorem Complex.finiteAbelPlanaLogPuncturedRectangularCollar_subset_puncturedRectangle
    {N : ℕ}
    {x₀ x₁ T ρ : ℝ}
    {c : ℂ}
    (hrectangle :
      ({z : ℂ | z.re ∈ Set.uIcc x₀ x₁ ∧ z.im ∈ Set.uIcc (-T) T} : Set ℂ) ⊆
        Complex.finiteAbelPlanaClosedRectangle N T)
    (havoid :
      ∀ z : ℂ,
        z.re ∈ Set.uIcc x₀ x₁ →
          z.im ∈ Set.uIcc (-T) T →
            z ∉ Metric.ball c ρ →
              ∀ m ∈ Finset.range (N + 2), z ∉ Metric.ball (m : ℂ) ρ) :
    Complex.finiteAbelPlanaLogPuncturedRectangularCollar x₀ x₁ T c ρ ⊆
      Complex.finiteAbelPlanaPuncturedRectangle N T ρ := by
  intro z hz
  have hzdata :
      z.re ∈ Set.uIcc x₀ x₁ ∧ z.im ∈ Set.uIcc (-T) T ∧
        z ∉ Metric.ball c ρ :=
    Complex.mem_finiteAbelPlanaLogPuncturedRectangularCollar_iff.mp hz
  exact
    Complex.mem_finiteAbelPlanaPuncturedRectangle_iff.mpr
      ⟨hrectangle ⟨hzdata.1, hzdata.2.1⟩,
        havoid z hzdata.1 hzdata.2.1 hzdata.2.2⟩

/-- Continuity of the Abel-Plana rectangle integrand on any punctured
rectangular collar contained in the ambient finite punctured rectangle. -/
theorem Complex.continuousOn_finiteAbelPlanaLogRectangleIntegrand_puncturedRectangularCollar
    {w : ℂ}
    {N : ℕ}
    {x₀ x₁ T ρ : ℝ}
    {c : ℂ}
    (hcollar :
      Complex.finiteAbelPlanaLogPuncturedRectangularCollar x₀ x₁ T c ρ ⊆
        Complex.finiteAbelPlanaPuncturedRectangle N T ρ)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    ContinuousOn
      (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
      (Complex.finiteAbelPlanaLogPuncturedRectangularCollar x₀ x₁ T c ρ) := by
  exact hcont.mono hcollar

/-- Holomorphy of the Abel-Plana rectangle integrand on any punctured
rectangular collar contained in the ambient finite punctured rectangle. -/
theorem Complex.differentiableOn_finiteAbelPlanaLogRectangleIntegrand_puncturedRectangularCollar
    {w : ℂ}
    {N : ℕ}
    {x₀ x₁ T ρ : ℝ}
    {c : ℂ}
    (hcollar :
      Complex.finiteAbelPlanaLogPuncturedRectangularCollar x₀ x₁ T c ρ ⊆
        Complex.finiteAbelPlanaPuncturedRectangle N T ρ)
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    DifferentiableOn ℂ
      (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
      (Complex.finiteAbelPlanaLogPuncturedRectangularCollar x₀ x₁ T c ρ) := by
  exact hdiff.mono hcollar

/-- Generic oriented boundary integral of a rectangular collar with one round
deleted disk.

The convention is the ordinary rectangle boundary minus the counterclockwise
inner circular boundary. -/
noncomputable def Complex.puncturedRectangularCollarBoundaryIntegral
    (f : ℂ → ℂ)
    (x₀ x₁ T : ℝ)
    (c : ℂ)
    (ρ : ℝ) : ℂ :=
  (∫ x : ℝ in x₀..x₁, f ((x : ℂ) - Complex.I * (T : ℂ))) -
    (∫ x : ℝ in x₀..x₁, f ((x : ℂ) + Complex.I * (T : ℂ))) +
      Complex.I * (∫ y : ℝ in (-T)..T, f ((x₁ : ℂ) + Complex.I * (y : ℂ))) -
        Complex.I * (∫ y : ℝ in (-T)..T, f ((x₀ : ℂ) + Complex.I * (y : ℂ))) -
          circleIntegral f c ρ

/-- The right half-rectangle collar outside a deleted disk centered at `c`.

This is the local model for a left endpoint indentation: the safe vertical side
is at `Re z = c.re + a`, while the deleted inner boundary is the right
semicircle of radius `ρ` about `c`. -/
def Complex.rightHalfRectangleDeletedDiskDomain
    (c : ℂ)
    (T a ρ : ℝ) : Set ℂ :=
  ({z : ℂ | z.re ∈ Set.uIcc c.re (c.re + a) ∧
      z.im ∈ Set.uIcc (c.im - T) (c.im + T)} : Set ℂ) \
    Metric.ball c ρ

/-- The left half-rectangle collar outside a deleted disk centered at `c`.

This is the local model for a right endpoint indentation or the left
semicollar around an interior deleted integer. -/
def Complex.leftHalfRectangleDeletedDiskDomain
    (c : ℂ)
    (T a ρ : ℝ) : Set ℂ :=
  ({z : ℂ | z.re ∈ Set.uIcc (c.re - a) c.re ∧
      z.im ∈ Set.uIcc (c.im - T) (c.im + T)} : Set ℂ) \
    Metric.ball c ρ

/-- The actual right half-rectangle collar used by the local indentation
Cauchy theorem.

The ambient `T`-height versions below only supply regularity on a larger
neighborhood.  The curvilinear boundary itself lives at height `ρ`, so this is
the owner domain for the local Cauchy-Goursat theorem. -/
def Complex.rightHalfRectangleDeletedDiskCoreDomain
    (c : ℂ)
    (a ρ : ℝ) : Set ℂ :=
  ({z : ℂ | z.re ∈ Set.uIcc c.re (c.re + a) ∧
      z.im ∈ Set.uIcc (c.im - ρ) (c.im + ρ)} : Set ℂ) \
    Metric.ball c ρ

/-- The actual left half-rectangle collar used by the local indentation
Cauchy theorem. -/
def Complex.leftHalfRectangleDeletedDiskCoreDomain
    (c : ℂ)
    (a ρ : ℝ) : Set ℂ :=
  ({z : ℂ | z.re ∈ Set.uIcc (c.re - a) c.re ∧
      z.im ∈ Set.uIcc (c.im - ρ) (c.im + ρ)} : Set ℂ) \
    Metric.ball c ρ

/-- Lower quarter of the right tangent-box cap outside the deleted disk. -/
def Complex.rightDeletedDiskLowerTangentBoxCapDomain
    (c : ℂ)
    (ρ : ℝ) : Set ℂ :=
  ({z : ℂ | z.re ∈ Set.uIcc c.re (c.re + ρ) ∧
      z.im ∈ Set.uIcc (c.im - ρ) c.im} : Set ℂ) \
    Metric.ball c ρ

/-- Upper quarter of the right tangent-box cap outside the deleted disk. -/
def Complex.rightDeletedDiskUpperTangentBoxCapDomain
    (c : ℂ)
    (ρ : ℝ) : Set ℂ :=
  ({z : ℂ | z.re ∈ Set.uIcc c.re (c.re + ρ) ∧
      z.im ∈ Set.uIcc c.im (c.im + ρ)} : Set ℂ) \
    Metric.ball c ρ

/-- The right semicircle written as a graph over the vertical coordinate. -/
noncomputable def Complex.rightDeletedDiskTangentBoxCircleGraphRe
    (c : ℂ)
    (ρ y : ℝ) : ℝ :=
  c.re + Real.sqrt (ρ ^ 2 - (y - c.im) ^ 2)

/-- Unfolding of the real-coordinate graph for the right deleted disk. -/
theorem Complex.rightDeletedDiskTangentBoxCircleGraphRe_unfold
    (c : ℂ)
    (ρ y : ℝ) :
    Complex.rightDeletedDiskTangentBoxCircleGraphRe c ρ y =
      c.re + Real.sqrt (ρ ^ 2 - (y - c.im) ^ 2) := by
  rfl

/-- The shifted graph coordinate is bounded by the radius. -/
theorem Complex.rightDeletedDiskTangentBoxCircleGraphRe_shift_le_radius
    (c : ℂ)
    {ρ y : ℝ}
    (hρ : 0 ≤ ρ) :
    Real.sqrt (ρ ^ 2 - (y - c.im) ^ 2) ≤ ρ := by
  exact
    (Real.sqrt_le_iff).mpr
      ⟨hρ, sub_le_self (ρ ^ 2) (sq_nonneg (y - c.im))⟩

/-- Shifted graph control gives absolute graph control in real coordinates. -/
theorem Complex.rightDeletedDiskTangentBoxCircleGraphRe_le_of_shift
    {c z : ℂ}
    {ρ : ℝ}
    (h :
      Real.sqrt (ρ ^ 2 - (z.im - c.im) ^ 2) ≤ z.re - c.re) :
    Complex.rightDeletedDiskTangentBoxCircleGraphRe c ρ z.im ≤ z.re := by
  calc
    Complex.rightDeletedDiskTangentBoxCircleGraphRe c ρ z.im =
        c.re + Real.sqrt (ρ ^ 2 - (z.im - c.im) ^ 2) :=
      Complex.rightDeletedDiskTangentBoxCircleGraphRe_unfold c ρ z.im
    _ =
        Real.sqrt (ρ ^ 2 - (z.im - c.im) ^ 2) + c.re :=
      add_comm c.re (Real.sqrt (ρ ^ 2 - (z.im - c.im) ^ 2))
    _ ≤ z.re :=
      le_sub_iff_add_le.mp h

/-- The circular graph lies to the left of the outer right edge of the tangent
box. -/
theorem Complex.rightDeletedDiskTangentBoxCircleGraphRe_le_right_edge
    (c : ℂ)
    {ρ y : ℝ}
    (hρ : 0 ≤ ρ) :
    Complex.rightDeletedDiskTangentBoxCircleGraphRe c ρ y ≤ c.re + ρ := by
  have hsqrt_le :
      Real.sqrt (ρ ^ 2 - (y - c.im) ^ 2) ≤ ρ := by
    exact
      Complex.rightDeletedDiskTangentBoxCircleGraphRe_shift_le_radius c hρ
  calc
    Complex.rightDeletedDiskTangentBoxCircleGraphRe c ρ y =
        c.re + Real.sqrt (ρ ^ 2 - (y - c.im) ^ 2) :=
      Complex.rightDeletedDiskTangentBoxCircleGraphRe_unfold c ρ y
    _ ≤ c.re + ρ :=
      add_le_add_left hsqrt_le c.re

/-- Any point to the right of the circular graph is to the right of the
circle center. -/
theorem Complex.center_re_le_of_graphRe_le
    {c z : ℂ}
    {ρ : ℝ}
    (h :
      Complex.rightDeletedDiskTangentBoxCircleGraphRe c ρ z.im ≤ z.re) :
    c.re ≤ z.re := by
  have hcenter :
      c.re ≤ Complex.rightDeletedDiskTangentBoxCircleGraphRe c ρ z.im := by
    calc
      c.re ≤ c.re + Real.sqrt (ρ ^ 2 - (z.im - c.im) ^ 2) :=
        le_add_of_nonneg_right
          (Real.sqrt_nonneg (ρ ^ 2 - (z.im - c.im) ^ 2))
      _ = Complex.rightDeletedDiskTangentBoxCircleGraphRe c ρ z.im :=
        (Complex.rightDeletedDiskTangentBoxCircleGraphRe_unfold c ρ z.im).symm
  exact hcenter.trans h

/-- Absolute graph control gives the shifted graph inequality. -/
theorem Complex.rightDeletedDiskTangentBox_shift_le_of_graphRe_le
    {c z : ℂ}
    {ρ : ℝ}
    (h :
      Complex.rightDeletedDiskTangentBoxCircleGraphRe c ρ z.im ≤ z.re) :
    Real.sqrt (ρ ^ 2 - (z.im - c.im) ^ 2) ≤ z.re - c.re := by
  exact
    le_sub_iff_add_le.mpr
      (by
        calc
          Real.sqrt (ρ ^ 2 - (z.im - c.im) ^ 2) + c.re =
              c.re + Real.sqrt (ρ ^ 2 - (z.im - c.im) ^ 2) :=
            add_comm (Real.sqrt (ρ ^ 2 - (z.im - c.im) ^ 2)) c.re
          _ = Complex.rightDeletedDiskTangentBoxCircleGraphRe c ρ z.im :=
            rfl
          _ ≤ z.re :=
            h)

/-- Adding `π` to a circle angle negates the complex exponential. -/
theorem Complex.exp_I_mul_ofReal_add_pi
    (θ : ℝ) :
    Complex.exp (Complex.I * (((θ + Real.pi : ℝ) : ℂ))) =
      -Complex.exp (Complex.I * (θ : ℂ)) := by
  have hsplit :
      Complex.I * (((θ + Real.pi : ℝ) : ℂ)) =
        Complex.I * (θ : ℂ) + (Real.pi : ℂ) * Complex.I := by
    calc
      Complex.I * (((θ + Real.pi : ℝ) : ℂ)) =
          Complex.I * ((θ : ℂ) + (Real.pi : ℂ)) := by
        exact congrArg (fun z : ℂ => Complex.I * z)
          (Complex.ofReal_add θ Real.pi)
      _ = Complex.I * (θ : ℂ) + Complex.I * (Real.pi : ℂ) := by
        exact mul_add Complex.I (θ : ℂ) (Real.pi : ℂ)
      _ = Complex.I * (θ : ℂ) + (Real.pi : ℂ) * Complex.I := by
        exact congrArg
          (fun z : ℂ => Complex.I * (θ : ℂ) + z)
          (mul_comm Complex.I (Real.pi : ℂ))
  calc
    Complex.exp (Complex.I * (((θ + Real.pi : ℝ) : ℂ))) =
        Complex.exp (Complex.I * (θ : ℂ) + (Real.pi : ℂ) * Complex.I) := by
      exact congrArg Complex.exp hsplit
    _ = Complex.exp (Complex.I * (θ : ℂ)) *
        Complex.exp ((Real.pi : ℂ) * Complex.I) := by
      exact Complex.exp_add (Complex.I * (θ : ℂ)) ((Real.pi : ℂ) * Complex.I)
    _ = Complex.exp (Complex.I * (θ : ℂ)) * (-1) := by
      exact congrArg
        (fun z : ℂ => Complex.exp (Complex.I * (θ : ℂ)) * z)
        Complex.exp_pi_mul_I
    _ = -Complex.exp (Complex.I * (θ : ℂ)) :=
      mul_neg_one (Complex.exp (Complex.I * (θ : ℂ)))

/-- Shifting the left right-semicircle endpoint by `π` gives `π / 2`. -/
theorem Real.neg_pi_div_two_add_pi_eq_pi_div_two :
    -(Real.pi / 2) + Real.pi = Real.pi / 2 := by
  calc
    -(Real.pi / 2) + Real.pi =
        Real.pi - Real.pi / 2 := by
      exact
        (add_comm (-(Real.pi / 2)) Real.pi).trans
          (sub_eq_add_neg Real.pi (Real.pi / 2)).symm
    _ = Real.pi / 2 := by
      exact sub_eq_iff_eq_add.mpr (add_halves Real.pi).symm

/-- Shifting the right right-semicircle endpoint by `π` gives `3π / 2`. -/
theorem Real.pi_div_two_add_pi_eq_three_pi_div_two :
    Real.pi / 2 + Real.pi = 3 * Real.pi / 2 := by
  have hthree_mul_pi :
      (3 : ℝ) * Real.pi = Real.pi + Real.pi + Real.pi := by
    calc
      (3 : ℝ) * Real.pi = (3 : ℕ) • Real.pi := by
        exact (nsmul_eq_mul 3 Real.pi).symm
      _ = Real.pi + (Real.pi + Real.pi) :=
        three_nsmul Real.pi
      _ = Real.pi + Real.pi + Real.pi :=
        (add_assoc Real.pi Real.pi Real.pi).symm
  have hpair :
      (Real.pi + Real.pi) / 2 = Real.pi := by
    calc
      (Real.pi + Real.pi) / 2 =
          Real.pi / 2 + Real.pi / 2 :=
        add_div Real.pi Real.pi 2
      _ = Real.pi :=
        add_halves Real.pi
  have hthree :
      (3 : ℝ) * Real.pi / 2 =
        Real.pi + Real.pi / 2 := by
    calc
      (3 : ℝ) * Real.pi / 2 =
          (Real.pi + Real.pi + Real.pi) / 2 := by
        exact congrArg (fun z : ℝ => z / 2) hthree_mul_pi
      _ = (Real.pi + Real.pi) / 2 + Real.pi / 2 := by
        exact add_div (Real.pi + Real.pi) Real.pi 2
      _ = Real.pi + Real.pi / 2 := by
        exact congrArg (fun z : ℝ => z + Real.pi / 2) hpair
  calc
    Real.pi / 2 + Real.pi =
        Real.pi + Real.pi / 2 :=
      add_comm (Real.pi / 2) Real.pi
    _ = 3 * Real.pi / 2 :=
      hthree.symm

/-- Reflecting the right endpoint of `[x, x + a]` through `x`. -/
theorem Real.two_mul_sub_add_self
    (x a : ℝ) :
    2 * x - (x + a) = x - a := by
  calc
    2 * x - (x + a) = (x + x) - (x + a) := by
      exact congrArg (fun t : ℝ => t - (x + a)) (two_mul x)
    _ = x - a :=
      add_sub_add_left_eq_sub x a x

/-- Reflecting the center endpoint through itself. -/
theorem Real.two_mul_sub_self
    (x : ℝ) :
    2 * x - x = x := by
  calc
    2 * x - x = (x + x) - x := by
      exact congrArg (fun t : ℝ => t - x) (two_mul x)
    _ = x :=
      add_sub_cancel_right x x

/-- Reflecting the left endpoint of `[x - a, x + a]` through `x`. -/
theorem Real.two_mul_sub_sub_self
    (x a : ℝ) :
    2 * x - (x - a) = x + a := by
  have hcancel :
      (x + x) + -x = x := by
    calc
      (x + x) + -x = (x + x) - x :=
        (sub_eq_add_neg (x + x) x).symm
      _ = x :=
        add_sub_cancel_right x x
  have hneg_sub :
      -(x - a) = -x + a := by
    calc
      -(x - a) = a - x :=
        neg_sub x a
      _ = a + -x :=
        sub_eq_add_neg a x
      _ = -x + a :=
        add_comm a (-x)
  calc
    2 * x - (x - a) = (x + x) - (x - a) := by
      exact congrArg (fun t : ℝ => t - (x - a)) (two_mul x)
    _ = (x + x) + -(x - a) :=
      sub_eq_add_neg (x + x) (x - a)
    _ = (x + x) + (-x + a) := by
      exact congrArg (fun t : ℝ => (x + x) + t) hneg_sub
    _ = ((x + x) + -x) + a :=
      (add_assoc (x + x) (-x) a).symm
    _ = x + a := by
      exact congrArg (fun t : ℝ => t + a) hcancel

/-- The lower tangent-box cap as the closed graph region to the right of the
deleted circle.  This is the domain used by the polygonal-exhaustion proof of
the lower quarter-cap Cauchy theorem. -/
def Complex.rightDeletedDiskLowerTangentBoxGraphDomain
    (c : ℂ)
    (ρ : ℝ) : Set ℂ :=
  {z : ℂ |
    z.im ∈ Set.uIcc (c.im - ρ) c.im ∧
      z.re ∈
        Set.uIcc
          (Complex.rightDeletedDiskTangentBoxCircleGraphRe c ρ z.im)
          (c.re + ρ)}

/-- The upper tangent-box cap as the closed graph region to the right of the
deleted circle.  This is the domain used by the polygonal-exhaustion proof of
the upper quarter-cap Cauchy theorem. -/
def Complex.rightDeletedDiskUpperTangentBoxGraphDomain
    (c : ℂ)
    (ρ : ℝ) : Set ℂ :=
  {z : ℂ |
    z.im ∈ Set.uIcc c.im (c.im + ρ) ∧
      z.re ∈
        Set.uIcc
          (Complex.rightDeletedDiskTangentBoxCircleGraphRe c ρ z.im)
          (c.re + ρ)}

/-- Real coordinate form of the right circular graph inside a tangent box.

If `0 ≤ x ≤ ρ` and `|y| ≤ ρ`, then lying outside the open disk of radius `ρ`
is equivalent to lying to the right of the graph
`x = sqrt (ρ² - y²)`. -/
theorem Real.tangentBox_outside_circle_iff_graph_right
    {x y ρ : ℝ}
    (hρ : 0 < ρ)
    (hx : x ∈ Set.uIcc 0 ρ)
    (hy : y ∈ Set.uIcc (-ρ) ρ) :
    ρ ≤ Real.sqrt (x ^ 2 + y ^ 2) ↔
      Real.sqrt (ρ ^ 2 - y ^ 2) ≤ x := by
  have hx_bounds : 0 ≤ x ∧ x ≤ ρ := by
    exact
      Eq.mp
        (congrArg (fun S : Set ℝ => x ∈ S) (Set.uIcc_of_le hρ.le))
        hx
  have hy_bounds : -ρ ≤ y ∧ y ≤ ρ := by
    exact
      Eq.mp
        (congrArg
          (fun S : Set ℝ => y ∈ S)
          (Set.uIcc_of_le (Real.binet_neg_radius_le_radius hρ.le)))
        hy
  have hx_nonneg : 0 ≤ x := hx_bounds.1
  have hsum_nonneg : 0 ≤ x ^ 2 + y ^ 2 := by
    exact add_nonneg (sq_nonneg x) (sq_nonneg y)
  have hrad_nonneg : 0 ≤ ρ ^ 2 - y ^ 2 := by
    have hy_abs : |y| ≤ ρ := by
      exact abs_le.mpr ⟨hy_bounds.1, hy_bounds.2⟩
    have hy_sq : y ^ 2 ≤ ρ ^ 2 := by
      exact sq_le_sq' hy_bounds.1 hy_bounds.2
    exact sub_nonneg.mpr hy_sq
  constructor
  · intro hcircle
    have hsquare :
        ρ ^ 2 ≤ x ^ 2 + y ^ 2 := by
      have hmul :
          ρ * ρ ≤
            Real.sqrt (x ^ 2 + y ^ 2) *
              Real.sqrt (x ^ 2 + y ^ 2) :=
        mul_self_le_mul_self hρ.le hcircle
      calc
        ρ ^ 2 = ρ * ρ := by
          exact sq ρ
        _ ≤ Real.sqrt (x ^ 2 + y ^ 2) *
            Real.sqrt (x ^ 2 + y ^ 2) :=
          hmul
        _ = x ^ 2 + y ^ 2 :=
          Real.mul_self_sqrt hsum_nonneg
    exact
      (Real.sqrt_le_iff).mpr
        ⟨hx_nonneg,
          (Real.circle_square_le_iff_sub_square_le).mp hsquare⟩
  · intro hgraph
    have hgraph_sq : ρ ^ 2 - y ^ 2 ≤ x ^ 2 :=
      (Real.sqrt_le_iff.mp hgraph).2
    have hsquare : ρ ^ 2 ≤ x ^ 2 + y ^ 2 := by
      exact (Real.circle_square_le_iff_sub_square_le).mpr hgraph_sq
    exact
      (Real.le_sqrt hρ.le hsum_nonneg).mpr hsquare

/-- Lower half specialization of the tangent-box circle graph criterion. -/
theorem Real.lowerTangentBox_outside_circle_iff_graph_right
    {x y ρ : ℝ}
    (hρ : 0 < ρ)
    (hx : x ∈ Set.uIcc 0 ρ)
    (hy : y ∈ Set.uIcc (-ρ) 0) :
    ρ ≤ Real.sqrt (x ^ 2 + y ^ 2) ↔
      Real.sqrt (ρ ^ 2 - y ^ 2) ≤ x := by
  have hy_full : y ∈ Set.uIcc (-ρ) ρ := by
    have hy_bounds : -ρ ≤ y ∧ y ≤ 0 := by
      exact
        Eq.mp
          (congrArg
            (fun S : Set ℝ => y ∈ S)
            (Set.uIcc_of_le (Real.binet_neg_radius_le_zero hρ.le)))
          hy
    have hleft : -ρ ≤ y := hy_bounds.1
    have hright : y ≤ ρ := hy_bounds.2.trans hρ.le
    exact
      Eq.mpr
        (congrArg
          (fun S : Set ℝ => y ∈ S)
          (Set.uIcc_of_le (Real.binet_neg_radius_le_radius hρ.le)))
        (And.intro hleft hright)
  exact Real.tangentBox_outside_circle_iff_graph_right hρ hx hy_full

/-- Upper half specialization of the tangent-box circle graph criterion. -/
theorem Real.upperTangentBox_outside_circle_iff_graph_right
    {x y ρ : ℝ}
    (hρ : 0 < ρ)
    (hx : x ∈ Set.uIcc 0 ρ)
    (hy : y ∈ Set.uIcc 0 ρ) :
    ρ ≤ Real.sqrt (x ^ 2 + y ^ 2) ↔
      Real.sqrt (ρ ^ 2 - y ^ 2) ≤ x := by
  have hy_full : y ∈ Set.uIcc (-ρ) ρ := by
    have hy_bounds : 0 ≤ y ∧ y ≤ ρ := by
      exact
        Eq.mp
          (congrArg (fun S : Set ℝ => y ∈ S) (Set.uIcc_of_le hρ.le))
          hy
    have hleft : -ρ ≤ y :=
      (Real.binet_neg_radius_le_zero hρ.le).trans hy_bounds.1
    have hright : y ≤ ρ := hy_bounds.2
    exact
      Eq.mpr
        (congrArg
          (fun S : Set ℝ => y ∈ S)
          (Set.uIcc_of_le (Real.binet_neg_radius_le_radius hρ.le)))
        (And.intro hleft hright)
  exact Real.tangentBox_outside_circle_iff_graph_right hρ hx hy_full

/-- The right core collar is the `T = ρ` specialization of the taller ambient
right collar. -/
theorem Complex.rightHalfRectangleDeletedDiskCoreDomain_eq_heightDomain
    (c : ℂ)
    (a ρ : ℝ) :
    Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ =
      Complex.rightHalfRectangleDeletedDiskDomain c ρ a ρ := by
  rfl

/-- The left core collar is the `T = ρ` specialization of the taller ambient
left collar. -/
theorem Complex.leftHalfRectangleDeletedDiskCoreDomain_eq_heightDomain
    (c : ℂ)
    (a ρ : ℝ) :
    Complex.leftHalfRectangleDeletedDiskCoreDomain c a ρ =
      Complex.leftHalfRectangleDeletedDiskDomain c ρ a ρ := by
  rfl

/-- The finite right collar core is compact. -/
theorem Complex.isCompact_rightHalfRectangleDeletedDiskCoreDomain_self
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ) :
    IsCompact (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ) := by
  have hre_order : c.re ≤ c.re + ρ :=
    Real.binet_le_add_radius c.re ρ hρ.le
  have him_order : c.im - ρ ≤ c.im + ρ :=
    Real.binet_sub_radius_le_add_radius c.im ρ hρ.le
  have hrect_closed :
      IsClosed
        ({z : ℂ |
          z.re ∈ Set.uIcc c.re (c.re + ρ) ∧
            z.im ∈ Set.uIcc (c.im - ρ) (c.im + ρ)} : Set ℂ) := by
    have hre_closed :
        IsClosed {z : ℂ | z.re ∈ Set.Icc c.re (c.re + ρ)} :=
      isClosed_Icc.preimage Complex.continuous_re
    have him_closed :
        IsClosed {z : ℂ | z.im ∈ Set.Icc (c.im - ρ) (c.im + ρ)} :=
      isClosed_Icc.preimage Complex.continuous_im
    have hset :
        ({z : ℂ |
          z.re ∈ Set.uIcc c.re (c.re + ρ) ∧
            z.im ∈ Set.uIcc (c.im - ρ) (c.im + ρ)} : Set ℂ) =
          ({z : ℂ | z.re ∈ Set.Icc c.re (c.re + ρ)} ∩
            {z : ℂ | z.im ∈ Set.Icc (c.im - ρ) (c.im + ρ)}) := by
      ext z
      have hre_iff :
          z.re ∈ Set.uIcc c.re (c.re + ρ) ↔
            z.re ∈ Set.Icc c.re (c.re + ρ) :=
        (congrArg (fun S : Set ℝ => z.re ∈ S)
          (Set.uIcc_of_le hre_order)).to_iff
      have him_iff :
          z.im ∈ Set.uIcc (c.im - ρ) (c.im + ρ) ↔
            z.im ∈ Set.Icc (c.im - ρ) (c.im + ρ) :=
        (congrArg (fun S : Set ℝ => z.im ∈ S)
          (Set.uIcc_of_le him_order)).to_iff
      exact
        Iff.trans
          (and_congr hre_iff him_iff)
          Iff.rfl
    exact hset.symm ▸ hre_closed.inter him_closed
  have hclosed :
      IsClosed (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ) := by
    have hcore_eq :
        Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ =
          ({z : ℂ |
            z.re ∈ Set.uIcc c.re (c.re + ρ) ∧
              z.im ∈ Set.uIcc (c.im - ρ) (c.im + ρ)} : Set ℂ) \
            Metric.ball c ρ := rfl
    have hcore_closed :
        IsClosed
          (({z : ℂ |
            z.re ∈ Set.uIcc c.re (c.re + ρ) ∧
              z.im ∈ Set.uIcc (c.im - ρ) (c.im + ρ)} : Set ℂ) \
            Metric.ball c ρ) :=
      hrect_closed.inter Metric.isOpen_ball.isClosed_compl
    exact hcore_eq.symm ▸ hcore_closed
  have hbounded :
      Bornology.IsBounded
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ) := by
    refine (Metric.isBounded_iff_subset_closedBall c).2 ⟨2 * ρ, ?_⟩
    intro z hz
    have hrect :
        z.re ∈ Set.uIcc c.re (c.re + ρ) ∧
          z.im ∈ Set.uIcc (c.im - ρ) (c.im + ρ) := hz.1
    have hre_pair : c.re ≤ z.re ∧ z.re ≤ c.re + ρ := by
      exact
        Eq.mp
          (congrArg (fun S : Set ℝ => z.re ∈ S) (Set.uIcc_of_le hre_order))
          hrect.1
    have him_pair : c.im - ρ ≤ z.im ∧ z.im ≤ c.im + ρ := by
      exact
        Eq.mp
          (congrArg (fun S : Set ℝ => z.im ∈ S) (Set.uIcc_of_le him_order))
          hrect.2
    have hre_abs : |c.re - z.re| ≤ ρ := by
      exact
        Real.abs_center_sub_le_radius_of_mem_right_interval
          hρ.le hre_pair
    have him_abs : |c.im - z.im| ≤ ρ := by
      exact
        Real.abs_center_sub_le_radius_of_mem_center_interval
          him_pair
    have hre_abs_bounds : -ρ ≤ c.re - z.re ∧ c.re - z.re ≤ ρ :=
      abs_le.mp hre_abs
    have him_abs_bounds : -ρ ≤ c.im - z.im ∧ c.im - z.im ≤ ρ :=
      abs_le.mp him_abs
    have hre_sq : (c.re - z.re) ^ 2 ≤ ρ ^ 2 :=
      sq_le_sq' hre_abs_bounds.1 hre_abs_bounds.2
    have him_sq : (c.im - z.im) ^ 2 ≤ ρ ^ 2 :=
      sq_le_sq' him_abs_bounds.1 him_abs_bounds.2
    have hrad_le :
        (c.re - z.re) ^ 2 + (c.im - z.im) ^ 2 ≤ (2 * ρ) ^ 2 := by
      exact
        Real.two_square_radius_dominates_two_coordinate_squares
          hre_sq him_sq
    have hdist :
        dist c z ≤ Real.sqrt ((2 * ρ) ^ 2) := by
      exact
        Eq.mpr
          (congrArg
            (fun r : ℝ => r ≤ Real.sqrt ((2 * ρ) ^ 2))
            (Complex.dist_eq_re_im c z))
          (Real.sqrt_le_sqrt hrad_le)
    have hsqrt : Real.sqrt ((2 * ρ) ^ 2) = 2 * ρ :=
      Real.sqrt_sq (mul_nonneg zero_le_two hρ.le)
    have hdist_to_center : dist z c ≤ 2 * ρ := by
      calc
        dist z c = dist c z := dist_comm z c
        _ ≤ Real.sqrt ((2 * ρ) ^ 2) := hdist
        _ = 2 * ρ := hsqrt
    exact Metric.mem_closedBall.mpr hdist_to_center
  exact Metric.isCompact_of_isClosed_isBounded hclosed hbounded

/-- Continuity on the finite right collar core is uniformly continuous there. -/
theorem Complex.uniformContinuousOn_rightHalfRectangleDeletedDiskCoreDomain_self
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    UniformContinuousOn f
      (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ) := by
  exact
    (Complex.isCompact_rightHalfRectangleDeletedDiskCoreDomain_self c hρ).uniformContinuousOn_of_continuous
      hcont

/-- Oriented boundary integral of the right half-rectangle core collar outside
the deleted disk.

This is `lower - upper + right vertical - inner right semicircle`, written in
the interval-integral convention already used throughout the Abel-Plana file. -/
noncomputable def Complex.rightHalfRectangleDeletedDiskCoreBoundaryIntegral
    (f : ℂ → ℂ)
    (c : ℂ)
    (a ρ : ℝ) : ℂ :=
  (∫ x : ℝ in c.re..(c.re + a),
      f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) +
      -(∫ x : ℝ in c.re..(c.re + a),
        f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) +
        Complex.I *
          (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
            f (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
      ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
        f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- Ordinary rectangular tail of the right deleted half-rectangle core.

This is the straight rectangular piece between the vertical line tangent to the
deleted disk and the safe vertical side at `c.re + a`. -/
noncomputable def Complex.rightHalfRectangleDeletedDiskCoreRectangularTailBoundaryIntegral
    (f : ℂ → ℂ)
    (c : ℂ)
    (a ρ : ℝ) : ℂ :=
  (∫ x : ℝ in (c.re + ρ)..(c.re + a),
      f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) -
    (∫ x : ℝ in (c.re + ρ)..(c.re + a),
      f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) +
      Complex.I *
        (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
          f (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
        Complex.I *
          (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
            f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))

/-- Unfolding of the ordinary rectangular tail boundary convention. -/
theorem Complex.rightHalfRectangleDeletedDiskCoreRectangularTailBoundaryIntegral_unfold
    (f : ℂ → ℂ)
    (c : ℂ)
    (a ρ : ℝ) :
    Complex.rightHalfRectangleDeletedDiskCoreRectangularTailBoundaryIntegral f c a ρ =
      (∫ x : ℝ in (c.re + ρ)..(c.re + a),
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) -
        (∫ x : ℝ in (c.re + ρ)..(c.re + a),
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) +
          Complex.I *
            (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
              f (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
            Complex.I *
              (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
                f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) :=
  rfl

/-- The tangent-width semicircular core of the right deleted half-rectangle.

This is the only genuinely curvilinear local object left after removing the
ordinary rectangular tail. -/
noncomputable def Complex.rightHalfRectangleDeletedDiskSemicircularCoreBoundaryIntegral
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ) : ℂ :=
  Complex.rightHalfRectangleDeletedDiskCoreBoundaryIntegral f c ρ ρ

/-- Lower quarter-cap boundary of the right tangent-box collar.

The boundary is the lower tangent chord, the lower half of the vertical tangent
chord, and the lower circular indentation arc with deleted-boundary
orientation. -/
noncomputable def Complex.rightDeletedDiskLowerTangentBoxCapBoundaryIntegral
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ) : ℂ :=
  (∫ x : ℝ in c.re..(c.re + ρ),
      f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) +
    Complex.I *
      (∫ y : ℝ in (c.im - ρ)..c.im,
        f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
      ∫ θ : ℝ in (-(Real.pi / 2))..0,
        f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- Upper quarter-cap boundary of the right tangent-box collar.

The boundary is the upper half of the vertical tangent chord, the upper tangent
chord with opposite orientation, and the upper circular indentation arc with
deleted-boundary orientation. -/
noncomputable def Complex.rightDeletedDiskUpperTangentBoxCapBoundaryIntegral
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ) : ℂ :=
  -(∫ x : ℝ in c.re..(c.re + ρ),
      f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) +
    Complex.I *
      (∫ y : ℝ in c.im..(c.im + ρ),
        f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
      ∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2),
        f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- Complex line integral over the straight segment from `z₀` to `z₁`. -/
noncomputable def Complex.lineSegmentIntegral
    (f : ℂ → ℂ)
    (z₀ z₁ : ℂ) : ℂ :=
  ∫ t : ℝ in (0 : ℝ)..1,
    f (((1 - t : ℝ) : ℂ) * z₀ + ((t : ℝ) : ℂ) * z₁) * (z₁ - z₀)

/-- Uniform partition point on `[a,b]`, using `m + 1` subintervals. -/
noncomputable def Real.uniformPartitionPoint
    (a b : ℝ)
    (m k : ℕ) : ℝ :=
  a + ((k : ℝ) / (m + 1 : ℝ)) * (b - a)

/-- Polygonal line integral along a parametrized curve sampled on the uniform
partition of `[a,b]`. -/
noncomputable def Complex.curveUniformPolygonalLineIntegral
    (f : ℂ → ℂ)
    (γ : ℝ → ℂ)
    (a b : ℝ)
    (m : ℕ) : ℂ :=
  ∑ k in Finset.range (m + 1),
    Complex.lineSegmentIntegral f
      (γ (Real.uniformPartitionPoint a b m k))
      (γ (Real.uniformPartitionPoint a b m (k + 1)))

/-- Lower circular-arc sample angle for the `m`th polygonal approximation. -/
noncomputable def Complex.lowerTangentBoxArcSampleAngle
    (m k : ℕ) : ℝ :=
  -(Real.pi / 2) + ((k : ℝ) / (m + 1 : ℝ)) * (Real.pi / 2)

/-- Upper circular-arc sample angle for the `m`th polygonal approximation. -/
noncomputable def Complex.upperTangentBoxArcSampleAngle
    (m k : ℕ) : ℝ :=
  ((k : ℝ) / (m + 1 : ℝ)) * (Real.pi / 2)

/-- Lower circular-arc sample point for the `m`th polygonal approximation. -/
noncomputable def Complex.lowerTangentBoxArcSamplePoint
    (c : ℂ)
    (ρ : ℝ)
    (m k : ℕ) : ℂ :=
  c + (ρ : ℂ) *
    Complex.exp (Complex.I *
      ((Complex.lowerTangentBoxArcSampleAngle m k : ℝ) : ℂ))

/-- Upper circular-arc sample point for the `m`th polygonal approximation. -/
noncomputable def Complex.upperTangentBoxArcSamplePoint
    (c : ℂ)
    (ρ : ℝ)
    (m k : ℕ) : ℂ :=
  c + (ρ : ℂ) *
    Complex.exp (Complex.I *
      ((Complex.upperTangentBoxArcSampleAngle m k : ℝ) : ℂ))

/-- The true lower circular arc integral appearing in the lower tangent-box
boundary. -/
noncomputable def Complex.lowerTangentBoxCircularArcIntegral
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ) : ℂ :=
  ∫ θ : ℝ in (-(Real.pi / 2))..0,
    f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
      (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- The true upper circular arc integral appearing in the upper tangent-box
boundary. -/
noncomputable def Complex.upperTangentBoxCircularArcIntegral
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ) : ℂ :=
  ∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2),
    f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
      (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- Polygonal chord-chain approximation to the lower circular arc. -/
noncomputable def Complex.lowerTangentBoxPolygonalArcIntegral
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m : ℕ) : ℂ :=
  ∑ k in Finset.range (m + 1),
    Complex.lineSegmentIntegral f
      (Complex.lowerTangentBoxArcSamplePoint c ρ m k)
      (Complex.lowerTangentBoxArcSamplePoint c ρ m (k + 1))

/-- Polygonal chord-chain approximation to the upper circular arc. -/
noncomputable def Complex.upperTangentBoxPolygonalArcIntegral
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m : ℕ) : ℂ :=
  ∑ k in Finset.range (m + 1),
    Complex.lineSegmentIntegral f
      (Complex.upperTangentBoxArcSamplePoint c ρ m k)
      (Complex.upperTangentBoxArcSamplePoint c ρ m (k + 1))

/-- Polygonal approximation to the lower tangent-box cap boundary. -/
noncomputable def Complex.rightDeletedDiskLowerTangentBoxPolygonalBoundaryIntegral
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m : ℕ) : ℂ :=
  (∫ x : ℝ in c.re..(c.re + ρ),
      f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) +
    Complex.I *
      (∫ y : ℝ in (c.im - ρ)..c.im,
        f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
      Complex.lowerTangentBoxPolygonalArcIntegral f c ρ m

/-- Polygonal approximation to the upper tangent-box cap boundary. -/
noncomputable def Complex.rightDeletedDiskUpperTangentBoxPolygonalBoundaryIntegral
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m : ℕ) : ℂ :=
  -(∫ x : ℝ in c.re..(c.re + ρ),
      f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) +
    Complex.I *
      (∫ y : ℝ in c.im..(c.im + ρ),
        f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
      Complex.upperTangentBoxPolygonalArcIntegral f c ρ m

/-- Oriented boundary integral of the left half-rectangle core collar outside
the deleted disk. -/
noncomputable def Complex.leftHalfRectangleDeletedDiskCoreBoundaryIntegral
    (f : ℂ → ℂ)
    (c : ℂ)
    (a ρ : ℝ) : ℂ :=
  (∫ x : ℝ in (c.re - a)..c.re,
      f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) +
      -(∫ x : ℝ in (c.re - a)..c.re,
        f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) -
        Complex.I *
          (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
            f (((c.re - a : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
      ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
        f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

end

end LFunctions
end Boundary
