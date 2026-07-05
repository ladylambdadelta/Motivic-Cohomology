import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseCore
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseCurvatureLower
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.SecondDerivativeVdc

/-!
# Real-phase shifted logarithmic differences

This file owns the elementary shifted-difference facts used by the
second-derivative van der Corput packet estimates for the logarithmic phase.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Shifted logarithmic phase used in the Weyl differencing step. -/
def Complex.logarithmicPhaseRealPhase_shiftedDifference
    (t : ℝ)
    (h : ℕ)
    (x : ℝ) : ℝ :=
  Complex.realPhase_secondDerivative_vdc_shiftedDifference
    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) h x

/-- The derivative of the shifted logarithmic phase difference is the
difference of the endpoint derivatives. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_deriv_eq
    (t : ℝ)
    {h : ℕ}
    {x : ℝ}
    (hx : 0 < x) :
    deriv (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) x =
      deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (x + h) -
        deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  have hh_nonneg : (0 : ℝ) ≤ ((h : ℕ) : ℝ) :=
    Nat.cast_nonneg h
  have hx_shift_pos : 0 < x + h :=
    lt_of_lt_of_le hx (le_add_of_nonneg_right hh_nonneg)
  have hleft :
      HasDerivAt (fun y : ℝ => φ (y + h))
        (deriv φ (x + h)) x := by
    have hid : HasDerivAt (fun y : ℝ => y) 1 x :=
      hasDerivAt_id x
    have hshift : HasDerivAt (fun y : ℝ => y + h) 1 x :=
      hid.add_const h
    have hphase_formula :
        HasDerivAt φ (-t / (x + h)) (x + h) :=
      Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_hasDerivAt
        t hx_shift_pos
    have hphase_deriv_eq :
        deriv φ (x + h) = -t / (x + h) :=
      hphase_formula.deriv
    have hphase :
        HasDerivAt φ (deriv φ (x + h)) (x + h) :=
      Eq.subst
        (motive := fun d : ℝ => HasDerivAt φ d (x + h))
        hphase_deriv_eq.symm
        hphase_formula
    have hcomp :
        HasDerivAt (fun y : ℝ => φ (y + h))
          ((deriv φ (x + h)) * 1) x :=
      hphase.comp x hshift
    exact
      Eq.subst
        (motive := fun d : ℝ =>
          HasDerivAt (fun y : ℝ => φ (y + h)) d x)
        (mul_one (deriv φ (x + h)))
        hcomp
  have hright_formula :
      HasDerivAt φ (-t / x) x :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_hasDerivAt
      t hx
  have hright_deriv_eq :
      deriv φ x = -t / x :=
    hright_formula.deriv
  have hright :
      HasDerivAt φ (deriv φ x) x :=
    Eq.subst
      (motive := fun d : ℝ => HasDerivAt φ d x)
      hright_deriv_eq.symm
      hright_formula
  have hsub :
      HasDerivAt
        (fun y : ℝ => φ (y + h) - φ y)
        (deriv φ (x + h) - deriv φ x)
        x :=
    hleft.sub hright
  exact hsub.deriv

/-- In the nonnegative branch, the shifted logarithmic derivative is the
difference of the positive reciprocal profile at the two endpoints. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_deriv_eq_norm_div_sub
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {h : ℕ}
    {x : ℝ}
    (hx : 0 < x) :
    deriv (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) x =
      ‖t‖ / x - ‖t‖ / (x + h) := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  have hh_nonneg : (0 : ℝ) ≤ ((h : ℕ) : ℝ) :=
    Nat.cast_nonneg h
  have hx_shift_pos : 0 < x + h :=
    lt_of_lt_of_le hx (le_add_of_nonneg_right hh_nonneg)
  have hshifted :
      deriv (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) x =
        deriv φ (x + h) - deriv φ x :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_deriv_eq
      t hx
  have hright_endpoint :
      deriv φ (x + h) =
        -(‖t‖ / (x + h)) :=
    Complex.logarithmicPhaseRealPhase_deriv_eq_neg_norm_div_parenthesized
      t ht_nonneg hx_shift_pos
  have hleft_endpoint :
      deriv φ x =
        -(‖t‖ / x) :=
    Complex.logarithmicPhaseRealPhase_deriv_eq_neg_norm_div_parenthesized
      t ht_nonneg hx
  have hendpoint_sub :
      deriv φ (x + h) - deriv φ x =
        ‖t‖ / x - ‖t‖ / (x + h) := by
    exact
      Eq.subst
        (motive := fun left : ℝ =>
          left - deriv φ x = ‖t‖ / x - ‖t‖ / (x + h))
        hright_endpoint.symm
        (Eq.subst
          (motive := fun right : ℝ =>
            -(‖t‖ / (x + h)) - right =
              ‖t‖ / x - ‖t‖ / (x + h))
          hleft_endpoint.symm
          (neg_sub_neg (‖t‖ / (x + h)) (‖t‖ / x)))
  exact Eq.trans hshifted hendpoint_sub

/-- A summation index in the shifted-correlation range lies in the parent
real block. -/
theorem Nat.cast_mem_parent_Icc_of_mem_shifted_Icc
    {a b h n : ℕ}
    (hn : n ∈ Finset.Icc a (b - h)) :
    (n : ℝ) ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) := by
  have hn_bounds : a ≤ n ∧ n ≤ b - h :=
    Finset.mem_Icc.mp hn
  have hn_le_b : n ≤ b := by
    have hb_sub_le : b - h ≤ b :=
      Nat.sub_le b h
    exact le_trans hn_bounds.2 hb_sub_le
  exact
    And.intro
      (Nat.cast_le.mpr hn_bounds.1)
      (Nat.cast_le.mpr (le_trans hn_le_b (Nat.le_succ b)))

/-- A shifted summation index in the shifted-correlation range lies in the
parent real block. -/
theorem Nat.cast_add_mem_parent_Icc_of_mem_shifted_Icc
    {a b h n : ℕ}
    (hh : h ≤ b - a)
    (hn : n ∈ Finset.Icc a (b - h)) :
    ((n : ℝ) + h) ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) := by
  have hn_bounds : a ≤ n ∧ n ≤ b - h :=
    Finset.mem_Icc.mp hn
  have h_le_b : h ≤ b :=
    le_trans hh (Nat.sub_le b a)
  have hn_add_le_sub_add : n + h ≤ (b - h) + h :=
    Nat.add_le_add_right hn_bounds.2 h
  have hsub_add_eq : (b - h) + h = b :=
    Nat.sub_add_cancel h_le_b
  have hn_add_le_b : n + h ≤ b :=
    Eq.subst
      (motive := fun r : ℕ => n + h ≤ r)
      hsub_add_eq
      hn_add_le_sub_add
  have ha_le_n_add : a ≤ n + h :=
    le_trans hn_bounds.1 (Nat.le_add_right n h)
  have hcast_add :
      (((n + h : ℕ) : ℝ)) = (n : ℝ) + h :=
    Nat.cast_add n h
  exact
    Eq.subst
      (motive := fun x : ℝ =>
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ))
      hcast_add
      (And.intro
        (Nat.cast_le.mpr ha_le_n_add)
        (Nat.cast_le.mpr (le_trans hn_add_le_b (Nat.le_succ b))))

/-- The right endpoint of the shifted real interval transports to the right
endpoint of the parent interval. -/
theorem Nat.cast_shifted_endpoint_add_le_parent_endpoint
    {a b h : ℕ}
    (hh : h ≤ b - a) :
    (((b - h + 1 : ℕ) : ℝ) + h) ≤ ((b + 1 : ℕ) : ℝ) := by
  have h_le_b : h ≤ b :=
    le_trans hh (Nat.sub_le b a)
  have hend_nat :
      (b - h + 1) + h = b + 1 := by
    calc
      (b - h + 1) + h = (b - h + h) + 1 :=
        add_right_comm (b - h) 1 h
      _ = b + 1 :=
        congrArg (fun n : ℕ => n + 1) (Nat.sub_add_cancel h_le_b)
  have hend_cast :
      (((b - h + 1) + h : ℕ) : ℝ) = ((b + 1 : ℕ) : ℝ) :=
    congrArg (fun n : ℕ => (n : ℝ)) hend_nat
  have hleft_cast :
      (((b - h + 1) + h : ℕ) : ℝ) =
        ((b - h + 1 : ℕ) : ℝ) + h :=
    Nat.cast_add (b - h + 1) h
  exact
    Eq.subst
      (motive := fun r : ℝ =>
        r ≤ ((b + 1 : ℕ) : ℝ))
      hleft_cast
      (le_of_eq hend_cast)

/-- A point in the shifted real interval lies in the parent real block. -/
theorem Real.mem_parent_Icc_of_mem_shifted_Icc
    {a b h : ℕ}
    {x : ℝ}
    (hx : x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)) :
    x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) := by
  have hright_nat : b - h + 1 ≤ b + 1 :=
    Nat.succ_le_succ (Nat.sub_le b h)
  exact
    And.intro hx.1
      (le_trans hx.2 (Nat.cast_le.mpr hright_nat))

/-- A shifted point in the shifted real interval lies in the parent real
block. -/
theorem Real.add_nat_mem_parent_Icc_of_mem_shifted_Icc
    {a b h : ℕ}
    {x : ℝ}
    (hh : h ≤ b - a)
    (hx : x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)) :
    x + h ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) := by
  have hh_nonneg : (0 : ℝ) ≤ ((h : ℕ) : ℝ) :=
    Nat.cast_nonneg h
  have hleft : (a : ℝ) ≤ x + h :=
    le_trans hx.1 (le_add_of_nonneg_right hh_nonneg)
  have hright :
      x + h ≤ ((b + 1 : ℕ) : ℝ) :=
    le_trans
      (add_le_add_right hx.2 ((h : ℕ) : ℝ))
      (Nat.cast_shifted_endpoint_add_le_parent_endpoint hh)
  exact And.intro hleft hright

/-- Derivative lower bound for a shifted logarithmic phase difference in the
positive-frequency branch. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_deriv_lower_of_growth
    (t : ℝ)
    {a b h : ℕ}
    {x : ℝ}
    (ha : 1 ≤ a)
    (hx : x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ))
    (hx_shift :
      x + h ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ))
    (hderiv_growth :
      ∀ u v : ℝ,
        u ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        v ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        u ≤ v →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (v - u) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) v -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) u)) :
    (‖t‖ *
        ((((b + 1 : ℕ) : ℝ) *
          (((b + 1 : ℕ) : ℝ)))⁻¹) *
        ((h : ℕ) : ℝ) ≤
      deriv (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) x) := by
  have ha_pos : (0 : ℝ) < (a : ℝ) :=
    Nat.cast_pos.mpr (Nat.lt_of_succ_le ha)
  have hx_pos : 0 < x :=
    lt_of_lt_of_le ha_pos hx.1
  have hh_nonneg : (0 : ℝ) ≤ ((h : ℕ) : ℝ) :=
    Nat.cast_nonneg h
  have hx_le_shift : x ≤ x + h :=
    le_add_of_nonneg_right hh_nonneg
  have hgrowth :
      (‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          ((x + h) - x) ≤
        deriv
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) (x + h) -
        deriv
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x) :=
    hderiv_growth x (x + h) hx hx_shift hx_le_shift
  have hdiff :
      (x + h) - x = ((h : ℕ) : ℝ) := by
    exact add_sub_cancel_left x ((h : ℕ) : ℝ)
  have hderiv_eq :
      deriv (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) x =
        deriv
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) (x + h) -
        deriv
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_deriv_eq t hx_pos
  exact
    Eq.subst
      (motive := fun left : ℝ =>
        left ≤ deriv (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) x)
      (congrArg
        (fun r : ℝ =>
          ‖t‖ *
            ((((b + 1 : ℕ) : ℝ) *
              (((b + 1 : ℕ) : ℝ)))⁻¹) *
            r)
        hdiff)
      (Eq.subst
        (motive := fun right : ℝ =>
          ‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              ((x + h) - x) ≤ right)
        hderiv_eq.symm
        hgrowth)

/-- Integer-index form of the shifted-difference derivative lower bound on a
shifted-correlation packet. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_deriv_lower_of_growth_at_nat
    (t : ℝ)
    {a b h n : ℕ}
    (ha : 1 ≤ a)
    (hh : h ≤ b - a)
    (hn : n ∈ Finset.Icc a (b - h))
    (hderiv_growth :
      ∀ u v : ℝ,
        u ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        v ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        u ≤ v →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (v - u) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) v -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) u)) :
    (‖t‖ *
        ((((b + 1 : ℕ) : ℝ) *
          (((b + 1 : ℕ) : ℝ)))⁻¹) *
        ((h : ℕ) : ℝ) ≤
      deriv (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) n) := by
  have hn_parent :
      (n : ℝ) ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
    Nat.cast_mem_parent_Icc_of_mem_shifted_Icc hn
  have hn_shift_parent :
      ((n : ℝ) + h) ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
    Nat.cast_add_mem_parent_Icc_of_mem_shifted_Icc hh hn
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_deriv_lower_of_growth
      t ha hn_parent hn_shift_parent hderiv_growth

/-- Integer-index shifted-difference derivative lower bound in the
positive-frequency branch. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_deriv_lower_of_nonneg_at_nat
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b h n : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hh : h ≤ b - a)
    (hn : n ∈ Finset.Icc a (b - h)) :
    (‖t‖ *
        ((((b + 1 : ℕ) : ℝ) *
          (((b + 1 : ℕ) : ℝ)))⁻¹) *
        ((h : ℕ) : ℝ) ≤
      deriv (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) n) := by
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_deriv_lower_of_growth_at_nat
      t ha hh hn
      (Complex.logarithmicPhaseRealPhase_deriv_growth_on_integer_block
        t ht ht_nonneg ha hab)

/-- Real-interval form of the shifted-difference derivative lower bound on a
shifted-correlation packet. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_deriv_lower_on_shifted_Icc
    (t : ℝ)
    {a b h : ℕ}
    (ha : 1 ≤ a)
    (hh : h ≤ b - a)
    {x : ℝ}
    (hx : x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ))
    (hderiv_growth :
      ∀ u v : ℝ,
        u ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        v ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        u ≤ v →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (v - u) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) v -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) u)) :
    (‖t‖ *
        ((((b + 1 : ℕ) : ℝ) *
          (((b + 1 : ℕ) : ℝ)))⁻¹) *
        ((h : ℕ) : ℝ) ≤
      deriv (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) x) := by
  have hx_parent :
      x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
    Real.mem_parent_Icc_of_mem_shifted_Icc hx
  have hx_shift_parent :
      x + h ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
    Real.add_nat_mem_parent_Icc_of_mem_shifted_Icc hh hx
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_deriv_lower_of_growth
      t ha hx_parent hx_shift_parent hderiv_growth

/-- Real-interval shifted-difference derivative lower bound in the
positive-frequency branch. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_deriv_lower_on_shifted_Icc_of_nonneg
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b h : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hh : h ≤ b - a)
    {x : ℝ}
    (hx : x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)) :
    (‖t‖ *
        ((((b + 1 : ℕ) : ℝ) *
          (((b + 1 : ℕ) : ℝ)))⁻¹) *
        ((h : ℕ) : ℝ) ≤
      deriv (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) x) := by
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_deriv_lower_on_shifted_Icc
      t ha hh hx
      (Complex.logarithmicPhaseRealPhase_deriv_growth_on_integer_block
        t ht ht_nonneg ha hab)

/-- Normed real-interval form of the shifted-difference derivative lower
bound. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_deriv_norm_lower_on_shifted_Icc
    (t : ℝ)
    {a b h : ℕ}
    (ha : 1 ≤ a)
    (hh : h ≤ b - a)
    {x : ℝ}
    (hx : x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ))
    (hderiv_growth :
      ∀ u v : ℝ,
        u ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        v ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        u ≤ v →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (v - u) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) v -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) u)) :
    (‖t‖ *
        ((((b + 1 : ℕ) : ℝ) *
          (((b + 1 : ℕ) : ℝ)))⁻¹) *
        ((h : ℕ) : ℝ) ≤
      ‖deriv (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) x‖) := by
  have hlower :
      (‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          ((h : ℕ) : ℝ) ≤
        deriv (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) x) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_deriv_lower_on_shifted_Icc
      t ha hh hx hderiv_growth
  exact
    le_trans hlower
      (le_abs_self
        (deriv (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) x))

/-- Normed shifted-difference derivative lower bound in the positive-frequency
branch. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_deriv_norm_lower_on_shifted_Icc_of_nonneg
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b h : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hh : h ≤ b - a)
    {x : ℝ}
    (hx : x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)) :
    (‖t‖ *
        ((((b + 1 : ℕ) : ℝ) *
          (((b + 1 : ℕ) : ℝ)))⁻¹) *
        ((h : ℕ) : ℝ) ≤
      ‖deriv (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) x‖) := by
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_deriv_norm_lower_on_shifted_Icc
      t ha hh hx
      (Complex.logarithmicPhaseRealPhase_deriv_growth_on_integer_block
        t ht ht_nonneg ha hab)

/-- The shifted-difference lower-derivative scale is positive for nonzero
shift and nonzero logarithmic frequency. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_lowerParameter_pos
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {b h : ℕ}
    (hpos : 1 ≤ h) :
    0 <
      ‖t‖ *
        ((((b + 1 : ℕ) : ℝ) *
          (((b + 1 : ℕ) : ℝ)))⁻¹) *
        ((h : ℕ) : ℝ) := by
  have ht_pos : 0 < ‖t‖ :=
    lt_of_lt_of_le zero_lt_one ht
  have hB_pos : 0 < (((b + 1 : ℕ) : ℝ)) :=
    Nat.cast_pos.mpr (Nat.succ_pos b)
  have hBB_pos :
      0 <
        (((b + 1 : ℕ) : ℝ) *
          (((b + 1 : ℕ) : ℝ))) :=
    mul_pos hB_pos hB_pos
  have hBB_inv_pos :
      0 <
        ((((b + 1 : ℕ) : ℝ) *
          (((b + 1 : ℕ) : ℝ)))⁻¹) :=
    inv_pos.mpr hBB_pos
  have hh_pos : 0 < ((h : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.lt_of_succ_le hpos)
  exact
    mul_pos
      (mul_pos ht_pos hBB_inv_pos)
      hh_pos

/-- In the positive-frequency branch with nonzero shift, the shifted
logarithmic derivative is nonnegative on the shifted correlation interval. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_deriv_nonneg_on_shifted_Icc_of_nonneg
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b h : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hpos : 1 ≤ h)
    (hh : h ≤ b - a)
    {x : ℝ}
    (hx : x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)) :
    0 ≤ deriv (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) x := by
  have hparameter_pos :
      0 <
        ‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          ((h : ℕ) : ℝ) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_lowerParameter_pos
      t ht hpos
  have hlower :
      ‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          ((h : ℕ) : ℝ) ≤
        deriv (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) x :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_deriv_lower_on_shifted_Icc_of_nonneg
      t ht ht_nonneg ha hab hh hx
  exact le_trans hparameter_pos.le hlower

/-- On the positive-frequency shifted interval, the norm of the shifted
derivative is the derivative itself. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_deriv_norm_eq_on_shifted_Icc_of_nonneg
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b h : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hpos : 1 ≤ h)
    (hh : h ≤ b - a)
    {x : ℝ}
    (hx : x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)) :
    ‖deriv (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) x‖ =
      deriv (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) x := by
  exact
    Real.norm_of_nonneg
      (Complex.logarithmicPhaseRealPhase_shiftedDifference_deriv_nonneg_on_shifted_Icc_of_nonneg
        t ht ht_nonneg ha hab hpos hh hx)

/-- The adjacent increment of a shifted difference is the difference of the
two adjacent increments of the underlying phase. -/
theorem Complex.realPhase_secondDerivative_vdc_shiftedDifference_integerIncrement_eq
    (φ : ℝ → ℝ)
    (h n : ℕ) :
    Complex.realPhase_integerIncrement
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference φ h) n =
      Complex.realPhase_integerIncrement φ (n + h) -
        Complex.realPhase_integerIncrement φ n := by
  have hsucc_add :
      (((n + 1 : ℕ) : ℝ) + h) = (((n + h + 1 : ℕ) : ℝ)) := by
    calc
      (((n + 1 : ℕ) : ℝ) + h) =
          (((n + 1 + h : ℕ) : ℝ)) := by
        exact (Nat.cast_add (n + 1) h).symm
      _ = (((n + h + 1 : ℕ) : ℝ)) := by
        exact congrArg (fun m : ℕ => (m : ℝ)) (Nat.add_right_comm n 1 h)
  have hn_add :
      ((n : ℝ) + h) = (((n + h : ℕ) : ℝ)) := by
    exact (Nat.cast_add n h).symm
  have hsubtract_four_terms :
      (φ (n + h + 1 : ℕ) - φ (n + 1 : ℕ)) -
          (φ (n + h : ℕ) - φ n) =
        (φ (n + h + 1 : ℕ) - φ (n + h : ℕ)) -
          (φ (n + 1 : ℕ) - φ n) := by
    let A : ℝ := φ (n + h + 1 : ℕ)
    let B : ℝ := φ (n + 1 : ℕ)
    let C : ℝ := φ (n + h : ℕ)
    let D : ℝ := φ n
    have hleft₁ :
        (A - B) - (C - D) = (A + -B) + (-(C + -D)) := by
      calc
        (A - B) - (C - D) = (A + -B) - (C - D) :=
          congrArg (fun r : ℝ => r - (C - D)) (sub_eq_add_neg A B)
        _ = (A + -B) - (C + -D) :=
          congrArg (fun r : ℝ => (A + -B) - r) (sub_eq_add_neg C D)
        _ = (A + -B) + (-(C + -D)) :=
          sub_eq_add_neg (A + -B) (C + -D)
    have hneg_C_D :
        -(C + -D) = -C + D := by
      calc
        -(C + -D) = -C + -(-D) :=
          neg_add C (-D)
        _ = -C + D :=
          congrArg (fun r : ℝ => -C + r) (neg_neg D)
    have hleft₂ :
        (A + -B) + (-(C + -D)) =
          (A + -C) + (-B + D) := by
      calc
        (A + -B) + (-(C + -D)) =
            (A + -B) + (-C + D) :=
          congrArg (fun r : ℝ => (A + -B) + r) hneg_C_D
        _ = A + -B + -C + D :=
          (add_assoc (A + -B) (-C) D).symm
        _ = A + (-B + -C) + D :=
          congrArg (fun r : ℝ => r + D) (add_assoc A (-B) (-C))
        _ = A + (-C + -B) + D :=
          congrArg (fun r : ℝ => A + r + D) (add_comm (-B) (-C))
        _ = A + -C + -B + D :=
          congrArg (fun r : ℝ => r + D) (add_assoc A (-C) (-B)).symm
        _ = (A + -C) + (-B + D) :=
          add_assoc (A + -C) (-B) D
    have hright₁ :
        (A + -C) + (-B + D) =
          (A - C) - (B - D) := by
      calc
        (A + -C) + (-B + D) =
            (A - C) + (-B + D) :=
          congrArg (fun r : ℝ => r + (-B + D)) (sub_eq_add_neg A C).symm
        _ = (A - C) + -(B + -D) := by
          have hneg_B_D : -(B + -D) = -B + D := by
            calc
              -(B + -D) = -B + -(-D) :=
                neg_add B (-D)
              _ = -B + D :=
                congrArg (fun r : ℝ => -B + r) (neg_neg D)
          exact
            congrArg (fun r : ℝ => (A - C) + r) hneg_B_D.symm
        _ = (A - C) - (B + -D) :=
          (sub_eq_add_neg (A - C) (B + -D)).symm
        _ = (A - C) - (B - D) :=
          congrArg (fun r : ℝ => (A - C) - r) (sub_eq_add_neg B D).symm
    exact Eq.trans hleft₁ (Eq.trans hleft₂ hright₁)
  calc
    Complex.realPhase_integerIncrement
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference φ h) n =
        (φ (((n + 1 : ℕ) : ℝ) + h) - φ (n + 1 : ℕ)) -
          (φ ((n : ℝ) + h) - φ n) := by
      rfl
    _ =
        (φ (n + h + 1 : ℕ) - φ (n + 1 : ℕ)) -
          (φ (n + h : ℕ) - φ n) := by
      exact
        Eq.subst
          (motive := fun r : ℝ =>
            (φ (((n + 1 : ℕ) : ℝ) + h) - φ (n + 1 : ℕ)) -
              (φ ((n : ℝ) + h) - φ n) =
            (φ (n + h + 1 : ℕ) - φ (n + 1 : ℕ)) -
              (φ r - φ n))
          hn_add
          (Eq.subst
            (motive := fun r : ℝ =>
              (φ (((n + 1 : ℕ) : ℝ) + h) - φ (n + 1 : ℕ)) -
                (φ ((n : ℝ) + h) - φ n) =
              (φ r - φ (n + 1 : ℕ)) -
                (φ ((n : ℝ) + h) - φ n))
            hsucc_add
            rfl)
    _ =
        (φ (n + h + 1 : ℕ) - φ (n + h : ℕ)) -
          (φ (n + 1 : ℕ) - φ n) := by
      exact hsubtract_four_terms
    _ =
        Complex.realPhase_integerIncrement φ (n + h) -
          Complex.realPhase_integerIncrement φ n := by
      rfl

/-- Concrete logarithmic shifted adjacent increments are second differences
of the logarithmic adjacent increment profile. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_integerIncrement_eq
    (t : ℝ)
    (h n : ℕ) :
    Complex.realPhase_integerIncrement
        (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) n =
      Complex.realPhase_integerIncrement
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (n + h) -
        Complex.realPhase_integerIncrement
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          n := by
  exact
    Complex.realPhase_secondDerivative_vdc_shiftedDifference_integerIncrement_eq
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      h n

/-- Shifted correlation sum appearing in Weyl differencing for the logarithmic
real phase. -/
def Complex.logarithmicPhaseRealPhase_shiftedCorrelation
    (t : ℝ)
    (h a b : ℕ) : ℂ :=
  Complex.realPhase_secondDerivative_vdc_shiftedCorrelation
    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) h a b

/-- Trivial cardinality bound for a shifted logarithmic correlation. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedCorrelation_norm_le_card
    (t : ℝ)
    (h a b : ℕ) :
    ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖ ≤
      ((Finset.Icc a (b - h)).card : ℝ) := by
  exact
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelation_norm_le_card
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      h a b

/-- Finite first-derivative estimate for a shifted correlation packet, with
the actual Kusmin-Landau hypotheses exposed. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedCorrelation_bound_of_firstDerivative_data
    (t : ℝ)
    {a b h : ℕ}
    {lam : ℝ}
    (ha : 1 ≤ a)
    (habh : a ≤ b - h)
    (hlam_pos : 0 < lam)
    (hderiv_antitone :
      AntitoneOn
        (fun x : ℝ =>
          ‖deriv (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) x‖)
        (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)))
    (hderiv_lower :
      ∀ x : ℝ,
        x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ) →
          lam ≤
            ‖deriv (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) x‖)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) a (b - h))
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) a (b - h))
    (hsep :
      Complex.realPhase_integerIncrementSeparatedOn
        (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) a (b - h) lam) :
    ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖ ≤
      4 * (lam⁻¹ + 1) + 4 * Real.pi * lam⁻¹ := by
  exact
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelation_bound_of_firstDerivative_data
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      ha habh hlam_pos hderiv_antitone hderiv_lower
      hinc_mono hred_mono hsep

/-- Shifted-correlation bound where the derivative lower bound is supplied by
the positive-curvature growth of the parent logarithmic phase. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedCorrelation_bound_of_growth_and_firstDerivative_data
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b h : ℕ}
    (ha : 1 ≤ a)
    (hpos : 1 ≤ h)
    (hh : h ≤ b - a)
    (habh : a ≤ b - h)
    (hderiv_growth :
      ∀ u v : ℝ,
        u ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        v ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        u ≤ v →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (v - u) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) v -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) u))
    (hderiv_antitone :
      AntitoneOn
        (fun x : ℝ =>
          ‖deriv (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) x‖)
        (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)))
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) a (b - h))
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) a (b - h))
    (hsep :
      Complex.realPhase_integerIncrementSeparatedOn
        (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) a (b - h)
        (‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          ((h : ℕ) : ℝ))) :
    ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖ ≤
      4 *
          ((‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              ((h : ℕ) : ℝ))⁻¹ +
            1) +
        4 * Real.pi *
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              ((h : ℕ) : ℝ))⁻¹ := by
  let lam : ℝ :=
    ‖t‖ *
        ((((b + 1 : ℕ) : ℝ) *
          (((b + 1 : ℕ) : ℝ)))⁻¹) *
      ((h : ℕ) : ℝ)
  have hlam_pos : 0 < lam :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_lowerParameter_pos
      t ht hpos
  have hderiv_lower :
      ∀ x : ℝ,
        x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ) →
          lam ≤
            ‖deriv (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) x‖ :=
    fun x hx =>
      Complex.logarithmicPhaseRealPhase_shiftedDifference_deriv_norm_lower_on_shifted_Icc
        t ha hh hx hderiv_growth
  exact
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelation_bound_of_curvatureScale_data
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      ht ha hpos habh hderiv_antitone hderiv_lower
      hinc_mono hred_mono hsep

/-- Shifted-correlation bound in the positive-frequency branch, with parent
derivative growth discharged from the curvature owner theorem. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedCorrelation_bound_of_nonneg_firstDerivative_data
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b h : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hpos : 1 ≤ h)
    (hh : h ≤ b - a)
    (habh : a ≤ b - h)
    (hderiv_antitone :
      AntitoneOn
        (fun x : ℝ =>
          ‖deriv (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) x‖)
        (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)))
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) a (b - h))
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) a (b - h))
    (hsep :
      Complex.realPhase_integerIncrementSeparatedOn
        (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) a (b - h)
        (‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          ((h : ℕ) : ℝ))) :
    ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖ ≤
      4 *
          ((‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              ((h : ℕ) : ℝ))⁻¹ +
            1) +
        4 * Real.pi *
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              ((h : ℕ) : ℝ))⁻¹ := by
  exact
    Complex.logarithmicPhaseRealPhase_shiftedCorrelation_bound_of_growth_and_firstDerivative_data
      t ht ha hpos hh habh
      (Complex.logarithmicPhaseRealPhase_deriv_growth_on_integer_block
        t ht ht_nonneg ha hab)
      hderiv_antitone hinc_mono hred_mono hsep

end

end LFunctions
end Boundary
