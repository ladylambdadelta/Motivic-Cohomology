import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseCore
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

end

end LFunctions
end Boundary
