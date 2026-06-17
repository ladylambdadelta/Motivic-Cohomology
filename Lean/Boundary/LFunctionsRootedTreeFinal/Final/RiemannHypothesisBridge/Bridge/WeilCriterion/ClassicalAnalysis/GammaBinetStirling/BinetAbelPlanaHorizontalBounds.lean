import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaCore
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaCotangentKernel

/-!
# Horizontal finite-strip bounds for the Abel-Plana contour

This file owns the pointwise estimates for the decaying horizontal
cotangent-remainder edges in the finite-height Abel-Plana rectangle.  The
contour file owns the rectangle residue accounting and the integral side
estimates; the finite-strip pointwise majorants live here.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open Filter

/-- Membership transport from unordered to ordered finite horizontal interval. -/
theorem Real.mem_Ioc_of_mem_uIoc_zero_nat_succ
    (N : ℕ)
    {x : ℝ}
    (hx : x ∈ Set.uIoc (0 : ℝ) (N + 1 : ℝ)) :
    x ∈ Set.Ioc (0 : ℝ) (N + 1 : ℝ) := by
  have hN_nonneg : (0 : ℝ) ≤ (N + 1 : ℝ) :=
    add_nonneg (Nat.cast_nonneg N) zero_le_one
  exact
    Eq.mp
      (congrArg (fun s : Set ℝ => x ∈ s) (Set.uIoc_of_le hN_nonneg))
      hx

/-- The Abel-Plana horizontal signs have unit norm. -/
theorem Complex.norm_eq_one_of_eq_I_or_neg_I
    {sgn : ℂ}
    (hsgn : sgn = Complex.I ∨ sgn = -Complex.I) :
    ‖sgn‖ = (1 : ℝ) := by
  cases hsgn with
  | inl hI =>
      exact Eq.subst (motive := fun z : ℂ => ‖z‖ = (1 : ℝ)) hI.symm Complex.norm_I
  | inr hnegI =>
      have hneg_norm : ‖-Complex.I‖ = (1 : ℝ) := by
        calc
          ‖-Complex.I‖ = ‖Complex.I‖ := norm_neg Complex.I
          _ = (1 : ℝ) := Complex.norm_I
      exact Eq.subst (motive := fun z : ℂ => ‖z‖ = (1 : ℝ)) hnegI.symm hneg_norm

/-- Multiplication by either horizontal sign has zero real part on real inputs. -/
theorem Complex.ofReal_mul_horizontal_sign_re_eq_zero
    (T : ℝ)
    {sgn : ℂ}
    (hsgn : sgn = Complex.I ∨ sgn = -Complex.I) :
    ((T : ℂ) * sgn).re = 0 := by
  cases hsgn with
  | inl hI =>
      exact
        Eq.subst
          (motive := fun z : ℂ => ((T : ℂ) * z).re = 0)
          hI.symm
          (calc
            ((T : ℂ) * Complex.I).re = -((T : ℂ).im) :=
              Complex.mul_I_re (T : ℂ)
            _ = -0 := congrArg Neg.neg (Complex.ofReal_im T)
            _ = 0 := neg_zero)
  | inr hnegI =>
      have hbase :
          ((T : ℂ) * (-Complex.I)).re = 0 := by
        calc
          ((T : ℂ) * (-Complex.I)).re =
              (-((T : ℂ) * Complex.I)).re := by
            exact congrArg Complex.re (mul_neg (T : ℂ) Complex.I)
          _ = -(((T : ℂ) * Complex.I).re) := Complex.neg_re ((T : ℂ) * Complex.I)
          _ = -0 := by
            exact congrArg Neg.neg
              (calc
                ((T : ℂ) * Complex.I).re = -((T : ℂ).im) :=
                  Complex.mul_I_re (T : ℂ)
                _ = -0 := congrArg Neg.neg (Complex.ofReal_im T)
                _ = 0 := neg_zero)
          _ = 0 := neg_zero
      exact
        Eq.subst
          (motive := fun z : ℂ => ((T : ℂ) * z).re = 0)
          hnegI.symm
          hbase

/-- The lower horizontal parametrization written with addition by `-I`. -/
theorem Complex.lowerHorizontal_add_negI_eq_sub
    (x T : ℝ) :
    ((x : ℂ) + (T : ℂ) * (-Complex.I)) =
      ((x : ℂ) - (T : ℂ) * Complex.I) := by
  calc
    ((x : ℂ) + (T : ℂ) * (-Complex.I))
        = (x : ℂ) + (-((T : ℂ) * Complex.I)) := by
      exact congrArg (fun z : ℂ => (x : ℂ) + z) (mul_neg (T : ℂ) Complex.I)
    _ = (x : ℂ) - (T : ℂ) * Complex.I := by
      exact (sub_eq_add_neg (x : ℂ) ((T : ℂ) * Complex.I)).symm

/-- Reassociation of the scalar logarithmic majorant argument. -/
theorem Real.log_horizontal_majorant_argument_assoc
    (a b c : ℝ) :
    Real.log (1 + (a + b) + c) + Real.pi + 1 =
      Real.log (1 + a + b + c) + Real.pi + 1 := by
  have harg : 1 + (a + b) + c = 1 + a + b + c := by
    calc
      1 + (a + b) + c = (1 + (a + b)) + c := rfl
      _ = ((1 + a) + b) + c := congrArg (fun y : ℝ => y + c) (add_assoc 1 a b).symm
      _ = 1 + a + b + c := rfl
  exact congrArg (fun y : ℝ => Real.log y + Real.pi + 1) harg

/-- Tail comparison obtained by adding the interval center to both sides. -/
theorem Real.tail_sub_le_abs_implies_le_add_abs
    {a C R : ℝ}
    (hR : a - C ≤ |R|) :
    a ≤ C + |R| := by
    calc
      a = C + (a - C) := by
        calc
          a = C + a - C := (add_sub_cancel_left C a).symm
          _ = (C + a) + -C := sub_eq_add_neg (C + a) C
          _ = C + (a + -C) := add_assoc C a (-C)
          _ = C + (a - C) := by
            exact congrArg (fun y : ℝ => C + y) (sub_eq_add_neg a C).symm
      _ ≤ C + |R| := add_le_add_left hR C

/-- The finite horizontal bound is below the one-shifted log argument. -/
theorem Real.horizontal_M_le_one_add
    (C R : ℝ) :
    C + |R| ≤ 1 + C + |R| := by
  calc
    C + |R| ≤ 1 + (C + |R|) := le_add_of_nonneg_left zero_le_one
    _ = 1 + C + |R| := (add_assoc 1 C |R|).symm

/-- Adding the common `π` terms to a logarithmic estimate. -/
theorem Real.abs_log_add_pi_le_log_add_pi_add_one
    {a b : ℝ}
    (h : a ≤ b + 1) :
    a + Real.pi ≤ b + Real.pi + 1 := by
  calc
    a + Real.pi ≤ (b + 1) + Real.pi := add_le_add_right h Real.pi
    _ = b + Real.pi + 1 := by
      calc
        (b + 1) + Real.pi = b + (1 + Real.pi) := add_assoc b 1 Real.pi
        _ = b + (Real.pi + 1) := congrArg (fun y : ℝ => b + y) (add_comm 1 Real.pi)
        _ = b + Real.pi + 1 := (add_assoc b Real.pi 1).symm

/-- Scalar reassociation for the pointwise horizontal majorant. -/
theorem Real.horizontal_pointwise_majorant_assoc
    (C L E : ℝ) :
    L * (C * E) = C * L * E := by
  calc
    L * (C * E) = (L * C) * E := (mul_assoc L C E).symm
    _ = (C * L) * E := congrArg (fun y : ℝ => y * E) (mul_comm L C)
    _ = C * L * E := rfl

/-- Uniform norm upper bound for horizontal Abel-Plana log arguments. -/
theorem Complex.norm_finiteAbelPlana_horizontalArgument_le
    (w : ℂ)
    (N : ℕ)
    (sgn : ℂ)
    (hsgn : sgn = Complex.I ∨ sgn = -Complex.I) :
    ∀ T : ℝ,
      ∀ x ∈ Set.uIoc (0 : ℝ) (N + 1 : ℝ),
        ‖w + ((x : ℂ) + (T : ℂ) * sgn)‖ ≤
          ‖w‖ + (N + 1 : ℝ) + |T| := by
  intro T x hx
  have hxIoc : x ∈ Set.Ioc (0 : ℝ) (N + 1 : ℝ) := by
    exact Real.mem_Ioc_of_mem_uIoc_zero_nat_succ N hx
  have hx_abs_le : |x| ≤ (N + 1 : ℝ) := by
    have hx_nonneg : 0 ≤ x := le_of_lt hxIoc.1
    have hx_abs : |x| = x := abs_of_nonneg hx_nonneg
    exact Eq.subst (motive := fun y : ℝ => y ≤ (N + 1 : ℝ)) hx_abs.symm hxIoc.2
  have hsgn_norm : ‖sgn‖ = (1 : ℝ) := by
    exact Complex.norm_eq_one_of_eq_I_or_neg_I hsgn
  have hTsgn_norm : ‖(T : ℂ) * sgn‖ = |T| := by
    calc
      ‖(T : ℂ) * sgn‖ = ‖(T : ℂ)‖ * ‖sgn‖ := norm_mul _ _
      _ = |T| * 1 := by
        exact congrArg₂ HMul.hMul (RCLike.norm_ofReal T) hsgn_norm
      _ = |T| := mul_one |T|
  have hx_norm : ‖(x : ℂ)‖ = |x| := RCLike.norm_ofReal x
  calc
    ‖w + ((x : ℂ) + (T : ℂ) * sgn)‖
        ≤ ‖w‖ + ‖(x : ℂ) + (T : ℂ) * sgn‖ :=
      norm_add_le w ((x : ℂ) + (T : ℂ) * sgn)
    _ ≤ ‖w‖ + (‖(x : ℂ)‖ + ‖(T : ℂ) * sgn‖) := by
      exact add_le_add_left
        (norm_add_le (x : ℂ) ((T : ℂ) * sgn))
        ‖w‖
    _ = ‖w‖ + (|x| + |T|) := by
      exact congrArg (fun y : ℝ => ‖w‖ + y)
        (congrArg₂ HAdd.hAdd hx_norm hTsgn_norm)
    _ ≤ ‖w‖ + ((N + 1 : ℝ) + |T|) := by
      exact add_le_add_left (add_le_add_right hx_abs_le |T|) ‖w‖
    _ = ‖w‖ + (N + 1 : ℝ) + |T| := by
      exact (add_assoc ‖w‖ (N + 1 : ℝ) |T|).symm

/-- Uniform positive lower bound for horizontal Abel-Plana log arguments in
the open right half-plane. -/
theorem Complex.finiteAbelPlana_horizontalArgument_norm_ge_re
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (sgn : ℂ)
    (hsgn : sgn = Complex.I ∨ sgn = -Complex.I) :
    ∀ T : ℝ,
      ∀ x ∈ Set.uIoc (0 : ℝ) (N + 1 : ℝ),
        w.re ≤ ‖w + ((x : ℂ) + (T : ℂ) * sgn)‖ := by
  intro T x hx
  have hxIoc : x ∈ Set.Ioc (0 : ℝ) (N + 1 : ℝ) := by
    exact Real.mem_Ioc_of_mem_uIoc_zero_nat_succ N hx
  have hx_nonneg : 0 ≤ x := le_of_lt hxIoc.1
  have hsgn_re : ((T : ℂ) * sgn).re = 0 := by
    exact Complex.ofReal_mul_horizontal_sign_re_eq_zero T hsgn
  let z : ℂ := w + ((x : ℂ) + (T : ℂ) * sgn)
  have hz_re : z.re = w.re + x := by
    have hraw :
        (w + ((x : ℂ) + (T : ℂ) * sgn)).re = w.re + x := by
      calc
        (w + ((x : ℂ) + (T : ℂ) * sgn)).re =
          w.re + (((x : ℂ) + (T : ℂ) * sgn).re) :=
          Complex.add_re w ((x : ℂ) + (T : ℂ) * sgn)
        _ = w.re + ((x : ℂ).re + ((T : ℂ) * sgn).re) := by
          exact congrArg (fun y : ℝ => w.re + y)
            (Complex.add_re (x : ℂ) ((T : ℂ) * sgn))
        _ = w.re + (x + 0) := by
          exact congrArg₂ HAdd.hAdd rfl
            (congrArg₂ HAdd.hAdd (Complex.ofReal_re x) hsgn_re)
        _ = w.re + x := by
          exact congrArg (fun y : ℝ => w.re + y) (add_zero x)
    exact hraw
  have hw_le_re : w.re ≤ z.re := by
    exact
      Eq.subst
        (motive := fun y : ℝ => w.re ≤ y)
        hz_re.symm
        (le_add_of_nonneg_right hx_nonneg)
  have hz_re_nonneg : 0 ≤ z.re := le_trans (le_of_lt hw) hw_le_re
  have hz_re_le_norm : z.re ≤ ‖z‖ := by
    calc
      z.re ≤ |z.re| := le_abs_self z.re
      _ ≤ Complex.abs z := Complex.abs_re_le_abs z
      _ = ‖z‖ := (Complex.norm_eq_abs z).symm
  exact le_trans hw_le_re hz_re_le_norm

/-- Scalar logarithmic comparison used by the horizontal finite-strip log
bound. -/
theorem Real.eventually_abs_log_of_bounded_interval_le_log_one_add
    {m : ℝ}
    (hm : 0 < m)
    (C : ℝ) :
    ∀ᶠ R : ℝ in atTop,
      ∀ r : ℝ,
        m ≤ r →
          r ≤ C + |R| →
            |Real.log r| + Real.pi ≤
              Real.log (1 + C + |R|) + Real.pi + 1 := by
  have hlog_atTop :
      Tendsto (fun R : ℝ => Real.log (1 + C + |R|) + 1)
        atTop atTop := by
    have harg_atTop : Tendsto (fun R : ℝ => 1 + C + |R|) atTop atTop := by
      have habs_atTop : Tendsto (fun R : ℝ => |R|) atTop atTop := by
        exact tendsto_abs_atTop_atTop
      exact tendsto_atTop_add_const_left atTop (1 + C) habs_atTop
    exact tendsto_atTop_add_const_right atTop 1
      (Real.tendsto_log_atTop.comp harg_atTop)
  have hfixed :
      ∀ᶠ R : ℝ in atTop,
        |Real.log m| ≤ Real.log (1 + C + |R|) + 1 :=
    hlog_atTop.eventually_ge_atTop |Real.log m|
  have hM_ge_m :
      ∀ᶠ R : ℝ in atTop,
        m ≤ C + |R| := by
    have htail : ∀ᶠ R : ℝ in atTop, m - C ≤ |R| := by
      exact tendsto_abs_atTop_atTop.eventually_ge_atTop (m - C)
    filter_upwards [htail] with R hR
    exact Real.tail_sub_le_abs_implies_le_add_abs hR
  have hM_ge_one :
      ∀ᶠ R : ℝ in atTop,
        1 ≤ C + |R| := by
    have htail : ∀ᶠ R : ℝ in atTop, 1 - C ≤ |R| := by
      exact tendsto_abs_atTop_atTop.eventually_ge_atTop (1 - C)
    filter_upwards [htail] with R hR
    exact Real.tail_sub_le_abs_implies_le_add_abs hR
  filter_upwards [hfixed, hM_ge_m, hM_ge_one] with R hfixedR hMR hMone r hmr hrM
  let M : ℝ := C + |R|
  have hmM : m ≤ M := hMR
  have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one hMone
  have hlog_interval :
      |Real.log r| ≤ max |Real.log m| |Real.log M| :=
    Real.arctan_fixed_tail_abs_log_le_max_abs_log_of_bounds
      hm hmM hmr hrM
  have hlogM_nonneg : 0 ≤ Real.log M :=
    Real.log_nonneg hMone
  have hlogM_abs : |Real.log M| = Real.log M :=
    abs_of_nonneg hlogM_nonneg
  have hM_le_arg : M ≤ 1 + C + |R| := by
    show C + |R| ≤ 1 + C + |R|
    exact Real.horizontal_M_le_one_add C R
  have harg_pos : 0 < 1 + C + |R| :=
    lt_of_lt_of_le hM_pos hM_le_arg
  have hlogM_le :
      |Real.log M| ≤ Real.log (1 + C + |R|) + 1 := by
    exact
      Eq.subst
        (motive := fun y : ℝ => y ≤ Real.log (1 + C + |R|) + 1)
        hlogM_abs.symm
        (le_trans
          (Real.log_le_log hM_pos hM_le_arg)
          (le_add_of_nonneg_right zero_le_one))
  have hmax_le :
      max |Real.log m| |Real.log M| ≤
        Real.log (1 + C + |R|) + 1 :=
    max_le hfixedR hlogM_le
  have habs_le :
      |Real.log r| ≤ Real.log (1 + C + |R|) + 1 :=
    le_trans hlog_interval hmax_le
  exact Real.abs_log_add_pi_le_log_add_pi_add_one habs_le

/-- Uniform finite-strip principal-log growth for horizontal Abel-Plana
arguments.

This is the shared logarithmic estimate behind both the upper and lower
horizontal edges.  The proof is the elementary two-sided norm estimate:
`w.re ≤ ‖w + x ± iT‖ ≤ ‖w‖ + (N+1) + |T|`, together with the principal-log
formula `log z = log ‖z‖ + i arg z` and the eventual inequality
`sqrt((log r)^2 + π^2) ≤ log(1+r) + 1`. -/
theorem Complex.norm_finiteAbelPlanaLogSummand_horizontal_le_log_majorant
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (sgn : ℂ) :
    sgn = Complex.I ∨ sgn = -Complex.I →
    ∀ᶠ T : ℝ in atTop,
      ∀ x ∈ Set.uIoc (0 : ℝ) (N + 1 : ℝ),
        ‖Complex.finiteAbelPlanaLogSummand w
            ((x : ℂ) + (T : ℂ) * sgn)‖ ≤
          Real.log (1 + ‖w‖ + (N + 1 : ℝ) + |T|) + Real.pi + 1 := by
  intro hsgn
  have hscalar :
      ∀ᶠ T : ℝ in atTop,
        ∀ r : ℝ,
          w.re ≤ r →
            r ≤ ‖w‖ + (N + 1 : ℝ) + |T| →
              |Real.log r| + Real.pi ≤
                Real.log (1 + (‖w‖ + (N + 1 : ℝ)) + |T|) + Real.pi + 1 :=
    Real.eventually_abs_log_of_bounded_interval_le_log_one_add
      hw (‖w‖ + (N + 1 : ℝ))
  filter_upwards [hscalar] with T hT x hx
  let z : ℂ := w + ((x : ℂ) + (T : ℂ) * sgn)
  have hz_lower : w.re ≤ ‖z‖ :=
    Complex.finiteAbelPlana_horizontalArgument_norm_ge_re
      hw N sgn hsgn T x hx
  have hz_upper : ‖z‖ ≤ ‖w‖ + (N + 1 : ℝ) + |T| :=
    Complex.norm_finiteAbelPlana_horizontalArgument_le
      w N sgn hsgn T x hx
  have hlog_norm :
      ‖Complex.log z‖ ≤ |Real.log ‖z‖| + Real.pi :=
    Complex.arctan_fixed_tail_log_norm_le_abs_log_norm_add_pi z
  have hscalar_z :
      |Real.log ‖z‖| + Real.pi ≤
        Real.log (1 + (‖w‖ + (N + 1 : ℝ)) + |T|) + Real.pi + 1 :=
    hT ‖z‖ hz_lower hz_upper
  calc
    ‖Complex.finiteAbelPlanaLogSummand w
        ((x : ℂ) + (T : ℂ) * sgn)‖ =
        ‖Complex.log z‖ := by
      rfl
    _ ≤ |Real.log ‖z‖| + Real.pi := hlog_norm
    _ ≤ Real.log (1 + (‖w‖ + (N + 1 : ℝ)) + |T|) + Real.pi + 1 := hscalar_z
    _ = Real.log (1 + ‖w‖ + (N + 1 : ℝ) + |T|) + Real.pi + 1 := by
      exact Real.log_horizontal_majorant_argument_assoc ‖w‖ (N + 1 : ℝ) |T|

/-- Finite-height horizontal-edge majorant after integrating the pointwise
finite-strip bound over `0 ≤ x ≤ N + 1`. -/
noncomputable def Complex.finiteAbelPlanaLogHorizontalEdgeMajorant
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) : ℝ :=
    (4 * (Real.pi + 1)) * (N + 1 : ℝ) *
      (Real.log (1 + ‖w‖ + (N + 1 : ℝ) + |T|) + Real.pi + 1) *
        Real.exp (-(2 * Real.pi * |T|))

/-- Reassociation used to pass from the pointwise horizontal majorant to the
integrated edge majorant. -/
theorem Real.horizontal_edge_majorant_assoc
    (A B C D : ℝ) :
    (A * C * D) * B = A * B * C * D := by
  calc
    (A * C * D) * B = ((A * C) * D) * B := rfl
    _ = (A * C) * (D * B) := mul_assoc (A * C) D B
    _ = (A * C) * (B * D) := by
      exact congrArg (fun y : ℝ => (A * C) * y) (mul_comm D B)
    _ = ((A * C) * B) * D := (mul_assoc (A * C) B D).symm
    _ = (A * (C * B)) * D := by
      exact congrArg (fun y : ℝ => y * D) (mul_assoc A C B)
    _ = (A * (B * C)) * D := by
      exact congrArg (fun y : ℝ => (A * y) * D) (mul_comm C B)
    _ = ((A * B) * C) * D := by
      exact congrArg (fun y : ℝ => y * D) (mul_assoc A B C).symm
    _ = A * B * C * D := rfl

/-- The interval length of `[0, N+1]` in the horizontal estimate. -/
theorem Real.horizontal_interval_length_abs
    (N : ℕ) :
    |((N + 1 : ℕ) : ℝ) - (0 : ℝ)| = (N + 1 : ℝ) := by
  have hnonneg : 0 ≤ (N + 1 : ℝ) :=
    add_nonneg (Nat.cast_nonneg N) zero_le_one
  have hcast_one : ((1 : ℕ) : ℝ) = 1 :=
    Nat.cast_one
  have hcast : ((N + 1 : ℕ) : ℝ) = (N + 1 : ℝ) := by
    calc
      ((N + 1 : ℕ) : ℝ) = (N : ℝ) + ((1 : ℕ) : ℝ) :=
        Nat.cast_add N 1
      _ = (N : ℝ) + 1 := congrArg (fun y : ℝ => (N : ℝ) + y) hcast_one
      _ = (N + 1 : ℝ) := rfl
  calc
    |((N + 1 : ℕ) : ℝ) - (0 : ℝ)| =
        |((N + 1 : ℕ) : ℝ)| := by
      exact congrArg abs (sub_zero ((N + 1 : ℕ) : ℝ))
    _ = |(N + 1 : ℝ)| := congrArg abs hcast
    _ = (N + 1 : ℝ) := abs_of_nonneg hnonneg

/-- The interval length of `[0, N + 1]` after endpoint normalization in `ℝ`. -/
theorem Real.horizontal_interval_length_abs_real
    (N : ℕ) :
    |(N + 1 : ℝ) - (0 : ℝ)| = (N + 1 : ℝ) := by
  have hnonneg : 0 ≤ (N + 1 : ℝ) :=
    add_nonneg (Nat.cast_nonneg N) zero_le_one
  calc
    |(N + 1 : ℝ) - (0 : ℝ)| = |(N + 1 : ℝ)| := by
      exact congrArg abs (sub_zero (N + 1 : ℝ))
    _ = (N + 1 : ℝ) := abs_of_nonneg hnonneg

/-- The bottom horizontal edge with its natural endpoint normalized in `ℝ`. -/
theorem Complex.finiteAbelPlanaLogBottomHorizontalEdge_eq_real_endpoint
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogBottomHorizontalEdge N w T =
      ∫ x : ℝ in (0 : ℝ)..(N + 1 : ℝ),
        Complex.finiteAbelPlanaLogSummand w
          ((x : ℂ) - (T : ℂ) * Complex.I) *
        (Complex.finiteAbelPlanaCotangentKernel
            ((x : ℂ) - (T : ℂ) * Complex.I) -
          (Real.pi : ℂ) * Complex.I) := by
  have hcast_one : ((1 : ℕ) : ℝ) = 1 :=
    Nat.cast_one
  have hcast : ((N + 1 : ℕ) : ℝ) = (N + 1 : ℝ) := by
    calc
      ((N + 1 : ℕ) : ℝ) = (N : ℝ) + ((1 : ℕ) : ℝ) :=
        Nat.cast_add N 1
      _ = (N : ℝ) + 1 := congrArg (fun y : ℝ => (N : ℝ) + y) hcast_one
      _ = (N + 1 : ℝ) := rfl
  show
    (∫ x : ℝ in (0 : ℝ)..(((N + 1 : ℕ) : ℝ)),
        Complex.finiteAbelPlanaLogSummand w
          ((x : ℂ) - (T : ℂ) * Complex.I) *
        (Complex.finiteAbelPlanaCotangentKernel
            ((x : ℂ) - (T : ℂ) * Complex.I) -
          (Real.pi : ℂ) * Complex.I))
      =
    ∫ x : ℝ in (0 : ℝ)..(N + 1 : ℝ),
        Complex.finiteAbelPlanaLogSummand w
          ((x : ℂ) - (T : ℂ) * Complex.I) *
        (Complex.finiteAbelPlanaCotangentKernel
            ((x : ℂ) - (T : ℂ) * Complex.I) -
          (Real.pi : ℂ) * Complex.I)
  exact
    congrArg
      (fun b : ℝ =>
        ∫ x : ℝ in (0 : ℝ)..b,
          Complex.finiteAbelPlanaLogSummand w
            ((x : ℂ) - (T : ℂ) * Complex.I) *
          (Complex.finiteAbelPlanaCotangentKernel
              ((x : ℂ) - (T : ℂ) * Complex.I) -
            (Real.pi : ℂ) * Complex.I))
      hcast

/-- The top horizontal edge with its natural endpoint normalized in `ℝ`. -/
theorem Complex.finiteAbelPlanaLogTopHorizontalEdge_eq_real_endpoint
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogTopHorizontalEdge N w T =
      ∫ x : ℝ in (0 : ℝ)..(N + 1 : ℝ),
        Complex.finiteAbelPlanaLogSummand w
          ((x : ℂ) + (T : ℂ) * Complex.I) *
        (Complex.finiteAbelPlanaCotangentKernel
            ((x : ℂ) + (T : ℂ) * Complex.I) +
          (Real.pi : ℂ) * Complex.I) := by
  have hcast_one : ((1 : ℕ) : ℝ) = 1 :=
    Nat.cast_one
  have hcast : ((N + 1 : ℕ) : ℝ) = (N + 1 : ℝ) := by
    calc
      ((N + 1 : ℕ) : ℝ) = (N : ℝ) + ((1 : ℕ) : ℝ) :=
        Nat.cast_add N 1
      _ = (N : ℝ) + 1 := congrArg (fun y : ℝ => (N : ℝ) + y) hcast_one
      _ = (N + 1 : ℝ) := rfl
  show
    (∫ x : ℝ in (0 : ℝ)..(((N + 1 : ℕ) : ℝ)),
        Complex.finiteAbelPlanaLogSummand w
          ((x : ℂ) + (T : ℂ) * Complex.I) *
        (Complex.finiteAbelPlanaCotangentKernel
            ((x : ℂ) + (T : ℂ) * Complex.I) +
          (Real.pi : ℂ) * Complex.I))
      =
    ∫ x : ℝ in (0 : ℝ)..(N + 1 : ℝ),
        Complex.finiteAbelPlanaLogSummand w
          ((x : ℂ) + (T : ℂ) * Complex.I) *
        (Complex.finiteAbelPlanaCotangentKernel
            ((x : ℂ) + (T : ℂ) * Complex.I) +
          (Real.pi : ℂ) * Complex.I)
  exact
    congrArg
      (fun b : ℝ =>
        ∫ x : ℝ in (0 : ℝ)..b,
          Complex.finiteAbelPlanaLogSummand w
            ((x : ℂ) + (T : ℂ) * Complex.I) *
          (Complex.finiteAbelPlanaCotangentKernel
              ((x : ℂ) + (T : ℂ) * Complex.I) +
            (Real.pi : ℂ) * Complex.I))
      hcast

/-- Pointwise scalar majorant for the decaying cotangent-remainder kernel on
finite horizontal Abel-Plana edges. -/
noncomputable def Complex.finiteAbelPlanaLogHorizontalPointwiseMajorant
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) : ℝ :=
  (4 * (Real.pi + 1)) *
    (Real.log (1 + ‖w‖ + (N + 1 : ℝ) + |T|) + Real.pi + 1) *
      Real.exp (-(2 * Real.pi * |T|))

/-- The pointwise horizontal majorant unfolded in scalar normal form. -/
theorem Complex.finiteAbelPlanaLogHorizontalPointwiseMajorant_unfold
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogHorizontalPointwiseMajorant N w T =
      (4 * (Real.pi + 1)) *
        (Real.log (1 + ‖w‖ + (N + 1 : ℝ) + |T|) + Real.pi + 1) *
          Real.exp (-(2 * Real.pi * |T|)) :=
  rfl

/-- The horizontal edge majorant unfolded in scalar normal form. -/
theorem Complex.finiteAbelPlanaLogHorizontalEdgeMajorant_unfold
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogHorizontalEdgeMajorant N w T =
      (4 * (Real.pi + 1)) * (N + 1 : ℝ) *
        (Real.log (1 + ‖w‖ + (N + 1 : ℝ) + |T|) + Real.pi + 1) *
          Real.exp (-(2 * Real.pi * |T|)) :=
  rfl

/-- Local scalar normalization of the pointwise horizontal majorant. -/
theorem Complex.finiteAbelPlanaLogHorizontalPointwiseMajorant_eq_local_factors
    (N : ℕ)
    (w : ℂ)
    (T : ℝ)
    (L C E : ℝ)
    (hL :
      L = Real.log (1 + ‖w‖ + (N + 1 : ℝ) + |T|) + Real.pi + 1)
    (hC : C = 4 * (Real.pi + 1))
    (hE : E = Real.exp (-(2 * Real.pi * |T|))) :
    C * L * E =
      Complex.finiteAbelPlanaLogHorizontalPointwiseMajorant N w T := by
  calc
    C * L * E =
        (4 * (Real.pi + 1)) *
          (Real.log (1 + ‖w‖ + (N + 1 : ℝ) + |T|) + Real.pi + 1) *
            Real.exp (-(2 * Real.pi * |T|)) := by
      exact congrArg₂ HMul.hMul
        (congrArg₂ HMul.hMul hC hL)
        hE
    _ = Complex.finiteAbelPlanaLogHorizontalPointwiseMajorant N w T :=
      (Complex.finiteAbelPlanaLogHorizontalPointwiseMajorant_unfold N w T).symm

/-- Local scalar normalization of the integrated horizontal majorant. -/
theorem Complex.finiteAbelPlanaLogHorizontalEdgeMajorant_eq_local_factors
    (N : ℕ)
    (w : ℂ)
    (T : ℝ)
    (A B C D : ℝ)
    (hA : A = 4 * (Real.pi + 1))
    (hB : B = (N + 1 : ℝ))
    (hC :
      C = Real.log (1 + ‖w‖ + (N + 1 : ℝ) + |T|) + Real.pi + 1)
    (hD : D = Real.exp (-(2 * Real.pi * |T|))) :
    A * B * C * D =
      Complex.finiteAbelPlanaLogHorizontalEdgeMajorant N w T := by
  calc
    A * B * C * D =
        (4 * (Real.pi + 1)) * (N + 1 : ℝ) *
          (Real.log (1 + ‖w‖ + (N + 1 : ℝ) + |T|) + Real.pi + 1) *
            Real.exp (-(2 * Real.pi * |T|)) := by
      exact congrArg₂ HMul.hMul
        (congrArg₂ HMul.hMul
          (congrArg₂ HMul.hMul hA hB)
          hC)
        hD
    _ = Complex.finiteAbelPlanaLogHorizontalEdgeMajorant N w T :=
      (Complex.finiteAbelPlanaLogHorizontalEdgeMajorant_unfold N w T).symm

/-- Principal-log growth on the lower finite horizontal strip.

For fixed `w` in the right half-plane and fixed finite width `N + 1`, the
principal logarithm of `w + x - iT` has at most logarithmic growth in `|T|`,
uniformly for `x ∈ uIoc 0 (N + 1)`. -/
theorem Complex.norm_finiteAbelPlanaLogSummand_lowerHorizontal_le_log_majorant
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ x ∈ Set.uIoc (0 : ℝ) (N + 1 : ℝ),
        ‖Complex.finiteAbelPlanaLogSummand w
            ((x : ℂ) - (T : ℂ) * Complex.I)‖ ≤
          Real.log (1 + ‖w‖ + (N + 1 : ℝ) + |T|) + Real.pi + 1 := by
  have hbase :
      ∀ᶠ T : ℝ in atTop,
        ∀ x ∈ Set.uIoc (0 : ℝ) (N + 1 : ℝ),
          ‖Complex.finiteAbelPlanaLogSummand w
              ((x : ℂ) + (T : ℂ) * (-Complex.I))‖ ≤
            Real.log (1 + ‖w‖ + (N + 1 : ℝ) + |T|) + Real.pi + 1 :=
    Complex.norm_finiteAbelPlanaLogSummand_horizontal_le_log_majorant
      hw N (-Complex.I) (Or.inr rfl)
  filter_upwards [hbase] with T hT x hx
  have harg :
      ((x : ℂ) + (T : ℂ) * (-Complex.I)) =
        ((x : ℂ) - (T : ℂ) * Complex.I) := by
    exact Complex.lowerHorizontal_add_negI_eq_sub x T
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        ‖Complex.finiteAbelPlanaLogSummand w z‖ ≤
          Real.log (1 + ‖w‖ + (N + 1 : ℝ) + |T|) + Real.pi + 1)
      harg
      (hT x hx)

/-- Principal-log growth on the upper finite horizontal strip.

This is the upper-half-plane analogue of
`norm_finiteAbelPlanaLogSummand_lowerHorizontal_le_log_majorant`. -/
theorem Complex.norm_finiteAbelPlanaLogSummand_upperHorizontal_le_log_majorant
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ x ∈ Set.uIoc (0 : ℝ) (N + 1 : ℝ),
        ‖Complex.finiteAbelPlanaLogSummand w
            ((x : ℂ) + (T : ℂ) * Complex.I)‖ ≤
          Real.log (1 + ‖w‖ + (N + 1 : ℝ) + |T|) + Real.pi + 1 := by
  exact
    Complex.norm_finiteAbelPlanaLogSummand_horizontal_le_log_majorant
      hw N Complex.I (Or.inl rfl)

/-- Pointwise estimate on the lower horizontal cotangent-remainder integrand.

This is the finite-strip estimate: the logarithmic summand contributes at most
logarithmic growth in `|T|`, while the lower-half-plane cotangent remainder
contributes exponential decay. -/
theorem Complex.norm_finiteAbelPlanaLogBottomHorizontalIntegrand_le_majorant
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ x ∈ Set.uIoc (0 : ℝ) (N + 1 : ℝ),
        ‖Complex.finiteAbelPlanaLogSummand w
            ((x : ℂ) - (T : ℂ) * Complex.I) *
          (Complex.finiteAbelPlanaCotangentKernel
              ((x : ℂ) - (T : ℂ) * Complex.I) -
            (Real.pi : ℂ) * Complex.I)‖ ≤
          Complex.finiteAbelPlanaLogHorizontalPointwiseMajorant N w T := by
  filter_upwards
    [Complex.norm_finiteAbelPlanaLogSummand_lowerHorizontal_le_log_majorant
      hw N,
      Complex.norm_finiteAbelPlanaCotangentKernel_lowerHorizontal_remainder_le_exp
      N] with T hlog hcot x hx
  let L : ℝ :=
    Real.log (1 + ‖w‖ + (N + 1 : ℝ) + |T|) + Real.pi + 1
  let E : ℝ :=
    Real.exp (-(2 * Real.pi * |T|))
  let C : ℝ := 4 * (Real.pi + 1)
  have hlog_x :
      ‖Complex.finiteAbelPlanaLogSummand w
          ((x : ℂ) - (T : ℂ) * Complex.I)‖ ≤ L :=
    hlog x hx
  have hcot_x :
      ‖Complex.finiteAbelPlanaCotangentKernel
          ((x : ℂ) - (T : ℂ) * Complex.I) -
        (Real.pi : ℂ) * Complex.I‖ ≤ C * E :=
    hcot x hx
  have hL_nonneg : 0 ≤ L :=
    le_trans (norm_nonneg _) hlog_x
  have hCE_nonneg : 0 ≤ C * E :=
    le_trans (norm_nonneg _) hcot_x
  have hmul :
      ‖Complex.finiteAbelPlanaLogSummand w
          ((x : ℂ) - (T : ℂ) * Complex.I)‖ *
        ‖Complex.finiteAbelPlanaCotangentKernel
          ((x : ℂ) - (T : ℂ) * Complex.I) -
        (Real.pi : ℂ) * Complex.I‖ ≤
        L * (C * E) :=
    mul_le_mul hlog_x hcot_x (norm_nonneg _) hL_nonneg
  calc
    ‖Complex.finiteAbelPlanaLogSummand w
        ((x : ℂ) - (T : ℂ) * Complex.I) *
      (Complex.finiteAbelPlanaCotangentKernel
          ((x : ℂ) - (T : ℂ) * Complex.I) -
        (Real.pi : ℂ) * Complex.I)‖ =
        ‖Complex.finiteAbelPlanaLogSummand w
          ((x : ℂ) - (T : ℂ) * Complex.I)‖ *
        ‖Complex.finiteAbelPlanaCotangentKernel
          ((x : ℂ) - (T : ℂ) * Complex.I) -
        (Real.pi : ℂ) * Complex.I‖ := by
      exact norm_mul _ _
    _ ≤ L * (C * E) := hmul
    _ = Complex.finiteAbelPlanaLogHorizontalPointwiseMajorant N w T := by
      exact Eq.trans
        (Real.horizontal_pointwise_majorant_assoc C L E)
        (Complex.finiteAbelPlanaLogHorizontalPointwiseMajorant_eq_local_factors
          N w T L C E rfl rfl rfl)

/-- Pointwise estimate on the upper horizontal cotangent-remainder integrand.

This is the upper-half-plane analogue of
`norm_finiteAbelPlanaLogBottomHorizontalIntegrand_le_majorant`. -/
theorem Complex.norm_finiteAbelPlanaLogTopHorizontalIntegrand_le_majorant
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ x ∈ Set.uIoc (0 : ℝ) (N + 1 : ℝ),
        ‖Complex.finiteAbelPlanaLogSummand w
            ((x : ℂ) + (T : ℂ) * Complex.I) *
          (Complex.finiteAbelPlanaCotangentKernel
              ((x : ℂ) + (T : ℂ) * Complex.I) +
            (Real.pi : ℂ) * Complex.I)‖ ≤
          Complex.finiteAbelPlanaLogHorizontalPointwiseMajorant N w T := by
  filter_upwards
    [Complex.norm_finiteAbelPlanaLogSummand_upperHorizontal_le_log_majorant
      hw N,
      Complex.norm_finiteAbelPlanaCotangentKernel_upperHorizontal_remainder_le_exp
      N] with T hlog hcot x hx
  let L : ℝ :=
    Real.log (1 + ‖w‖ + (N + 1 : ℝ) + |T|) + Real.pi + 1
  let E : ℝ :=
    Real.exp (-(2 * Real.pi * |T|))
  let C : ℝ := 4 * (Real.pi + 1)
  have hlog_x :
      ‖Complex.finiteAbelPlanaLogSummand w
          ((x : ℂ) + (T : ℂ) * Complex.I)‖ ≤ L :=
    hlog x hx
  have hcot_x :
      ‖Complex.finiteAbelPlanaCotangentKernel
          ((x : ℂ) + (T : ℂ) * Complex.I) +
        (Real.pi : ℂ) * Complex.I‖ ≤ C * E :=
    hcot x hx
  have hL_nonneg : 0 ≤ L :=
    le_trans (norm_nonneg _) hlog_x
  have hmul :
      ‖Complex.finiteAbelPlanaLogSummand w
          ((x : ℂ) + (T : ℂ) * Complex.I)‖ *
        ‖Complex.finiteAbelPlanaCotangentKernel
          ((x : ℂ) + (T : ℂ) * Complex.I) +
        (Real.pi : ℂ) * Complex.I‖ ≤
        L * (C * E) :=
    mul_le_mul hlog_x hcot_x (norm_nonneg _) hL_nonneg
  calc
    ‖Complex.finiteAbelPlanaLogSummand w
        ((x : ℂ) + (T : ℂ) * Complex.I) *
      (Complex.finiteAbelPlanaCotangentKernel
          ((x : ℂ) + (T : ℂ) * Complex.I) +
        (Real.pi : ℂ) * Complex.I)‖ =
        ‖Complex.finiteAbelPlanaLogSummand w
          ((x : ℂ) + (T : ℂ) * Complex.I)‖ *
        ‖Complex.finiteAbelPlanaCotangentKernel
          ((x : ℂ) + (T : ℂ) * Complex.I) +
        (Real.pi : ℂ) * Complex.I‖ := by
      exact norm_mul _ _
    _ ≤ L * (C * E) := hmul
    _ = Complex.finiteAbelPlanaLogHorizontalPointwiseMajorant N w T := by
      exact Eq.trans
        (Real.horizontal_pointwise_majorant_assoc C L E)
        (Complex.finiteAbelPlanaLogHorizontalPointwiseMajorant_eq_local_factors
          N w T L C E rfl rfl rfl)

/-- The horizontal integrals are bounded by the integrated pointwise
majorant.

This is the boring integral-envelope lemma that bridges the pointwise strip
estimates to the contour-level horizontal edge bounds. -/
theorem Complex.norm_finiteAbelPlanaLogHorizontalEdge_le_majorant
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      ‖Complex.finiteAbelPlanaLogBottomHorizontalEdge N w T‖ ≤
        Complex.finiteAbelPlanaLogHorizontalEdgeMajorant N w T ∧
      ‖Complex.finiteAbelPlanaLogTopHorizontalEdge N w T‖ ≤
        Complex.finiteAbelPlanaLogHorizontalEdgeMajorant N w T := by
  filter_upwards
    [Complex.norm_finiteAbelPlanaLogBottomHorizontalIntegrand_le_majorant hw N,
      Complex.norm_finiteAbelPlanaLogTopHorizontalIntegrand_le_majorant hw N] with
    T hbot htop
  constructor
  ·
    have hnorm :
        ‖∫ x : ℝ in (0 : ℝ)..(N + 1 : ℝ),
            Complex.finiteAbelPlanaLogSummand w
              ((x : ℂ) - (T : ℂ) * Complex.I) *
            (Complex.finiteAbelPlanaCotangentKernel
                ((x : ℂ) - (T : ℂ) * Complex.I) -
              (Real.pi : ℂ) * Complex.I)‖ ≤
          Complex.finiteAbelPlanaLogHorizontalPointwiseMajorant N w T *
            |(N + 1 : ℝ) - (0 : ℝ)| :=
      intervalIntegral.norm_integral_le_of_norm_le_const
        (fun x hx => hbot x hx)
    calc
      ‖Complex.finiteAbelPlanaLogBottomHorizontalEdge N w T‖ =
          ‖∫ x : ℝ in (0 : ℝ)..(N + 1 : ℝ),
            Complex.finiteAbelPlanaLogSummand w
              ((x : ℂ) - (T : ℂ) * Complex.I) *
            (Complex.finiteAbelPlanaCotangentKernel
                ((x : ℂ) - (T : ℂ) * Complex.I) -
              (Real.pi : ℂ) * Complex.I)‖ := by
        exact congrArg norm
          (Complex.finiteAbelPlanaLogBottomHorizontalEdge_eq_real_endpoint N w T)
      _ ≤ Complex.finiteAbelPlanaLogHorizontalPointwiseMajorant N w T *
            |(N + 1 : ℝ) - (0 : ℝ)| := hnorm
      _ = Complex.finiteAbelPlanaLogHorizontalEdgeMajorant N w T := by
        let A : ℝ := 4 * (Real.pi + 1)
        let B : ℝ := (N + 1 : ℝ)
        let C : ℝ :=
          Real.log (1 + ‖w‖ + (N + 1 : ℝ) + |T|) + Real.pi + 1
        let D : ℝ := Real.exp (-(2 * Real.pi * |T|))
        have hsource :
            Complex.finiteAbelPlanaLogHorizontalPointwiseMajorant N w T *
                |(N + 1 : ℝ) - (0 : ℝ)| =
              (A * C * D) * |(N + 1 : ℝ) - (0 : ℝ)| := by
          exact congrArg
            (fun y : ℝ => y * |(N + 1 : ℝ) - (0 : ℝ)|)
            (Complex.finiteAbelPlanaLogHorizontalPointwiseMajorant_unfold N w T)
        calc
          Complex.finiteAbelPlanaLogHorizontalPointwiseMajorant N w T *
              |(N + 1 : ℝ) - (0 : ℝ)| =
              (A * C * D) * |(N + 1 : ℝ) - (0 : ℝ)| := hsource
          _ =
              (A * C * D) * B := by
            exact congrArg (fun y : ℝ => (A * C * D) * y)
              (Real.horizontal_interval_length_abs_real N)
          _ = A * B * C * D :=
            Real.horizontal_edge_majorant_assoc A B C D
          _ = Complex.finiteAbelPlanaLogHorizontalEdgeMajorant N w T :=
            Complex.finiteAbelPlanaLogHorizontalEdgeMajorant_eq_local_factors
              N w T A B C D rfl rfl rfl rfl
  ·
    have hnorm :
        ‖∫ x : ℝ in (0 : ℝ)..(N + 1 : ℝ),
            Complex.finiteAbelPlanaLogSummand w
              ((x : ℂ) + (T : ℂ) * Complex.I) *
            (Complex.finiteAbelPlanaCotangentKernel
                ((x : ℂ) + (T : ℂ) * Complex.I) +
              (Real.pi : ℂ) * Complex.I)‖ ≤
          Complex.finiteAbelPlanaLogHorizontalPointwiseMajorant N w T *
            |(N + 1 : ℝ) - (0 : ℝ)| :=
      intervalIntegral.norm_integral_le_of_norm_le_const
        (fun x hx => htop x hx)
    calc
      ‖Complex.finiteAbelPlanaLogTopHorizontalEdge N w T‖ =
          ‖∫ x : ℝ in (0 : ℝ)..(N + 1 : ℝ),
            Complex.finiteAbelPlanaLogSummand w
              ((x : ℂ) + (T : ℂ) * Complex.I) *
            (Complex.finiteAbelPlanaCotangentKernel
                ((x : ℂ) + (T : ℂ) * Complex.I) +
              (Real.pi : ℂ) * Complex.I)‖ := by
        exact congrArg norm
          (Complex.finiteAbelPlanaLogTopHorizontalEdge_eq_real_endpoint N w T)
      _ ≤ Complex.finiteAbelPlanaLogHorizontalPointwiseMajorant N w T *
            |(N + 1 : ℝ) - (0 : ℝ)| := hnorm
      _ = Complex.finiteAbelPlanaLogHorizontalEdgeMajorant N w T := by
        let A : ℝ := 4 * (Real.pi + 1)
        let B : ℝ := (N + 1 : ℝ)
        let C : ℝ :=
          Real.log (1 + ‖w‖ + (N + 1 : ℝ) + |T|) + Real.pi + 1
        let D : ℝ := Real.exp (-(2 * Real.pi * |T|))
        have hsource :
            Complex.finiteAbelPlanaLogHorizontalPointwiseMajorant N w T *
                |(N + 1 : ℝ) - (0 : ℝ)| =
              (A * C * D) * |(N + 1 : ℝ) - (0 : ℝ)| := by
          exact congrArg
            (fun y : ℝ => y * |(N + 1 : ℝ) - (0 : ℝ)|)
            (Complex.finiteAbelPlanaLogHorizontalPointwiseMajorant_unfold N w T)
        calc
          Complex.finiteAbelPlanaLogHorizontalPointwiseMajorant N w T *
              |(N + 1 : ℝ) - (0 : ℝ)| =
              (A * C * D) * |(N + 1 : ℝ) - (0 : ℝ)| := hsource
          _ =
              (A * C * D) * B := by
            exact congrArg (fun y : ℝ => (A * C * D) * y)
              (Real.horizontal_interval_length_abs_real N)
          _ = A * B * C * D :=
            Real.horizontal_edge_majorant_assoc A B C D
          _ = Complex.finiteAbelPlanaLogHorizontalEdgeMajorant N w T :=
            Complex.finiteAbelPlanaLogHorizontalEdgeMajorant_eq_local_factors
              N w T A B C D rfl rfl rfl rfl

end

end LFunctions
end Boundary
