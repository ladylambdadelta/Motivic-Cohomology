import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.FirstDerivative.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.ReciprocalVariation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.ReciprocalDensity.Regularity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.ReciprocalDensity.Calculus.Owner

/-!
# Reciprocal-density API theorems

This file contains the owner API theorems providing the final integration bounds and
estimates used by downstream modules.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi
/-- Owner API: endpoint contribution in the finite Abel decomposition after the
canonical cutoff. -/
theorem reciprocalDensity_logarithmicPhase_finiteAbelEndpoint_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
          ⌊((M : ℕ) : ℝ)⌋₊‖ +
      ‖(((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
          ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊‖ ≤
      2 + 8 * Real.log (3 + ‖t‖) := by
  exact
    logarithmicPhase_firstDerivative_finiteAbel_endpoint_arithmetic
      t ht hNM

/-- Owner API: reciprocal-derivative integral contribution in the finite Abel
decomposition after the canonical cutoff. -/
theorem reciprocalDensity_logarithmicPhase_finiteAbelDerivativeIntegral_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hpartial :
      ∀ {x : ℝ},
        (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x →
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
            8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ((1 : ℝ) / x ^ 2) *
          (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)) := by
  exact
    logarithmicPhase_firstDerivative_finiteAbel_integral_arithmetic
      t ht hpartial hNM

/-- Honest finite-endpoint majorant for the cutoff Abel tail.

This records the endpoint contribution plus the scalar reciprocal-density
integral that is actually proved at the reciprocal-variation owner layer. -/
def boundaryLineOnePointRealParam_logarithmicPhaseFiniteAbelTailMajorant
    (t : ℝ)
    (M : ℕ) : ℝ :=
  (2 + 8 * Real.log (3 + ‖t‖)) +
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
      ((1 : ℝ) / x ^ 2) *
        (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))

/-- Finite reciprocal-weighted logarithmic-phase tail estimate after the
canonical cutoff.

This is the owner theorem needed by Abel transport: the finite tail of
`n⁻¹ n^{-it}` is controlled by the endpoint and reciprocal-derivative terms in
the Abel/Euler-Maclaurin identity. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_finiteAbelTail_norm_le
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hpartial :
      ∀ {x : ℝ},
        (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x →
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
            8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∑ k ∈ Finset.Ioc ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
        ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseFiniteAbelTailMajorant t M := by
  let N : ℕ := ⌊2 + ‖t‖⌋₊
  let SM : ℂ :=
    ((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ) *
      boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
        ⌊((M : ℕ) : ℝ)⌋₊
  let SN : ℂ :=
    (((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
      boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
        ⌊(((N : ℕ) : ℝ))⌋₊
  let J : ℂ :=
    ∫ x in Set.Ioc (((N : ℕ) : ℝ)) ((M : ℕ) : ℝ),
      deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊
  have hf_diff :
      ∀ x ∈ Set.Icc (((N : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        DifferentiableAt ℝ (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x := by
    intro x hx
    have hx_pos : 0 < x :=
      lt_of_lt_of_le
        (Nat.cast_pos.mpr (boundaryLineOnePointRealParam_cutoff_pos t))
        hx.1
    exact (complexReciprocalOfReal_hasDerivAt hx_pos).differentiableAt
  have hf_int :
      IntegrableOn
        (deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)))
        (Set.Icc (((N : ℕ) : ℝ)) ((M : ℕ) : ℝ)) := by
    let d : ℝ → ℂ := fun x => -(1 : ℂ) / (x : ℂ) ^ 2
    have hd_cont : ContinuousOn d
        (Set.Icc (((N : ℕ) : ℝ)) ((M : ℕ) : ℝ)) := by
      intro x hx
      have hx_pos : 0 < x :=
        lt_of_lt_of_le
          (Nat.cast_pos.mpr (boundaryLineOnePointRealParam_cutoff_pos t))
          hx.1
      have hx_complex_ne : ((x : ℂ) ≠ 0) :=
        Complex.ofReal_ne_zero.mpr hx_pos.ne'
      have hx_sq_ne : ((x : ℂ) ^ 2) ≠ 0 :=
        pow_ne_zero 2 hx_complex_ne
      have hden :
          ContinuousAt (fun y : ℝ => ((y : ℂ) ^ 2)) x :=
        (Complex.continuous_ofReal.continuousAt.pow 2)
      have hquot :
          ContinuousAt (fun y : ℝ => (1 : ℂ) / ((y : ℂ) ^ 2)) x :=
        continuousAt_const.div hden hx_sq_ne
      exact hquot.neg.continuousWithinAt
    have hd_int : IntegrableOn d
        (Set.Icc (((N : ℕ) : ℝ)) ((M : ℕ) : ℝ)) :=
      ContinuousOn.integrableOn_Icc hd_cont
    have hd_eq : EqOn d
        (deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)))
        (Set.Icc (((N : ℕ) : ℝ)) ((M : ℕ) : ℝ)) :=
      fun x hx =>
        let hx_pos : 0 < x :=
          lt_of_lt_of_le
            (Nat.cast_pos.mpr (boundaryLineOnePointRealParam_cutoff_pos t))
            hx.1
        (complexReciprocalOfReal_deriv_eq hx_pos).symm
    exact hd_int.congr_fun hd_eq measurableSet_Icc
  have hidentity :
      (∑ k ∈ Finset.Ioc ⌊(((N : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
          ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))) =
        SM - SN - J := by
    exact
      abelSummation_boundaryLineOnePointRealParam_cutoff_finite_tail_endpoint_derivative_identity
        t hNM hf_diff hf_int
  have hendpoint :
      ‖SM‖ + ‖SN‖ ≤ 2 + 8 * Real.log (3 + ‖t‖) := by
    exact
      reciprocalDensity_logarithmicPhase_finiteAbelEndpoint_bound
        t ht hNM
  have hintegral :
      ‖J‖ ≤
        ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          ((1 : ℝ) / x ^ 2) *
            (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)) := by
    exact
      reciprocalDensity_logarithmicPhase_finiteAbelDerivativeIntegral_bound
        t ht hpartial hNM
  have htriangle :
      ‖SM - SN - J‖ ≤ ‖SM‖ + ‖SN‖ + ‖J‖ := by
    have hfirst : ‖SM - SN - J‖ ≤ ‖SM - SN‖ + ‖J‖ :=
      norm_sub_le (SM - SN) J
    have hsecond : ‖SM - SN‖ ≤ ‖SM‖ + ‖SN‖ :=
      norm_sub_le SM SN
    exact le_trans hfirst (add_le_add_right hsecond ‖J‖)
  have hpost_triangle :
      ‖SM‖ + ‖SN‖ + ‖J‖ ≤
        (2 + 8 * Real.log (3 + ‖t‖)) +
          ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
            ((1 : ℝ) / x ^ 2) *
              (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)) := by
    exact add_le_add hendpoint hintegral
  exact Eq.subst
    (motive := fun z : ℂ =>
      ‖z‖ ≤
        boundaryLineOnePointRealParam_logarithmicPhaseFiniteAbelTailMajorant t M)
    hidentity.symm
    (Eq.subst
      (motive := fun r : ℝ => ‖SM - SN - J‖ ≤ r)
      (show
        (2 + 8 * Real.log (3 + ‖t‖)) +
          ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
            ((1 : ℝ) / x ^ 2) *
              (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)) =
          boundaryLineOnePointRealParam_logarithmicPhaseFiniteAbelTailMajorant t M by
        rfl)
      (le_trans htriangle hpost_triangle))

/-- The enlarged logarithmic argument `3 + |t|` is absorbed by twice the
canonical boundary-line logarithm.  This is duplicated locally rather than
importing the downstream boundary-growth layer back into reciprocal density. -/
theorem reciprocalDensity_log_three_add_norm_le_two_mul_log_two_add_norm
    (t : ℝ) :
    Real.log (3 + ‖t‖) ≤
      2 * Real.log (2 + ‖t‖) := by
  let x : ℝ := ‖t‖
  have hx_nonneg : 0 ≤ x :=
    norm_nonneg t
  have hleft_pos : 0 < 3 + x := by
    have hthree_pos : (0 : ℝ) < 3 :=
      three_pos
    exact lt_of_lt_of_le hthree_pos (le_add_of_nonneg_right hx_nonneg)
  have harg_pos : 0 < 2 + x :=
    lt_of_lt_of_le zero_lt_two (le_add_of_nonneg_right hx_nonneg)
  have harg_ne : (2 : ℝ) + x ≠ 0 :=
    ne_of_gt harg_pos
  have htwo_ne : (2 : ℝ) ≠ 0 :=
    ne_of_gt zero_lt_two
  have harg_ge_two : (2 : ℝ) ≤ 2 + x :=
    le_add_of_nonneg_right hx_nonneg
  have hthree_le :
      3 + x ≤ 2 * (2 + x) := by
    have hx_le_two_x : x ≤ 2 * x := by
      calc
        x = 1 * x := by
          exact (one_mul x).symm
        _ ≤ 2 * x :=
          mul_le_mul_of_nonneg_right one_le_two hx_nonneg
    calc
      3 + x ≤ 4 + 2 * x :=
        add_le_add (by exact three_le_four) hx_le_two_x
      _ = 2 * (2 + x) := by
        exact (left_distrib 2 2 x).symm
  have hlog_le :
      Real.log (3 + x) ≤ Real.log (2 * (2 + x)) :=
    Real.log_le_log hleft_pos hthree_le
  have hlog_mul :
      Real.log (2 * (2 + x)) =
        Real.log 2 + Real.log (2 + x) :=
    Real.log_mul htwo_ne harg_ne
  have hlog_two_le :
      Real.log 2 ≤ Real.log (2 + x) :=
    Real.log_le_log zero_lt_two harg_ge_two
  have hsum_le :
      Real.log 2 + Real.log (2 + x) ≤
        Real.log (2 + x) + Real.log (2 + x) :=
    add_le_add_right hlog_two_le (Real.log (2 + x))
  calc
    Real.log (3 + ‖t‖) = Real.log (3 + x) := rfl
    _ ≤ Real.log (2 * (2 + x)) :=
      hlog_le
    _ = Real.log 2 + Real.log (2 + x) :=
      hlog_mul
    _ ≤ Real.log (2 + x) + Real.log (2 + x) :=
      hsum_le
    _ = 2 * Real.log (2 + x) := by
      exact (two_mul (Real.log (2 + x))).symm
    _ = 2 * Real.log (2 + ‖t‖) := rfl

/-- The explicit cutoff Abel-tail constant is bounded by a fixed multiple of
the canonical boundary-line logarithm. -/
theorem boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant_le_log
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t ≤
      36 * Real.log (2 + ‖t‖) := by
  let L : ℝ := Real.log (2 + ‖t‖)
  have hlog_one : (1 : ℝ) ≤ L :=
    one_le_log_two_add_norm_of_one_le_norm ht
  have hfour_le : (4 : ℝ) ≤ 4 * L := by
    calc
        (4 : ℝ) = 4 * 1 := by
          exact (mul_one 4).symm
      _ ≤ 4 * L :=
        mul_le_mul_of_nonneg_left hlog_one
          (Nat.cast_le.mpr (show (0 : ℕ) ≤ 4 by decide) : (0 : ℝ) ≤ 4)
  have hlog_three :
      Real.log (3 + ‖t‖) ≤ 2 * L :=
    reciprocalDensity_log_three_add_norm_le_two_mul_log_two_add_norm t
  have hsixteen :
      16 * Real.log (3 + ‖t‖) ≤ 32 * L := by
    calc
      16 * Real.log (3 + ‖t‖) ≤ 16 * (2 * L) :=
        mul_le_mul_of_nonneg_left hlog_three
          (Nat.cast_le.mpr (show (0 : ℕ) ≤ 16 by decide) : (0 : ℝ) ≤ 16)
        _ = 32 * L := by
          calc
            16 * (2 * L) = (16 * 2) * L :=
              (mul_assoc 16 2 L).symm
            _ = 32 * L := by
            exact congrArg
              (fun c : ℝ => c * L)
              (by
                have hnat : (16 : ℕ) * 2 = 32 := by decide
                have hcast :
                    (((16 : ℕ) * 2 : ℕ) : ℝ) = (32 : ℝ) :=
                  congrArg (fun n : ℕ => (n : ℝ)) hnat
                exact Eq.trans (Nat.cast_mul 16 2) hcast)
  calc
    boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t =
        4 + 16 * Real.log (3 + ‖t‖) := rfl
      _ ≤ 4 * L + 32 * L :=
        add_le_add hfour_le hsixteen
      _ = 36 * L := by
        calc
          4 * L + 32 * L = (4 + 32) * L :=
            (add_mul 4 32 L).symm
          _ = 36 * L := by
          exact congrArg
            (fun c : ℝ => c * L)
            (by
              have hnat : (4 : ℕ) + 32 = 36 := by decide
              have hcast :
                  (((4 : ℕ) + 32 : ℕ) : ℝ) = (36 : ℝ) :=
                congrArg (fun n : ℕ => (n : ℝ)) hnat
              exact Eq.trans (Nat.cast_add 4 32) hcast)
    _ = 36 * Real.log (2 + ‖t‖) := rfl

/-- Adjacent finite interval sums split over `Ioc` blocks. -/
theorem finite_sum_Ioc_eq_sub_left
    {α : Type*}
    [AddCommGroup α]
    {C N M : ℕ}
    (hCN : C ≤ N)
    (hNM : N ≤ M)
    (f : ℕ → α) :
    (∑ n ∈ Finset.Ioc N M, f n) =
      (∑ n ∈ Finset.Ioc C M, f n) -
        ∑ n ∈ Finset.Ioc C N, f n := by
  classical
  have hdisjoint :
      Disjoint (Finset.Ioc C N) (Finset.Ioc N M) := by
    intro n hn_left hn_right
    have hn_le_N : n ≤ N :=
      (Finset.mem_Ioc.mp hn_left).2
    have hN_lt_n : N < n :=
      (Finset.mem_Ioc.mp hn_right).1
    exact not_le_of_gt hN_lt_n hn_le_N
  have hunion :
      Finset.Ioc C N ∪ Finset.Ioc N M = Finset.Ioc C M :=
    Finset.Ioc_union_Ioc_eq_Ioc hCN hNM
  have hsum_union :
      (∑ n ∈ Finset.Ioc C N ∪ Finset.Ioc N M, f n) =
        (∑ n ∈ Finset.Ioc C N, f n) +
          ∑ n ∈ Finset.Ioc N M, f n := by
    exact Finset.sum_union hdisjoint
  have hmain :
      (∑ n ∈ Finset.Ioc C M, f n) =
        (∑ n ∈ Finset.Ioc C N, f n) +
          ∑ n ∈ Finset.Ioc N M, f n := by
    exact Eq.trans (congrArg (fun s : Finset ℕ => ∑ n ∈ s, f n) hunion.symm) hsum_union
  calc
    (∑ n ∈ Finset.Ioc N M, f n) =
        ((∑ n ∈ Finset.Ioc C N, f n) +
          ∑ n ∈ Finset.Ioc N M, f n) -
          ∑ n ∈ Finset.Ioc C N, f n := by
      let A : α := ∑ n ∈ Finset.Ioc C N, f n
      let B : α := ∑ n ∈ Finset.Ioc N M, f n
      have hcancel :
          (A + B) - A = B := by
        calc
          (A + B) - A = (A + B) + -A := by
            exact sub_eq_add_neg (A + B) A
          _ = A + (B + -A) := by
            exact add_assoc A B (-A)
          _ = A + (-A + B) := by
            exact congrArg (fun y : α => A + y) (add_comm B (-A))
          _ = (A + -A) + B := by
            exact (add_assoc A (-A) B).symm
          _ = 0 + B := by
            exact congrArg (fun y : α => y + B) (add_right_neg A)
          _ = B := by
            exact zero_add B
      exact hcancel.symm
    _ = (∑ n ∈ Finset.Ioc C M, f n) -
        ∑ n ∈ Finset.Ioc C N, f n := by
      exact congrArg (fun z : α => z - ∑ n ∈ Finset.Ioc C N, f n) hmain.symm

/-- Post-cutoff finite sub-blocks are bounded as differences of two cutoff
tails. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_finiteTail_norm_le
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hpartial :
      ∀ {x : ℝ},
        (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x →
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
            8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))
    {N M : ℕ}
    (hCN : ⌊2 + ‖t‖⌋₊ ≤ N)
    (hNM : N ≤ M) :
    ‖∑ n ∈ Finset.Ioc N M,
        ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseFiniteAbelTailMajorant t M +
        boundaryLineOnePointRealParam_logarithmicPhaseFiniteAbelTailMajorant t N := by
  let C : ℕ := ⌊2 + ‖t‖⌋₊
  let f : ℕ → ℂ :=
    fun n => ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))
  have hsplit :
      (∑ n ∈ Finset.Ioc N M, f n) =
        (∑ n ∈ Finset.Ioc C M, f n) -
          ∑ n ∈ Finset.Ioc C N, f n :=
    finite_sum_Ioc_eq_sub_left hCN hNM f
  have hM_floor : ⌊((M : ℕ) : ℝ)⌋₊ = M := by
    exact Nat.floor_natCast M
  have hN_floor : ⌊((N : ℕ) : ℝ)⌋₊ = N := by
    exact Nat.floor_natCast N
  have hC_floor : ⌊(((C : ℕ) : ℝ))⌋₊ = C := by
    exact Nat.floor_natCast C
  have hM_tail :
      ‖∑ n ∈ Finset.Ioc C M, f n‖ ≤
        boundaryLineOnePointRealParam_logarithmicPhaseFiniteAbelTailMajorant t M := by
    exact boundaryLineOnePointRealParam_logarithmicPhase_finiteAbelTail_norm_le
      t ht hpartial (le_trans hCN hNM)
  have hN_tail :
      ‖∑ n ∈ Finset.Ioc C N, f n‖ ≤
        boundaryLineOnePointRealParam_logarithmicPhaseFiniteAbelTailMajorant t N := by
    exact boundaryLineOnePointRealParam_logarithmicPhase_finiteAbelTail_norm_le
      t ht hpartial hCN
  have htriangle :
      ‖(∑ n ∈ Finset.Ioc C M, f n) -
          ∑ n ∈ Finset.Ioc C N, f n‖ ≤
        boundaryLineOnePointRealParam_logarithmicPhaseFiniteAbelTailMajorant t M +
          boundaryLineOnePointRealParam_logarithmicPhaseFiniteAbelTailMajorant t N := by
    exact le_trans
      (norm_sub_le (∑ n ∈ Finset.Ioc C M, f n) (∑ n ∈ Finset.Ioc C N, f n))
      (add_le_add hM_tail hN_tail)
  exact Eq.subst
    (motive := fun z : ℂ =>
      ‖z‖ ≤
        boundaryLineOnePointRealParam_logarithmicPhaseFiniteAbelTailMajorant t M +
          boundaryLineOnePointRealParam_logarithmicPhaseFiniteAbelTailMajorant t N)
    hsplit.symm
    htriangle

/-- Honest piecewise majorant for arbitrary finite reciprocal-weighted
logarithmic-phase tails.

The three cases are: the whole block is before the canonical cutoff, the whole
block is after it, or the block crosses it. -/
def boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailMajorant
    (t : ℝ)
    (N M : ℕ) : ℝ :=
  if M ≤ ⌊2 + ‖t‖⌋₊ then
    2 * Real.log (2 + ‖t‖)
  else if ⌊2 + ‖t‖⌋₊ ≤ N then
    boundaryLineOnePointRealParam_logarithmicPhaseFiniteAbelTailMajorant t M +
      boundaryLineOnePointRealParam_logarithmicPhaseFiniteAbelTailMajorant t N
  else
    2 * Real.log (2 + ‖t‖) +
      boundaryLineOnePointRealParam_logarithmicPhaseFiniteAbelTailMajorant t M

/-- All finite reciprocal-weighted logarithmic-phase tails are logarithmically
bounded, using the constructive pre-cutoff estimate and the cutoff Abel tail. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_finiteTail_norm_le
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hpartial :
      ∀ {x : ℝ},
        (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x →
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
            8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))
    {N M : ℕ}
    (hN : 1 ≤ N)
    (hNM : N ≤ M) :
    ‖∑ n ∈ Finset.Ioc N M,
        ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailMajorant t N M := by
  match Decidable.em (M ≤ ⌊2 + ‖t‖⌋₊) with
  | Or.inl hMcut =>
    have hpre :
        ‖∑ n ∈ Finset.Ioc N M,
            ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
          2 * Real.log (2 + ‖t‖) :=
      boundaryLineOnePointRealParam_logarithmicPhase_preCutoff_finiteTail_norm_le
        t ht hN hMcut
    exact
      Eq.subst
        (motive := fun r : ℝ =>
          ‖∑ n ∈ Finset.Ioc N M,
              ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤ r)
        (show
          2 * Real.log (2 + ‖t‖) =
            boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailMajorant t N M by
          exact (if_pos hMcut).symm)
        hpre
  | Or.inr hMcut =>
    have hC_le_M : ⌊2 + ‖t‖⌋₊ ≤ M :=
      Nat.le_of_not_ge hMcut
    match Decidable.em (⌊2 + ‖t‖⌋₊ ≤ N) with
    | Or.inl hC_le_N =>
      have hpost :
          ‖∑ n ∈ Finset.Ioc N M,
              ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
            boundaryLineOnePointRealParam_logarithmicPhaseFiniteAbelTailMajorant t M +
              boundaryLineOnePointRealParam_logarithmicPhaseFiniteAbelTailMajorant t N :=
        boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_finiteTail_norm_le
          t ht hpartial hC_le_N hNM
      exact
        Eq.subst
          (motive := fun r : ℝ =>
            ‖∑ n ∈ Finset.Ioc N M,
                ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤ r)
          (show
            boundaryLineOnePointRealParam_logarithmicPhaseFiniteAbelTailMajorant t M +
                boundaryLineOnePointRealParam_logarithmicPhaseFiniteAbelTailMajorant t N =
              boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailMajorant t N M by
            exact (if_pos hC_le_N).symm.trans (if_neg hMcut).symm)
          hpost
    | Or.inr hC_le_N =>
      have hN_le_C : N ≤ ⌊2 + ‖t‖⌋₊ :=
        Nat.le_of_not_ge hC_le_N
      let C : ℕ := ⌊2 + ‖t‖⌋₊
      let f : ℕ → ℂ :=
        fun n => ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))
      have hsplit_union :
          Finset.Ioc N C ∪ Finset.Ioc C M = Finset.Ioc N M :=
        Finset.Ioc_union_Ioc_eq_Ioc hN_le_C hC_le_M
      have hdisjoint :
          Disjoint (Finset.Ioc N C) (Finset.Ioc C M) := by
        intro n hn_left hn_right
        have hn_le_C : n ≤ C :=
          (Finset.mem_Ioc.mp hn_left).2
        have hC_lt_n : C < n :=
          (Finset.mem_Ioc.mp hn_right).1
        exact not_le_of_gt hC_lt_n hn_le_C
      have hsplit_sum :
          (∑ n ∈ Finset.Ioc N M, f n) =
            (∑ n ∈ Finset.Ioc N C, f n) +
              ∑ n ∈ Finset.Ioc C M, f n := by
        calc
          (∑ n ∈ Finset.Ioc N M, f n) =
              ∑ n ∈ Finset.Ioc N C ∪ Finset.Ioc C M, f n := by
            exact congrArg (fun s : Finset ℕ => ∑ n ∈ s, f n) hsplit_union.symm
          _ = (∑ n ∈ Finset.Ioc N C, f n) +
              ∑ n ∈ Finset.Ioc C M, f n :=
            Finset.sum_union hdisjoint
      have hpre :
          ‖∑ n ∈ Finset.Ioc N C, f n‖ ≤
            2 * Real.log (2 + ‖t‖) :=
        boundaryLineOnePointRealParam_logarithmicPhase_preCutoff_finiteTail_norm_le
          t ht hN (le_rfl : C ≤ ⌊2 + ‖t‖⌋₊)
      have hC_floor : ⌊(((C : ℕ) : ℝ))⌋₊ = C := by
        exact Nat.floor_natCast C
      have hM_floor : ⌊((M : ℕ) : ℝ)⌋₊ = M := by
        exact Nat.floor_natCast M
      have hcut :
          ‖∑ n ∈ Finset.Ioc C M, f n‖ ≤
            boundaryLineOnePointRealParam_logarithmicPhaseFiniteAbelTailMajorant t M := by
        exact boundaryLineOnePointRealParam_logarithmicPhase_finiteAbelTail_norm_le
          t ht hpartial hC_le_M
      have htriangle :
          ‖(∑ n ∈ Finset.Ioc N C, f n) +
              ∑ n ∈ Finset.Ioc C M, f n‖ ≤
            2 * Real.log (2 + ‖t‖) +
              boundaryLineOnePointRealParam_logarithmicPhaseFiniteAbelTailMajorant t M := by
        exact le_trans
          (norm_add_le (∑ n ∈ Finset.Ioc N C, f n) (∑ n ∈ Finset.Ioc C M, f n))
          (add_le_add hpre hcut)
      exact Eq.subst
        (motive := fun z : ℂ =>
          ‖z‖ ≤ boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailMajorant t N M)
        hsplit_sum.symm
        (Eq.subst
          (motive := fun r : ℝ =>
            ‖(∑ n ∈ Finset.Ioc N C, f n) +
                ∑ n ∈ Finset.Ioc C M, f n‖ ≤ r)
          (show
            2 * Real.log (2 + ‖t‖) +
                boundaryLineOnePointRealParam_logarithmicPhaseFiniteAbelTailMajorant t M =
              boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailMajorant t N M by
            exact (if_neg hC_le_N).symm.trans (if_neg hMcut).symm)
          htriangle)

end

end
end LFunctions
end Boundary
