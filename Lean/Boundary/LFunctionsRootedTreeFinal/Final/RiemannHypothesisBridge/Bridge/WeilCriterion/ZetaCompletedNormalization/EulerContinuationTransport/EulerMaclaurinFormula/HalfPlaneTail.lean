import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.BernoulliCore

/-!
# Euler-Maclaurin half-plane tail algebra

This file owns the elementary pole-cleared algebra and convergent half-plane
Dirichlet-tail transports used before the finite-interval Euler-Maclaurin layer.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
open MeasureTheory Filter
local notation "π" => Real.pi

theorem eulerMaclaurinPoleClearedZetaFinitePart_eq_mul_raw
    (z : ℂ) :
    eulerMaclaurinPoleClearedZetaFinitePart z =
      (z - 1) * eulerMaclaurinZetaFinitePart z := by
  unfold eulerMaclaurinPoleClearedZetaFinitePart
  unfold eulerMaclaurinZetaFinitePart
  rfl

/-- Away from `s = 1`, the pole-cleared main term is `(s - 1)` times the raw
Euler-Maclaurin integral main term. -/
theorem eulerMaclaurinPoleClearedZetaMainTerm_eq_mul_raw
    {z : ℂ}
    (hz_ne_one : z ≠ 1) :
    eulerMaclaurinPoleClearedZetaMainTerm z =
      (z - 1) * eulerMaclaurinZetaMainTerm z := by
  unfold eulerMaclaurinPoleClearedZetaMainTerm
  unfold eulerMaclaurinZetaMainTerm
  let A : ℂ :=
    ((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ ((1 : ℂ) - z)
  have hden_ne : z - 1 ≠ 0 :=
    sub_ne_zero.mpr hz_ne_one
  calc
    A = A := rfl
    _ = (z - 1) * (A / (z - 1)) := by
      exact (mul_div_cancel₀ A hden_ne).symm

/-- The pole-cleared endpoint correction is `(s - 1)` times the raw endpoint
correction. -/
theorem eulerMaclaurinPoleClearedZetaEndpointTerm_eq_mul_raw
    (z : ℂ) :
    eulerMaclaurinPoleClearedZetaEndpointTerm z =
      (z - 1) * eulerMaclaurinZetaEndpointTerm z := by
  unfold eulerMaclaurinPoleClearedZetaEndpointTerm
  unfold eulerMaclaurinZetaEndpointTerm
  let U : ℂ :=
    1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z)
  calc
    (-((z - 1) / 2)) * U =
        ((z - 1) * (-(1 / 2 : ℂ))) * U := by
      have hdiv_inv :
          (z - 1) / 2 = (z - 1) * (2 : ℂ)⁻¹ :=
        div_eq_mul_inv (z - 1) (2 : ℂ)
      have hinv :
          (2 : ℂ)⁻¹ = (1 / 2 : ℂ) :=
        (one_div (2 : ℂ)).symm
      have hdiv :
          (z - 1) / 2 = (z - 1) * (1 / 2 : ℂ) :=
        Eq.trans hdiv_inv (congrArg (fun w : ℂ => (z - 1) * w) hinv)
      calc
        (-((z - 1) / 2)) * U =
            (-((z - 1) * (1 / 2 : ℂ))) * U := by
          exact congrArg (fun w : ℂ => (-w) * U) hdiv
        _ = ((z - 1) * (-(1 / 2 : ℂ))) * U := by
          exact congrArg (fun w : ℂ => w * U) (mul_neg (z - 1) (1 / 2 : ℂ)).symm
    _ = (z - 1) * ((-(1 / 2 : ℂ)) * U) := by
      exact mul_assoc (z - 1) (-(1 / 2 : ℂ)) U

/-- The pole-cleared Bernoulli remainder is `(s - 1)` times the raw
Euler-Maclaurin Bernoulli remainder. -/
theorem eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder_eq_mul_raw
    (z : ℂ) :
    eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder z =
      (z - 1) * eulerMaclaurinZetaBernoulliIntegralRemainder z := by
  unfold eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder
  unfold eulerMaclaurinZetaBernoulliIntegralRemainder
  let I : ℂ := eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z
  calc
    -((z - 1) * z) * I =
        ((z - 1) * -z) * I := by
      exact congrArg (fun w : ℂ => w * I) (mul_neg (z - 1) z).symm
    _ = (z - 1) * (-z * I) := by
      exact mul_assoc (z - 1) (-z) I

/-- Adding back a subtracted term. -/
theorem complex_eq_add_of_sub_eq
    {A B C : ℂ}
    (h : A - B = C) :
    A = B + C := by
  have hcancel : B + (A - B) = A := by
    calc
      B + (A - B) = B + (A + -B) := by
        exact congrArg (fun w : ℂ => B + w) (sub_eq_add_neg A B)
      _ = B + A + -B := by
        exact (add_assoc B A (-B)).symm
      _ = A + B + -B := by
        exact congrArg (fun w : ℂ => w + -B) (add_comm B A)
      _ = A + (B + -B) := by
        exact add_assoc A B (-B)
      _ = A + 0 := by
        exact congrArg (fun w : ℂ => A + w) (add_neg_cancel B)
      _ = A := by
        exact add_zero A
  calc
    A = B + (A - B) := by
      exact hcancel.symm
    _ = B + C := by
      exact congrArg (fun w : ℂ => B + w) h

/-- Complement of `Icc 1 N` as a post-cutoff indicator for functions whose
zeroth term vanishes. -/
theorem nat_not_Icc_one_indicator_eq_cutoff_if_of_zero
    {E : Type*}
    [Zero E]
    (f : ℕ → E)
    (N n : ℕ)
    (hf_zero : f 0 = 0) :
    ({m : ℕ | m ∉ Finset.Icc 1 N}.indicator f n) =
      if N < n then f n else 0 := by
  if hN_lt_n : N < n then
    have hn_not_mem : n ∉ Finset.Icc 1 N := by
      intro hn_mem
      have hn_le_N : n ≤ N :=
        (Finset.mem_Icc.mp hn_mem).2
      exact (Nat.not_lt_of_ge hn_le_N) hN_lt_n
    have hn_mem_tail : n ∈ {m : ℕ | m ∉ Finset.Icc 1 N} :=
      hn_not_mem
    have hleft :
        ({m : ℕ | m ∉ Finset.Icc 1 N}.indicator f n) = f n :=
      Set.indicator_of_mem hn_mem_tail f
    have hright :
        (if N < n then f n else 0) = f n :=
      if_pos hN_lt_n
    exact Eq.trans hleft hright.symm
  else
    if hn_zero : n = 0 then
      have hn_not_mem : n ∉ Finset.Icc 1 N := by
        intro hn_mem
        have hone_le_n : 1 ≤ n :=
          (Finset.mem_Icc.mp hn_mem).1
        have hone_le_zero : (1 : ℕ) ≤ 0 :=
          Eq.subst (motive := fun m : ℕ => 1 ≤ m) hn_zero hone_le_n
        exact (Nat.not_succ_le_zero 0) hone_le_zero
      have hn_mem_tail : n ∈ {m : ℕ | m ∉ Finset.Icc 1 N} :=
        hn_not_mem
      have hleft :
          ({m : ℕ | m ∉ Finset.Icc 1 N}.indicator f n) = f n :=
        Set.indicator_of_mem hn_mem_tail f
      have hf_n_zero : f n = 0 :=
        Eq.subst (motive := fun m : ℕ => f m = 0) hn_zero.symm hf_zero
      have hright :
          (if N < n then f n else 0) = 0 :=
        if_neg hN_lt_n
      exact Eq.trans hleft (Eq.trans hf_n_zero hright.symm)
    else
      have hn_pos : 0 < n :=
        Nat.pos_of_ne_zero hn_zero
      have hone_le_n : 1 ≤ n :=
        Nat.succ_le_of_lt hn_pos
      have hn_le_N : n ≤ N :=
        Nat.le_of_not_gt hN_lt_n
      have hn_mem_Icc : n ∈ Finset.Icc 1 N :=
        Finset.mem_Icc.mpr ⟨hone_le_n, hn_le_N⟩
      have hn_not_mem_tail : n ∉ {m : ℕ | m ∉ Finset.Icc 1 N} := by
        intro hn_mem_tail
        exact hn_mem_tail hn_mem_Icc
      have hleft :
          ({m : ℕ | m ∉ Finset.Icc 1 N}.indicator f n) = 0 :=
        Set.indicator_of_not_mem hn_not_mem_tail f
      have hright :
          (if N < n then f n else 0) = 0 :=
        if_neg hN_lt_n
      exact Eq.trans hleft hright.symm

/-- The zeroth Dirichlet monomial vanishes in the convergent half-plane. -/
theorem riemannZeta_dirichletTerm_zero_of_one_lt_re
    {z : ℂ}
    (hz : 1 < z.re) :
    (1 : ℂ) / ((0 : ℂ) ^ z) = 0 := by
  have hz_ne_zero : z ≠ 0 :=
    Complex.ne_zero_of_one_lt_re hz
  have hpow_zero : (0 : ℂ) ^ z = 0 :=
    (Complex.cpow_eq_zero_iff (0 : ℂ) z).mpr ⟨rfl, hz_ne_zero⟩
  calc
    (1 : ℂ) / ((0 : ℂ) ^ z) = (1 : ℂ) / 0 := by
      exact congrArg (fun w : ℂ => (1 : ℂ) / w) hpow_zero
    _ = 0 := by
      exact div_zero (1 : ℂ)

/-- In the convergent half-plane, removing the finite Dirichlet window from
`ζ(s)` leaves the post-cutoff Dirichlet tail as a `HasSum`. -/
theorem eulerMaclaurin_riemannZeta_halfPlane_finite_split_tail_hasSum
    (z : ℂ)
    (hz : 1 < z.re) :
    HasSum
      (fun n : ℕ =>
        if eulerMaclaurinPoleClearedZetaCutoff z < n then
          (1 : ℂ) / ((n : ℂ) ^ z)
        else
          0)
      (riemannZeta z - eulerMaclaurinZetaFinitePart z) := by
  let N : ℕ := eulerMaclaurinPoleClearedZetaCutoff z
  let f : ℕ → ℂ := fun n : ℕ => (1 : ℂ) / ((n : ℂ) ^ z)
  have hf_summable : Summable f :=
    (Complex.summable_one_div_nat_cpow (p := z)).mpr hz
  have hζ_eq : riemannZeta z = ∑' n : ℕ, f n :=
    zeta_eq_tsum_one_div_nat_cpow hz
  have hf_has_tsum : HasSum f (∑' n : ℕ, f n) :=
    hf_summable.hasSum
  have hf_has_zeta : HasSum f (riemannZeta z) :=
    Eq.subst
      (motive := fun S : ℂ => HasSum f S)
      hζ_eq.symm
      hf_has_tsum
  have htail_compl :
      HasSum
        (fun x : {n : ℕ // n ∉ Finset.Icc 1 N} => f x)
        (riemannZeta z - ∑ n ∈ Finset.Icc 1 N, f n) :=
    ((Finset.Icc 1 N).hasSum_iff_compl).mp hf_has_zeta
  have htail_indicator :
      HasSum
        ({n : ℕ | n ∉ Finset.Icc 1 N}.indicator f)
        (riemannZeta z - ∑ n ∈ Finset.Icc 1 N, f n) := by
    exact
      (hasSum_subtype_iff_indicator
        (s := {n : ℕ | n ∉ Finset.Icc 1 N})
        (f := f)).mp
        htail_compl
  have hf_zero : f 0 = 0 := by
    unfold f
    have hzero_cast : ((0 : ℕ) : ℂ) = 0 :=
      Nat.cast_zero
    calc
      (1 : ℂ) / (((0 : ℕ) : ℂ) ^ z) =
          (1 : ℂ) / ((0 : ℂ) ^ z) := by
        exact congrArg (fun w : ℂ => (1 : ℂ) / (w ^ z)) hzero_cast
      _ = 0 :=
        riemannZeta_dirichletTerm_zero_of_one_lt_re hz
  have hindicator :
      ({n : ℕ | n ∉ Finset.Icc 1 N}.indicator f) =
        (fun k : ℕ => if N < k then f k else 0) :=
    funext
      (fun n : ℕ =>
        nat_not_Icc_one_indicator_eq_cutoff_if_of_zero f N n hf_zero)
  have htail_if :
      HasSum
        (fun k : ℕ => if N < k then f k else 0)
        (riemannZeta z - ∑ n ∈ Finset.Icc 1 N, f n) :=
    Eq.subst
      (motive := fun g : ℕ → ℂ =>
        HasSum g (riemannZeta z - ∑ n ∈ Finset.Icc 1 N, f n))
      hindicator
      htail_indicator
  unfold eulerMaclaurinZetaFinitePart
  exact htail_if

/-- The exponent `-z` is integrable at infinity exactly in the half-plane
`1 < Re z`. -/
theorem eulerMaclaurin_cpow_neg_re_lt_neg_one_of_one_lt_re
    {z : ℂ}
    (hhalf_plane : 1 < z.re) :
    (-z).re < -1 := by
  have hneg : -z.re < -1 :=
    neg_lt_neg hhalf_plane
  exact
    Eq.subst
      (motive := fun x : ℝ => x < -1)
      (Complex.neg_re z).symm
      hneg

/-- The Euler-Maclaurin cutoff is a positive lower endpoint for improper
integrals. -/
theorem eulerMaclaurinPoleClearedZetaCutoff_real_pos
    (z : ℂ) :
    0 < (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)) := by
  exact Nat.cast_pos.mpr (eulerMaclaurinPoleClearedZetaCutoff_pos z)

/-- Mathlib's improper-integral formula applied to the zeta tail exponent
`-z`. -/
theorem eulerMaclaurin_riemannZeta_postCutoffTail_integral_cpow_neg_formula
    (z : ℂ)
    (hhalf_plane : 1 < z.re) :
    (∫ x in Set.Ioi (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)),
        (((x : ℝ) : ℂ) ^ (-z))) =
      -((((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ) : ℂ) ^
          ((-z) + 1)) /
        ((-z) + 1) := by
  exact
    integral_Ioi_cpow_of_lt
      (eulerMaclaurin_cpow_neg_re_lt_neg_one_of_one_lt_re hhalf_plane)
      (eulerMaclaurinPoleClearedZetaCutoff_real_pos z)

/-- Algebraic normalization of the improper-integral value.

This is the remaining `cpow` and division transport from mathlib's
`-N^((-z)+1)/((-z)+1)` to the owner term `N^(1-z)/(z-1)`. -/
theorem eulerMaclaurin_riemannZeta_postCutoffTail_integralFormula_eq_mainTerm
    (z : ℂ) :
    -((((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ) : ℂ) ^
          ((-z) + 1)) /
        ((-z) + 1) =
      eulerMaclaurinZetaMainTerm z := by
  unfold eulerMaclaurinZetaMainTerm
  let N : ℕ := eulerMaclaurinPoleClearedZetaCutoff z
  let A : ℂ := ((N : ℕ) : ℂ)
  have hbase :
      (((N : ℕ) : ℝ) : ℂ) = A :=
    Complex.ofReal_natCast N
  have hexponent :
      (-z) + 1 = (1 : ℂ) - z := by
    calc
      (-z) + 1 = (1 : ℂ) + (-z) := by
        exact add_comm (-z) (1 : ℂ)
      _ = (1 : ℂ) - z := by
        exact (sub_eq_add_neg (1 : ℂ) z).symm
  have hden :
      (-z) + 1 = -((z - 1)) := by
    calc
      (-z) + 1 = (1 : ℂ) - z :=
        hexponent
      _ = -(z - 1) := by
        exact (neg_sub z (1 : ℂ)).symm
  have hpow :
      ((((N : ℕ) : ℝ) : ℂ) ^ ((-z) + 1)) =
        A ^ ((1 : ℂ) - z) := by
    exact congrArg₂ (fun b e : ℂ => b ^ e) hbase hexponent
  calc
    -((((N : ℕ) : ℝ) : ℂ) ^ ((-z) + 1)) / ((-z) + 1) =
        -(A ^ ((1 : ℂ) - z)) / ((-z) + 1) := by
      exact congrArg
        (fun W : ℂ => -W / ((-z) + 1))
        hpow
    _ = -(A ^ ((1 : ℂ) - z)) / (-(z - 1)) := by
      exact congrArg
        (fun D : ℂ => -(A ^ ((1 : ℂ) - z)) / D)
        hden
    _ = A ^ ((1 : ℂ) - z) / (z - 1) := by
      exact neg_div_neg_eq (A ^ ((1 : ℂ) - z)) (z - 1)

/-- The Euler-Maclaurin integral main term for the post-cutoff tail.

For `N = ⌊2 + ‖z‖⌋₊`, mathlib's improper-integral formula for
`∫_N^∞ x^{-z} dx` gives `N^(1-z)/(z-1)` when `1 < Re z`.  This lemma records
the normalization used by the zeta owner definitions; the remaining work is
the standard `cpow` exponent arithmetic transporting
`integral_Ioi_cpow_of_lt` from exponent `-z`. -/
theorem eulerMaclaurin_riemannZeta_postCutoffTail_integralMain_eq_mainTerm_standard
    (z : ℂ)
    (hhalf_plane : 1 < z.re) :
    (∫ x in Set.Ioi (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)),
        (((x : ℝ) : ℂ) ^ (-z))) =
      eulerMaclaurinZetaMainTerm z := by
  exact
    Eq.trans
      (eulerMaclaurin_riemannZeta_postCutoffTail_integral_cpow_neg_formula
        z hhalf_plane)
      (eulerMaclaurin_riemannZeta_postCutoffTail_integralFormula_eq_mainTerm z)

/-- Endpoint normalization for the strict post-cutoff first-order
Euler-Maclaurin tail.

The endpoint correction is exactly `-(1/2)N^{-z}` in the owner notation. -/
theorem eulerMaclaurin_riemannZeta_postCutoffTail_endpoint_eq_endpointTerm
    (z : ℂ) :
    (-(1 / 2 : ℂ)) *
        (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z)) =
      eulerMaclaurinZetaEndpointTerm z := by
  unfold eulerMaclaurinZetaEndpointTerm
  rfl

/-- Remainder-sign normalization for the first-order Euler-Maclaurin tail.

With `B₁({x}) = {x} - 1/2`, the first-order remainder for
`f(x) = x^{-z}` is
`-z ∫_N^∞ B₁({x}) x^{-z-1} dx`, matching the raw owner remainder. -/
theorem eulerMaclaurin_riemannZeta_postCutoffTail_remainderSign_eq_remainderTerm
    (z : ℂ) :
    -z * eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z =
      eulerMaclaurinZetaBernoulliIntegralRemainder z := by
  unfold eulerMaclaurinZetaBernoulliIntegralRemainder
  rfl

/-- Derivative of the complex power profile used in the zeta tail.

On the positive real ray, the derivative of `x ↦ x^{-z}` is
`-z · x^{-z-1}`.  This is the calculus input in the first-order
Euler-Maclaurin formula. -/
theorem eulerMaclaurin_cpow_neg_deriv_eq
    (z : ℂ)
    {x : ℝ}
    (hx : 0 < x) :
    deriv (fun t : ℝ => (((t : ℝ) : ℂ) ^ (-z))) x =
      -z * (((x : ℝ) : ℂ) ^ (-(z + 1))) := by
  have hslit : ((x : ℂ) : ℂ) ∈ Complex.slitPlane :=
    Complex.ofReal_mem_slitPlane.mpr hx
  have hcomplex :
      HasDerivAt
        (fun w : ℂ => w ^ (-z))
        ((-z) * ((x : ℂ) ^ ((-z) - 1)) * 1)
        (x : ℂ) :=
    (hasDerivAt_id (x : ℂ)).cpow_const hslit
  have hreal :
      HasDerivAt
        (fun t : ℝ => (((t : ℝ) : ℂ) ^ (-z)))
        ((-z) * ((x : ℂ) ^ ((-z) - 1)) * 1)
        x :=
    hcomplex.comp_ofReal
  have hexponent :
      ((-z) - 1) = -(z + 1) := by
    calc
      ((-z) - 1) = (-z) + (-(1 : ℂ)) := by
        exact sub_eq_add_neg (-z) (1 : ℂ)
      _ = -(z + 1) := by
        exact (neg_add z (1 : ℂ)).symm
  have hvalue :
      ((-z) * ((x : ℂ) ^ ((-z) - 1)) * 1) =
        -z * (((x : ℝ) : ℂ) ^ (-(z + 1))) := by
    calc
      ((-z) * ((x : ℂ) ^ ((-z) - 1)) * 1) =
          (-z) * ((x : ℂ) ^ ((-z) - 1)) := by
        exact mul_one ((-z) * ((x : ℂ) ^ ((-z) - 1)))
      _ = -z * (((x : ℝ) : ℂ) ^ (-(z + 1))) := by
        exact congrArg
          (fun W : ℂ => -z * W)
          (congrArg (fun E : ℂ => ((x : ℂ) ^ E)) hexponent)
  exact Eq.trans hreal.deriv hvalue

/-- Positive natural reciprocal as a negative complex power.

This is the pointwise bridge between the Dirichlet summand notation
`1 / n^z` and the Euler-Maclaurin function notation `n^{-z}`. -/
theorem eulerMaclaurin_positiveNat_one_div_cpow_eq_cpow_neg
    (z : ℂ)
    {n : ℕ}
    (hn : 0 < n) :
    (1 : ℂ) / ((n : ℂ) ^ z) = (n : ℂ) ^ (-z) := by
  have hn_ne : (n : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  calc
    (1 : ℂ) / ((n : ℂ) ^ z) = (((n : ℂ) ^ z)⁻¹) := by
      exact one_div (((n : ℂ) ^ z))
    _ = (n : ℂ) ^ (-z) := by
      exact (Complex.cpow_neg (n : ℂ) z).symm

/-- Pointwise transport between the Euler-Maclaurin function-tail notation and
the Dirichlet reciprocal notation after a positive cutoff. -/
theorem eulerMaclaurin_cpow_neg_postCutoffTail_terms_eq_one_div
    (z : ℂ)
    (N : ℕ)
    (hN : 0 < N) :
    (fun n : ℕ =>
      if N < n then (((n : ℕ) : ℝ) : ℂ) ^ (-z) else 0) =
      (fun n : ℕ =>
        if N < n then (1 : ℂ) / ((n : ℂ) ^ z) else 0) := by
  exact funext
    (fun n : ℕ => by
      by_cases hn : N < n
      · have hn_pos : 0 < n :=
          lt_trans hN hn
        have hif_left :
            (if N < n then (((n : ℕ) : ℝ) : ℂ) ^ (-z) else 0) =
              (((n : ℕ) : ℝ) : ℂ) ^ (-z) :=
          if_pos hn
        have hif_right :
            (if N < n then (1 : ℂ) / ((n : ℂ) ^ z) else 0) =
              (1 : ℂ) / ((n : ℂ) ^ z) :=
          if_pos hn
        have hcast : (((n : ℕ) : ℝ) : ℂ) = (n : ℂ) :=
          Complex.ofReal_natCast n
        have hpow :
            (((n : ℕ) : ℝ) : ℂ) ^ (-z) =
              (n : ℂ) ^ (-z) :=
          congrArg (fun w : ℂ => w ^ (-z)) hcast
        have hrecip :
            (1 : ℂ) / ((n : ℂ) ^ z) = (n : ℂ) ^ (-z) :=
          eulerMaclaurin_positiveNat_one_div_cpow_eq_cpow_neg z hn_pos
        exact Eq.trans hif_left
          (Eq.trans hpow (Eq.trans hrecip.symm hif_right.symm))
      · have hif_left :
            (if N < n then (((n : ℕ) : ℝ) : ℂ) ^ (-z) else 0) = 0 :=
          if_neg hn
        have hif_right :
            (if N < n then (1 : ℂ) / ((n : ℂ) ^ z) else 0) = 0 :=
          if_neg hn
        exact Eq.trans hif_left hif_right.symm)

/-- `HasSum` transport between the Euler-Maclaurin function-tail notation and
the Dirichlet reciprocal notation after a positive cutoff. -/
theorem eulerMaclaurin_cpow_neg_postCutoffTail_hasSum_iff_one_div
    (z : ℂ)
    (N : ℕ)
    (hN : 0 < N)
    (S : ℂ) :
    HasSum
      (fun n : ℕ =>
        if N < n then (((n : ℕ) : ℝ) : ℂ) ^ (-z) else 0)
      S ↔
    HasSum
      (fun n : ℕ =>
        if N < n then (1 : ℂ) / ((n : ℂ) ^ z) else 0)
      S := by
  have hterms :
      (fun n : ℕ =>
        if N < n then (((n : ℕ) : ℝ) : ℂ) ^ (-z) else 0) =
        (fun n : ℕ =>
          if N < n then (1 : ℂ) / ((n : ℂ) ^ z) else 0) :=
    eulerMaclaurin_cpow_neg_postCutoffTail_terms_eq_one_div z N hN
  constructor
  · intro hsum
    exact Eq.subst
      (motive := fun f : ℕ → ℂ => HasSum f S)
      hterms
      hsum
  · intro hsum
    exact Eq.subst
      (motive := fun f : ℕ → ℂ => HasSum f S)
      hterms.symm
      hsum

end
end LFunctions
end Boundary
