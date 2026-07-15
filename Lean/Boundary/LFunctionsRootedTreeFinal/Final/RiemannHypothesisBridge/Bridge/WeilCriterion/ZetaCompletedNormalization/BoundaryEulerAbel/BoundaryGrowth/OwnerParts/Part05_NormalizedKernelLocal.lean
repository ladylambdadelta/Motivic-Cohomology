import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.Part04_ClassicalPrefixAndSplitting
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.SetIntegral

/-!
# Boundary growth owner part 5

This file is a mechanical forward-order split of `BoundaryGrowth.Owner`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
open MeasureTheory
local notation "π" => Real.pi

/-- Pointwise normalization of the unweighted logarithmic-phase derivative on
the positive real axis.  This is the algebraic bridge from the standard
Euler-Maclaurin derivative `-z * x^-(z+1)` to the public
`((-it) / x) * x^(-it)` kernel. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_unweightedDerivative_standard_eq_normalized
    (t : ℝ)
    {x : ℝ}
    (hx : 0 < x) :
    -((t : ℂ) * Complex.I) *
        (((x : ℝ) : ℂ) ^ (-(((t : ℂ) * Complex.I) + 1))) =
      (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
        (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) := by
  have hx_ne : (x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hx.ne'
  have hexponent :
      (-(((t : ℂ) * Complex.I) + 1)) =
        -((t : ℂ) * Complex.I) + (-1 : ℂ) :=
    neg_add ((t : ℂ) * Complex.I) (1 : ℂ)
  have hcpow_add :
      (((x : ℝ) : ℂ) ^ (-((t : ℂ) * Complex.I) + (-1 : ℂ))) =
        (((x : ℝ) : ℂ) ^ (-((t : ℂ) * Complex.I)) ) *
          (((x : ℝ) : ℂ) ^ (-1 : ℂ)) :=
    Complex.cpow_add (-((t : ℂ) * Complex.I)) (-1 : ℂ) hx_ne
  have hcpow_neg_one :
      (((x : ℝ) : ℂ) ^ (-1 : ℂ)) = (x : ℂ)⁻¹ :=
    Complex.cpow_neg_one (x : ℂ)
  have hstandard :
      -((t : ℂ) * Complex.I) *
          (((x : ℝ) : ℂ) ^ (-(((t : ℂ) * Complex.I) + 1))) =
        -((t : ℂ) * Complex.I) *
          ((((x : ℝ) : ℂ) ^ (-((t : ℂ) * Complex.I)) ) * (x : ℂ)⁻¹) := by
    calc
      -((t : ℂ) * Complex.I) *
          (((x : ℝ) : ℂ) ^ (-(((t : ℂ) * Complex.I) + 1))) =
          -((t : ℂ) * Complex.I) *
            (((x : ℝ) : ℂ) ^ (-(((t : ℂ) * Complex.I) + 1))) := Eq.refl _
      _ = -((t : ℂ) * Complex.I) *
            (((x : ℝ) : ℂ) ^ (-((t : ℂ) * Complex.I) + (-1 : ℂ))) :=
        congrArg
          (fun y : ℂ => -((t : ℂ) * Complex.I) * (((x : ℝ) : ℂ) ^ y))
          hexponent
      _ = -((t : ℂ) * Complex.I) *
          ((((x : ℝ) : ℂ) ^ (-((t : ℂ) * Complex.I)) ) *
          (((x : ℝ) : ℂ) ^ (-1 : ℂ))) :=
        congrArg (fun y : ℂ => -((t : ℂ) * Complex.I) * y) hcpow_add
      _ = -((t : ℂ) * Complex.I) *
          ((((x : ℝ) : ℂ) ^ (-((t : ℂ) * Complex.I)) ) * (x : ℂ)⁻¹) :=
        congrArg
          (fun y : ℂ => -((t : ℂ) * Complex.I) *
            ((((x : ℝ) : ℂ) ^ (-((t : ℂ) * Complex.I)) ) * y))
          hcpow_neg_one
  have hnormalized :
      -((t : ℂ) * Complex.I) *
          ((((x : ℝ) : ℂ) ^ (-((t : ℂ) * Complex.I)) ) * (x : ℂ)⁻¹) =
        ((-((t : ℂ) * Complex.I) / (x : ℂ)) *
          (((x : ℝ) : ℂ) ^ (-((t : ℂ) * Complex.I)) )) := by
    have hdiv : -((t : ℂ) * Complex.I) / (x : ℂ) =
        -((t : ℂ) * Complex.I) * (x : ℂ)⁻¹ :=
      div_eq_mul_inv (-((t : ℂ) * Complex.I)) (x : ℂ)
    calc
      -((t : ℂ) * Complex.I) *
          ((((x : ℝ) : ℂ) ^ (-((t : ℂ) * Complex.I)) ) * (x : ℂ)⁻¹) =
          (-((t : ℂ) * Complex.I) * (x : ℂ)⁻¹) *
            (((x : ℝ) : ℂ) ^ (-((t : ℂ) * Complex.I)) ) :=
        Eq.trans
          (congrArg
            (fun y : ℂ => -((t : ℂ) * Complex.I) * y)
            (mul_comm (((x : ℝ) : ℂ) ^ (-((t : ℂ) * Complex.I)) ) ((x : ℂ)⁻¹)))
          (mul_assoc (-((t : ℂ) * Complex.I)) (x : ℂ)⁻¹
            (((x : ℝ) : ℂ) ^ (-((t : ℂ) * Complex.I)) )).symm
      _ = (-((t : ℂ) * Complex.I) / (x : ℂ)) *
          (((x : ℝ) : ℂ) ^ (-((t : ℂ) * Complex.I)) ) :=
        congrArg
          (fun y : ℂ => y * (((x : ℝ) : ℂ) ^ (-((t : ℂ) * Complex.I)) ))
          hdiv.symm
  have hneg_mul :
      -((t : ℂ) * Complex.I) = -(t : ℂ) * Complex.I :=
    (neg_mul (t : ℂ) Complex.I).symm
  have hphase_neg_mul :
      -((t : ℂ) * Complex.I) = -(t : ℂ) * Complex.I :=
    (neg_mul (t : ℂ) Complex.I).symm
  exact Eq.trans hstandard
    (Eq.trans hnormalized
      (congrArg
        (fun z : ℂ => (z / (x : ℂ)) *
          (((x : ℝ) : ℂ) ^ z))
        hphase_neg_mul))

/-- Integral normalization for the unweighted Euler-Maclaurin Bernoulli
remainder on the finite post-cutoff interval. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_bernoulliRemainder_standard_eq_normalized
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        (-((t : ℂ) * Complex.I) *
          (((x : ℝ) : ℂ) ^ (-(((t : ℂ) * Complex.I) + 1))))) =
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) := by
  let s : Set ℝ :=
    Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ))
  have hcongr :
      Set.EqOn
        (fun x : ℝ =>
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (-((t : ℂ) * Complex.I) *
              (((x : ℝ) : ℂ) ^ (-(((t : ℂ) * Complex.I) + 1)))))
        (fun x : ℝ =>
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))
        s := by
    intro x hx
    have hx_u :
        x ∈
          Set.uIcc
            (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
            (((M : ℕ) : ℝ)) := by
      have hle :
          (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ (((M : ℕ) : ℝ)) :=
        Nat.cast_le.mpr hM
      have hx_icc :
          x ∈
            Set.Icc
              (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
              (((M : ℕ) : ℝ)) :=
        ⟨le_of_lt hx.1, hx.2⟩
      exact (Set.uIcc_of_le hle).symm ▸ hx_icc
    have hx_pos :
        0 < x :=
      boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_mem_interval_pos
        t hM hx_u
    exact congrArg
      (fun y : ℂ => ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * y)
      (boundaryLineOnePointRealParam_logarithmicPhasePartialSum_unweightedDerivative_standard_eq_normalized
        t hx_pos)
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hcongr

/-- Pointwise norm of the normalized unweighted logarithmic-phase derivative
kernel on the positive real axis. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_normalizedDerivativeKernel_norm_eq
    (t : ℝ)
    {x : ℝ}
    (hx : 0 < x) :
    ‖(((-(t : ℂ) * Complex.I) / (x : ℂ)) *
        (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ =
      ‖t‖ / x := by
  let K : ℂ := ((-(t : ℂ) * Complex.I) / (x : ℂ))
  have hphase :
      boundaryLineOnePointRealParam_logarithmicPhaseFunction t x =
        ((x : ℂ) ^ (-(t : ℂ) * Complex.I)) :=
    boundaryLineOnePointRealParam_logarithmicPhaseFunction_eq_cpow_of_pos
      t hx
  have hderiv :
      deriv (boundaryLineOnePointRealParam_logarithmicPhaseFunction t) x =
        K * boundaryLineOnePointRealParam_logarithmicPhaseFunction t x :=
    boundaryLineOnePointRealParam_logarithmicPhaseFunction_deriv_eq
      t hx
  have hkernel_to_function :
      ‖K * (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ =
        ‖K * boundaryLineOnePointRealParam_logarithmicPhaseFunction t x‖ := by
    exact congrArg (fun z : ℂ => ‖K * z‖) hphase.symm
  have hfunction_to_deriv :
      ‖K * boundaryLineOnePointRealParam_logarithmicPhaseFunction t x‖ =
        ‖deriv (boundaryLineOnePointRealParam_logarithmicPhaseFunction t) x‖ :=
    congrArg norm hderiv.symm
  have hderiv_norm :
      ‖deriv (boundaryLineOnePointRealParam_logarithmicPhaseFunction t) x‖ =
        ‖t‖ / x :=
    boundaryLineOnePointRealParam_logarithmicPhaseFunction_deriv_norm_eq
      t hx
  exact Eq.trans hkernel_to_function (Eq.trans hfunction_to_deriv hderiv_norm)

/-- Pointwise norm majorization for the first-periodic-Bernoulli normalized
unweighted logarithmic-phase derivative kernel on the post-cutoff interval. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_pointwise_norm_le_norm_div
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∀ x ∈ Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
      ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
        ‖t‖ / x := by
  intro x hx
  have hx_u :
      x ∈
        Set.uIcc
          (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
          (((M : ℕ) : ℝ)) := by
    have hle :
        (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ (((M : ℕ) : ℝ)) :=
      Nat.cast_le.mpr hM
    have hx_icc :
        x ∈
          Set.Icc
            (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
            (((M : ℕ) : ℝ)) :=
      ⟨le_of_lt hx.1, hx.2⟩
    exact (Set.uIcc_of_le hle).symm ▸ hx_icc
  have hx_pos :
      0 < x :=
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_mem_interval_pos
      t hM hx_u
  let B : ℂ := ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
  let K : ℂ :=
    (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
      (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
  have hB : ‖B‖ ≤ (1 : ℝ) :=
    eulerMaclaurinFirstPeriodicBernoulli_norm_cast_le_one_finite x
  have hK :
      ‖K‖ = ‖t‖ / x :=
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_normalizedDerivativeKernel_norm_eq
      t hx_pos
  have hmul :
      ‖B * K‖ = ‖B‖ * ‖K‖ :=
    norm_mul B K
  have hproduct :
      ‖B‖ * ‖K‖ ≤ (1 : ℝ) * (‖t‖ / x) := by
    exact mul_le_mul hB (le_of_eq hK) (norm_nonneg K) zero_le_one
  exact
    Eq.subst
      (motive := fun r : ℝ => r ≤ ‖t‖ / x)
      hmul.symm
      (Eq.subst
        (motive := fun r : ℝ => ‖B‖ * ‖K‖ ≤ r)
        (one_mul (‖t‖ / x))
        hproduct)

/-- After the canonical cutoff, the first-periodic-Bernoulli normalized
unweighted logarithmic-phase derivative kernel is pointwise bounded by one. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_pointwise_norm_le_one
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∀ x ∈ Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
      ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
        1 := by
  intro x hx
  have hnorm_div :
      ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
        ‖t‖ / x :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_pointwise_norm_le_norm_div
      t hM x hx
  have hx_u :
      x ∈
        Set.uIcc
          (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
          (((M : ℕ) : ℝ)) := by
    have hle :
        (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ (((M : ℕ) : ℝ)) :=
      Nat.cast_le.mpr hM
    have hx_icc :
        x ∈
          Set.Icc
            (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
            (((M : ℕ) : ℝ)) :=
      ⟨le_of_lt hx.1, hx.2⟩
    exact (Set.uIcc_of_le hle).symm ▸ hx_icc
  have hx_pos :
      0 < x :=
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_mem_interval_pos
      t hM hx_u
  have hx_ge_cutoff :
      (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ x :=
    le_of_lt hx.1
  have hcutoff_ge :
      (1 : ℝ) + ‖t‖ ≤ ((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) :=
    boundaryLineOnePointRealParam_postCutoff_one_add_norm_le_cutoff t
  have ht_le_x :
      ‖t‖ ≤ x := by
    have ht_le_one_add : ‖t‖ ≤ (1 : ℝ) + ‖t‖ :=
      le_add_of_nonneg_left zero_le_one
    exact le_trans ht_le_one_add (le_trans hcutoff_ge hx_ge_cutoff)
  have hdiv_le_one :
      ‖t‖ / x ≤ 1 :=
    (div_le_one₀ hx_pos).mpr ht_le_x
  exact le_trans hnorm_div hdiv_le_one

/-- Bochner norm domination for the normalized unweighted Bernoulli kernel by
the constant-one finite-interval majorant. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_integral_norm_le_constOneIntegral
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
      ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        (1 : ℝ) := by
  let s : Set ℝ :=
    Set.Ioc
      (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
      (((M : ℕ) : ℝ))
  let f : ℝ → ℂ := fun x =>
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
      (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
        (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
  let g : ℝ → ℝ := fun _x => (1 : ℝ)
  have hle :
      (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ (((M : ℕ) : ℝ)) :=
    Nat.cast_le.mpr hM
  have hg :
      Integrable g (volume.restrict s) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp
      (intervalIntegrable_const (μ := volume) (a := (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)))
        (b := (((M : ℕ) : ℝ))) (c := (1 : ℝ)))
  have hbound :
      ∀ᵐ x ∂volume.restrict s, ‖f x‖ ≤ g x :=
    (ae_restrict_mem measurableSet_Ioc).mono
      (fun x hx =>
        boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_pointwise_norm_le_one
          t hM x hx)
  exact norm_integral_le_of_norm_le hg hbound

/-- Bochner norm domination for the normalized unweighted Bernoulli kernel by
the logarithmic absolute majorant `|t| / x`.

This is the sharp absolute-value estimate available before using cancellation
of the first-periodic Bernoulli factor.  The remaining defect theorem needs the
strictly stronger oscillatory improvement of this bound. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_integral_norm_le_normDivIntegral
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
      ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ‖t‖ / x := by
  let s : Set ℝ :=
    Set.Ioc
      (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
      (((M : ℕ) : ℝ))
  let f : ℝ → ℂ := fun x =>
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
      (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
        (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
  let g : ℝ → ℝ := fun x => ‖t‖ / x
  have hle :
      (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ (((M : ℕ) : ℝ)) :=
    Nat.cast_le.mpr hM
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_cutoff_pos t
  have hcutoff_real_pos :
      (0 : ℝ) < (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) :=
    Nat.cast_pos.mpr hcutoff_pos
  have hM_pos : 0 < M :=
    lt_of_lt_of_le hcutoff_pos hM
  have hM_real_pos : (0 : ℝ) < (((M : ℕ) : ℝ)) :=
    Nat.cast_pos.mpr hM_pos
  have hg_interval :
      IntervalIntegrable g volume
        (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
        (((M : ℕ) : ℝ)) := by
    have hinv_interval :
        IntervalIntegrable (fun x : ℝ => x⁻¹) volume
          (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
          (((M : ℕ) : ℝ)) := by
      have hzero_not_mem :
          (0 : ℝ) ∉
            Set.uIcc
              (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
              (((M : ℕ) : ℝ)) :=
        by
          have hcutoff_le_M :
              (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ (((M : ℕ) : ℝ)) :=
            Nat.cast_le.mpr hM
          intro hzero
          have hzeroIcc :
              (0 : ℝ) ∈
                Set.Icc
                  (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
                  (((M : ℕ) : ℝ)) :=
            (Set.uIcc_of_le hcutoff_le_M).symm ▸ hzero
          exact (not_lt_of_ge hzeroIcc.1) hcutoff_real_pos
      exact (intervalIntegrable_inv_iff.mpr (Or.inr hzero_not_mem))
    have hconst_mul :
        IntervalIntegrable (fun x : ℝ => ‖t‖ * x⁻¹) volume
          (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
          (((M : ℕ) : ℝ)) :=
      hinv_interval.const_mul ‖t‖
    exact hconst_mul.congr
      (Filter.Eventually.of_forall
        (fun x =>
          (div_eq_mul_inv ‖t‖ x).symm))
  have hg :
      Integrable g (volume.restrict s) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp hg_interval
  have hbound :
      ∀ᵐ x ∂volume.restrict s, ‖f x‖ ≤ g x :=
    (ae_restrict_mem measurableSet_Ioc).mono
      (fun x hx =>
        boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_pointwise_norm_le_norm_div
          t hM x hx)
  exact norm_integral_le_of_norm_le hg hbound

/-- One-interval constant cancellation for the first-periodic Bernoulli factor.

This is the local cancellation input used by the finite-defect route: constants
may be subtracted from the slowly varying normalized kernel on each unit
interval without changing the Bernoulli integral. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_oneInterval_const_mul_integral_eq_zero
    (n : ℕ)
    (c : ℂ) :
    (∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * c) = 0 := by
  let s : Set ℝ :=
    Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ))
  let B : ℝ → ℂ := fun x =>
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
  have hmul :
      (∫ x in s, B x * c) = (∫ x in s, B x) * c :=
    MeasureTheory.integral_mul_right c B
  have hzero :
      (∫ x in s, B x) = 0 :=
    eulerMaclaurinFirstPeriodicBernoulli_oneInterval_integral_eq_zero n
  calc
    (∫ x in s, B x * c) = (∫ x in s, B x) * c :=
      hmul
    _ = 0 * c := by
      exact congrArg (fun z : ℂ => z * c) hzero
    _ = 0 := by
      exact zero_mul c

/-- Exact local subtraction identity for the normalized-kernel variation
argument on a single unit interval.

After subtracting the left-endpoint value of the slowly varying factor, the
constant part vanishes by the Bernoulli zero-mean identity above.  The remaining
future estimate is therefore a genuine local-variation bound for
`K x - K n`, not an absolute-value estimate for `K x`. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_oneInterval_subtract_leftEndpoint
    (n : ℕ)
    (K : ℝ → ℂ)
    (hBK :
      Integrable
        (fun x : ℝ =>
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * K x)
        (volume.restrict
          (Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)))))
    (hBc :
      Integrable
        (fun x : ℝ =>
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            K (((n : ℕ) : ℝ)))
        (volume.restrict
          (Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ))))) :
    (∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * K x) =
      (∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (K x - K (((n : ℕ) : ℝ)))) := by
  let s : Set ℝ :=
    Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ))
  let B : ℝ → ℂ := fun x =>
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
  let c : ℂ := K (((n : ℕ) : ℝ))
  have hpoint :
      (fun x : ℝ => B x * (K x - c)) =
        (fun x : ℝ => B x * K x - B x * c) := by
    funext x
    exact mul_sub (B x) (K x) c
  have hsub :
      (∫ x in s, B x * K x - B x * c) =
        (∫ x in s, B x * K x) - (∫ x in s, B x * c) :=
    MeasureTheory.integral_sub hBK hBc
  have hconst :
      (∫ x in s, B x * c) = 0 :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_oneInterval_const_mul_integral_eq_zero
      n c
  have hvariation :
      (∫ x in s, B x * (K x - c)) =
        (∫ x in s, B x * K x) := by
    calc
      (∫ x in s, B x * (K x - c)) =
          (∫ x in s, B x * K x - B x * c) := by
        exact congrArg (fun f : ℝ → ℂ => ∫ x in s, f x) hpoint
      _ = (∫ x in s, B x * K x) - (∫ x in s, B x * c) :=
        hsub
      _ = (∫ x in s, B x * K x) - 0 := by
        exact congrArg
          (fun z : ℂ => (∫ x in s, B x * K x) - z)
          hconst
      _ = (∫ x in s, B x * K x) := by
        exact sub_zero (∫ x in s, B x * K x)
  exact hvariation.symm

/-- Pointwise local-variation domination after subtracting the unit-interval
left endpoint.

Together with
`boundaryLineOnePointRealParam_firstPeriodicBernoulli_oneInterval_subtract_leftEndpoint`,
this reduces the finite-defect estimate to bounding the movement of the
normalized kernel itself on each unit interval. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_oneInterval_subtracted_pointwise_norm_le
    (n : ℕ)
    (K : ℝ → ℂ) :
    ∀ x : ℝ,
      ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (K x - K (((n : ℕ) : ℝ)))‖ ≤
        ‖K x - K (((n : ℕ) : ℝ))‖ := by
  intro x
  let B : ℂ := ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
  let D : ℂ := K x - K (((n : ℕ) : ℝ))
  have hB : ‖B‖ ≤ (1 : ℝ) :=
    eulerMaclaurinFirstPeriodicBernoulli_norm_cast_le_one_finite x
  have hmul : ‖B * D‖ = ‖B‖ * ‖D‖ :=
    norm_mul B D
  have hprod : ‖B‖ * ‖D‖ ≤ (1 : ℝ) * ‖D‖ :=
    mul_le_mul hB (le_rfl : ‖D‖ ≤ ‖D‖) (norm_nonneg D) zero_le_one
  exact Eq.subst
    (motive := fun r : ℝ => r ≤ ‖D‖)
    hmul.symm
    (Eq.subst
      (motive := fun r : ℝ => ‖B‖ * ‖D‖ ≤ r)
      (one_mul ‖D‖)
      hprod)

/-- Pointwise movement bound for the normalized logarithmic-phase derivative
kernel on one interval.

The right side separates the elementary reciprocal drift from the genuinely
oscillatory phase drift.  Summing this estimate after the Bernoulli zero-mean
subtraction is the remaining finite-defect task. -/
theorem boundaryLineOnePointRealParam_normalizedKernel_movement_norm_le_reciprocal_add_phase
    (t x y : ℝ) :
    ‖(((-(t : ℂ) * Complex.I) / (x : ℂ)) *
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
        (((-(t : ℂ) * Complex.I) / (y : ℂ)) *
          (((y : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
      ‖(-(t : ℂ) * Complex.I)‖ *
          ‖(x : ℂ)⁻¹ - (y : ℂ)⁻¹‖ *
            ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ +
        ‖(-(t : ℂ) * Complex.I)‖ *
          ‖(y : ℂ)⁻¹‖ *
            ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
              (((y : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ := by
  let a : ℂ := -(t : ℂ) * Complex.I
  let bx : ℂ := (x : ℂ)⁻¹
  let bY : ℂ := (y : ℂ)⁻¹
  let px : ℂ := (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))
  let py : ℂ := (((y : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))
  have hx_div : (-(t : ℂ) * Complex.I) / (x : ℂ) = a * bx :=
    div_eq_mul_inv a (x : ℂ)
  have hy_div : (-(t : ℂ) * Complex.I) / (y : ℂ) = a * bY :=
    div_eq_mul_inv a (y : ℂ)
  have hdecomp :
      (a * bx) * px - (a * bY) * py =
        a * ((bx - bY) * px + bY * (px - py)) := by
    calc
      (a * bx) * px - (a * bY) * py =
          a * (bx * px) - a * (bY * py) := by
        exact congrArg₂ Sub.sub
          (mul_assoc a bx px)
          (mul_assoc a bY py)
      _ = a * (bx * px - bY * py) := by
        exact (mul_sub a (bx * px) (bY * py)).symm
      _ = a * (((bx - bY) * px) + bY * (px - py)) := by
        have hinner :
            bx * px - bY * py =
              (bx - bY) * px + bY * (px - py) := by
          calc
            bx * px - bY * py =
                (bx * px - bY * px) + (bY * px - bY * py) := by
              have hcancel :
                  (bx * px - bY * px) + (bY * px - bY * py) =
                    bx * px - bY * py := by
                calc
                  (bx * px - bY * px) + (bY * px - bY * py) =
                      (bx * px + -(bY * px)) + (bY * px + -(bY * py)) := by
                    exact congrArg₂ Add.add
                      (sub_eq_add_neg (bx * px) (bY * px))
                      (sub_eq_add_neg (bY * px) (bY * py))
                  _ = bx * px + (-(bY * px) + (bY * px + -(bY * py))) := by
                    exact add_assoc (bx * px) (-(bY * px)) (bY * px + -(bY * py))
                  _ = bx * px + ((-(bY * px) + bY * px) + -(bY * py)) := by
                    exact congrArg (fun z : ℂ => bx * px + z)
                      (add_assoc (-(bY * px)) (bY * px) (-(bY * py))).symm
                  _ = bx * px + (0 + -(bY * py)) := by
                    exact congrArg
                      (fun z : ℂ => bx * px + (z + -(bY * py)))
                      (neg_add_cancel (bY * px))
                  _ = bx * px + -(bY * py) := by
                    exact congrArg (fun z : ℂ => bx * px + z)
                      (zero_add (-(bY * py)))
                  _ = bx * px - bY * py := by
                    exact (sub_eq_add_neg (bx * px) (bY * py)).symm
              exact hcancel.symm
            _ = ((bx - bY) * px) + (bY * px - bY * py) := by
              exact congrArg (fun z : ℂ => z + (bY * px - bY * py))
                (sub_mul bx bY px).symm
            _ = ((bx - bY) * px) + bY * (px - py) := by
              exact congrArg (fun z : ℂ => ((bx - bY) * px) + z)
                (mul_sub bY px py).symm
        exact congrArg (fun z : ℂ => a * z) hinner
  have htarget_eq :
      ((-(t : ℂ) * Complex.I) / (x : ℂ)) * px -
          ((-(t : ℂ) * Complex.I) / (y : ℂ)) * py =
        a * ((bx - bY) * px + bY * (px - py)) := by
    calc
      ((-(t : ℂ) * Complex.I) / (x : ℂ)) * px -
          ((-(t : ℂ) * Complex.I) / (y : ℂ)) * py =
          (a * bx) * px - ((-(t : ℂ) * Complex.I) / (y : ℂ)) * py := by
        exact congrArg
          (fun z : ℂ => z * px - ((-(t : ℂ) * Complex.I) / (y : ℂ)) * py)
          hx_div
      _ = (a * bx) * px - (a * bY) * py := by
        exact congrArg
          (fun z : ℂ => (a * bx) * px - z * py)
          hy_div
      _ = a * ((bx - bY) * px + bY * (px - py)) :=
        hdecomp
  have hnorm_decomp :
      ‖a * ((bx - bY) * px + bY * (px - py))‖ ≤
        ‖a‖ * (‖(bx - bY) * px‖ + ‖bY * (px - py)‖) := by
    calc
      ‖a * ((bx - bY) * px + bY * (px - py))‖ =
          ‖a‖ * ‖(bx - bY) * px + bY * (px - py)‖ := by
        exact norm_mul a ((bx - bY) * px + bY * (px - py))
      _ ≤ ‖a‖ * (‖(bx - bY) * px‖ + ‖bY * (px - py)‖) :=
        mul_le_mul_of_nonneg_left
          (norm_add_le ((bx - bY) * px) (bY * (px - py)))
          (norm_nonneg a)
  have hsplit :
      ‖a‖ * (‖(bx - bY) * px‖ + ‖bY * (px - py)‖) =
        ‖a‖ * ‖bx - bY‖ * ‖px‖ + ‖a‖ * ‖bY‖ * ‖px - py‖ := by
    calc
      ‖a‖ * (‖(bx - bY) * px‖ + ‖bY * (px - py)‖) =
          ‖a‖ * (‖bx - bY‖ * ‖px‖ + ‖bY‖ * ‖px - py‖) := by
        exact congrArg (fun z : ℝ => ‖a‖ * z)
          (congrArg₂ Add.add
            (norm_mul (bx - bY) px)
            (norm_mul bY (px - py)))
      _ = ‖a‖ * (‖bx - bY‖ * ‖px‖) +
          ‖a‖ * (‖bY‖ * ‖px - py‖) := by
        exact mul_add ‖a‖ (‖bx - bY‖ * ‖px‖) (‖bY‖ * ‖px - py‖)
      _ = ‖a‖ * ‖bx - bY‖ * ‖px‖ + ‖a‖ * ‖bY‖ * ‖px - py‖ := by
        exact congrArg₂ Add.add
          (mul_assoc ‖a‖ ‖bx - bY‖ ‖px‖).symm
          (mul_assoc ‖a‖ ‖bY‖ ‖px - py‖).symm
  exact Eq.subst
    (motive := fun z : ℂ =>
      ‖z‖ ≤
        ‖a‖ * ‖bx - bY‖ * ‖px‖ +
          ‖a‖ * ‖bY‖ * ‖px - py‖)
    htarget_eq.symm
    (le_trans hnorm_decomp (le_of_eq hsplit))

/-- Quantitative reciprocal drift on a single unit interval. -/
theorem boundaryLineOnePointRealParam_oneInterval_reciprocal_movement_norm_le
    {n : ℕ}
    (hn : 0 < n)
    {x : ℝ}
    (hx : x ∈ Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ))) :
    ‖(x : ℂ)⁻¹ - (((n : ℕ) : ℝ) : ℂ)⁻¹‖ ≤
      (1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ)) := by
  let nr : ℝ := ((n : ℕ) : ℝ)
  have hnr_pos : 0 < nr :=
    Nat.cast_pos.mpr hn
  have hx_pos : 0 < x :=
    lt_trans hnr_pos hx.1
  have hx_ge : nr ≤ x :=
    le_of_lt hx.1
  have hx_le_succ : x ≤ (((n + 1 : ℕ) : ℝ)) :=
    hx.2
  have hsucc_eq : (((n + 1 : ℕ) : ℝ)) = nr + 1 :=
    Nat.cast_add_one n
  have hx_sub_le_one : x - nr ≤ 1 := by
    have hsub :
        x - nr ≤ (((n + 1 : ℕ) : ℝ)) - nr :=
      sub_le_sub_right hx_le_succ nr
    have hright :
        (((n + 1 : ℕ) : ℝ)) - nr = 1 := by
      calc
        (((n + 1 : ℕ) : ℝ)) - nr =
            (nr + 1) - nr := by
          exact congrArg (fun y : ℝ => y - nr) hsucc_eq
        _ = 1 := by
          exact add_sub_cancel_left nr 1
    exact Eq.subst
      (motive := fun r : ℝ => x - nr ≤ r)
      hright
      hsub
  have hnr_sub_nonpos : nr - x ≤ 0 := by
    exact sub_nonpos.mpr hx_ge
  have hnum_abs :
      |nr - x| = x - nr := by
    calc
      |nr - x| = -(nr - x) :=
        abs_of_nonpos hnr_sub_nonpos
      _ = x - nr := by
        exact neg_sub nr x
  have hnum_le_one : |nr - x| ≤ 1 := by
    exact Eq.subst
      (motive := fun r : ℝ => r ≤ 1)
      hnum_abs.symm
      hx_sub_le_one
  have hx_ne : (x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hx_pos.ne'
  have hn_ne : ((nr : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hnr_pos.ne'
  have hinv :
      (x : ℂ)⁻¹ - ((nr : ℝ) : ℂ)⁻¹ =
        (((nr : ℝ) : ℂ) - (x : ℂ)) / ((x : ℂ) * ((nr : ℝ) : ℂ)) :=
    inv_sub_inv hx_ne hn_ne
  have hnorm :
      ‖(x : ℂ)⁻¹ - ((nr : ℝ) : ℂ)⁻¹‖ =
        |nr - x| / (x * nr) := by
    have hnorm_div :
        ‖(((nr : ℝ) : ℂ) - (x : ℂ)) / ((x : ℂ) * ((nr : ℝ) : ℂ))‖ =
          ‖((nr : ℝ) : ℂ) - (x : ℂ)‖ /
            ‖(x : ℂ) * ((nr : ℝ) : ℂ)‖ :=
      norm_div (((nr : ℝ) : ℂ) - (x : ℂ)) ((x : ℂ) * ((nr : ℝ) : ℂ))
    have hnum :
        ‖((nr : ℝ) : ℂ) - (x : ℂ)‖ = |nr - x| := by
      have hsub :
          ((nr : ℝ) : ℂ) - (x : ℂ) = ((nr - x : ℝ) : ℂ) := by
        exact (Complex.ofReal_sub nr x).symm
      exact Eq.trans (congrArg norm hsub) (RCLike.norm_ofReal (nr - x))
    have hden :
        ‖(x : ℂ) * ((nr : ℝ) : ℂ)‖ = x * nr := by
      have hmul : ‖(x : ℂ) * ((nr : ℝ) : ℂ)‖ =
          ‖(x : ℂ)‖ * ‖((nr : ℝ) : ℂ)‖ :=
        norm_mul (x : ℂ) ((nr : ℝ) : ℂ)
      have hx_norm : ‖(x : ℂ)‖ = x := by
        exact Eq.trans (RCLike.norm_ofReal x) (abs_of_pos hx_pos)
      have hn_norm : ‖((nr : ℝ) : ℂ)‖ = nr := by
        exact Eq.trans (RCLike.norm_ofReal nr) (abs_of_pos hnr_pos)
      exact Eq.trans hmul
        (congrArg₂ (fun a b : ℝ => a * b) hx_norm hn_norm)
    exact Eq.trans (congrArg norm hinv)
      (Eq.trans hnorm_div
        (congrArg₂ (fun a b : ℝ => a / b) hnum hden))
  have hden_pos : 0 < x * nr :=
    mul_pos hx_pos hnr_pos
  have hnr_sq_pos : 0 < nr * nr :=
    mul_pos hnr_pos hnr_pos
  have hden_ge : nr * nr ≤ x * nr :=
    mul_le_mul_of_nonneg_right hx_ge (le_of_lt hnr_pos)
  have hquot_le :
      |nr - x| / (x * nr) ≤ (1 : ℝ) / (x * nr) :=
    div_le_div_of_nonneg_right hnum_le_one (le_of_lt hden_pos)
  have hone_div_le :
      (1 : ℝ) / (x * nr) ≤ (1 : ℝ) / (nr * nr) :=
    one_div_le_one_div_of_le hnr_sq_pos hden_ge
  exact Eq.subst
    (motive := fun r : ℝ =>
      r ≤ (1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ)))
    hnorm.symm
    (le_trans hquot_le hone_div_le)

/-- Quantitative phase drift on one unit interval after the logarithmic-phase
cutoff.

This is the local mean-value estimate for the genuinely oscillatory factor
`x^{-it}`.  It is kept separate from the reciprocal drift so the later finite
defect summation can use cancellation information interval by interval. -/
theorem boundaryLineOnePointRealParam_oneInterval_phase_drift_norm_le
    (t : ℝ)
    {n : ℕ}
    (hn : 0 < n)
    {x : ℝ}
    (hx : x ∈ Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ))) :
    ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
        ((((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      ‖t‖ / (((n : ℕ) : ℝ)) := by
  let nr : ℝ := ((n : ℕ) : ℝ)
  let phase : ℝ → ℂ :=
    boundaryLineOnePointRealParam_logarithmicPhaseFunction t
  let derivPhase : ℝ → ℂ := fun u =>
    (((-(t : ℂ) * Complex.I) / (u : ℂ)) * phase u)
  have hnr_pos : 0 < nr :=
    Nat.cast_pos.mpr hn
  have hx_pos : 0 < x :=
    lt_trans hnr_pos hx.1
  have hnr_le_x : nr ≤ x :=
    le_of_lt hx.1
  have hx_le_succ : x ≤ (((n + 1 : ℕ) : ℝ)) :=
    hx.2
  have hsucc_eq : (((n + 1 : ℕ) : ℝ)) = nr + 1 :=
    Nat.cast_add_one n
  have hx_sub_le_one : x - nr ≤ 1 := by
    have hsub :
        x - nr ≤ (((n + 1 : ℕ) : ℝ)) - nr :=
      sub_le_sub_right hx_le_succ nr
    have hright :
        (((n + 1 : ℕ) : ℝ)) - nr = 1 := by
      calc
        (((n + 1 : ℕ) : ℝ)) - nr =
            (nr + 1) - nr := by
          exact congrArg (fun y : ℝ => y - nr) hsucc_eq
        _ = 1 := by
          exact add_sub_cancel_left nr 1
    exact Eq.subst
      (motive := fun r : ℝ => x - nr ≤ r)
      hright
      hsub
  have hnr_mem : nr ∈ Set.Icc nr x :=
    ⟨le_rfl, hnr_le_x⟩
  have hx_mem : x ∈ Set.Icc nr x :=
    ⟨hnr_le_x, le_rfl⟩
  have hderiv :
      ∀ u ∈ Set.Icc nr x,
        HasDerivWithinAt phase (derivPhase u) (Set.Icc nr x) u := by
    intro u hu
    have hu_pos : 0 < u :=
      lt_of_lt_of_le hnr_pos hu.1
    exact
      (boundaryLineOnePointRealParam_logarithmicPhaseFunction_hasDerivAt
        t hu_pos).hasDerivWithinAt
  have hderiv_bound :
      ∀ u ∈ Set.Icc nr x, ‖derivPhase u‖ ≤ ‖t‖ / nr := by
    intro u hu
    have hu_pos : 0 < u :=
      lt_of_lt_of_le hnr_pos hu.1
    have hnorm_eq : ‖derivPhase u‖ = ‖t‖ / u :=
      boundaryLineOnePointRealParam_logarithmicPhaseFunction_derivative_norm_eq
        t hu_pos
    have hnum_nonneg : 0 ≤ ‖t‖ :=
      norm_nonneg t
    have hdiv_le : ‖t‖ / u ≤ ‖t‖ / nr :=
      div_le_div_of_nonneg_left hnum_nonneg hnr_pos hu.1
    exact Eq.subst
      (motive := fun r : ℝ => r ≤ ‖t‖ / nr)
      hnorm_eq.symm
      hdiv_le
  have hmvt :
      ‖phase x - phase nr‖ ≤ (‖t‖ / nr) * ‖x - nr‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (s := Set.Icc nr x)
      (f := phase)
      (f' := derivPhase)
      (C := ‖t‖ / nr)
      hderiv
      hderiv_bound
      (convex_Icc nr x)
      hnr_mem
      hx_mem
  have hdist_eq : ‖x - nr‖ = x - nr := by
    have hsub_nonneg : 0 ≤ x - nr :=
      sub_nonneg.mpr hnr_le_x
    exact Eq.trans (Real.norm_eq_abs (x - nr)) (abs_of_nonneg hsub_nonneg)
  have hscale_nonneg : 0 ≤ ‖t‖ / nr :=
    div_nonneg (norm_nonneg t) (le_of_lt hnr_pos)
  have hmvt_unit : ‖phase x - phase nr‖ ≤ ‖t‖ / nr := by
    have hscaled :
        (‖t‖ / nr) * ‖x - nr‖ ≤ (‖t‖ / nr) * 1 := by
      exact mul_le_mul_of_nonneg_left
        (Eq.subst
          (motive := fun r : ℝ => r ≤ 1)
          hdist_eq.symm
          hx_sub_le_one)
        hscale_nonneg
    exact le_trans hmvt
      (Eq.subst
        (motive := fun r : ℝ => (‖t‖ / nr) * ‖x - nr‖ ≤ r)
        (mul_one (‖t‖ / nr))
        hscaled)
  have hx_phase :
      phase x = ((x : ℂ) ^ (-(t : ℂ) * Complex.I)) :=
    boundaryLineOnePointRealParam_logarithmicPhaseFunction_eq_cpow_of_pos
      t hx_pos
  have hn_phase :
      phase nr = ((nr : ℂ) ^ (-(t : ℂ) * Complex.I)) :=
    boundaryLineOnePointRealParam_logarithmicPhaseFunction_eq_cpow_of_pos
      t hnr_pos
  have htarget_eq :
      ((x : ℂ) ^ (-(t : ℂ) * Complex.I)) -
          ((nr : ℂ) ^ (-(t : ℂ) * Complex.I)) =
        phase x - phase nr := by
    exact congrArg₂ Sub.sub hx_phase.symm hn_phase.symm
  exact Eq.subst
    (motive := fun z : ℂ => ‖z‖ ≤ ‖t‖ / (((n : ℕ) : ℝ)))
    htarget_eq.symm
    hmvt_unit

/-- One-interval movement bound for the normalized derivative kernel after
separating reciprocal drift and phase drift. -/
theorem boundaryLineOnePointRealParam_oneInterval_normalizedKernel_movement_norm_le
    (t : ℝ)
    {n : ℕ}
    (hn : 0 < n)
    {x : ℝ}
    (hx : x ∈ Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ))) :
    ‖(((-(t : ℂ) * Complex.I) / (x : ℂ)) *
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
        (((-(t : ℂ) * Complex.I) / ((((n : ℕ) : ℝ) : ℂ))) *
          (((((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))‖ ≤
      ‖t‖ *
          ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))) *
            ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ +
        ‖t‖ *
          ‖(((n : ℕ) : ℝ) : ℂ)⁻¹‖ *
            (‖t‖ / (((n : ℕ) : ℝ))) := by
  let nr : ℝ := ((n : ℕ) : ℝ)
  have hsplit :
      ‖(((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
          (((-(t : ℂ) * Complex.I) / (nr : ℂ)) *
            (((nr : ℂ) ^ (-(t : ℂ) * Complex.I))))‖ ≤
        ‖(-(t : ℂ) * Complex.I)‖ *
            ‖(x : ℂ)⁻¹ - (nr : ℂ)⁻¹‖ *
              ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ +
          ‖(-(t : ℂ) * Complex.I)‖ *
            ‖(nr : ℂ)⁻¹‖ *
              ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                ((nr : ℂ) ^ (-(t : ℂ) * Complex.I))‖ :=
    boundaryLineOnePointRealParam_normalizedKernel_movement_norm_le_reciprocal_add_phase
      t x nr
  have ha_norm : ‖(-(t : ℂ) * Complex.I)‖ = ‖t‖ :=
    logarithmicPhaseFunction_derivative_numerator_norm t
  have hrecip :
      ‖(x : ℂ)⁻¹ - (nr : ℂ)⁻¹‖ ≤
        (1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ)) :=
    boundaryLineOnePointRealParam_oneInterval_reciprocal_movement_norm_le
      hn hx
  have hphase :
      ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
          ((nr : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
        ‖t‖ / (((n : ℕ) : ℝ)) :=
    boundaryLineOnePointRealParam_oneInterval_phase_drift_norm_le t hn hx
  have hphase_norm_nonneg :
      0 ≤ ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ :=
    norm_nonneg (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))
  have hfirst :
      ‖(-(t : ℂ) * Complex.I)‖ *
          ‖(x : ℂ)⁻¹ - (nr : ℂ)⁻¹‖ *
            ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
        ‖t‖ *
          ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))) *
            ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ := by
    have hmiddle :
        ‖t‖ * ‖(x : ℂ)⁻¹ - (nr : ℂ)⁻¹‖ ≤
          ‖t‖ * ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left hrecip (norm_nonneg t)
    have hproduct :
        ‖t‖ * ‖(x : ℂ)⁻¹ - (nr : ℂ)⁻¹‖ *
            ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
          ‖t‖ *
            ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))) *
              ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ :=
      mul_le_mul_of_nonneg_right hmiddle hphase_norm_nonneg
    exact Eq.subst
      (motive := fun r : ℝ =>
        r * ‖(x : ℂ)⁻¹ - (nr : ℂ)⁻¹‖ *
            ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
          ‖t‖ *
            ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))) *
              ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖)
      ha_norm.symm
      hproduct
  have hsecond :
      ‖(-(t : ℂ) * Complex.I)‖ *
          ‖(nr : ℂ)⁻¹‖ *
            ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
              ((nr : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
        ‖t‖ * ‖(((n : ℕ) : ℝ) : ℂ)⁻¹‖ *
          (‖t‖ / (((n : ℕ) : ℝ))) := by
    have hleft_nonneg : 0 ≤ ‖t‖ * ‖(nr : ℂ)⁻¹‖ :=
      mul_nonneg (norm_nonneg t) (norm_nonneg ((nr : ℂ)⁻¹))
    have hproduct :
        ‖t‖ * ‖(nr : ℂ)⁻¹‖ *
            ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
              ((nr : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
          ‖t‖ * ‖(nr : ℂ)⁻¹‖ *
            (‖t‖ / (((n : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left hphase hleft_nonneg
    exact Eq.subst
      (motive := fun r : ℝ =>
        r * ‖(nr : ℂ)⁻¹‖ *
            ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
              ((nr : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
          ‖t‖ * ‖(((n : ℕ) : ℝ) : ℂ)⁻¹‖ *
            (‖t‖ / (((n : ℕ) : ℝ))))
      ha_norm.symm
      hproduct
  exact le_trans hsplit (add_le_add hfirst hsecond)

/-- Pointwise one-interval bound after subtracting the left-endpoint
normalized kernel using the Bernoulli zero-mean cancellation. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_oneInterval_subtracted_normalizedKernel_pointwise_norm_le
    (t : ℝ)
    {n : ℕ}
    (hn : 0 < n)
    {x : ℝ}
    (hx : x ∈ Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ))) :
    ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        (((( -(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
          (((-(t : ℂ) * Complex.I) / ((((n : ℕ) : ℝ) : ℂ))) *
            (((((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))))‖ ≤
      ‖t‖ *
          ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))) *
            ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ +
        ‖t‖ *
          ‖(((n : ℕ) : ℝ) : ℂ)⁻¹‖ *
            (‖t‖ / (((n : ℕ) : ℝ))) := by
  let K : ℝ → ℂ := fun y =>
    (((-(t : ℂ) * Complex.I) / (y : ℂ)) *
      (((y : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
  have hbernoulli :
      ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (K x - K (((n : ℕ) : ℝ)))‖ ≤
        ‖K x - K (((n : ℕ) : ℝ))‖ :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_oneInterval_subtracted_pointwise_norm_le
      n K x
  have hmovement :
      ‖K x - K (((n : ℕ) : ℝ))‖ ≤
        ‖t‖ *
            ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))) *
              ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ +
          ‖t‖ *
            ‖(((n : ℕ) : ℝ) : ℂ)⁻¹‖ *
              (‖t‖ / (((n : ℕ) : ℝ))) :=
    boundaryLineOnePointRealParam_oneInterval_normalizedKernel_movement_norm_le
      t hn hx
  exact le_trans hbernoulli hmovement

/-- Unit norm of the positive-real logarithmic phase written in complex-power
notation. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_cpow_norm_eq_one_of_pos
    (t : ℝ)
    {x : ℝ}
    (hx : 0 < x) :
    ‖((x : ℂ) ^ (-(t : ℂ) * Complex.I))‖ = (1 : ℝ) := by
  have hphase :
      boundaryLineOnePointRealParam_logarithmicPhaseFunction t x =
        ((x : ℂ) ^ (-(t : ℂ) * Complex.I)) :=
    boundaryLineOnePointRealParam_logarithmicPhaseFunction_eq_cpow_of_pos
      t hx
  have hnorm :
      ‖boundaryLineOnePointRealParam_logarithmicPhaseFunction t x‖ =
        (1 : ℝ) :=
    boundaryLineOnePointRealParam_logarithmicPhaseFunction_norm t x
  exact Eq.trans (congrArg norm hphase.symm) hnorm

/-- Norm of the reciprocal of a positive real embedded in `ℂ`. -/
theorem boundaryLineOnePointRealParam_complex_inv_ofReal_norm_eq_inv
    {x : ℝ}
    (hx : 0 < x) :
    ‖((x : ℂ)⁻¹)‖ = x⁻¹ := by
  have hnorm_inv :
      ‖((x : ℂ)⁻¹)‖ = (‖(x : ℂ)‖)⁻¹ :=
    norm_inv (x : ℂ)
  have hnorm_real :
      ‖(x : ℂ)‖ = x := by
    exact Eq.trans (RCLike.norm_ofReal x) (abs_of_pos hx)
  exact Eq.trans hnorm_inv (congrArg Inv.inv hnorm_real)

/-- A point in the natural unit interval `(n,n+1]` is positive when its
left endpoint is positive. -/
theorem boundaryLineOnePointRealParam_oneInterval_point_pos
    {n : ℕ}
    (hn : 0 < n)
    {x : ℝ}
    (hx : x ∈ Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ))) :
    0 < x :=
  lt_trans (Nat.cast_pos.mpr hn) hx.1

/-- Normalization of the reciprocal-movement term by the unit norm of the
positive-real logarithmic phase. -/
theorem boundaryLineOnePointRealParam_reciprocalMovement_phaseNorm_normalization
    (t : ℝ)
    {n : ℕ}
    {x : ℝ}
    (hx : 0 < x) :
    ‖t‖ *
          ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))) *
          ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ =
      ‖t‖ *
        ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))) := by
  have hphaseNorm :
      ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ = (1 : ℝ) :=
    boundaryLineOnePointRealParam_logarithmicPhase_cpow_norm_eq_one_of_pos
      t hx
  have hreplacePhase :
      ‖t‖ *
            ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))) *
            ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ =
        ‖t‖ *
            ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))) *
            (1 : ℝ) :=
    congrArg
      (fun phaseNorm : ℝ =>
        ‖t‖ *
          ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))) *
          phaseNorm)
      hphaseNorm
  exact Eq.trans hreplacePhase
    (mul_one
      (‖t‖ *
        ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ)))))

/-- Normalization of the phase-movement coefficient by the norm of the
positive natural endpoint reciprocal. -/
theorem boundaryLineOnePointRealParam_phaseMovement_endpointInvNorm_normalization
    (t : ℝ)
    {n : ℕ}
    (hn : 0 < n) :
    ‖t‖ * ‖(((n : ℕ) : ℝ) : ℂ)⁻¹‖ *
          (‖t‖ / (((n : ℕ) : ℝ))) =
      ‖t‖ * (((n : ℕ) : ℝ)⁻¹) *
          (‖t‖ / (((n : ℕ) : ℝ))) := by
  have hendpointPos : 0 < ((n : ℕ) : ℝ) :=
    Nat.cast_pos.mpr hn
  have hinverseNorm :
      ‖((((n : ℕ) : ℝ) : ℂ)⁻¹)‖ = (((n : ℕ) : ℝ))⁻¹ :=
    boundaryLineOnePointRealParam_complex_inv_ofReal_norm_eq_inv
      hendpointPos
  exact congrArg
    (fun inverseNorm : ℝ =>
      ‖t‖ * inverseNorm * (‖t‖ / (((n : ℕ) : ℝ))))
    hinverseNorm

/-- The raw two-term movement majorant equals its scalar normal form on a
positive natural unit interval. -/
theorem boundaryLineOnePointRealParam_scalarMovement_majorant_normalization
    (t : ℝ)
    {n : ℕ}
    (hn : 0 < n)
    {x : ℝ}
    (hx : x ∈ Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ))) :
    ‖t‖ *
          ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))) *
          ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ +
        ‖t‖ * ‖(((n : ℕ) : ℝ) : ℂ)⁻¹‖ *
          (‖t‖ / (((n : ℕ) : ℝ))) =
      ‖t‖ *
          ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))) +
        ‖t‖ * (((n : ℕ) : ℝ)⁻¹) *
          (‖t‖ / (((n : ℕ) : ℝ))) := by
  have hxPos : 0 < x :=
    boundaryLineOnePointRealParam_oneInterval_point_pos hn hx
  have hreciprocalTerm :=
    boundaryLineOnePointRealParam_reciprocalMovement_phaseNorm_normalization
      t (n := n) (x := x) hxPos
  have hphaseTerm :=
    boundaryLineOnePointRealParam_phaseMovement_endpointInvNorm_normalization
      t hn
  exact congrArg₂ Add.add hreciprocalTerm hphaseTerm

/-- Simplified pointwise one-interval bound for the Bernoulli-subtracted
normalized kernel.

This is the absolute local movement estimate.  The later finite-defect theorem
still needs the genuine oscillatory summation/blocking upgrade; this lemma
only supplies the correct local integrand bound after the Bernoulli zero-mean
subtraction. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_oneInterval_subtracted_normalizedKernel_pointwise_norm_le_scalarMovement
    (t : ℝ)
    {n : ℕ}
    (hn : 0 < n)
    {x : ℝ}
    (hx : x ∈ Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ))) :
    ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        (((( -(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
          (((-(t : ℂ) * Complex.I) / ((((n : ℕ) : ℝ) : ℂ))) *
            (((((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))))‖ ≤
      ‖t‖ *
          ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))) +
        ‖t‖ *
            (((n : ℕ) : ℝ)⁻¹) *
            (‖t‖ / (((n : ℕ) : ℝ))) := by
  have hraw :
      ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((( -(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
            (((-(t : ℂ) * Complex.I) / ((((n : ℕ) : ℝ) : ℂ))) *
            (((((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))))‖ ≤
        ‖t‖ *
            ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))) *
              ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ +
          ‖t‖ *
            ‖(((n : ℕ) : ℝ) : ℂ)⁻¹‖ *
              (‖t‖ / (((n : ℕ) : ℝ))) :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_oneInterval_subtracted_normalizedKernel_pointwise_norm_le
      t hn hx
  have hright :
      ‖t‖ *
          ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))) *
            ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ +
        ‖t‖ *
          ‖(((n : ℕ) : ℝ) : ℂ)⁻¹‖ *
            (‖t‖ / (((n : ℕ) : ℝ))) =
      ‖t‖ *
          ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))) +
        ‖t‖ *
          (((n : ℕ) : ℝ)⁻¹) *
            (‖t‖ / (((n : ℕ) : ℝ))) :=
    boundaryLineOnePointRealParam_scalarMovement_majorant_normalization
      t hn hx
  exact Eq.subst
    (motive := fun r : ℝ =>
      ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((( -(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
            (((-(t : ℂ) * Complex.I) / ((((n : ℕ) : ℝ) : ℂ))) *
              (((((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))))‖ ≤ r)
    hright
    hraw

/-- One-interval integral domination for the Bernoulli-subtracted normalized
kernel by the scalar movement majorant. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_oneInterval_subtracted_normalizedKernel_integral_norm_le_scalarMovement
    (t : ℝ)
    {n : ℕ}
    (hn : 0 < n) :
    ‖∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((( -(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
            (((-(t : ℂ) * Complex.I) / ((((n : ℕ) : ℝ) : ℂ))) *
              (((((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))))‖ ≤
      ∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)),
        (‖t‖ *
            ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))) +
          ‖t‖ *
            (((n : ℕ) : ℝ)⁻¹) *
              (‖t‖ / (((n : ℕ) : ℝ)))) := by
  let s : Set ℝ := Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ))
  let f : ℝ → ℂ := fun x =>
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
      (((( -(t : ℂ) * Complex.I) / (x : ℂ)) *
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
        (((-(t : ℂ) * Complex.I) / ((((n : ℕ) : ℝ) : ℂ))) *
          (((((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))))
  let G : ℝ :=
    ‖t‖ *
        ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))) +
      ‖t‖ *
        (((n : ℕ) : ℝ)⁻¹) *
          (‖t‖ / (((n : ℕ) : ℝ)))
  let g : ℝ → ℝ := fun _x => G
  have hle :
      (((n : ℕ) : ℝ)) ≤ (((n + 1 : ℕ) : ℝ)) :=
    Nat.cast_le.mpr (Nat.le_succ n)
  have hg :
      Integrable g (volume.restrict s) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp
      (intervalIntegrable_const (μ := volume) (a := (((n : ℕ) : ℝ)))
        (b := (((n + 1 : ℕ) : ℝ))) (c := G))
  have hbound :
      ∀ᵐ x ∂volume.restrict s, ‖f x‖ ≤ g x :=
    (ae_restrict_mem measurableSet_Ioc).mono
      (fun x hx =>
        boundaryLineOnePointRealParam_firstPeriodicBernoulli_oneInterval_subtracted_normalizedKernel_pointwise_norm_le_scalarMovement
          t hn hx)
  exact norm_integral_le_of_norm_le hg hbound

/-- Every index in the post-cutoff open-right interval is positive. -/
theorem boundaryLineOnePointRealParam_postCutoff_Ioc_index_pos
    (t : ℝ)
    {M n : ℕ}
    (hn : n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M) :
    0 < n := by
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_cutoff_pos t
  have hcutoff_lt_n : ⌊2 + ‖t‖⌋₊ < n :=
    (Finset.mem_Ioc.mp hn).1
  exact lt_trans hcutoff_pos hcutoff_lt_n

/-- Finite summation of the one-interval scalar movement bounds over the
post-cutoff interval.

This is the finite accumulation theorem produced directly by the one-interval
movement and Bernoulli cancellation lemmas.  The remaining hard step for the
visible selected endpoint/variation theorem is the oscillatory blocking
upgrade from this absolute scalar movement sum to the required
`4 * sqrt (1 + |t|) * log (2 + M)` finite-defect bound. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_postCutoff_subtracted_normalizedKernel_sum_integral_norm_le_scalarMovementSum
    (t : ℝ)
    {M : ℕ} :
    (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
      ‖∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((( -(t : ℂ) * Complex.I) / (x : ℂ)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
              (((-(t : ℂ) * Complex.I) / ((((n : ℕ) : ℝ) : ℂ))) *
                (((((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))))‖) ≤
      ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)),
          (‖t‖ *
              ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))) +
            ‖t‖ *
              (((n : ℕ) : ℝ)⁻¹) *
                (‖t‖ / (((n : ℕ) : ℝ)))) := by
  exact
    Finset.sum_le_sum
      (fun n hn =>
        boundaryLineOnePointRealParam_firstPeriodicBernoulli_oneInterval_subtracted_normalizedKernel_integral_norm_le_scalarMovement
          t
          (boundaryLineOnePointRealParam_postCutoff_Ioc_index_pos t hn))

/-- Right-endpoint indexed form of the one-interval Bernoulli cancellation
movement estimate.

The global post-cutoff remainder is naturally indexed by right endpoints
`n ∈ (C,M]`; the contributing unit interval is therefore based at `n - 1`.
This is the local estimate in exactly that indexing. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_rightEndpointInterval_subtracted_normalizedKernel_integral_norm_le_scalarMovement
    (t : ℝ)
    {M n : ℕ}
    (hn : n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M) :
    ‖∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n - 1 + 1 : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
            (((-(t : ℂ) * Complex.I) /
                (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I))))))‖ ≤
      ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n - 1 + 1 : ℕ) : ℝ)),
        (‖t‖ *
            ((1 : ℝ) /
              (((((n - 1 : ℕ) : ℕ) : ℝ)) *
                ((((n - 1 : ℕ) : ℕ) : ℝ)))) +
          ‖t‖ *
            (((((n - 1 : ℕ) : ℕ) : ℝ))⁻¹) *
              (‖t‖ / (((((n - 1 : ℕ) : ℕ) : ℝ))))) := by
  let m : ℕ := n - 1
  have hcutoff_lt_n : ⌊2 + ‖t‖⌋₊ < n :=
    (Finset.mem_Ioc.mp hn).1
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_cutoff_pos t
  have hone_lt_n : 1 < n :=
    lt_of_le_of_lt (Nat.succ_le_of_lt hcutoff_pos) hcutoff_lt_n
  have hm_pos : 0 < m :=
    Nat.sub_pos_of_lt hone_lt_n
  exact
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_oneInterval_subtracted_normalizedKernel_integral_norm_le_scalarMovement
      t hm_pos

/-- Right-endpoint indexed local estimate over the literal interval `(n-1,n]`.

This is only the endpoint arithmetic transport of
`boundaryLineOnePointRealParam_firstPeriodicBernoulli_rightEndpointInterval_subtracted_normalizedKernel_integral_norm_le_scalarMovement`;
it keeps the finite-block cancellation statement aligned with the global
post-cutoff interval decomposition. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_Ioc_pred_self_subtracted_normalizedKernel_integral_norm_le_scalarMovement
    (t : ℝ)
    {M n : ℕ}
    (hn : n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M) :
    ‖∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
            (((-(t : ℂ) * Complex.I) /
                (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I))))))‖ ≤
      ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        (‖t‖ *
            ((1 : ℝ) /
              (((((n - 1 : ℕ) : ℕ) : ℝ)) *
                ((((n - 1 : ℕ) : ℕ) : ℝ)))) +
          ‖t‖ *
            (((((n - 1 : ℕ) : ℕ) : ℝ))⁻¹) *
              (‖t‖ / (((((n - 1 : ℕ) : ℕ) : ℝ))))) := by
  have hcutoff_lt_n : ⌊2 + ‖t‖⌋₊ < n :=
    (Finset.mem_Ioc.mp hn).1
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_cutoff_pos t
  have hn_pos : 0 < n :=
    lt_trans hcutoff_pos hcutoff_lt_n
  have hsucc : n - 1 + 1 = n :=
    Nat.sub_add_cancel hn_pos
  exact
    Eq.subst
      (motive := fun q : ℕ =>
        ‖∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((q : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                  (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
                (((-(t : ℂ) * Complex.I) /
                    (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                    (-(t : ℂ) * Complex.I))))))‖ ≤
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((q : ℕ) : ℝ)),
            (‖t‖ *
                ((1 : ℝ) /
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) *
                    ((((n - 1 : ℕ) : ℕ) : ℝ)))) +
              ‖t‖ *
                (((((n - 1 : ℕ) : ℕ) : ℝ))⁻¹) *
                  (‖t‖ / (((((n - 1 : ℕ) : ℕ) : ℝ))))))
      hsucc
      (boundaryLineOnePointRealParam_firstPeriodicBernoulli_rightEndpointInterval_subtracted_normalizedKernel_integral_norm_le_scalarMovement
        t hn)

/-- Finite summation of the right-endpoint indexed local Bernoulli cancellation
movement estimates.

This is the source-level finite block estimate immediately upstream of the
normalized Bernoulli block-cancellation theorem. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_postCutoff_rightEndpointInterval_subtracted_normalizedKernel_sum_integral_norm_le_scalarMovementSum
    (t : ℝ)
    {M : ℕ} :
    (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
      ‖∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n - 1 + 1 : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
              (((-(t : ℂ) * Complex.I) /
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))))))‖) ≤
      ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n - 1 + 1 : ℕ) : ℝ)),
          (‖t‖ *
              ((1 : ℝ) /
                (((((n - 1 : ℕ) : ℕ) : ℝ)) *
                  ((((n - 1 : ℕ) : ℕ) : ℝ)))) +
            ‖t‖ *
              (((((n - 1 : ℕ) : ℕ) : ℝ))⁻¹) *
                (‖t‖ / (((((n - 1 : ℕ) : ℕ) : ℝ))))) := by
  exact
    Finset.sum_le_sum
      (fun n hn =>
        boundaryLineOnePointRealParam_firstPeriodicBernoulli_rightEndpointInterval_subtracted_normalizedKernel_integral_norm_le_scalarMovement
          t hn)

/-- Finite summation of the literal `(n-1,n]` right-endpoint local cancellation
estimates.

This is the block-local norm estimate in the same indexing as the post-cutoff
Euler-Maclaurin finite defect. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_postCutoff_Ioc_pred_self_subtracted_normalizedKernel_sum_integral_norm_le_scalarMovementSum
    (t : ℝ)
    {M : ℕ} :
    (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
      ‖∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
              (((-(t : ℂ) * Complex.I) /
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))))))‖) ≤
      ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          (‖t‖ *
              ((1 : ℝ) /
                (((((n - 1 : ℕ) : ℕ) : ℝ)) *
                  ((((n - 1 : ℕ) : ℕ) : ℝ)))) +
            ‖t‖ *
              (((((n - 1 : ℕ) : ℕ) : ℝ))⁻¹) *
                (‖t‖ / (((((n - 1 : ℕ) : ℕ) : ℝ))))) := by
  exact
    Finset.sum_le_sum
      (fun n hn =>
        boundaryLineOnePointRealParam_firstPeriodicBernoulli_Ioc_pred_self_subtracted_normalizedKernel_integral_norm_le_scalarMovement
          t hn)

/-- Norm bound for the finite sum of right-endpoint local Bernoulli
cancellation blocks.

This is the assembled finite local-movement estimate.  It is the last purely
absolute estimate before the genuinely oscillatory block-cancellation
absorption needed for the `2 * sqrt (1 + |t|) * log (2 + M)` remainder bound. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_postCutoff_Ioc_pred_self_subtracted_normalizedKernel_sum_norm_le_scalarMovementSum
    (t : ℝ)
    {M : ℕ} :
    ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
              ((-(t : ℂ) * Complex.I) /
                (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ) *
                  (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                    (-(t : ℂ) * Complex.I))))‖ ≤
      ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          (‖t‖ *
              ((1 : ℝ) /
                (((((n - 1 : ℕ) : ℕ) : ℝ)) *
                  ((((n - 1 : ℕ) : ℕ) : ℝ)))) +
            ‖t‖ *
              (((((n - 1 : ℕ) : ℕ) : ℝ))⁻¹) *
                (‖t‖ / (((((n - 1 : ℕ) : ℕ) : ℝ))))) := by
  let F : ℕ → ℂ := fun n =>
    ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
          (((-(t : ℂ) * Complex.I) /
              (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I))))))
  let G : ℕ → ℝ := fun n =>
    ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
      (‖t‖ *
          ((1 : ℝ) /
            (((((n - 1 : ℕ) : ℕ) : ℝ)) *
              ((((n - 1 : ℕ) : ℕ) : ℝ)))) +
        ‖t‖ *
          (((((n - 1 : ℕ) : ℕ) : ℝ))⁻¹) *
            (‖t‖ / (((((n - 1 : ℕ) : ℕ) : ℝ)))))
  have htriangle :
      ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, F n‖ ≤
        ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, ‖F n‖ :=
    norm_sum_le (Finset.Ioc ⌊2 + ‖t‖⌋₊ M) F
  have hlocal :
      (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, ‖F n‖) ≤
        ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, G n :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_postCutoff_Ioc_pred_self_subtracted_normalizedKernel_sum_integral_norm_le_scalarMovementSum
      t
  exact le_trans htriangle hlocal

/-- Natural right-endpoint unit intervals `(n-1,n]` are pairwise disjoint.

This is the measure-theoretic owner input needed to assemble the local
Bernoulli zero-mean blocks into the global post-cutoff remainder integral. -/
theorem boundaryGrowth_pairwiseDisjoint_Ioc_pred_self_natCast :
    Pairwise
      (Disjoint on
        (fun n : ℕ =>
          Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)))) := by
  have hmono : Monotone (fun n : ℕ => ((n : ℕ) : ℝ)) :=
    fun _ _ hle => Nat.cast_le.mpr hle
  exact hmono.pairwise_disjoint_on_Ioc_pred

/-- Finite-subset form of the disjointness of natural right-endpoint unit
intervals. -/
theorem boundaryGrowth_pairwiseDisjoint_finset_Ioc_pred_self_natCast
    (s : Finset ℕ) :
    Set.Pairwise (↑s : Set ℕ)
      (Disjoint on
        (fun n : ℕ =>
          Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)))) := by
  intro i _hi j _hj hij
  exact boundaryGrowth_pairwiseDisjoint_Ioc_pred_self_natCast hij

/-- Finite set-integral decomposition over natural right-endpoint unit
intervals.

This is the measure-theoretic assembly lemma needed to replace the global
post-cutoff Bernoulli remainder integral by the finite sum of local
zero-mean blocks. -/
theorem boundaryGrowth_integral_finset_biUnion_Ioc_pred_self_natCast
    (s : Finset ℕ)
    (f : ℝ → ℂ)
    (hf :
      ∀ n ∈ s,
        IntegrableOn f
          (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)))
          volume) :
    (∫ x in ⋃ n ∈ s,
        Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)), f x) =
      ∑ n ∈ s,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)), f x := by
  exact
    integral_finset_biUnion
      s
      (fun n _hn => measurableSet_Ioc)
      (boundaryGrowth_pairwiseDisjoint_finset_Ioc_pred_self_natCast s)
      hf

/-- Membership in the natural right-endpoint interval `(n-1,n]` is equivalent
to having natural ceiling `n`. -/
theorem boundaryGrowth_mem_Ioc_pred_self_iff_natCeil_eq
    {n : ℕ}
    (hn : n ≠ 0)
    (x : ℝ) :
    x ∈ Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)) ↔
      Nat.ceil x = n := by
  have hpre :
      (Nat.ceil : ℝ → ℕ) ⁻¹' {n} =
        Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)) :=
    Nat.preimage_ceil_of_ne_zero hn
  have hmem :
      x ∈ (Nat.ceil : ℝ → ℕ) ⁻¹' {n} ↔
        x ∈ Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)) :=
    Iff.of_eq (congrArg (fun s : Set ℝ => x ∈ s) hpre)
  exact Iff.intro
    (fun hx =>
      have hx_pre :
          x ∈ (Nat.ceil : ℝ → ℕ) ⁻¹' {n} :=
        hmem.mpr hx
      Set.mem_singleton_iff.mp hx_pre)
    (fun hx =>
      hmem.mp
        (Set.mem_singleton_iff.mpr hx))

/-- The finite union of natural right-endpoint intervals over `(C,M]` covers
exactly the real interval `(C,M]`. -/
theorem boundaryGrowth_biUnion_Ioc_pred_self_natCast_eq_Ioc
    (C M : ℕ) :
    (Set.iUnion fun n : ℕ =>
      Set.iUnion fun _hn : n ∈ Finset.Ioc C M =>
        Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ))) =
      Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)) := by
  exact Set.ext
    (fun x =>
      Iff.intro
        (fun hx =>
          let hx_index : ∃ n : ℕ,
              x ∈ Set.iUnion fun _hn : n ∈ Finset.Ioc C M =>
                Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)) :=
            Set.mem_iUnion.mp hx
          Exists.elim hx_index
            (fun n hx_block =>
              let hx_membership : ∃ hn_mem : n ∈ Finset.Ioc C M,
                  x ∈ Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)) :=
                Set.mem_iUnion.mp hx_block
              Exists.elim hx_membership
                (fun hn_mem hx_interval =>
              have hC_lt_n : C < n :=
                (Finset.mem_Ioc.mp hn_mem).1
              have hn_le_M : n ≤ M :=
                (Finset.mem_Ioc.mp hn_mem).2
              have hC_le_pred : C ≤ n - 1 :=
                Nat.le_sub_one_of_lt hC_lt_n
              have hC_real_le_pred :
                  (((C : ℕ) : ℝ)) ≤ ((((n - 1 : ℕ) : ℕ) : ℝ)) :=
                Nat.cast_le.mpr hC_le_pred
              have hleft :
                  (((C : ℕ) : ℝ)) < x :=
                lt_of_le_of_lt hC_real_le_pred hx_interval.1
              have hright :
                  x ≤ (((M : ℕ) : ℝ)) :=
                le_trans hx_interval.2 (Nat.cast_le.mpr hn_le_M)
              ⟨hleft, hright⟩)))
        (fun hx =>
          let n : ℕ := Nat.ceil x
          have hn_eq : Nat.ceil x = n := rfl
          have hC_lt_n : C < n := by
            exact Nat.lt_ceil.mpr hx.1
          have hn_le_M : n ≤ M := by
            exact Nat.ceil_le.mpr hx.2
          have hn_ne_zero : n ≠ 0 :=
            ne_of_gt (lt_of_le_of_lt (Nat.zero_le C) hC_lt_n)
          have hx_interval :
              x ∈ Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)) :=
            (boundaryGrowth_mem_Ioc_pred_self_iff_natCeil_eq hn_ne_zero x).mpr
              hn_eq
          Set.mem_iUnion.mpr
            ⟨n, Set.mem_iUnion.mpr
              ⟨Finset.mem_Ioc.mpr ⟨hC_lt_n, hn_le_M⟩, hx_interval⟩⟩))

/-- Exact finite-block decomposition of the global normalized Bernoulli
remainder into right-endpoint local zero-mean blocks, assuming the concrete
local integrability facts needed by the Bochner subtraction identity.

The remaining owner task after this lemma is to discharge these integrability
facts for the normalized kernel and then apply the oscillatory block estimate
to the displayed finite sum. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_integral_eq_sum_Ioc_pred_self_subtracted_of_integrable
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hBK :
      ∀ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        Integrable
          (fun x : ℝ =>
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))
          (volume.restrict
            (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)))))
    (hBc :
      ∀ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        Integrable
          (fun x : ℝ =>
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              ((-(t : ℂ) * Complex.I /
                (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))))
          (volume.restrict
            (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ))))) :
    (∫ x in Set.Ioc
        (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
        (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
      ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
              (((-(t : ℂ) * Complex.I) /
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I)))))) := by
  let C : ℕ := ⌊2 + ‖t‖⌋₊
  let f : ℝ → ℂ := fun x =>
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
      (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
        (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
  let K : ℝ → ℂ := fun x =>
    (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
      (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
  have hcover :
      (⋃ n ∈ (↑(Finset.Ioc C M) : Set ℕ),
          Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ))) =
        Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)) :=
    boundaryGrowth_biUnion_Ioc_pred_self_natCast_eq_Ioc C M
  have hdomain :
      (∫ x in Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)), f x) =
        ∫ x in ⋃ n ∈ (↑(Finset.Ioc C M) : Set ℕ),
          Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)), f x :=
    congrArg
      (fun s : Set ℝ => ∫ x in s, f x)
      hcover.symm
  have hsplit :
      (∫ x in ⋃ n ∈ (↑(Finset.Ioc C M) : Set ℕ),
          Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)), f x) =
        ∑ n ∈ Finset.Ioc C M,
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)), f x :=
    boundaryGrowth_integral_finset_biUnion_Ioc_pred_self_natCast
      (Finset.Ioc C M) f
      (fun n hn => hBK n hn)
  have hlocal :
      (∑ n ∈ Finset.Ioc C M,
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)), f x) =
        ∑ n ∈ Finset.Ioc C M,
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (K x - K (((((n - 1 : ℕ) : ℕ) : ℝ)))) := by
    exact Finset.sum_congr rfl
      (fun n hn =>
        have hC_lt_n : C < n :=
          (Finset.mem_Ioc.mp hn).1
        have hcutoff_pos : 0 < C :=
          boundaryLineOnePointRealParam_cutoff_pos t
        have hn_pos : 0 < n :=
          lt_trans hcutoff_pos hC_lt_n
        have hsucc : n - 1 + 1 = n :=
          Nat.sub_add_cancel hn_pos
        have hBK_local :
            Integrable
              (fun x : ℝ =>
                ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * K x)
              (volume.restrict
                (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ))
                  ((((n - 1 + 1 : ℕ) : ℕ) : ℝ)))) :=
          Eq.subst
            (motive := fun q : ℕ =>
              Integrable
                (fun x : ℝ =>
                  ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * K x)
                (volume.restrict
                  (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ))
                    ((((q : ℕ) : ℕ) : ℝ)))))
            hsucc.symm
            (hBK n hn)
        have hBc_local :
            Integrable
              (fun x : ℝ =>
                ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                  K (((n - 1 : ℕ) : ℝ)))
              (volume.restrict
                (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ))
                  ((((n - 1 + 1 : ℕ) : ℕ) : ℝ)))) :=
          Eq.subst
            (motive := fun q : ℕ =>
              Integrable
                (fun x : ℝ =>
                  ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                    K (((n - 1 : ℕ) : ℝ)))
                (volume.restrict
                  (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ))
                    ((((q : ℕ) : ℕ) : ℝ)))))
            hsucc.symm
            (hBc n hn)
        have hraw :
            (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ))
                ((((n - 1 + 1 : ℕ) : ℕ) : ℝ)),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * K x) =
              (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ))
                ((((n - 1 + 1 : ℕ) : ℕ) : ℝ)),
                ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                  (K x - K (((((n - 1 : ℕ) : ℕ) : ℝ))))) :=
          boundaryLineOnePointRealParam_firstPeriodicBernoulli_oneInterval_subtract_leftEndpoint
            (n - 1)
            K
            hBK_local
            hBc_local
        Eq.subst
          (motive := fun q : ℕ =>
            (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((q : ℕ) : ℝ)),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * K x) =
              (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((q : ℕ) : ℝ)),
                ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                  (K x - K (((((n - 1 : ℕ) : ℕ) : ℝ))))))
          hsucc
          hraw)
  calc
    (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        ∫ x in Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)), f x := rfl
    _ = ∫ x in ⋃ n ∈ (↑(Finset.Ioc C M) : Set ℕ),
          Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)), f x :=
      hdomain
    _ = ∑ n ∈ Finset.Ioc C M,
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)), f x :=
      hsplit
    _ = ∑ n ∈ Finset.Ioc C M,
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (K x - K (((((n - 1 : ℕ) : ℕ) : ℝ)))) :=
      hlocal
    _ = ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                  (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
                (((-(t : ℂ) * Complex.I) /
                    (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                    (-(t : ℂ) * Complex.I)))))) := rfl

/-- Norm consequence of the global-to-local zero-mean block decomposition.

This is the exact bridge from the normalized Bernoulli remainder to the finite
sum of local scalar movement controls.  The remaining cancellation task is to
absorb that finite local expression into the sharper
`2 * sqrt (1 + |t|) * log (2 + M)` bound. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_integral_norm_le_scalarMovementSum_of_integrable
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hBK :
      ∀ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        Integrable
          (fun x : ℝ =>
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))
          (volume.restrict
            (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)))))
    (hBc :
      ∀ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        Integrable
          (fun x : ℝ =>
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((-(t : ℂ) * Complex.I) /
                (((n - 1 : ℕ) : ℝ) : ℂ)) *
                ((((n - 1 : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))) )
          (volume.restrict
            (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ))))) :
    ‖∫ x in Set.Ioc
        (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
        (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
      ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          (‖t‖ *
              ((1 : ℝ) /
                (((((n - 1 : ℕ) : ℕ) : ℝ)) *
                  ((((n - 1 : ℕ) : ℕ) : ℝ)))) +
            ‖t‖ *
              (((((n - 1 : ℕ) : ℕ) : ℝ))⁻¹) *
                (‖t‖ / (((((n - 1 : ℕ) : ℕ) : ℝ))))) := by
  have hdecomp :
      (∫ x in Set.Ioc
          (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
          (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                  (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
                (((-(t : ℂ) * Complex.I) /
                    (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                    (-(t : ℂ) * Complex.I)))))) :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_integral_eq_sum_Ioc_pred_self_subtracted_of_integrable
      t hM hBK hBc
  have hsum :
      ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                  (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
                (((-(t : ℂ) * Complex.I) /
                    (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                    (-(t : ℂ) * Complex.I))))))‖ ≤
        ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            (‖t‖ *
                ((1 : ℝ) /
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) *
                    ((((n - 1 : ℕ) : ℕ) : ℝ)))) +
              ‖t‖ *
                (((((n - 1 : ℕ) : ℕ) : ℝ))⁻¹) *
                  (‖t‖ / (((((n - 1 : ℕ) : ℕ) : ℝ))))) :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_postCutoff_Ioc_pred_self_subtracted_normalizedKernel_sum_norm_le_scalarMovementSum
      t
  exact Eq.subst
    (motive := fun z : ℂ =>
      ‖z‖ ≤
        ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            (‖t‖ *
                ((1 : ℝ) /
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) *
                    ((((n - 1 : ℕ) : ℕ) : ℝ)))) +
              ‖t‖ *
                (((((n - 1 : ℕ) : ℕ) : ℝ))⁻¹) *
                  (‖t‖ / (((((n - 1 : ℕ) : ℕ) : ℝ))))))
    hdecomp.symm
    hsum

/-- Local integrability of the constant left-endpoint normalized kernel after
multiplication by the first periodic Bernoulli factor.

This discharges the constant half of the local zero-mean subtraction
integrability requirements in the global block decomposition. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_Ioc_pred_self_leftEndpoint_normalizedKernel_integrable
    (t : ℝ)
    {M n : ℕ}
    (hn : n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M) :
    Integrable
      (fun x : ℝ =>
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((-(t : ℂ) * Complex.I) /
              (((n - 1 : ℕ) : ℝ) : ℂ)) *
            ((((n - 1 : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I))))
      (volume.restrict
        (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)))) := by
  let c : ℂ :=
    ((-(t : ℂ) * Complex.I) /
        (((n - 1 : ℕ) : ℝ) : ℂ)) *
      ((((n - 1 : ℕ) : ℝ) : ℂ) ^
        (-(t : ℂ) * Complex.I))
  have hle :
      ((((n - 1 : ℕ) : ℕ) : ℝ)) ≤ (((n : ℕ) : ℝ)) := by
    exact Nat.cast_le.mpr (Nat.sub_le n 1)
  have hc_integrable :
      IntegrableOn
        (fun constantArgument : ℝ => c)
        (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)))
        volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp
      (intervalIntegrable_const
        (μ := volume)
        (a := ((((n - 1 : ℕ) : ℕ) : ℝ)))
        (b := (((n : ℕ) : ℝ)))
        (c := c))
  have hmul :
      IntegrableOn
        (fun x : ℝ =>
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * c)
        (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)))
        volume :=
    eulerMaclaurin_bernoulli_mul_integrableOn_Ioc
      (fun constantArgument : ℝ => c)
      ((((n - 1 : ℕ) : ℕ) : ℝ))
      (((n : ℕ) : ℝ))
      hc_integrable
  change
    IntegrableOn
      (fun x : ℝ =>
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * c)
      (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)))
      volume
  exact hmul

/-- Local integrability of the nonconstant normalized logarithmic-phase kernel
on one post-cutoff unit block. -/
theorem boundaryLineOnePointRealParam_Ioc_pred_self_normalizedKernel_integrable
    (t : ℝ)
    {M n : ℕ}
    (hn : n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M) :
    Integrable
      (fun x : ℝ =>
        (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))
      (volume.restrict
        (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)))) := by
  have hC_lt_n : ⌊2 + ‖t‖⌋₊ < n :=
    (Finset.mem_Ioc.mp hn).1
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_cutoff_pos t
  have hone_le_cutoff : 1 ≤ ⌊2 + ‖t‖⌋₊ :=
    Nat.succ_le_of_lt hcutoff_pos
  have hone_lt_n : 1 < n :=
    lt_of_le_of_lt hone_le_cutoff hC_lt_n
  have hn_pred_pos : 0 < n - 1 :=
    Nat.sub_pos_of_lt hone_lt_n
  have hle :
      ((((n - 1 : ℕ) : ℕ) : ℝ)) ≤ (((n : ℕ) : ℝ)) :=
    Nat.cast_le.mpr (Nat.sub_le n 1)
  have hcont_cpow :
      ContinuousOn
        (fun x : ℝ => (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
        (Set.Icc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ))) := by
    intro x hx
    have hx_pos : 0 < x :=
      lt_of_lt_of_le (Nat.cast_pos.mpr hn_pred_pos) hx.1
    exact
      (Complex.continuousAt_ofReal_cpow_const x (-(t : ℂ) * Complex.I)
        (Or.inr (ne_of_gt hx_pos))).continuousWithinAt
  have hcont_inv :
      ContinuousOn
        (fun x : ℝ => (x : ℂ)⁻¹)
        (Set.Icc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ))) := by
    intro x hx
    have hx_pos : 0 < x :=
      lt_of_lt_of_le (Nat.cast_pos.mpr hn_pred_pos) hx.1
    exact
      (Complex.continuous_ofReal.continuousAt.inv₀
        (by
          exact Complex.ofReal_ne_zero.mpr (ne_of_gt hx_pos))).continuousWithinAt
  have hconst_mul_inv :
      ContinuousOn
        (fun x : ℝ => (-(t : ℂ) * Complex.I) * (x : ℂ)⁻¹)
        (Set.Icc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ))) :=
    continuousOn_const.mul hcont_inv
  have hdiv_eq :
      (fun x : ℝ => (-(t : ℂ) * Complex.I) / (x : ℂ)) =
        (fun x : ℝ => (-(t : ℂ) * Complex.I) * (x : ℂ)⁻¹) := by
    funext x
    exact div_eq_mul_inv (-(t : ℂ) * Complex.I) (x : ℂ)
  have hcont_kernel :
      ContinuousOn
        (fun x : ℝ =>
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))
        (Set.Icc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ))) := by
    exact
      Eq.subst
        (motive := fun φ : ℝ → ℂ =>
          ContinuousOn
            (fun x : ℝ =>
              φ x * (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
            (Set.Icc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ))))
        hdiv_eq.symm
        (hconst_mul_inv.mul hcont_cpow)
  have hinterval :
      IntervalIntegrable
        (fun x : ℝ =>
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))
        volume
        ((((n - 1 : ℕ) : ℕ) : ℝ))
        (((n : ℕ) : ℝ)) :=
    hcont_kernel.intervalIntegrable_of_Icc hle
  exact
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp hinterval

/-- Local integrability of the nonconstant normalized logarithmic-phase kernel
after multiplication by the first periodic Bernoulli factor. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_Ioc_pred_self_normalizedKernel_integrable
    (t : ℝ)
    {M n : ℕ}
    (hn : n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M) :
    Integrable
      (fun x : ℝ =>
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))
      (volume.restrict
        (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)))) := by
  have hkernel :
      IntegrableOn
        (fun x : ℝ =>
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))
        (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)))
        volume :=
    boundaryLineOnePointRealParam_Ioc_pred_self_normalizedKernel_integrable
      t hn
  exact
    eulerMaclaurin_bernoulli_mul_integrableOn_Ioc
      (fun x : ℝ =>
        (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))
      ((((n - 1 : ℕ) : ℕ) : ℝ))
      (((n : ℕ) : ℝ))
      hkernel

/-- Exact finite-block decomposition of the global normalized Bernoulli
remainder into right-endpoint local zero-mean blocks, with the concrete local
normalized-kernel integrability facts discharged. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_integral_eq_sum_Ioc_pred_self_subtracted
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (∫ x in Set.Ioc
        (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
        (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
      ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
              (((-(t : ℂ) * Complex.I) /
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I)))))) := by
  exact
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_integral_eq_sum_Ioc_pred_self_subtracted_of_integrable
      t
      hM
      (fun n hn =>
        boundaryLineOnePointRealParam_firstPeriodicBernoulli_Ioc_pred_self_normalizedKernel_integrable
          t hn)
      (fun n hn =>
        boundaryLineOnePointRealParam_firstPeriodicBernoulli_Ioc_pred_self_leftEndpoint_normalizedKernel_integrable
          t hn)

/-- Norm form of the exact global-to-local oscillatory block decomposition for
the normalized Bernoulli remainder.

This keeps the cancellation problem on the finite complex block sum, before
passing to any absolute scalar movement envelope. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_integral_norm_eq_sum_Ioc_pred_self_subtracted_norm
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc
        (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
        (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ =
      ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
              (((-(t : ℂ) * Complex.I) /
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))))))‖ := by
  exact
    congrArg
      (fun z : ℂ => ‖z‖)
      (boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_integral_eq_sum_Ioc_pred_self_subtracted
        t hM)

/-- The normalized Bernoulli remainder cancellation estimate follows from the
corresponding finite oscillatory block-sum estimate.

This is the precise bridge from the true finite block cancellation theorem to
the selected endpoint/variation package. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_integral_norm_le_of_finiteOscillatoryBlockSum
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hblocks :
      ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
              (((-(t : ℂ) * Complex.I) /
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))))))‖ ≤
        2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M)) :
    ‖∫ x in Set.Ioc
        (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
        (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
      2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact
    Eq.subst
      (motive := fun r : ℝ =>
        r ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M))
      (boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_integral_norm_eq_sum_Ioc_pred_self_subtracted_norm
        t hM).symm
      hblocks

/-- The canonical post-cutoff scale dominates the unit bound used by the
summable reciprocal-drift part of the finite block decomposition. -/
theorem boundaryLineOnePointRealParam_one_le_two_sqrt_one_add_norm_mul_log_two_add_postCutoff
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (1 : ℝ) ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt (1 + ‖t‖) := by
    have hone_le_one_add_norm : (1 : ℝ) ≤ 1 + ‖t‖ :=
      le_add_of_nonneg_right (norm_nonneg t)
    exact Real.one_le_sqrt.mpr hone_le_one_add_norm
  have hM_ge_one_add_norm :
      (1 : ℝ) + ‖t‖ ≤ (M : ℝ) :=
    le_trans
      (boundaryLineOnePointRealParam_postCutoff_one_add_norm_le_cutoff t)
      (Nat.cast_le.mpr hM)
  have harg_le :
      2 + ‖t‖ ≤ (2 : ℝ) + M := by
    have hone_add_one :
        (1 : ℝ) + 1 = 2 :=
      one_add_one_eq_two
    have htwo_add_norm :
        2 + ‖t‖ = 1 + (1 + ‖t‖) := by
      calc
        2 + ‖t‖ = ((1 : ℝ) + 1) + ‖t‖ := by
          exact congrArg (fun x : ℝ => x + ‖t‖) hone_add_one.symm
        _ = 1 + (1 + ‖t‖) := by
          exact add_assoc (1 : ℝ) 1 ‖t‖
    calc
      2 + ‖t‖ = 1 + (1 + ‖t‖) :=
        htwo_add_norm
      _ ≤ 1 + (M : ℝ) :=
        add_le_add_left hM_ge_one_add_norm 1
      _ ≤ 2 + (M : ℝ) :=
        add_le_add_right (show (1 : ℝ) ≤ 2 from one_le_two) (M : ℝ)
  have hlog_lower_norm : (1 : ℝ) ≤ Real.log (2 + ‖t‖) :=
    one_le_log_two_add_norm_of_one_le_norm ht
  have hlog_lower_M : (1 : ℝ) ≤ Real.log (2 + M) := by
    have harg_pos : 0 < 2 + ‖t‖ := by
      exact lt_of_lt_of_le zero_lt_two
        (le_add_of_nonneg_right (norm_nonneg t))
    have hlog_le :
        Real.log (2 + ‖t‖) ≤ Real.log (2 + M) :=
      Real.log_le_log harg_pos harg_le
    exact le_trans hlog_lower_norm hlog_le
  have hproduct_ge_one :
      (1 : ℝ) ≤ Real.sqrt (1 + ‖t‖) * Real.log (2 + M) :=
    calc
      (1 : ℝ) = 1 * 1 := (one_mul 1).symm
      _ ≤ Real.sqrt (1 + ‖t‖) * Real.log (2 + M) :=
        mul_le_mul hsqrt_ge_one hlog_lower_M zero_le_one
          (le_trans zero_le_one hsqrt_ge_one)
  calc
    (1 : ℝ) ≤ Real.sqrt (1 + ‖t‖) * Real.log (2 + M) :=
      hproduct_ge_one
    _ ≤ 2 * (Real.sqrt (1 + ‖t‖) * Real.log (2 + M)) :=
      le_mul_of_one_le_left
        (mul_nonneg (Real.sqrt_nonneg (1 + ‖t‖))
          (le_trans (show (0 : ℝ) ≤ 1 from zero_le_one) hlog_lower_M))
        (show (1 : ℝ) ≤ 2 from one_le_two)
    _ = 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) :=
      (mul_assoc 2 (Real.sqrt (1 + ‖t‖)) (Real.log (2 + M))).symm

/-- The canonical post-cutoff scale itself dominates the unit reciprocal-drift
bound. -/
theorem boundaryLineOnePointRealParam_one_le_sqrt_one_add_norm_mul_log_two_add_postCutoff
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (1 : ℝ) ≤ Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt (1 + ‖t‖) := by
    have hone_le_one_add_norm : (1 : ℝ) ≤ 1 + ‖t‖ :=
      le_add_of_nonneg_right (norm_nonneg t)
    exact Real.one_le_sqrt.mpr hone_le_one_add_norm
  have hM_ge_one_add_norm :
      (1 : ℝ) + ‖t‖ ≤ (M : ℝ) :=
    le_trans
      (boundaryLineOnePointRealParam_postCutoff_one_add_norm_le_cutoff t)
      (Nat.cast_le.mpr hM)
  have harg_le :
      2 + ‖t‖ ≤ (2 : ℝ) + M := by
    have hone_add_one :
        (1 : ℝ) + 1 = 2 :=
      one_add_one_eq_two
    have htwo_add_norm :
        2 + ‖t‖ = 1 + (1 + ‖t‖) := by
      calc
        2 + ‖t‖ = ((1 : ℝ) + 1) + ‖t‖ := by
          exact congrArg (fun x : ℝ => x + ‖t‖) hone_add_one.symm
        _ = 1 + (1 + ‖t‖) := by
          exact add_assoc (1 : ℝ) 1 ‖t‖
    calc
      2 + ‖t‖ = 1 + (1 + ‖t‖) :=
        htwo_add_norm
      _ ≤ 1 + (M : ℝ) :=
        add_le_add_left hM_ge_one_add_norm 1
      _ ≤ 2 + (M : ℝ) :=
        add_le_add_right (show (1 : ℝ) ≤ 2 from one_le_two) (M : ℝ)
  have hlog_lower_norm : (1 : ℝ) ≤ Real.log (2 + ‖t‖) :=
    one_le_log_two_add_norm_of_one_le_norm ht
  have hlog_lower_M : (1 : ℝ) ≤ Real.log (2 + M) := by
    have harg_pos : 0 < 2 + ‖t‖ := by
      exact lt_of_lt_of_le zero_lt_two
        (le_add_of_nonneg_right (norm_nonneg t))
    have hlog_le :
        Real.log (2 + ‖t‖) ≤ Real.log (2 + M) :=
      Real.log_le_log harg_pos harg_le
    exact le_trans hlog_lower_norm hlog_le
  calc
    (1 : ℝ) = 1 * 1 := (one_mul 1).symm
    _ ≤ Real.sqrt (1 + ‖t‖) * Real.log (2 + M) :=
      mul_le_mul hsqrt_ge_one hlog_lower_M zero_le_one
        (le_trans zero_le_one hsqrt_ge_one)


end
end LFunctions
end Boundary
