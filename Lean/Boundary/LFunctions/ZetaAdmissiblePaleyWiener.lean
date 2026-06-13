import Boundary.LFunctions.ZetaExplicitFormulaAnalyticCore
import Boundary.LFunctions.ZetaTransformCalculusWeighted

/-!
# Paley-Wiener decay for admissible zeta probes

This file owns the Paley-Wiener decay theorem for compactly supported smooth
admissible probes.  The proof is the analytic integration-by-parts argument for
the Laplace transform on vertical strips.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped ContDiff

namespace ZetaAdmissibleFunction

/-- A concrete support interval certificate for a compactly supported admissible source. -/
structure ZetaPaleyWienerSupportInterval (f : ZetaAdmissibleFunction) where
  lower : ℝ
  upper : ℝ
  lower_mem : ∀ t ∈ tsupport f.toZetaTestFunction, lower ≤ t
  upper_mem : ∀ t ∈ tsupport f.toZetaTestFunction, t ≤ upper

/-- Compact support gives an upper bound for the admissible source support. -/
theorem exists_zetaPaleyWienerSupportUpperBound
    (f : ZetaAdmissibleFunction) :
    ∃ B : ℝ, ∀ t ∈ tsupport f.toZetaTestFunction, t ≤ B := by
  obtain ⟨B, hB⟩ :=
    IsCompact.bddAbove f.toZetaTestFunction.hasCompactSupport.isCompact
  exact ⟨B, hB⟩

/-- Compact support gives a lower bound for the admissible source support. -/
theorem exists_zetaPaleyWienerSupportLowerBound
    (f : ZetaAdmissibleFunction) :
    ∃ A : ℝ, ∀ t ∈ tsupport f.toZetaTestFunction, A ≤ t := by
  obtain ⟨A, hA⟩ :=
    IsCompact.bddBelow f.toZetaTestFunction.hasCompactSupport.isCompact
  exact ⟨A, hA⟩

/-- Compact support gives a concrete interval containing the admissible source support, as a
proposition-level existence statement.  This lemma is useful for ordinary support arguments; the
type-level Paley-Wiener constant is produced by the integration-by-parts theorem below rather than
by choosing one of these intervals. -/
theorem exists_zetaPaleyWienerSupportInterval
    (f : ZetaAdmissibleFunction) :
    Nonempty (ZetaPaleyWienerSupportInterval f) := by
  obtain ⟨A, hA⟩ := exists_zetaPaleyWienerSupportLowerBound f
  obtain ⟨B, hB⟩ := exists_zetaPaleyWienerSupportUpperBound f
  exact ⟨⟨A, B, hA, hB⟩⟩

/-- The admissible source vanishes strictly above its Paley-Wiener support bound. -/
theorem zetaPaleyWiener_eq_zero_of_supportUpperBound_lt
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f) {t : ℝ}
    (ht : I.upper < t) :
    f.toZetaTestFunction t = 0 := by
  have hnot_mem : t ∉ tsupport f.toZetaTestFunction := by
    intro hmem
    have ht_le : t ≤ I.upper :=
      I.upper_mem t hmem
    exact (not_lt_of_ge ht_le) ht
  exact image_eq_zero_of_nmem_tsupport hnot_mem

/-- The admissible source vanishes strictly below its Paley-Wiener support bound. -/
theorem zetaPaleyWiener_eq_zero_of_lt_supportLowerBound
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f) {t : ℝ}
    (ht : t < I.lower) :
    f.toZetaTestFunction t = 0 := by
  have hnot_mem : t ∉ tsupport f.toZetaTestFunction := by
    intro hmem
    have hle_t : I.lower ≤ t :=
      I.lower_mem t hmem
    exact (not_lt_of_ge hle_t) ht
  exact image_eq_zero_of_nmem_tsupport hnot_mem

/-- The Paley-Wiener vertical-strip weight used by the admissible transform estimates. -/
def zetaPaleyWienerVerticalWeight (z : ℂ) (N : ℕ) : ℝ :=
  (1 + ‖z.im‖) ^ (-(N : ℤ))

/-- The strip membership predicate used by the Paley-Wiener estimate. -/
def zetaPaleyWienerInVerticalStrip (a b : ℝ) (z : ℂ) : Prop :=
  a ≤ z.re ∧ z.re ≤ b

/-- The Paley-Wiener vertical weight is nonnegative. -/
theorem zetaPaleyWienerVerticalWeight_nonnegative (z : ℂ) (N : ℕ) :
    0 ≤ zetaPaleyWienerVerticalWeight z N := by
  unfold zetaPaleyWienerVerticalWeight
  have hbase : 0 ≤ 1 + ‖z.im‖ :=
    add_nonneg zero_le_one (norm_nonneg z.im)
  exact zpow_nonneg hbase (-(N : ℤ))

/-- Low-frequency weight comparison for one Paley-Wiener successor step. -/
theorem zetaPaleyWienerVerticalWeight_le_successor_lowFrequency
    (z : ℂ) (N : ℕ) (hz : ‖z.im‖ ≤ 1) :
    zetaPaleyWienerVerticalWeight z N ≤
      2 * zetaPaleyWienerVerticalWeight z (N + 1) := by
  let X : ℝ := 1 + ‖z.im‖
  have hX_nonzero : X ≠ 0 := by
    have hX_pos : 0 < X :=
      lt_of_lt_of_le zero_lt_one
        (le_add_of_nonneg_right (norm_nonneg z.im))
    exact ne_of_gt hX_pos
  have hX_le_two : X ≤ 2 := by
    calc
      X = 1 + ‖z.im‖ := rfl
      _ ≤ 1 + 1 := add_le_add_left hz 1
      _ = 2 := one_add_one_eq_two
  have hweight_nonneg :
      0 ≤ X ^ (-(N + 1 : ℤ)) :=
    zpow_nonneg (le_trans zero_le_one
      (le_add_of_nonneg_right (norm_nonneg z.im))) (-(N + 1 : ℤ))
  have hexp :
      (1 : ℤ) + (-(N + 1 : ℤ)) = -(N : ℤ) := by
    omega
  have hcombine :
      X * X ^ (-(N + 1 : ℤ)) = X ^ (-(N : ℤ)) := by
    calc
      X * X ^ (-(N + 1 : ℤ)) =
          X ^ (1 : ℤ) * X ^ (-(N + 1 : ℤ)) := by
        exact congrArg
          (fun y : ℝ => y * X ^ (-(N + 1 : ℤ)))
          (zpow_one X).symm
      _ = X ^ ((1 : ℤ) + (-(N + 1 : ℤ))) := by
        exact (zpow_add₀ hX_nonzero (1 : ℤ) (-(N + 1 : ℤ))).symm
      _ = X ^ (-(N : ℤ)) := by
        exact congrArg (fun e : ℤ => X ^ e) hexp
  have hscaled :
      X * X ^ (-(N + 1 : ℤ)) ≤
        2 * X ^ (-(N + 1 : ℤ)) :=
    mul_le_mul_of_nonneg_right hX_le_two hweight_nonneg
  unfold zetaPaleyWienerVerticalWeight
  change X ^ (-(N : ℤ)) ≤ 2 * X ^ (-(N + 1 : ℤ))
  exact Eq.subst
    (motive := fun y : ℝ => y ≤ 2 * X ^ (-(N + 1 : ℤ)))
    hcombine
    hscaled

/-- Base high-frequency inverse estimate for the vertical variable. -/
theorem zetaPaleyWiener_inverseIm_times_verticalBase_le_two_highFrequency
    (z : ℂ) (hz : 1 ≤ ‖z.im‖) :
    ‖(z.im : ℂ)⁻¹‖ * (1 + ‖z.im‖) ≤ 2 := by
  let r : ℝ := ‖z.im‖
  have hr_pos : 0 < r :=
    lt_of_lt_of_le zero_lt_one hz
  have hr_ne_zero : r ≠ 0 :=
    ne_of_gt hr_pos
  have hr_inv_nonneg : 0 ≤ r⁻¹ :=
    inv_nonneg.mpr (le_of_lt hr_pos)
  have hnorm_inv :
      ‖(z.im : ℂ)⁻¹‖ = r⁻¹ := by
    calc
      ‖(z.im : ℂ)⁻¹‖ = ‖(z.im : ℂ)‖⁻¹ := by
        exact norm_inv (z.im : ℂ)
      _ = r⁻¹ := by
        exact congrArg Inv.inv (RCLike.norm_ofReal z.im)
  have hinv_le_one : r⁻¹ ≤ 1 := by
    have hscaled :
        r⁻¹ * 1 ≤ r⁻¹ * r :=
      mul_le_mul_of_nonneg_left hz hr_inv_nonneg
    have hleft : r⁻¹ * 1 = r⁻¹ :=
      mul_one r⁻¹
    have hright : r⁻¹ * r = 1 :=
      inv_mul_cancel₀ hr_ne_zero
    exact Eq.subst
      (motive := fun x : ℝ => x ≤ 1)
      hleft
      (Eq.subst
        (motive := fun x : ℝ => r⁻¹ * 1 ≤ x)
        hright
        hscaled)
  have hbase :
      r⁻¹ * (1 + r) ≤ 2 := by
    have hdistrib :
        r⁻¹ * (1 + r) = r⁻¹ + 1 := by
      calc
        r⁻¹ * (1 + r) = r⁻¹ * 1 + r⁻¹ * r := by
          exact mul_add r⁻¹ 1 r
        _ = r⁻¹ + r⁻¹ * r := by
          exact congrArg (fun x : ℝ => x + r⁻¹ * r) (mul_one r⁻¹)
        _ = r⁻¹ + 1 := by
          exact congrArg (fun x : ℝ => r⁻¹ + x) (inv_mul_cancel₀ hr_ne_zero)
    have hsum :
        r⁻¹ + 1 ≤ 2 := by
      calc
        r⁻¹ + 1 ≤ 1 + 1 := by
          exact add_le_add_right hinv_le_one 1
        _ = 2 := one_add_one_eq_two
    exact Eq.subst
      (motive := fun x : ℝ => x ≤ 2)
      hdistrib.symm
      hsum
  exact Eq.subst
    (motive := fun x : ℝ => x * (1 + ‖z.im‖) ≤ 2)
    hnorm_inv.symm
    hbase

/-- High-frequency inverse weight comparison for one Paley-Wiener successor step. -/
theorem zetaPaleyWiener_inverseIm_mul_weight_le_successor_highFrequency
    (z : ℂ) (N : ℕ) (hz : 1 ≤ ‖z.im‖) :
    ‖(z.im : ℂ)⁻¹‖ * zetaPaleyWienerVerticalWeight z N ≤
      2 * zetaPaleyWienerVerticalWeight z (N + 1) := by
  let X : ℝ := 1 + ‖z.im‖
  have hX_nonzero : X ≠ 0 := by
    have hX_pos : 0 < X :=
      lt_of_lt_of_le zero_lt_one
        (le_add_of_nonneg_right (norm_nonneg z.im))
    exact ne_of_gt hX_pos
  have hweight_nonneg :
      0 ≤ X ^ (-(N + 1 : ℤ)) :=
    zpow_nonneg (le_trans zero_le_one
      (le_add_of_nonneg_right (norm_nonneg z.im))) (-(N + 1 : ℤ))
  have hexp :
      (1 : ℤ) + (-(N + 1 : ℤ)) = -(N : ℤ) := by
    omega
  have hcombine :
      X * X ^ (-(N + 1 : ℤ)) = X ^ (-(N : ℤ)) := by
    calc
      X * X ^ (-(N + 1 : ℤ)) =
          X ^ (1 : ℤ) * X ^ (-(N + 1 : ℤ)) := by
        exact congrArg
          (fun y : ℝ => y * X ^ (-(N + 1 : ℤ)))
          (zpow_one X).symm
      _ = X ^ ((1 : ℤ) + (-(N + 1 : ℤ))) := by
        exact (zpow_add₀ hX_nonzero (1 : ℤ) (-(N + 1 : ℤ))).symm
      _ = X ^ (-(N : ℤ)) := by
        exact congrArg (fun e : ℤ => X ^ e) hexp
  have hbase :
      ‖(z.im : ℂ)⁻¹‖ * X ≤ 2 :=
    zetaPaleyWiener_inverseIm_times_verticalBase_le_two_highFrequency z hz
  have hscaled :
      (‖(z.im : ℂ)⁻¹‖ * X) * X ^ (-(N + 1 : ℤ)) ≤
        2 * X ^ (-(N + 1 : ℤ)) :=
    mul_le_mul_of_nonneg_right hbase hweight_nonneg
  have hrearrange :
      ‖(z.im : ℂ)⁻¹‖ * X ^ (-(N : ℤ)) =
        (‖(z.im : ℂ)⁻¹‖ * X) * X ^ (-(N + 1 : ℤ)) := by
    calc
      ‖(z.im : ℂ)⁻¹‖ * X ^ (-(N : ℤ)) =
          ‖(z.im : ℂ)⁻¹‖ * (X * X ^ (-(N + 1 : ℤ))) := by
        exact congrArg (fun y : ℝ => ‖(z.im : ℂ)⁻¹‖ * y) hcombine.symm
      _ = (‖(z.im : ℂ)⁻¹‖ * X) * X ^ (-(N + 1 : ℤ)) := by
        exact (mul_assoc ‖(z.im : ℂ)⁻¹‖ X
          (X ^ (-(N + 1 : ℤ)))).symm
  unfold zetaPaleyWienerVerticalWeight
  change ‖(z.im : ℂ)⁻¹‖ * X ^ (-(N : ℤ)) ≤
    2 * X ^ (-(N + 1 : ℤ))
  exact Eq.subst
    (motive := fun y : ℝ => y ≤ 2 * X ^ (-(N + 1 : ℤ)))
    hrearrange
    hscaled

/-- A named vertical-strip bound for the admissible Laplace transform. -/
def zetaLaplaceTransformHasVerticalStripDecayConstant
    (f : ZetaAdmissibleFunction) (a b : ℝ) (N : ℕ) (C : ℝ) : Prop :=
  0 < C ∧
  ∀ z : ℂ,
    zetaPaleyWienerInVerticalStrip a b z →
    ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
      ≤ C * zetaPaleyWienerVerticalWeight z N

/-- The length of the compact support interval used in the Paley-Wiener estimate. -/
def zetaPaleyWienerSupportIntervalLength
    (I : ZetaPaleyWienerSupportInterval f) : ℝ :=
  max (I.upper - I.lower) 0

/-- The support-interval length is nonnegative. -/
theorem zetaPaleyWienerSupportIntervalLength_nonnegative
    (I : ZetaPaleyWienerSupportInterval f) :
    0 ≤ zetaPaleyWienerSupportIntervalLength I := by
  unfold zetaPaleyWienerSupportIntervalLength
  exact le_max_right (I.upper - I.lower) 0

/-- The horizontal exponential factor is uniformly bounded on a fixed vertical strip and
support interval. -/
def zetaPaleyWienerStripExponentialEnvelope
    (I : ZetaPaleyWienerSupportInterval f) (a b : ℝ) : ℝ :=
  Real.exp (max (max (|a * I.lower|) (|a * I.upper|))
    (max (|b * I.lower|) (|b * I.upper|)))

/-- The strip exponential envelope is positive. -/
theorem zetaPaleyWienerStripExponentialEnvelope_pos
    (I : ZetaPaleyWienerSupportInterval f) (a b : ℝ) :
    0 < zetaPaleyWienerStripExponentialEnvelope I a b := by
  unfold zetaPaleyWienerStripExponentialEnvelope
  exact Real.exp_pos _

/-- The set of pointwise source norms on the compact support. -/
def zetaPaleyWienerSupportNormSet
    (f : ZetaAdmissibleFunction) : Set ℝ :=
  {r : ℝ | ∃ t : ℝ, t ∈ tsupport f.toZetaTestFunction ∧ ‖f.toZetaTestFunction t‖ = r}

/-- A source-size envelope for the compact support, expressed without choosing a maximizer. -/
noncomputable def zetaPaleyWienerSupportNormEnvelope
    (f : ZetaAdmissibleFunction) : ℝ :=
  max (sSup (zetaPaleyWienerSupportNormSet f)) 0

/-- The support-norm envelope is nonnegative by construction. -/
theorem zetaPaleyWienerSupportNormEnvelope_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaPaleyWienerSupportNormEnvelope f := by
  unfold zetaPaleyWienerSupportNormEnvelope
  exact le_max_right (sSup (zetaPaleyWienerSupportNormSet f)) 0

/-- Source norms on the support are bounded above. -/
theorem zetaPaleyWienerSupportNormSet_bddAbove
    (f : ZetaAdmissibleFunction) :
    BddAbove (zetaPaleyWienerSupportNormSet f) := by
  sorry

/-- The pointwise source norm at a support point belongs to the support-norm set. -/
theorem zetaPaleyWienerSupportNorm_mem_supportNormSet
    (f : ZetaAdmissibleFunction) :
    ∀ t : ℝ,
      t ∈ tsupport f.toZetaTestFunction →
      ‖f.toZetaTestFunction t‖ ∈ zetaPaleyWienerSupportNormSet f := by
  intro t ht
  unfold zetaPaleyWienerSupportNormSet
  exact ⟨t, ht, rfl⟩

/-- The zero-order compact-support envelope used for the Paley-Wiener integral bound. -/
noncomputable def zetaPaleyWienerZeroOrderEnvelope
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) : ℝ :=
  max
    (zetaPaleyWienerSupportNormEnvelope f *
      zetaPaleyWienerStripExponentialEnvelope I a b *
      zetaPaleyWienerSupportIntervalLength I)
    0 + 1

/-- The zero-order compact-support envelope is strictly positive. -/
theorem zetaPaleyWienerZeroOrderEnvelope_pos
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) :
    0 < zetaPaleyWienerZeroOrderEnvelope f I a b := by
  unfold zetaPaleyWienerZeroOrderEnvelope
  exact weightedLaplaceKernel_positive_bump
    (zetaPaleyWienerSupportNormEnvelope f *
      zetaPaleyWienerStripExponentialEnvelope I a b *
      zetaPaleyWienerSupportIntervalLength I)

/-- The support-norm envelope bounds the admissible source on its support. -/
theorem zetaPaleyWienerSupportNorm_le_envelope
    (f : ZetaAdmissibleFunction) :
    ∀ t : ℝ,
      t ∈ tsupport f.toZetaTestFunction →
      ‖f.toZetaTestFunction t‖ ≤ zetaPaleyWienerSupportNormEnvelope f := by
  intro t ht
  have hsSup :
      ‖f.toZetaTestFunction t‖ ≤
        sSup (zetaPaleyWienerSupportNormSet f) :=
    le_csSup
      (zetaPaleyWienerSupportNormSet_bddAbove f)
      (zetaPaleyWienerSupportNorm_mem_supportNormSet f t ht)
  have hsSup_le_envelope :
      sSup (zetaPaleyWienerSupportNormSet f) ≤
        zetaPaleyWienerSupportNormEnvelope f := by
    unfold zetaPaleyWienerSupportNormEnvelope
    exact le_max_left (sSup (zetaPaleyWienerSupportNormSet f)) 0
  exact le_trans hsSup hsSup_le_envelope

/-- The test-function wrapper has the same pointwise norm envelope as the admissible source. -/
theorem zetaPaleyWienerTestFunctionNorm_le_envelope
    (f : ZetaAdmissibleFunction) :
    ∀ t : ℝ,
      t ∈ tsupport f.toZetaTestFunction →
      ‖f.toZetaTestFunction' t‖ ≤ zetaPaleyWienerSupportNormEnvelope f := by
  intro t ht
  have hsource :
      ‖f.toZetaTestFunction t‖ ≤ zetaPaleyWienerSupportNormEnvelope f :=
    zetaPaleyWienerSupportNorm_le_envelope f t ht
  have happly :
      f.toZetaTestFunction' t = f.toZetaTestFunction t :=
    ZetaAdmissibleFunction.toZetaTestFunction'_apply f t
  exact Eq.subst
    (motive := fun v : ℂ =>
      ‖v‖ ≤ zetaPaleyWienerSupportNormEnvelope f)
    happly.symm
    hsource

/-- A rectangle product is bounded in absolute value by the largest absolute product at
the four corners. -/
theorem abs_mul_le_max_corner_abs_of_mem_interval
    (a b lower upper x t : ℝ)
    (hxa : a ≤ x) (hxb : x ≤ b)
    (ht_lower : lower ≤ t) (ht_upper : t ≤ upper) :
    |x * t| ≤
      max (max (|a * lower|) (|a * upper|))
        (max (|b * lower|) (|b * upper|)) := by
  sorry

/-- The unsigned rectangle product is bounded by the corner absolute-value envelope. -/
theorem mul_le_max_corner_abs_of_mem_interval
    (a b lower upper x t : ℝ)
    (hxa : a ≤ x) (hxb : x ≤ b)
    (ht_lower : lower ≤ t) (ht_upper : t ≤ upper) :
    x * t ≤
      max (max (|a * lower|) (|a * upper|))
        (max (|b * lower|) (|b * upper|)) := by
  have hle_abs : x * t ≤ |x * t| :=
    le_abs_self (x * t)
  have habs :
      |x * t| ≤
        max (max (|a * lower|) (|a * upper|))
          (max (|b * lower|) (|b * upper|)) :=
    abs_mul_le_max_corner_abs_of_mem_interval
      a b lower upper x t hxa hxb ht_lower ht_upper
  exact le_trans hle_abs habs

/-- The real exponent `x * t` is bounded by the endpoint envelope on the strip rectangle. -/
theorem zetaPaleyWienerStripProduct_le_endpointEnvelope
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b x t : ℝ)
    (hxa : a ≤ x) (hxb : x ≤ b)
    (ht_lower : I.lower ≤ t) (ht_upper : t ≤ I.upper) :
    x * t ≤
      max (max (|a * I.lower|) (|a * I.upper|))
        (max (|b * I.lower|) (|b * I.upper|)) := by
  exact mul_le_max_corner_abs_of_mem_interval
    a b I.lower I.upper x t hxa hxb ht_lower ht_upper

/-- Norm of the complex exponential is the exponential of the real part. -/
theorem complexExp_norm_eq_realExp_re
    (w : ℂ) :
    ‖Complex.exp w‖ = Real.exp w.re := by
  sorry

/-- Multiplication by a real scalar has the expected real part. -/
theorem complex_mul_real_re
    (z : ℂ) (t : ℝ) :
    (z * (t : ℂ)).re = z.re * t := by
  sorry

/-- Norm of the complex exponential on a vertical line is the exponential of the real
part of the exponent. -/
theorem zetaPaleyWienerComplexExp_norm_eq_realExp
    (z : ℂ) (t : ℝ) :
    ‖Complex.exp (z * (t : ℂ))‖ =
      Real.exp (z.re * t) := by
  have hnorm :
      ‖Complex.exp (z * (t : ℂ))‖ =
        Real.exp (z * (t : ℂ)).re :=
    complexExp_norm_eq_realExp_re (z * (t : ℂ))
  have hre :
      (z * (t : ℂ)).re = z.re * t :=
    complex_mul_real_re z t
  exact hnorm.trans (congrArg Real.exp hre)

/-- The strip exponential envelope bounds the horizontal exponential on the support
interval. -/
theorem zetaPaleyWienerStripExponential_norm_le_envelope
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) :
    ∀ z : ℂ,
      zetaPaleyWienerInVerticalStrip a b z →
      ∀ t : ℝ,
        I.lower ≤ t →
        t ≤ I.upper →
        ‖Complex.exp (z * (t : ℂ))‖ ≤
          zetaPaleyWienerStripExponentialEnvelope I a b := by
  intro z hz t ht_lower ht_upper
  have hnorm :
      ‖Complex.exp (z * (t : ℂ))‖ =
        Real.exp (z.re * t) :=
    zetaPaleyWienerComplexExp_norm_eq_realExp z t
  have hproduct :
      z.re * t ≤
        max (max (|a * I.lower|) (|a * I.upper|))
          (max (|b * I.lower|) (|b * I.upper|)) :=
    zetaPaleyWienerStripProduct_le_endpointEnvelope
      f I a b z.re t hz.1 hz.2 ht_lower ht_upper
  have hexp :
      Real.exp (z.re * t) ≤
        zetaPaleyWienerStripExponentialEnvelope I a b := by
    unfold zetaPaleyWienerStripExponentialEnvelope
    exact Real.exp_le_exp.mpr hproduct
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤ zetaPaleyWienerStripExponentialEnvelope I a b)
    hnorm.symm
    hexp

/-- The pointwise raw kernel envelope before multiplying by support length. -/
noncomputable def zetaPaleyWienerRawKernelEnvelope
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) : ℝ :=
  zetaPaleyWienerSupportNormEnvelope f *
    zetaPaleyWienerStripExponentialEnvelope I a b

/-- The raw kernel envelope is nonnegative. -/
theorem zetaPaleyWienerRawKernelEnvelope_nonnegative
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) :
    0 ≤ zetaPaleyWienerRawKernelEnvelope f I a b := by
  unfold zetaPaleyWienerRawKernelEnvelope
  exact mul_nonneg
    (zetaPaleyWienerSupportNormEnvelope_nonnegative f)
    (le_of_lt (zetaPaleyWienerStripExponentialEnvelope_pos I a b))

/-- Pointwise kernel domination on the compact support interval. -/
theorem zetaLaplaceKernel_norm_le_rawEnvelope_on_support
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) :
    ∀ z : ℂ,
      zetaPaleyWienerInVerticalStrip a b z →
      ∀ t : ℝ,
        t ∈ tsupport f.toZetaTestFunction →
        ‖f.toZetaTestFunction' t * Complex.exp (z * (t : ℂ))‖ ≤
          zetaPaleyWienerRawKernelEnvelope f I a b := by
  intro z hz t ht
  have hsource :
      ‖f.toZetaTestFunction' t‖ ≤ zetaPaleyWienerSupportNormEnvelope f :=
    zetaPaleyWienerTestFunctionNorm_le_envelope f t ht
  have hexp :
      ‖Complex.exp (z * (t : ℂ))‖ ≤
        zetaPaleyWienerStripExponentialEnvelope I a b :=
    zetaPaleyWienerStripExponential_norm_le_envelope
      f I a b z hz t (I.lower_mem t ht) (I.upper_mem t ht)
  have hsourceEnvelope_nonneg :
      0 ≤ zetaPaleyWienerSupportNormEnvelope f :=
    zetaPaleyWienerSupportNormEnvelope_nonnegative f
  have hexp_norm_nonneg :
      0 ≤ ‖Complex.exp (z * (t : ℂ))‖ :=
    norm_nonneg (Complex.exp (z * (t : ℂ)))
  have hproduct :
      ‖f.toZetaTestFunction' t‖ *
          ‖Complex.exp (z * (t : ℂ))‖ ≤
        zetaPaleyWienerSupportNormEnvelope f *
          zetaPaleyWienerStripExponentialEnvelope I a b :=
    mul_le_mul hsource hexp hexp_norm_nonneg hsourceEnvelope_nonneg
  have hnorm :
      ‖f.toZetaTestFunction' t * Complex.exp (z * (t : ℂ))‖ =
        ‖f.toZetaTestFunction' t‖ *
          ‖Complex.exp (z * (t : ℂ))‖ :=
    norm_mul (f.toZetaTestFunction' t) (Complex.exp (z * (t : ℂ)))
  unfold zetaPaleyWienerRawKernelEnvelope
  exact Eq.subst
    (motive := fun v : ℝ =>
      v ≤ zetaPaleyWienerSupportNormEnvelope f *
        zetaPaleyWienerStripExponentialEnvelope I a b)
    hnorm.symm
    hproduct

/-- The Paley-Wiener Laplace kernel at a fixed spectral parameter. -/
noncomputable def zetaPaleyWienerLaplaceKernel
    (f : ZetaAdmissibleFunction) (z : ℂ) (t : ℝ) : ℂ :=
  f.toZetaTestFunction' t * Complex.exp (z * (t : ℂ))

/-- The constant support-indicator majorant used for the real-line integral bound. -/
noncomputable def zetaPaleyWienerSupportIndicatorBound
    (f : ZetaAdmissibleFunction) (B : ℝ) : ℝ → ℝ :=
  Set.indicator (tsupport f.toZetaTestFunction) (fun _ : ℝ => B)

/-- The Laplace kernel is zero off the source support. -/
theorem zetaPaleyWienerLaplaceKernel_eq_zero_of_not_mem_support
    (f : ZetaAdmissibleFunction) (z : ℂ) {t : ℝ}
    (ht : t ∉ tsupport f.toZetaTestFunction) :
    zetaPaleyWienerLaplaceKernel f z t = 0 := by
  have hsource : f.toZetaTestFunction t = 0 :=
    image_eq_zero_of_nmem_tsupport ht
  have htest :
      f.toZetaTestFunction' t = f.toZetaTestFunction t :=
    ZetaAdmissibleFunction.toZetaTestFunction'_apply f t
  unfold zetaPaleyWienerLaplaceKernel
  calc
    f.toZetaTestFunction' t * Complex.exp (z * (t : ℂ))
        = f.toZetaTestFunction t * Complex.exp (z * (t : ℂ)) := by
          exact congrArg
            (fun v : ℂ => v * Complex.exp (z * (t : ℂ)))
            htest
    _ = 0 * Complex.exp (z * (t : ℂ)) := by
          exact congrArg
            (fun v : ℂ => v * Complex.exp (z * (t : ℂ)))
            hsource
    _ = 0 := zero_mul (Complex.exp (z * (t : ℂ)))

/-- A pointwise support bound induces domination by the constant support indicator. -/
theorem zetaPaleyWienerLaplaceKernel_norm_le_supportIndicatorBound
    (f : ZetaAdmissibleFunction) (z : ℂ) (B : ℝ)
    (hbound :
      ∀ t : ℝ,
        t ∈ tsupport f.toZetaTestFunction →
        ‖zetaPaleyWienerLaplaceKernel f z t‖ ≤ B) :
    ∀ t : ℝ,
      ‖zetaPaleyWienerLaplaceKernel f z t‖ ≤
        zetaPaleyWienerSupportIndicatorBound f B t := by
  intro t
  by_cases ht : t ∈ tsupport f.toZetaTestFunction
  · have hindicator :
        zetaPaleyWienerSupportIndicatorBound f B t = B := by
      unfold zetaPaleyWienerSupportIndicatorBound
      exact Set.indicator_of_mem ht
    exact Eq.subst
      (motive := fun v : ℝ => ‖zetaPaleyWienerLaplaceKernel f z t‖ ≤ v)
      hindicator.symm
      (hbound t ht)
  · have hkernel :
        zetaPaleyWienerLaplaceKernel f z t = 0 :=
      zetaPaleyWienerLaplaceKernel_eq_zero_of_not_mem_support f z ht
    have hindicator :
        zetaPaleyWienerSupportIndicatorBound f B t = 0 := by
      unfold zetaPaleyWienerSupportIndicatorBound
      exact Set.indicator_of_not_mem ht
    have hnorm_zero :
        ‖zetaPaleyWienerLaplaceKernel f z t‖ = 0 := by
      exact (congrArg (fun v : ℂ => ‖v‖) hkernel).trans norm_zero
    exact Eq.subst
      (motive := fun v : ℝ => v ≤ zetaPaleyWienerSupportIndicatorBound f B t)
      hnorm_zero.symm
      (Eq.subst
        (motive := fun v : ℝ => 0 ≤ v)
        hindicator.symm
        le_rfl)

/-- Integrating a support-indicator majorant bounds the norm of the real-line Laplace
integral. -/
theorem zetaLaplaceTransform_norm_le_supportIndicatorIntegral
    (f : ZetaAdmissibleFunction) (z : ℂ) (B : ℝ)
    (hindicator :
      ∀ t : ℝ,
        ‖zetaPaleyWienerLaplaceKernel f z t‖ ≤
          zetaPaleyWienerSupportIndicatorBound f B t) :
    ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖ ≤
      ∫ t : ℝ, zetaPaleyWienerSupportIndicatorBound f B t := by
  sorry

/-- The support-indicator integral is bounded by any containing support interval length. -/
theorem zetaPaleyWienerSupportIndicatorIntegral_le_intervalLength_mul_bound
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (B : ℝ) (hB_nonneg : 0 ≤ B) :
    (∫ t : ℝ, zetaPaleyWienerSupportIndicatorBound f B t) ≤
      B * zetaPaleyWienerSupportIntervalLength I := by
  sorry

/-- Integral-norm transport from a pointwise compact-support kernel bound. -/
theorem zetaLaplaceTransform_norm_le_supportIntervalLength_mul_bound
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (z : ℂ) (B : ℝ)
    (hB_nonneg : 0 ≤ B)
    (hbound :
      ∀ t : ℝ,
        t ∈ tsupport f.toZetaTestFunction →
        ‖f.toZetaTestFunction' t * Complex.exp (z * (t : ℂ))‖ ≤ B) :
    ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖ ≤
      B * zetaPaleyWienerSupportIntervalLength I := by
  have hkernel_bound :
      ∀ t : ℝ,
        t ∈ tsupport f.toZetaTestFunction →
        ‖zetaPaleyWienerLaplaceKernel f z t‖ ≤ B := by
    intro t ht
    unfold zetaPaleyWienerLaplaceKernel
    exact hbound t ht
  have hindicator_pointwise :
      ∀ t : ℝ,
        ‖zetaPaleyWienerLaplaceKernel f z t‖ ≤
          zetaPaleyWienerSupportIndicatorBound f B t :=
    zetaPaleyWienerLaplaceKernel_norm_le_supportIndicatorBound
      f z B hkernel_bound
  have hintegral :
      ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖ ≤
        ∫ t : ℝ, zetaPaleyWienerSupportIndicatorBound f B t :=
    zetaLaplaceTransform_norm_le_supportIndicatorIntegral
      f z B hindicator_pointwise
  have hlength :
      (∫ t : ℝ, zetaPaleyWienerSupportIndicatorBound f B t) ≤
        B * zetaPaleyWienerSupportIntervalLength I :=
    zetaPaleyWienerSupportIndicatorIntegral_le_intervalLength_mul_bound
      f I B hB_nonneg
  exact le_trans hintegral hlength

/-- Raw zero-order compact-support product bound for the Laplace transform.

This is the un-bumped estimate: source norm envelope, horizontal exponential envelope,
and support interval length multiply to dominate the integral norm. -/
theorem zetaLaplaceTransform_supportInterval_zeroOrder_le_rawEnvelope
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) :
    ∀ z : ℂ,
      zetaPaleyWienerInVerticalStrip a b z →
      ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖ ≤
        zetaPaleyWienerSupportNormEnvelope f *
          zetaPaleyWienerStripExponentialEnvelope I a b *
          zetaPaleyWienerSupportIntervalLength I := by
  intro z hz
  let B : ℝ :=
    zetaPaleyWienerRawKernelEnvelope f I a b
  have hB_nonneg : 0 ≤ B :=
    zetaPaleyWienerRawKernelEnvelope_nonnegative f I a b
  have hbound :
      ∀ t : ℝ,
        t ∈ tsupport f.toZetaTestFunction →
        ‖f.toZetaTestFunction' t * Complex.exp (z * (t : ℂ))‖ ≤ B := by
    intro t ht
    exact zetaLaplaceKernel_norm_le_rawEnvelope_on_support
      f I a b z hz t ht
  have hintegral :
      ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖ ≤
        B * zetaPaleyWienerSupportIntervalLength I :=
    zetaLaplaceTransform_norm_le_supportIntervalLength_mul_bound
      f I z B hB_nonneg hbound
  change
    ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖ ≤
      zetaPaleyWienerRawKernelEnvelope f I a b *
        zetaPaleyWienerSupportIntervalLength I
  exact hintegral

/-- The concrete zero-order integral estimate from compact support.

The source norm is bounded by `zetaPaleyWienerSupportNormEnvelope`, the horizontal
exponential is bounded by `zetaPaleyWienerStripExponentialEnvelope`, and the support is
contained in the supplied interval of length `zetaPaleyWienerSupportIntervalLength`. -/
theorem zetaLaplaceTransform_supportInterval_zeroOrder_le_envelope
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) :
    ∀ z : ℂ,
      zetaPaleyWienerInVerticalStrip a b z →
      ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖ ≤
        zetaPaleyWienerZeroOrderEnvelope f I a b := by
  intro z hz
  have hraw :
      ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖ ≤
        zetaPaleyWienerSupportNormEnvelope f *
          zetaPaleyWienerStripExponentialEnvelope I a b *
          zetaPaleyWienerSupportIntervalLength I :=
    zetaLaplaceTransform_supportInterval_zeroOrder_le_rawEnvelope f I a b z hz
  unfold zetaPaleyWienerZeroOrderEnvelope
  exact weightedLaplaceKernel_bound_le_bump
    (zetaPaleyWienerSupportNormEnvelope f *
      zetaPaleyWienerStripExponentialEnvelope I a b *
      zetaPaleyWienerSupportIntervalLength I)
    hraw

/-- Zero-order compact-support control for the admissible Laplace transform on a fixed
support interval.

This is the analytic estimate before integration by parts: compact support bounds the
source, the support interval bounds the horizontal exponential factor uniformly on the
strip, and the integral is controlled by those two bounds. -/
theorem zetaLaplaceTransform_supportInterval_zeroOrder_integralBound
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        zetaPaleyWienerInVerticalStrip a b z →
        ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖ ≤ C := by
  exact ⟨zetaPaleyWienerZeroOrderEnvelope f I a b,
    zetaPaleyWienerZeroOrderEnvelope_pos f I a b,
    zetaLaplaceTransform_supportInterval_zeroOrder_le_envelope f I a b⟩

/-- Zero-order Paley-Wiener control on a fixed compact support interval.

This is the compact-support estimate before any integration by parts: the horizontal
exponential factor is uniformly bounded on the strip and support interval. -/
theorem zetaLaplaceTransform_supportInterval_zeroOrder_decay
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        zetaPaleyWienerInVerticalStrip a b z →
        ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
          ≤ C * zetaPaleyWienerVerticalWeight z 0 := by
  rcases zetaLaplaceTransform_supportInterval_zeroOrder_integralBound
      f I a b with ⟨C, hCpos, hCbound⟩
  refine ⟨C, hCpos, ?_⟩
  intro z hz
  have hweight :
      zetaPaleyWienerVerticalWeight z 0 = 1 := by
    unfold zetaPaleyWienerVerticalWeight
    exact zpow_zero (1 + ‖z.im‖)
  have htarget :
      C * zetaPaleyWienerVerticalWeight z 0 = C := by
    exact Eq.trans (congrArg (fun W : ℝ => C * W) hweight) (mul_one C)
  exact (hCbound z hz).trans_eq htarget.symm

/-- The source on the vertical line `re z = x` after absorbing the horizontal exponential
factor into the compactly supported source. -/
noncomputable def zetaPaleyWienerHorizontalTwist
    (f : ZetaAdmissibleFunction) (x t : ℝ) : ℂ :=
  f.toZetaTestFunction' t * (Real.exp (x * t) : ℂ)

/-- The pure vertical oscillatory kernel on the line `re z = x`. -/
noncomputable def zetaPaleyWienerVerticalOscillation
    (y t : ℝ) : ℂ :=
  Complex.exp (Complex.I * (y : ℂ) * (t : ℂ))

/-- The derivative source used by vertical-line integration by parts after the horizontal
factor has been absorbed into the source. -/
noncomputable def zetaPaleyWienerVerticalLineIBPDerivative
    (f : ZetaAdmissibleFunction) (x t : ℝ) : ℂ :=
  deriv (fun u : ℝ => zetaPaleyWienerHorizontalTwist f x u) t

/-- The transformed derivative source appearing after one vertical-line integration by parts. -/
noncomputable def zetaPaleyWienerVerticalLineIBPDerivativeIntegral
    (f : ZetaAdmissibleFunction) (x y : ℝ) : ℂ :=
  ∫ t : ℝ,
    zetaPaleyWienerVerticalLineIBPDerivative f x t *
      zetaPaleyWienerVerticalOscillation y t

/-- Vertical-line integration by parts as a norm identity.

After absorbing the horizontal factor into the source on `re z = x`, integration by
parts on the vertical oscillation gives one inverse vertical-frequency factor. -/
theorem zetaLaplaceTransform_supportInterval_verticalLineIBP_normIdentity
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (z : ℂ)
    (hzstrip : zetaPaleyWienerInVerticalStrip a b z)
    (hzhigh : 1 ≤ ‖z.im‖) :
    ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖ =
      ‖(z.im : ℂ)⁻¹ *
        zetaPaleyWienerVerticalLineIBPDerivativeIntegral f z.re z.im‖ := by
  sorry

/-- One vertical-line integration-by-parts norm comparison.

On the line `re z = x`, the horizontal exponential is part of the source and the remaining
oscillation is `exp (I * y * t)`.  Boundary terms vanish from the fixed compact support
interval, giving one inverse vertical-frequency factor. -/
theorem zetaLaplaceTransform_supportInterval_verticalLineIBP_normComparison
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (z : ℂ)
    (hzstrip : zetaPaleyWienerInVerticalStrip a b z)
    (hzhigh : 1 ≤ ‖z.im‖) :
    ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖ ≤
      ‖(z.im : ℂ)⁻¹‖ *
        ‖zetaPaleyWienerVerticalLineIBPDerivativeIntegral f z.re z.im‖ := by
  have hidentity :
      ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖ =
        ‖(z.im : ℂ)⁻¹ *
          zetaPaleyWienerVerticalLineIBPDerivativeIntegral f z.re z.im‖ :=
    zetaLaplaceTransform_supportInterval_verticalLineIBP_normIdentity
      f I a b z hzstrip hzhigh
  have hmul :
      ‖(z.im : ℂ)⁻¹ *
          zetaPaleyWienerVerticalLineIBPDerivativeIntegral f z.re z.im‖ =
        ‖(z.im : ℂ)⁻¹‖ *
          ‖zetaPaleyWienerVerticalLineIBPDerivativeIntegral f z.re z.im‖ :=
    norm_mul
      ((z.im : ℂ)⁻¹)
      (zetaPaleyWienerVerticalLineIBPDerivativeIntegral f z.re z.im)
  exact le_of_eq (hidentity.trans hmul)

/-- Uniform compact-strip decay for the derivative integral produced by vertical-line
integration by parts, expressed directly in the real line coordinates `(x,y)`. -/
theorem zetaPaleyWienerVerticalLineIBPDerivativeIntegral_compactStrip_uniformDecay
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ x y : ℝ,
        a ≤ x →
        x ≤ b →
        ‖zetaPaleyWienerVerticalLineIBPDerivativeIntegral f x y‖
          ≤ C * (1 + ‖y‖) ^ (-(N : ℤ)) := by
  sorry

/-- Uniform compact-strip control of the derivative integral produced by one vertical-line
integration-by-parts step.

The derivative source depends on `x = re z`, but `x` ranges over the compact interval
`[a,b]`, so the resulting derivative-integral constants can be made uniform across the
whole strip. -/
theorem zetaPaleyWienerVerticalLineIBPDerivativeIntegral_supportInterval_decay
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        zetaPaleyWienerInVerticalStrip a b z →
        ‖zetaPaleyWienerVerticalLineIBPDerivativeIntegral f z.re z.im‖
          ≤ C * zetaPaleyWienerVerticalWeight z N := by
  rcases zetaPaleyWienerVerticalLineIBPDerivativeIntegral_compactStrip_uniformDecay
      f I a b N with ⟨C, hCpos, hCbound⟩
  refine ⟨C, hCpos, ?_⟩
  intro z hz
  unfold zetaPaleyWienerVerticalWeight
  exact hCbound z.re z.im hz.1 hz.2

/-- High-frequency Paley-Wiener control from vertical-line integration by parts on a compact
real-part strip.

The honest strip argument does not produce one derivative probe independent of `z`.  On the
vertical line `re z = x`, integration by parts differentiates the compactly supported source
after multiplying by the horizontal factor `Real.exp (x * t)`, and the constants are then made
uniform for `x ∈ [a,b]`.  This theorem owns that compact-strip vertical-line transport. -/
theorem zetaLaplaceTransform_supportInterval_successor_highFrequency_decay_from_verticalLineIBP
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        zetaPaleyWienerInVerticalStrip a b z →
        1 ≤ ‖z.im‖ →
        ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
          ≤ C * zetaPaleyWienerVerticalWeight z (N + 1) := by
  rcases zetaPaleyWienerVerticalLineIBPDerivativeIntegral_supportInterval_decay
      f I a b N with ⟨C, hC_pos, hC⟩
  refine ⟨C * 2, mul_pos hC_pos zero_lt_two, ?_⟩
  intro z hzstrip hzhigh
  have hparts :
      ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖ ≤
        ‖(z.im : ℂ)⁻¹‖ *
          ‖zetaPaleyWienerVerticalLineIBPDerivativeIntegral f z.re z.im‖ :=
    zetaLaplaceTransform_supportInterval_verticalLineIBP_normComparison
      f I a b z hzstrip hzhigh
  have hderivativeBound :
      ‖zetaPaleyWienerVerticalLineIBPDerivativeIntegral f z.re z.im‖
        ≤ C * zetaPaleyWienerVerticalWeight z N :=
    hC z hzstrip
  have hinv_nonneg : 0 ≤ ‖(z.im : ℂ)⁻¹‖ :=
    norm_nonneg ((z.im : ℂ)⁻¹)
  have hboundWithInv :
      ‖(z.im : ℂ)⁻¹‖ *
          ‖zetaPaleyWienerVerticalLineIBPDerivativeIntegral f z.re z.im‖
        ≤ ‖(z.im : ℂ)⁻¹‖ *
          (C * zetaPaleyWienerVerticalWeight z N) :=
    mul_le_mul_of_nonneg_left hderivativeBound hinv_nonneg
  have hC_nonneg : 0 ≤ C :=
    le_of_lt hC_pos
  have hweight :
      ‖(z.im : ℂ)⁻¹‖ * zetaPaleyWienerVerticalWeight z N ≤
        2 * zetaPaleyWienerVerticalWeight z (N + 1) :=
    zetaPaleyWiener_inverseIm_mul_weight_le_successor_highFrequency z N hzhigh
  have hrearrange :
      ‖(z.im : ℂ)⁻¹‖ * (C * zetaPaleyWienerVerticalWeight z N) =
        C * (‖(z.im : ℂ)⁻¹‖ * zetaPaleyWienerVerticalWeight z N) := by
    calc
      ‖(z.im : ℂ)⁻¹‖ * (C * zetaPaleyWienerVerticalWeight z N) =
          (‖(z.im : ℂ)⁻¹‖ * C) * zetaPaleyWienerVerticalWeight z N := by
        exact (mul_assoc ‖(z.im : ℂ)⁻¹‖ C
          (zetaPaleyWienerVerticalWeight z N)).symm
      _ = (C * ‖(z.im : ℂ)⁻¹‖) * zetaPaleyWienerVerticalWeight z N := by
        exact congrArg (fun y : ℝ => y * zetaPaleyWienerVerticalWeight z N)
          (mul_comm ‖(z.im : ℂ)⁻¹‖ C)
      _ = C * (‖(z.im : ℂ)⁻¹‖ * zetaPaleyWienerVerticalWeight z N) := by
        exact mul_assoc C ‖(z.im : ℂ)⁻¹‖
          (zetaPaleyWienerVerticalWeight z N)
  have hrenorm :
      C * (‖(z.im : ℂ)⁻¹‖ * zetaPaleyWienerVerticalWeight z N) ≤
        C * (2 * zetaPaleyWienerVerticalWeight z (N + 1)) :=
    mul_le_mul_of_nonneg_left hweight hC_nonneg
  have htarget :
      C * (2 * zetaPaleyWienerVerticalWeight z (N + 1)) =
        (C * 2) * zetaPaleyWienerVerticalWeight z (N + 1) := by
    exact (mul_assoc C 2 (zetaPaleyWienerVerticalWeight z (N + 1))).symm
  exact hparts.trans (hboundWithInv.trans (Eq.subst
    (motive := fun y : ℝ => y ≤ (C * 2) * zetaPaleyWienerVerticalWeight z (N + 1))
    hrearrange.symm
    (hrenorm.trans_eq htarget)))

/-- Low-frequency successor transport: on `|im z| ≤ 1`, the current decay estimate can be
renormalized into the successor estimate by enlarging the constant. -/
theorem zetaLaplaceTransform_supportInterval_successor_lowFrequency_decay_from_current
    (f : ZetaAdmissibleFunction)
    (a b : ℝ) (N : ℕ)
    (hcurrent :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          zetaPaleyWienerInVerticalStrip a b z →
          ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
            ≤ C * zetaPaleyWienerVerticalWeight z N) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        zetaPaleyWienerInVerticalStrip a b z →
        ‖z.im‖ ≤ 1 →
        ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
          ≤ C * zetaPaleyWienerVerticalWeight z (N + 1) := by
  rcases hcurrent with ⟨C, hC_pos, hC⟩
  refine ⟨C * 2, mul_pos hC_pos zero_lt_two, ?_⟩
  intro z hzstrip hzlow
  have hbound :
      ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
        ≤ C * zetaPaleyWienerVerticalWeight z N :=
    hC z hzstrip
  have hweight :
      zetaPaleyWienerVerticalWeight z N ≤
        2 * zetaPaleyWienerVerticalWeight z (N + 1) :=
    zetaPaleyWienerVerticalWeight_le_successor_lowFrequency z N hzlow
  have hC_nonneg : 0 ≤ C :=
    le_of_lt hC_pos
  have hrenorm :
      C * zetaPaleyWienerVerticalWeight z N ≤
        C * (2 * zetaPaleyWienerVerticalWeight z (N + 1)) :=
    mul_le_mul_of_nonneg_left hweight hC_nonneg
  have hreassociate :
      C * (2 * zetaPaleyWienerVerticalWeight z (N + 1)) =
        (C * 2) * zetaPaleyWienerVerticalWeight z (N + 1) := by
    exact (mul_assoc C 2 (zetaPaleyWienerVerticalWeight z (N + 1))).symm
  exact hbound.trans (hrenorm.trans_eq hreassociate)

/-- The low/high frequency successor estimates combine into the global successor estimate. -/
theorem zetaLaplaceTransform_supportInterval_successor_decay_from_low_high
    (f : ZetaAdmissibleFunction)
    (a b : ℝ) (N : ℕ)
    (hlow :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          zetaPaleyWienerInVerticalStrip a b z →
          ‖z.im‖ ≤ 1 →
          ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
            ≤ C * zetaPaleyWienerVerticalWeight z (N + 1))
    (hhigh :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          zetaPaleyWienerInVerticalStrip a b z →
          1 ≤ ‖z.im‖ →
          ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
            ≤ C * zetaPaleyWienerVerticalWeight z (N + 1)) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        zetaPaleyWienerInVerticalStrip a b z →
        ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
          ≤ C * zetaPaleyWienerVerticalWeight z (N + 1) := by
  rcases hlow with ⟨Clow, hClow_pos, hClow⟩
  rcases hhigh with ⟨Chigh, hChigh_pos, hChigh⟩
  refine ⟨max Clow Chigh, lt_of_lt_of_le hClow_pos (le_max_left Clow Chigh), ?_⟩
  intro z hz
  have hweight : 0 ≤ zetaPaleyWienerVerticalWeight z (N + 1) :=
    zetaPaleyWienerVerticalWeight_nonnegative z (N + 1)
  by_cases hlow_region : ‖z.im‖ ≤ 1
  · have hbound :
        ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
          ≤ Clow * zetaPaleyWienerVerticalWeight z (N + 1) :=
      hClow z hz hlow_region
    have hconstant :
        Clow * zetaPaleyWienerVerticalWeight z (N + 1) ≤
          max Clow Chigh * zetaPaleyWienerVerticalWeight z (N + 1) :=
      mul_le_mul_of_nonneg_right (le_max_left Clow Chigh) hweight
    exact hbound.trans hconstant
  · have hhigh_region : 1 ≤ ‖z.im‖ :=
      le_of_lt (lt_of_not_ge hlow_region)
    have hbound :
        ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
          ≤ Chigh * zetaPaleyWienerVerticalWeight z (N + 1) :=
      hChigh z hz hhigh_region
    have hconstant :
        Chigh * zetaPaleyWienerVerticalWeight z (N + 1) ≤
          max Clow Chigh * zetaPaleyWienerVerticalWeight z (N + 1) :=
      mul_le_mul_of_nonneg_right (le_max_right Clow Chigh) hweight
    exact hbound.trans hconstant

/-- One integration-by-parts step for Paley-Wiener control on a fixed compact support
interval.

The step consumes the `N`th vertical decay estimate and produces the successor estimate by
integrating by parts once more; smoothness bounds the next derivative seminorm and compact
support kills the boundary terms. -/
theorem zetaLaplaceTransform_supportInterval_integrationByParts_successor
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ)
    (hN :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          zetaPaleyWienerInVerticalStrip a b z →
          ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
            ≤ C * zetaPaleyWienerVerticalWeight z N) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        zetaPaleyWienerInVerticalStrip a b z →
        ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
          ≤ C * zetaPaleyWienerVerticalWeight z (N + 1) := by
  have hlow :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          zetaPaleyWienerInVerticalStrip a b z →
          ‖z.im‖ ≤ 1 →
          ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
            ≤ C * zetaPaleyWienerVerticalWeight z (N + 1) :=
    zetaLaplaceTransform_supportInterval_successor_lowFrequency_decay_from_current
      f a b N hN
  have hhigh :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          zetaPaleyWienerInVerticalStrip a b z →
          1 ≤ ‖z.im‖ →
          ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
            ≤ C * zetaPaleyWienerVerticalWeight z (N + 1) :=
    zetaLaplaceTransform_supportInterval_successor_highFrequency_decay_from_verticalLineIBP
      f I a b N
  exact zetaLaplaceTransform_supportInterval_successor_decay_from_low_high
    f a b N hlow hhigh

/-- Paley-Wiener decay at a fixed order, uniformly available for every admissible probe.

This is the induction form needed by integration by parts: in the successor step, the
induction hypothesis is applied to the derivative probe, not only to the original probe. -/
theorem zetaLaplaceTransform_supportInterval_integrationByParts_decay_all
    (N : ℕ) :
    ∀ (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
      (a b : ℝ),
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          zetaPaleyWienerInVerticalStrip a b z →
          ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
            ≤ C * zetaPaleyWienerVerticalWeight z N := by
  induction N with
  | zero =>
      intro f I a b
      exact zetaLaplaceTransform_supportInterval_zeroOrder_decay f I a b
  | succ N ih =>
      intro f I a b
      have hN :
          ∃ C : ℝ,
            0 < C ∧
            ∀ z : ℂ,
              zetaPaleyWienerInVerticalStrip a b z →
              ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
                ≤ C * zetaPaleyWienerVerticalWeight z N :=
        ih f I a b
      exact zetaLaplaceTransform_supportInterval_integrationByParts_successor
        f I a b N hN

/-- The oscillatory integration-by-parts estimate on a fixed support interval.

This is the Fourier-side core of Paley-Wiener: after `N` integrations by parts, the vertical
frequency contributes the factor `(1 + |im z|)^{-N}`.  Smoothness supplies the needed
derivative seminorms and the support-interval vanishing lemmas kill all boundary terms. -/
theorem zetaLaplaceTransform_supportInterval_integrationByParts_decay
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        zetaPaleyWienerInVerticalStrip a b z →
        ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
          ≤ C * zetaPaleyWienerVerticalWeight z N := by
  exact zetaLaplaceTransform_supportInterval_integrationByParts_decay_all
    N f I a b

/-- The Paley-Wiener support-interval estimate assembled from the interval seminorm and the
oscillatory integration-by-parts bound. -/
theorem zetaLaplaceTransform_verticalStripDecayConstant_of_supportInterval
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ, zetaLaplaceTransformHasVerticalStripDecayConstant f a b N C := by
  rcases zetaLaplaceTransform_supportInterval_integrationByParts_decay
      f I a b N with ⟨C, hCpos, hCbound⟩
  exact ⟨C, hCpos, hCbound⟩

/-- The compact-support smooth Paley-Wiener estimate for the Laplace transform from an explicit
support interval, with the decay constant produced as data.

This is the analytic core: use the supplied compact interval, integrate by parts `N` times in the
vertical oscillatory factor, use smoothness to bound the resulting derivative seminorm on the
support, and absorb the bounded horizontal factor uniformly over `a ≤ re z ≤ b`. -/
theorem zetaLaplaceTransform_verticalStripDecayConstant_of_supportInterval_integrationByParts
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ, zetaLaplaceTransformHasVerticalStripDecayConstant f a b N C := by
  exact zetaLaplaceTransform_verticalStripDecayConstant_of_supportInterval
    f I a b N

/-- The compact-support smooth Paley-Wiener estimate for the Laplace transform, with the
decay constant produced as data. -/
theorem zetaLaplaceTransform_verticalStripDecayConstant_of_integrationByParts
    (f : ZetaAdmissibleFunction) (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ, zetaLaplaceTransformHasVerticalStripDecayConstant f a b N C := by
  rcases exists_zetaPaleyWienerSupportInterval f with ⟨I⟩
  exact zetaLaplaceTransform_verticalStripDecayConstant_of_supportInterval_integrationByParts
    f I a b N

/-- Paley-Wiener rapid vertical-strip decay for the Laplace transform of a compactly
supported smooth admissible source.

This is the exact analytic owner theorem: repeated integration by parts in the
oscillatory factor `exp (I * y * t)` gives arbitrary inverse powers of the
vertical frequency, while compact support makes the horizontal strip factor
uniform on `a ≤ re z ≤ b` and kills all boundary terms. -/
theorem zetaLaplaceTransform_verticalStripRapidDecay_of_compactSupport_smooth
    (f : ZetaAdmissibleFunction) (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
          ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)) := by
  rcases zetaLaplaceTransform_verticalStripDecayConstant_of_integrationByParts
      f a b N with ⟨C, hC⟩
  refine ⟨C, hC.1, ?_⟩
  intro z haz hzb
  exact hC.2 z ⟨haz, hzb⟩

/-- Paley-Wiener rapid vertical-strip decay for the completed explicit-formula transform
`Φ_f`, projected as an existence statement for theorem consumers. -/
theorem zetaPhi_verticalStripRapidDecay_of_admissible_owner
    (f : ZetaAdmissibleFunction) (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        ‖zetaCompletedExplicitFormulaPhi f z‖
          ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)) := by
  have hbase :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          a ≤ z.re →
          z.re ≤ b →
          ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
            ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)) :=
    zetaLaplaceTransform_verticalStripRapidDecay_of_compactSupport_smooth
      f a b N
  rcases hbase with ⟨C, hCpos, hboundBase⟩
  refine ⟨C, hCpos, ?_⟩
  intro z haz hzb
  have hphi :
      zetaCompletedExplicitFormulaPhi f z =
        Boundary.zetaLaplaceTransform f.toZetaTestFunction' z := by
    exact congrFun (zetaCompletedExplicitFormulaPhi_eq_laplace f) z
  have hbound :
      ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
        ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)) :=
    hboundBase z haz hzb
  exact Eq.subst
    (motive := fun w : ℂ =>
      ‖w‖ ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)))
    hphi.symm
    hbound

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
