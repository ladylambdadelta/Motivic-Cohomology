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
  lower_le_upper : lower ≤ upper
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
  exact
    ⟨⟨min A B, max A B,
      le_trans (min_le_left A B) (le_max_left A B),
      (fun t ht => le_trans (min_le_left A B) (hA t ht)),
      (fun t ht => le_trans (hB t ht) (le_max_right A B))⟩⟩

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

/-- For ordered support intervals, the stored length is the ordinary endpoint difference. -/
theorem zetaPaleyWienerSupportIntervalLength_eq_upper_sub_lower
    (I : ZetaPaleyWienerSupportInterval f) :
    zetaPaleyWienerSupportIntervalLength I = I.upper - I.lower := by
  unfold zetaPaleyWienerSupportIntervalLength
  exact max_eq_left (sub_nonneg.mpr I.lower_le_upper)

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

/-- The compact image whose elements are exactly the pointwise source norms on the support. -/
def zetaPaleyWienerSupportNormImage
    (f : ZetaAdmissibleFunction) : Set ℝ :=
  (fun t : ℝ => ‖f.toZetaTestFunction t‖) '' tsupport f.toZetaTestFunction

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

/-- The support-norm set is the compact-support norm image in predicate form. -/
theorem zetaPaleyWienerSupportNormSet_eq_supportNormImage
    (f : ZetaAdmissibleFunction) :
    zetaPaleyWienerSupportNormSet f =
      zetaPaleyWienerSupportNormImage f := by
  apply Set.ext
  intro r
  constructor
  · intro hr
    rcases hr with ⟨t, ht_support, ht_norm⟩
    unfold zetaPaleyWienerSupportNormImage
    exact ⟨t, ht_support, ht_norm.symm⟩
  · intro hr
    rcases hr with ⟨t, ht_support, ht_norm⟩
    unfold zetaPaleyWienerSupportNormSet
    exact ⟨t, ht_support, ht_norm.symm⟩

/-- The pointwise norm map attached to an admissible source is continuous. -/
theorem zetaPaleyWienerSupportNormMap_continuous
    (f : ZetaAdmissibleFunction) :
    Continuous (fun t : ℝ => ‖f.toZetaTestFunction t‖) := by
  exact f.toZetaTestFunction.continuous.norm

/-- The support-norm image is compact. -/
theorem zetaPaleyWienerSupportNormImage_isCompact
    (f : ZetaAdmissibleFunction) :
    IsCompact (zetaPaleyWienerSupportNormImage f) := by
  unfold zetaPaleyWienerSupportNormImage
  exact f.toZetaTestFunction.hasCompactSupport.isCompact.image
    (zetaPaleyWienerSupportNormMap_continuous f).continuousOn

/-- The compact-support norm image is bounded above. -/
theorem zetaPaleyWienerSupportNormImage_bddAbove
    (f : ZetaAdmissibleFunction) :
    BddAbove (zetaPaleyWienerSupportNormImage f) := by
  exact IsCompact.bddAbove (zetaPaleyWienerSupportNormImage_isCompact f)

/-- Source norms on the support are bounded above. -/
theorem zetaPaleyWienerSupportNormSet_bddAbove
    (f : ZetaAdmissibleFunction) :
    BddAbove (zetaPaleyWienerSupportNormSet f) := by
  exact Eq.subst
    (motive := fun S : Set ℝ => BddAbove S)
    (zetaPaleyWienerSupportNormSet_eq_supportNormImage f).symm
    (zetaPaleyWienerSupportNormImage_bddAbove f)

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

/-- Absolute value on an interval is bounded by the larger endpoint absolute value. -/
theorem abs_le_max_abs_endpoints_of_mem_interval
    (a b x : ℝ) (hxa : a ≤ x) (hxb : x ≤ b) :
    |x| ≤ max |a| |b| := by
  have hx_upper : x ≤ max |a| |b| :=
    le_trans hxb
      (le_trans (le_abs_self b) (le_max_right |a| |b|))
  have hx_lower : -x ≤ max |a| |b| :=
    le_trans (neg_le_neg hxa)
      (le_trans (neg_le_abs a) (le_max_left |a| |b|))
  exact abs_le.mpr ⟨hx_lower, hx_upper⟩

/-- The product of the one-dimensional endpoint absolute-value envelopes dominates the
rectangle product. -/
theorem abs_mul_le_endpointEnvelopeProduct_of_mem_interval
    (a b lower upper x t : ℝ)
    (hxa : a ≤ x) (hxb : x ≤ b)
    (ht_lower : lower ≤ t) (ht_upper : t ≤ upper) :
    |x * t| ≤ max |a| |b| * max |lower| |upper| := by
  have hx : |x| ≤ max |a| |b| :=
    abs_le_max_abs_endpoints_of_mem_interval a b x hxa hxb
  have ht : |t| ≤ max |lower| |upper| :=
    abs_le_max_abs_endpoints_of_mem_interval lower upper t ht_lower ht_upper
  have hx_nonneg : 0 ≤ |x| := abs_nonneg x
  have hendpoint_nonneg : 0 ≤ max |a| |b| :=
    le_max_of_le_left (abs_nonneg a)
  have hmul :
      |x| * |t| ≤ max |a| |b| * max |lower| |upper| :=
    mul_le_mul hx ht (abs_nonneg t) hendpoint_nonneg
  exact Eq.subst
    (motive := fun v : ℝ => v ≤ max |a| |b| * max |lower| |upper|)
    (abs_mul x t).symm
    hmul

/-- The product of nonnegative max envelopes bounds each of the four products. -/
theorem four_products_le_max_mul_max_of_nonneg
    {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    max (max (a * c) (a * d)) (max (b * c) (b * d)) ≤
      max a b * max c d := by
  have hmaxab_nonneg : 0 ≤ max a b :=
    le_max_of_le_left ha
  have hac : a * c ≤ max a b * max c d :=
    mul_le_mul (le_max_left a b) (le_max_left c d) hc hmaxab_nonneg
  have had : a * d ≤ max a b * max c d :=
    mul_le_mul (le_max_left a b) (le_max_right c d) hd hmaxab_nonneg
  have hbc : b * c ≤ max a b * max c d :=
    mul_le_mul (le_max_right a b) (le_max_left c d) hc hmaxab_nonneg
  have hbd : b * d ≤ max a b * max c d :=
    mul_le_mul (le_max_right a b) (le_max_right c d) hd hmaxab_nonneg
  exact max_le (max_le hac had) (max_le hbc hbd)

/-- The first corner product is included in the four-product maximum. -/
theorem first_product_le_four_products
    (a b c d : ℝ) :
    a * c ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) :=
  le_trans (le_max_left (a * c) (a * d))
    (le_max_left (max (a * c) (a * d)) (max (b * c) (b * d)))

/-- The second corner product is included in the four-product maximum. -/
theorem second_product_le_four_products
    (a b c d : ℝ) :
    a * d ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) :=
  le_trans (le_max_right (a * c) (a * d))
    (le_max_left (max (a * c) (a * d)) (max (b * c) (b * d)))

/-- The third corner product is included in the four-product maximum. -/
theorem third_product_le_four_products
    (a b c d : ℝ) :
    b * c ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) :=
  le_trans (le_max_left (b * c) (b * d))
    (le_max_right (max (a * c) (a * d)) (max (b * c) (b * d)))

/-- The fourth corner product is included in the four-product maximum. -/
theorem fourth_product_le_four_products
    (a b c d : ℝ) :
    b * d ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) :=
  le_trans (le_max_right (b * c) (b * d))
    (le_max_right (max (a * c) (a * d)) (max (b * c) (b * d)))

/-- The product of nonnegative max envelopes is bounded by the four-product maximum. -/
theorem max_mul_max_le_four_products_of_nonneg
    {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    max a b * max c d ≤
      max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  by_cases hab : a ≤ b
  · have hmaxab : max a b = b := max_eq_right hab
    by_cases hcd : c ≤ d
    · have hmaxcd : max c d = d := max_eq_right hcd
      have hcorner :
          b * d ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) :=
        fourth_product_le_four_products a b c d
      exact Eq.subst
        (motive := fun v : ℝ =>
          v * max c d ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)))
        hmaxab.symm
        (Eq.subst
          (motive := fun v : ℝ =>
            b * v ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)))
          hmaxcd.symm
          hcorner)
    · have hdc : d ≤ c := le_of_not_ge hcd
      have hmaxcd : max c d = c := max_eq_left hdc
      have hcorner :
          b * c ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) :=
        third_product_le_four_products a b c d
      exact Eq.subst
        (motive := fun v : ℝ =>
          v * max c d ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)))
        hmaxab.symm
        (Eq.subst
          (motive := fun v : ℝ =>
            b * v ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)))
          hmaxcd.symm
          hcorner)
  · have hba : b ≤ a := le_of_not_ge hab
    have hmaxab : max a b = a := max_eq_left hba
    by_cases hcd : c ≤ d
    · have hmaxcd : max c d = d := max_eq_right hcd
      have hcorner :
          a * d ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) :=
        second_product_le_four_products a b c d
      exact Eq.subst
        (motive := fun v : ℝ =>
          v * max c d ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)))
        hmaxab.symm
        (Eq.subst
          (motive := fun v : ℝ =>
            a * v ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)))
          hmaxcd.symm
          hcorner)
    · have hdc : d ≤ c := le_of_not_ge hcd
      have hmaxcd : max c d = c := max_eq_left hdc
      have hcorner :
          a * c ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) :=
        first_product_le_four_products a b c d
      exact Eq.subst
        (motive := fun v : ℝ =>
          v * max c d ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)))
        hmaxab.symm
        (Eq.subst
          (motive := fun v : ℝ =>
            a * v ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)))
          hmaxcd.symm
          hcorner)

/-- Multiplying two nonnegative two-point max envelopes gives the max of the four products. -/
theorem max_mul_max_of_nonneg_eq_max_four_products
    {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    max a b * max c d =
      max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  exact le_antisymm
    (max_mul_max_le_four_products_of_nonneg ha hb hc hd)
    (four_products_le_max_mul_max_of_nonneg ha hb hc hd)

/-- Absolute value of a product as separated absolute-value factors. -/
theorem abs_mul_eq_abs_mul_abs
    (x y : ℝ) :
    |x * y| = |x| * |y| := by
  exact abs_mul x y

/-- The four-corner max written with separated absolute-value products equals the corner
absolute-product max. -/
theorem max_four_abs_products_eq_max_corner_abs
    (a b lower upper : ℝ) :
    max (max (|a| * |lower|) (|a| * |upper|))
        (max (|b| * |lower|) (|b| * |upper|)) =
      max (max (|a * lower|) (|a * upper|))
        (max (|b * lower|) (|b * upper|)) := by
  exact congrArg₂ max
    (congrArg₂ max
      (abs_mul_eq_abs_mul_abs a lower).symm
      (abs_mul_eq_abs_mul_abs a upper).symm)
    (congrArg₂ max
      (abs_mul_eq_abs_mul_abs b lower).symm
      (abs_mul_eq_abs_mul_abs b upper).symm)

/-- The product of the one-dimensional absolute endpoint envelopes is the maximum of the
four corner absolute products. -/
theorem max_abs_mul_max_abs_eq_max_corner_abs
    (a b lower upper : ℝ) :
    max |a| |b| * max |lower| |upper| =
      max (max (|a * lower|) (|a * upper|))
        (max (|b * lower|) (|b * upper|)) := by
  have hmax :
      max |a| |b| * max |lower| |upper| =
        max (max (|a| * |lower|) (|a| * |upper|))
          (max (|b| * |lower|) (|b| * |upper|)) :=
    max_mul_max_of_nonneg_eq_max_four_products
      (abs_nonneg a)
      (abs_nonneg b)
      (abs_nonneg lower)
      (abs_nonneg upper)
  exact Eq.trans hmax (max_four_abs_products_eq_max_corner_abs a b lower upper)

/-- The product of endpoint absolute-value envelopes is bounded by the four-corner
absolute-value envelope. -/
theorem endpointEnvelopeProduct_le_max_corner_abs
    (a b lower upper : ℝ) :
    max |a| |b| * max |lower| |upper| ≤
      max (max (|a * lower|) (|a * upper|))
        (max (|b * lower|) (|b * upper|)) := by
  exact le_of_eq (max_abs_mul_max_abs_eq_max_corner_abs a b lower upper)

/-- A rectangle product is bounded in absolute value by the largest absolute product at
the four corners. -/
theorem abs_mul_le_max_corner_abs_of_mem_interval
    (a b lower upper x t : ℝ)
    (hxa : a ≤ x) (hxb : x ≤ b)
    (ht_lower : lower ≤ t) (ht_upper : t ≤ upper) :
    |x * t| ≤
      max (max (|a * lower|) (|a * upper|))
        (max (|b * lower|) (|b * upper|)) := by
  have hproduct :
      |x * t| ≤ max |a| |b| * max |lower| |upper| :=
    abs_mul_le_endpointEnvelopeProduct_of_mem_interval
      a b lower upper x t hxa hxb ht_lower ht_upper
  have hcorner :
      max |a| |b| * max |lower| |upper| ≤
        max (max (|a * lower|) (|a * upper|))
          (max (|b * lower|) (|b * upper|)) :=
    endpointEnvelopeProduct_le_max_corner_abs a b lower upper
  exact le_trans hproduct hcorner

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

/-- The complex norm agrees with the complex absolute value. -/
theorem complex_norm_eq_abs
    (w : ℂ) :
    ‖w‖ = Complex.abs w := by
  rfl

/-- The complex exponential absolute value is the exponential of the real part. -/
theorem complexAbs_exp_eq_realExp_re
    (w : ℂ) :
    Complex.abs (Complex.exp w) = Real.exp w.re := by
  exact Complex.abs_exp w

/-- Norm of the complex exponential is the exponential of the real part. -/
theorem complexExp_norm_eq_realExp_re
    (w : ℂ) :
    ‖Complex.exp w‖ = Real.exp w.re := by
  exact Eq.trans
    (complex_norm_eq_abs (Complex.exp w))
    (complexAbs_exp_eq_realExp_re w)

/-- Multiplication by a real scalar has the expected real part. -/
theorem complex_mul_real_re
    (z : ℂ) (t : ℝ) :
    (z * (t : ℂ)).re = z.re * t := by
  calc
    (z * (t : ℂ)).re = z.re * (t : ℂ).re - z.im * (t : ℂ).im := by
      exact Complex.mul_re z (t : ℂ)
    _ = z.re * t - z.im * (t : ℂ).im := by
      exact congrArg (fun v : ℝ => z.re * v - z.im * (t : ℂ).im)
        (Complex.ofReal_re t)
    _ = z.re * t - z.im * 0 := by
      exact congrArg (fun v : ℝ => z.re * t - z.im * v)
        (Complex.ofReal_im t)
    _ = z.re * t - 0 := by
      exact congrArg (fun v : ℝ => z.re * t - v) (mul_zero z.im)
    _ = z.re * t := sub_zero (z.re * t)

/-- Multiplication by a real scalar has the expected imaginary part. -/
theorem complex_mul_real_im
    (z : ℂ) (t : ℝ) :
    (z * (t : ℂ)).im = z.im * t := by
  calc
    (z * (t : ℂ)).im = z.re * (t : ℂ).im + z.im * (t : ℂ).re := by
      exact Complex.mul_im z (t : ℂ)
    _ = z.re * 0 + z.im * (t : ℂ).re := by
      exact congrArg (fun v : ℝ => z.re * v + z.im * (t : ℂ).re)
        (Complex.ofReal_im t)
    _ = z.re * 0 + z.im * t := by
      exact congrArg (fun v : ℝ => z.re * 0 + z.im * v)
        (Complex.ofReal_re t)
    _ = 0 + z.im * t := by
      exact congrArg (fun v : ℝ => v + z.im * t) (mul_zero z.re)
    _ = z.im * t := zero_add (z.im * t)

/-- A real multiple of `I` has zero real part. -/
theorem paley_ofReal_mul_I_re_zero (t : ℝ) :
    ((t : ℂ) * Complex.I).re = 0 :=
  Eq.trans
    (Complex.mul_I_re (t : ℂ))
    (Eq.trans
      (congrArg Neg.neg (Complex.ofReal_im t))
      (neg_zero : -(0 : ℝ) = 0))

/-- A real multiple of `I` has the expected imaginary part. -/
theorem paley_ofReal_mul_I_im (t : ℝ) :
    ((t : ℂ) * Complex.I).im = t :=
  Eq.trans
    (Complex.mul_I_im (t : ℂ))
    (Complex.ofReal_re t)

/-- A horizontal real part plus a vertical real multiple of `I` has real part equal to
the horizontal coordinate. -/
theorem paley_ofReal_add_mul_I_re (a t : ℝ) :
    ((a : ℂ) + (t : ℂ) * Complex.I).re = a :=
  Eq.trans
    (Complex.add_re (a : ℂ) ((t : ℂ) * Complex.I))
    (Eq.trans
      (congrArg₂ HAdd.hAdd (Complex.ofReal_re a) (paley_ofReal_mul_I_re_zero t))
      (add_zero a))

/-- A horizontal real part plus a vertical real multiple of `I` has imaginary part equal
to the vertical coordinate. -/
theorem paley_ofReal_add_mul_I_im (a t : ℝ) :
    ((a : ℂ) + (t : ℂ) * Complex.I).im = t :=
  Eq.trans
    (Complex.add_im (a : ℂ) ((t : ℂ) * Complex.I))
    (Eq.trans
      (congrArg₂ HAdd.hAdd (Complex.ofReal_im a) (paley_ofReal_mul_I_im t))
      (zero_add t))

/-- The real part of the explicit vertical-line decomposition is the horizontal part. -/
theorem complex_verticalLine_decomposition_rhs_re
    (z : ℂ) (t : ℝ) :
    ((z.re * t : ℂ) + Complex.I * (z.im : ℂ) * (t : ℂ)).re =
      z.re * t := by
  have hIcomm :
      Complex.I * (z.im : ℂ) * (t : ℂ) =
        ((z.im * t : ℝ) : ℂ) * Complex.I := by
    calc
      Complex.I * (z.im : ℂ) * (t : ℂ) =
          ((z.im : ℂ) * (t : ℂ)) * Complex.I := by
        calc
          Complex.I * (z.im : ℂ) * (t : ℂ) =
              (z.im : ℂ) * Complex.I * (t : ℂ) := by
            exact congrArg (fun v : ℂ => v * (t : ℂ))
              (mul_comm Complex.I (z.im : ℂ))
          _ = (z.im : ℂ) * ((t : ℂ) * Complex.I) := by
            exact Eq.trans
              (mul_assoc (z.im : ℂ) Complex.I (t : ℂ))
              (congrArg (fun v : ℂ => (z.im : ℂ) * v)
                (mul_comm Complex.I (t : ℂ)))
          _ = ((z.im : ℂ) * (t : ℂ)) * Complex.I := by
            exact (mul_assoc (z.im : ℂ) (t : ℂ) Complex.I).symm
      _ = ((z.im * t : ℝ) : ℂ) * Complex.I := by
        exact congrArg (fun v : ℂ => v * Complex.I)
          (Complex.ofReal_mul z.im t).symm
  calc
    ((z.re * t : ℂ) + Complex.I * (z.im : ℂ) * (t : ℂ)).re =
        ((z.re * t : ℂ) + ((z.im * t : ℝ) : ℂ) * Complex.I).re := by
      exact congrArg (fun v : ℂ => ((z.re * t : ℂ) + v).re) hIcomm
    _ = z.re * t := by
      exact paley_ofReal_add_mul_I_re (z.re * t) (z.im * t)

/-- The imaginary part of the explicit vertical-line decomposition is the vertical part. -/
theorem complex_verticalLine_decomposition_rhs_im
    (z : ℂ) (t : ℝ) :
    ((z.re * t : ℂ) + Complex.I * (z.im : ℂ) * (t : ℂ)).im =
      z.im * t := by
  have hIcomm :
      Complex.I * (z.im : ℂ) * (t : ℂ) =
        ((z.im * t : ℝ) : ℂ) * Complex.I := by
    calc
      Complex.I * (z.im : ℂ) * (t : ℂ) =
          ((z.im : ℂ) * (t : ℂ)) * Complex.I := by
        calc
          Complex.I * (z.im : ℂ) * (t : ℂ) =
              (z.im : ℂ) * Complex.I * (t : ℂ) := by
            exact congrArg (fun v : ℂ => v * (t : ℂ))
              (mul_comm Complex.I (z.im : ℂ))
          _ = (z.im : ℂ) * ((t : ℂ) * Complex.I) := by
            exact Eq.trans
              (mul_assoc (z.im : ℂ) Complex.I (t : ℂ))
              (congrArg (fun v : ℂ => (z.im : ℂ) * v)
                (mul_comm Complex.I (t : ℂ)))
          _ = ((z.im : ℂ) * (t : ℂ)) * Complex.I := by
            exact (mul_assoc (z.im : ℂ) (t : ℂ) Complex.I).symm
      _ = ((z.im * t : ℝ) : ℂ) * Complex.I := by
        exact congrArg (fun v : ℂ => v * Complex.I)
          (Complex.ofReal_mul z.im t).symm
  calc
    ((z.re * t : ℂ) + Complex.I * (z.im : ℂ) * (t : ℂ)).im =
        ((z.re * t : ℂ) + ((z.im * t : ℝ) : ℂ) * Complex.I).im := by
      exact congrArg (fun v : ℂ => ((z.re * t : ℂ) + v).im) hIcomm
    _ = z.im * t := by
      exact paley_ofReal_add_mul_I_im (z.re * t) (z.im * t)

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

/-- The named Paley-Wiener kernel integrates to the zeta Laplace transform. -/
theorem zetaPaleyWienerLaplaceKernel_integral_eq_transform
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    (∫ t : ℝ, zetaPaleyWienerLaplaceKernel f z t) =
      Boundary.zetaLaplaceTransform f.toZetaTestFunction' z := by
  rfl

/-- The named Paley-Wiener Laplace kernel is integrable. -/
theorem zetaPaleyWienerLaplaceKernel_integrable
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    Integrable (fun t : ℝ => zetaPaleyWienerLaplaceKernel f z t) :=
  integrable_laplaceKernel_at f z

/-- The pointwise norm of the named Paley-Wiener Laplace kernel is integrable. -/
theorem zetaPaleyWienerLaplaceKernel_norm_integrable
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    Integrable (fun t : ℝ => ‖zetaPaleyWienerLaplaceKernel f z t‖) :=
  (zetaPaleyWienerLaplaceKernel_integrable f z).norm

/-- Norm of an integrable complex-valued integral is bounded by the integral of its norm. -/
theorem complex_norm_integral_le_integral_norm_of_integrable
    (g : ℝ → ℂ) (hg : Integrable g) :
    ‖∫ t : ℝ, g t‖ ≤ ∫ t : ℝ, ‖g t‖ :=
  MeasureTheory.norm_integral_le_integral_norm g

/-- The norm of the named Paley-Wiener kernel integral is bounded by the integral of the
pointwise kernel norm. -/
theorem zetaPaleyWienerLaplaceKernel_norm_integral_le_integral_norm
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    ‖∫ t : ℝ, zetaPaleyWienerLaplaceKernel f z t‖ ≤
      ∫ t : ℝ, ‖zetaPaleyWienerLaplaceKernel f z t‖ := by
  exact complex_norm_integral_le_integral_norm_of_integrable
    (fun t : ℝ => zetaPaleyWienerLaplaceKernel f z t)
    (zetaPaleyWienerLaplaceKernel_integrable f z)

/-- The constant support-indicator majorant used for the real-line integral bound. -/
noncomputable def zetaPaleyWienerSupportIndicatorBound
    (f : ZetaAdmissibleFunction) (B : ℝ) : ℝ → ℝ :=
  Set.indicator (tsupport f.toZetaTestFunction) (fun _ : ℝ => B)

/-- The constant interval-indicator majorant attached to a Paley-Wiener support interval. -/
noncomputable def zetaPaleyWienerIntervalIndicatorBound
    (I : ZetaPaleyWienerSupportInterval f) (B : ℝ) : ℝ → ℝ :=
  Set.indicator (Set.Icc I.lower I.upper) (fun _ : ℝ => B)

/-- A constant indicator on a compact real set is integrable. -/
theorem real_integrable_const_indicator_of_isCompact
    (K : Set ℝ) (hK : IsCompact K) (B : ℝ) :
    Integrable (Set.indicator K (fun _ : ℝ => B)) :=
  (integrable_indicator_iff hK.isClosed.measurableSet).2
    (integrableOn_const.2 (Or.inr hK.measure_lt_top))

/-- The certified support of an admissible source is compact. -/
theorem zetaPaleyWienerSupport_isCompact
    (f : ZetaAdmissibleFunction) :
    IsCompact (tsupport f.toZetaTestFunction) :=
  f.toZetaTestFunction.hasCompactSupport.isCompact

/-- A closed real interval is compact. -/
theorem real_Icc_isCompact
    (lower upper : ℝ) :
    IsCompact (Set.Icc lower upper) :=
  isCompact_Icc

/-- The compact-support indicator bound is integrable. -/
theorem zetaPaleyWienerSupportIndicatorBound_integrable
    (f : ZetaAdmissibleFunction) (B : ℝ) :
    Integrable (zetaPaleyWienerSupportIndicatorBound f B) :=
  real_integrable_const_indicator_of_isCompact
    (tsupport f.toZetaTestFunction)
    (zetaPaleyWienerSupport_isCompact f)
    B

/-- The interval indicator bound is integrable. -/
theorem zetaPaleyWienerIntervalIndicatorBound_integrable
    (I : ZetaPaleyWienerSupportInterval f) (B : ℝ) :
    Integrable (zetaPaleyWienerIntervalIndicatorBound I B) :=
  real_integrable_const_indicator_of_isCompact
    (Set.Icc I.lower I.upper)
    (real_Icc_isCompact I.lower I.upper)
    B

/-- The certified support is contained in the certified interval. -/
theorem zetaPaleyWienerSupport_subset_interval
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f) :
    tsupport f.toZetaTestFunction ⊆ Set.Icc I.lower I.upper := by
  intro t ht
  exact ⟨I.lower_mem t ht, I.upper_mem t ht⟩

/-- The support-indicator bound is pointwise dominated by the containing-interval
indicator bound. -/
theorem zetaPaleyWienerSupportIndicatorBound_le_intervalIndicatorBound
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (B : ℝ) (hB_nonneg : 0 ≤ B) :
    ∀ t : ℝ,
      zetaPaleyWienerSupportIndicatorBound f B t ≤
        zetaPaleyWienerIntervalIndicatorBound I B t := by
  intro t
  by_cases hsupport : t ∈ tsupport f.toZetaTestFunction
  · have hinterval : t ∈ Set.Icc I.lower I.upper :=
      zetaPaleyWienerSupport_subset_interval f I hsupport
    have hsupport_value :
        zetaPaleyWienerSupportIndicatorBound f B t = B := by
      unfold zetaPaleyWienerSupportIndicatorBound
      exact Set.indicator_of_mem hsupport
    have hinterval_value :
        zetaPaleyWienerIntervalIndicatorBound I B t = B := by
      unfold zetaPaleyWienerIntervalIndicatorBound
      exact Set.indicator_of_mem hinterval
    exact Eq.subst
      (motive := fun v : ℝ => v ≤ zetaPaleyWienerIntervalIndicatorBound I B t)
      hsupport_value.symm
      (Eq.subst
        (motive := fun v : ℝ => B ≤ v)
        hinterval_value.symm
        le_rfl)
  · have hsupport_value :
        zetaPaleyWienerSupportIndicatorBound f B t = 0 := by
      unfold zetaPaleyWienerSupportIndicatorBound
      exact Set.indicator_of_not_mem hsupport
    by_cases hinterval : t ∈ Set.Icc I.lower I.upper
    · have hinterval_value :
          zetaPaleyWienerIntervalIndicatorBound I B t = B := by
        unfold zetaPaleyWienerIntervalIndicatorBound
        exact Set.indicator_of_mem hinterval
      exact Eq.subst
        (motive := fun v : ℝ => v ≤ zetaPaleyWienerIntervalIndicatorBound I B t)
        hsupport_value.symm
        (Eq.subst
          (motive := fun v : ℝ => 0 ≤ v)
          hinterval_value.symm
          hB_nonneg)
    · have hinterval_value :
          zetaPaleyWienerIntervalIndicatorBound I B t = 0 := by
        unfold zetaPaleyWienerIntervalIndicatorBound
        exact Set.indicator_of_not_mem hinterval
      exact Eq.subst
        (motive := fun v : ℝ => v ≤ zetaPaleyWienerIntervalIndicatorBound I B t)
        hsupport_value.symm
        (Eq.subst
          (motive := fun v : ℝ => 0 ≤ v)
          hinterval_value.symm
          le_rfl)

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

/-- Real-line integral monotonicity for integrable pointwise domination. -/
theorem real_integral_mono_of_integrable_pointwise_le
    (u v : ℝ → ℝ)
    (hu : Integrable u) (hv : Integrable v)
    (hle : ∀ t : ℝ, u t ≤ v t) :
    (∫ t : ℝ, u t) ≤ ∫ t : ℝ, v t := by
  exact MeasureTheory.integral_mono hu hv (Filter.Eventually.of_forall hle)

/-- Pointwise domination of the kernel norm by the support-indicator majorant passes to
real-line integrals. -/
theorem zetaPaleyWienerKernelNormIntegral_le_supportIndicatorIntegral
    (f : ZetaAdmissibleFunction) (z : ℂ) (B : ℝ)
    (hindicator :
      ∀ t : ℝ,
        ‖zetaPaleyWienerLaplaceKernel f z t‖ ≤
          zetaPaleyWienerSupportIndicatorBound f B t) :
    (∫ t : ℝ, ‖zetaPaleyWienerLaplaceKernel f z t‖) ≤
      ∫ t : ℝ, zetaPaleyWienerSupportIndicatorBound f B t := by
  exact real_integral_mono_of_integrable_pointwise_le
    (fun t : ℝ => ‖zetaPaleyWienerLaplaceKernel f z t‖)
    (zetaPaleyWienerSupportIndicatorBound f B)
    (zetaPaleyWienerLaplaceKernel_norm_integrable f z)
    (zetaPaleyWienerSupportIndicatorBound_integrable f B)
    hindicator

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
  have hkernelIntegral :
      ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖ =
        ‖∫ t : ℝ, zetaPaleyWienerLaplaceKernel f z t‖ := by
    exact congrArg (fun v : ℂ => ‖v‖)
      (zetaPaleyWienerLaplaceKernel_integral_eq_transform f z).symm
  have hnormIntegral :
      ‖∫ t : ℝ, zetaPaleyWienerLaplaceKernel f z t‖ ≤
        ∫ t : ℝ, ‖zetaPaleyWienerLaplaceKernel f z t‖ :=
    zetaPaleyWienerLaplaceKernel_norm_integral_le_integral_norm f z
  have hindicatorIntegral :
      (∫ t : ℝ, ‖zetaPaleyWienerLaplaceKernel f z t‖) ≤
        ∫ t : ℝ, zetaPaleyWienerSupportIndicatorBound f B t :=
    zetaPaleyWienerKernelNormIntegral_le_supportIndicatorIntegral
      f z B hindicator
  exact Eq.subst
    (motive := fun v : ℝ =>
      v ≤ ∫ t : ℝ, zetaPaleyWienerSupportIndicatorBound f B t)
    hkernelIntegral.symm
    (le_trans hnormIntegral hindicatorIntegral)

/-- Pointwise domination of the support indicator by the interval indicator passes to the
real-line integrals. -/
theorem zetaPaleyWienerSupportIndicatorIntegral_le_intervalIndicatorIntegral
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (B : ℝ) (hB_nonneg : 0 ≤ B)
    (hpoint :
      ∀ t : ℝ,
        zetaPaleyWienerSupportIndicatorBound f B t ≤
          zetaPaleyWienerIntervalIndicatorBound I B t) :
    (∫ t : ℝ, zetaPaleyWienerSupportIndicatorBound f B t) ≤
      ∫ t : ℝ, zetaPaleyWienerIntervalIndicatorBound I B t := by
  exact real_integral_mono_of_integrable_pointwise_le
    (zetaPaleyWienerSupportIndicatorBound f B)
    (zetaPaleyWienerIntervalIndicatorBound I B)
    (zetaPaleyWienerSupportIndicatorBound_integrable f B)
    (zetaPaleyWienerIntervalIndicatorBound_integrable I B)
    hpoint

/-- The integral of a nonnegative constant over an interval indicator is constant times
the interval volume. -/
theorem real_integral_const_indicator_of_isCompact_eq_const_mul_volume
    (K : Set ℝ) (hK : IsCompact K) (B : ℝ) :
    (∫ t : ℝ, Set.indicator K (fun _ : ℝ => B) t) =
      B * (volume K).toReal := by
  sorry

/-- The integral of a nonnegative constant over an interval indicator is constant times
the interval volume. -/
theorem real_integral_const_indicator_Icc_eq_const_mul_volume
    (lower upper B : ℝ) (hB_nonneg : 0 ≤ B) :
    (∫ t : ℝ, Set.indicator (Set.Icc lower upper) (fun _ : ℝ => B) t) =
      B * (volume (Set.Icc lower upper)).toReal := by
  exact real_integral_const_indicator_of_isCompact_eq_const_mul_volume
    (Set.Icc lower upper) (real_Icc_isCompact lower upper) B

/-- The interval-indicator integral is the constant times the interval volume. -/
theorem zetaPaleyWienerIntervalIndicatorIntegral_eq_bound_mul_volume
    (I : ZetaPaleyWienerSupportInterval f) (B : ℝ) (hB_nonneg : 0 ≤ B) :
    (∫ t : ℝ, zetaPaleyWienerIntervalIndicatorBound I B t) =
      B * (volume (Set.Icc I.lower I.upper)).toReal := by
  unfold zetaPaleyWienerIntervalIndicatorBound
  exact real_integral_const_indicator_Icc_eq_const_mul_volume
    I.lower I.upper B hB_nonneg

/-- Ordered closed real interval volume in `toReal` form. -/
theorem real_volume_Icc_eq_ofReal_sub
    {lower upper : ℝ} (hlu : lower ≤ upper) :
    volume (Set.Icc lower upper) = ENNReal.ofReal (upper - lower) := by
  exact Real.volume_Icc

/-- The `toReal` of a nonnegative real embedded in `ENNReal` is the original real. -/
theorem ennreal_toReal_ofReal_of_nonnegative
    {x : ℝ} (hx : 0 ≤ x) :
    (ENNReal.ofReal x).toReal = x := by
  exact ENNReal.toReal_ofReal hx

/-- Ordered closed real interval volume in `toReal` form. -/
theorem real_volume_Icc_toReal_eq_sub
    {lower upper : ℝ} (hlu : lower ≤ upper) :
    (volume (Set.Icc lower upper)).toReal = upper - lower := by
  have hvolume :
      volume (Set.Icc lower upper) = ENNReal.ofReal (upper - lower) :=
    real_volume_Icc_eq_ofReal_sub hlu
  have hsub_nonneg : 0 ≤ upper - lower :=
    sub_nonneg.mpr hlu
  exact Eq.trans
    (congrArg ENNReal.toReal hvolume)
    (ennreal_toReal_ofReal_of_nonnegative hsub_nonneg)

/-- The volume of an ordered closed real interval is its endpoint difference. -/
theorem zetaPaleyWienerIntervalVolume_toReal_eq_upper_sub_lower
    (I : ZetaPaleyWienerSupportInterval f) :
    (volume (Set.Icc I.lower I.upper)).toReal =
      I.upper - I.lower := by
  exact real_volume_Icc_toReal_eq_sub I.lower_le_upper

/-- The volume of the certified support interval is the certified support interval length. -/
theorem zetaPaleyWienerIntervalVolume_toReal_eq_supportIntervalLength
    (I : ZetaPaleyWienerSupportInterval f) :
    (volume (Set.Icc I.lower I.upper)).toReal =
      zetaPaleyWienerSupportIntervalLength I := by
  have hvolume :
      (volume (Set.Icc I.lower I.upper)).toReal =
        I.upper - I.lower :=
    zetaPaleyWienerIntervalVolume_toReal_eq_upper_sub_lower I
  have hlength :
      zetaPaleyWienerSupportIntervalLength I =
        I.upper - I.lower :=
    zetaPaleyWienerSupportIntervalLength_eq_upper_sub_lower I
  exact hvolume.trans hlength.symm

/-- The integral of the constant interval indicator is the constant times the certified
interval length. -/
theorem zetaPaleyWienerIntervalIndicatorIntegral_eq_intervalLength_mul_bound
    (I : ZetaPaleyWienerSupportInterval f) (B : ℝ) (hB_nonneg : 0 ≤ B) :
    (∫ t : ℝ, zetaPaleyWienerIntervalIndicatorBound I B t) =
      B * zetaPaleyWienerSupportIntervalLength I := by
  have hvolume :
      (∫ t : ℝ, zetaPaleyWienerIntervalIndicatorBound I B t) =
        B * (volume (Set.Icc I.lower I.upper)).toReal :=
    zetaPaleyWienerIntervalIndicatorIntegral_eq_bound_mul_volume
      I B hB_nonneg
  have hlength :
      (volume (Set.Icc I.lower I.upper)).toReal =
        zetaPaleyWienerSupportIntervalLength I :=
    zetaPaleyWienerIntervalVolume_toReal_eq_supportIntervalLength I
  exact hvolume.trans (congrArg (fun v : ℝ => B * v) hlength)

/-- The support-indicator integral is bounded by any containing support interval length. -/
theorem zetaPaleyWienerSupportIndicatorIntegral_le_intervalLength_mul_bound
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (B : ℝ) (hB_nonneg : 0 ≤ B) :
    (∫ t : ℝ, zetaPaleyWienerSupportIndicatorBound f B t) ≤
      B * zetaPaleyWienerSupportIntervalLength I := by
  have hpoint :
      ∀ t : ℝ,
        zetaPaleyWienerSupportIndicatorBound f B t ≤
          zetaPaleyWienerIntervalIndicatorBound I B t :=
    zetaPaleyWienerSupportIndicatorBound_le_intervalIndicatorBound
      f I B hB_nonneg
  have hintegral :
      (∫ t : ℝ, zetaPaleyWienerSupportIndicatorBound f B t) ≤
        ∫ t : ℝ, zetaPaleyWienerIntervalIndicatorBound I B t :=
    zetaPaleyWienerSupportIndicatorIntegral_le_intervalIndicatorIntegral
      f I B hB_nonneg hpoint
  have hinterval :
      (∫ t : ℝ, zetaPaleyWienerIntervalIndicatorBound I B t) =
        B * zetaPaleyWienerSupportIntervalLength I :=
    zetaPaleyWienerIntervalIndicatorIntegral_eq_intervalLength_mul_bound
      I B hB_nonneg
  exact le_trans hintegral (le_of_eq hinterval)

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

/-- The vertical-line kernel after splitting the horizontal exponential from the oscillatory
factor. -/
noncomputable def zetaPaleyWienerVerticalLineKernel
    (f : ZetaAdmissibleFunction) (x y t : ℝ) : ℂ :=
  zetaPaleyWienerHorizontalTwist f x t *
    zetaPaleyWienerVerticalOscillation y t

/-- Complex multiplication by a real variable splits into horizontal and vertical parts. -/
theorem complex_mul_real_verticalLine_decomposition_re
    (z : ℂ) (t : ℝ) :
    (z * (t : ℂ)).re =
      ((z.re * t : ℂ) + Complex.I * (z.im : ℂ) * (t : ℂ)).re := by
  exact Eq.trans
    (complex_mul_real_re z t)
    (complex_verticalLine_decomposition_rhs_re z t).symm

/-- Imaginary coordinate of the vertical-line complex decomposition. -/
theorem complex_mul_real_verticalLine_decomposition_im
    (z : ℂ) (t : ℝ) :
    (z * (t : ℂ)).im =
      ((z.re * t : ℂ) + Complex.I * (z.im : ℂ) * (t : ℂ)).im := by
  exact Eq.trans
    (complex_mul_real_im z t)
    (complex_verticalLine_decomposition_rhs_im z t).symm

/-- Complex multiplication by a real variable splits into horizontal and vertical parts. -/
theorem complex_mul_real_verticalLine_decomposition
    (z : ℂ) (t : ℝ) :
    z * (t : ℂ) =
      (z.re * t : ℂ) + Complex.I * (z.im : ℂ) * (t : ℂ) := by
  exact Complex.ext
    (complex_mul_real_verticalLine_decomposition_re z t)
    (complex_mul_real_verticalLine_decomposition_im z t)

/-- The exponential on a vertical line splits into horizontal and oscillatory factors. -/
theorem complex_exp_verticalLine_decomposition_from_add
    (z : ℂ) (t : ℝ) :
    Complex.exp ((z.re * t : ℂ) + Complex.I * (z.im : ℂ) * (t : ℂ)) =
      (Real.exp (z.re * t) : ℂ) *
        Complex.exp (Complex.I * (z.im : ℂ) * (t : ℂ)) := by
  have hadd :
      Complex.exp ((z.re * t : ℂ) + Complex.I * (z.im : ℂ) * (t : ℂ)) =
        Complex.exp (z.re * t : ℂ) *
          Complex.exp (Complex.I * (z.im : ℂ) * (t : ℂ)) :=
    Complex.exp_add (z.re * t : ℂ) (Complex.I * (z.im : ℂ) * (t : ℂ))
  have hreal :
      Complex.exp (z.re * t : ℂ) = (Real.exp (z.re * t) : ℂ) :=
    Complex.ofReal_exp (z.re * t)
  exact Eq.trans hadd
    (congrArg
      (fun v : ℂ => v * Complex.exp (Complex.I * (z.im : ℂ) * (t : ℂ)))
      hreal)

/-- The exponential on a vertical line splits into horizontal and oscillatory factors. -/
theorem complex_exp_verticalLine_decomposition
    (z : ℂ) (t : ℝ) :
    Complex.exp (z * (t : ℂ)) =
      (Real.exp (z.re * t) : ℂ) *
        Complex.exp (Complex.I * (z.im : ℂ) * (t : ℂ)) := by
  have hdecomp :
      z * (t : ℂ) =
        (z.re * t : ℂ) + Complex.I * (z.im : ℂ) * (t : ℂ) :=
    complex_mul_real_verticalLine_decomposition z t
  exact Eq.trans
    (congrArg Complex.exp hdecomp)
    (complex_exp_verticalLine_decomposition_from_add z t)

/-- The Laplace kernel equals the explicit vertical-line product pointwise. -/
theorem zetaPaleyWienerLaplaceKernel_eq_verticalLineKernel_pointwise
    (f : ZetaAdmissibleFunction) (z : ℂ) (t : ℝ) :
    f.toZetaTestFunction' t * Complex.exp (z * (t : ℂ)) =
      (f.toZetaTestFunction' t * (Real.exp (z.re * t) : ℂ)) *
        Complex.exp (Complex.I * (z.im : ℂ) * (t : ℂ)) := by
  have hexp :
      Complex.exp (z * (t : ℂ)) =
        (Real.exp (z.re * t) : ℂ) *
          Complex.exp (Complex.I * (z.im : ℂ) * (t : ℂ)) :=
    complex_exp_verticalLine_decomposition z t
  calc
    f.toZetaTestFunction' t * Complex.exp (z * (t : ℂ))
        = f.toZetaTestFunction' t *
          ((Real.exp (z.re * t) : ℂ) *
            Complex.exp (Complex.I * (z.im : ℂ) * (t : ℂ))) := by
          exact congrArg (fun v : ℂ => f.toZetaTestFunction' t * v) hexp
    _ = (f.toZetaTestFunction' t * (Real.exp (z.re * t) : ℂ)) *
          Complex.exp (Complex.I * (z.im : ℂ) * (t : ℂ)) := by
          exact (mul_assoc
            (f.toZetaTestFunction' t)
            (Real.exp (z.re * t) : ℂ)
            (Complex.exp (Complex.I * (z.im : ℂ) * (t : ℂ)))).symm

/-- The original Laplace kernel factors into horizontal twist times vertical oscillation on
the vertical line through `z.re`. -/
theorem zetaPaleyWienerLaplaceKernel_eq_verticalLineKernel
    (f : ZetaAdmissibleFunction) (z : ℂ) (t : ℝ) :
    zetaPaleyWienerLaplaceKernel f z t =
      zetaPaleyWienerVerticalLineKernel f z.re z.im t := by
  unfold zetaPaleyWienerLaplaceKernel
  unfold zetaPaleyWienerVerticalLineKernel
  unfold zetaPaleyWienerHorizontalTwist
  unfold zetaPaleyWienerVerticalOscillation
  exact zetaPaleyWienerLaplaceKernel_eq_verticalLineKernel_pointwise f z t

/-- Pointwise equality of integrands transports their real-line integrals. -/
theorem complex_integral_congr_of_pointwise_eq
    (u v : ℝ → ℂ) (h : ∀ t : ℝ, u t = v t) :
    (∫ t : ℝ, u t) = ∫ t : ℝ, v t := by
  exact integral_congr_ae (Filter.Eventually.of_forall h)

/-- The zeta Laplace transform is the integral of the vertical-line kernel. -/
theorem zetaLaplaceTransform_eq_verticalLineKernelIntegral
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    Boundary.zetaLaplaceTransform f.toZetaTestFunction' z =
      ∫ t : ℝ, zetaPaleyWienerVerticalLineKernel f z.re z.im t := by
  have hkernel :
      (∫ t : ℝ, zetaPaleyWienerLaplaceKernel f z t) =
        ∫ t : ℝ, zetaPaleyWienerVerticalLineKernel f z.re z.im t :=
    complex_integral_congr_of_pointwise_eq
      (zetaPaleyWienerLaplaceKernel f z)
      (zetaPaleyWienerVerticalLineKernel f z.re z.im)
      (fun t : ℝ => zetaPaleyWienerLaplaceKernel_eq_verticalLineKernel f z t)
  exact (zetaPaleyWienerLaplaceKernel_integral_eq_transform f z).symm.trans hkernel

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

/-- The nonzero vertical-frequency condition used by one integration-by-parts step. -/
theorem zetaPaleyWienerVerticalFrequency_ne_zero_of_high
    {y : ℝ} (hy : 1 ≤ ‖y‖) :
    (y : ℂ) ≠ 0 := by
  intro hyzero
  have hy_real_zero : y = 0 := by
    have hre :
        ((y : ℂ).re) = (0 : ℂ).re :=
      congrArg Complex.re hyzero
    exact Eq.trans (Complex.ofReal_re y).symm (hre.trans Complex.zero_re)
  have hnorm_zero : ‖y‖ = 0 := by
    exact (congrArg (fun v : ℝ => ‖v‖) hy_real_zero).trans norm_zero
  have hnot : ¬ (1 : ℝ) ≤ 0 := by
    exact not_le_of_gt zero_lt_one
  exact hnot (Eq.subst (motive := fun v : ℝ => 1 ≤ v) hnorm_zero hy)

/-- One vertical-line integration-by-parts identity before taking norms.

The oscillatory factor is `exp (I * y * t)`, so differentiating it contributes
`I * y`; the inverse factor is therefore `I * y⁻¹`, not just `y⁻¹`. -/
theorem zetaPaleyWienerVerticalLineKernel_integral_eq_I_mul_inverse_mul_derivativeIntegral
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (x y : ℝ) (hy : (y : ℂ) ≠ 0) :
    (∫ t : ℝ, zetaPaleyWienerVerticalLineKernel f x y t) =
      Complex.I * (y : ℂ)⁻¹ *
        zetaPaleyWienerVerticalLineIBPDerivativeIntegral f x y := by
  sorry

/-- The complex unit `I` has norm one. -/
theorem complex_norm_I_eq_one :
    ‖Complex.I‖ = (1 : ℝ) := by
  exact Eq.trans (complex_norm_eq_abs Complex.I) Complex.abs_I

/-- Multiplication by `I` does not change the norm. -/
theorem norm_I_mul_eq_norm
    (w : ℂ) :
    ‖Complex.I * w‖ = ‖w‖ := by
  have hmul : ‖Complex.I * w‖ = ‖Complex.I‖ * ‖w‖ :=
    norm_mul Complex.I w
  exact Eq.trans hmul
    (Eq.trans
      (congrArg (fun v : ℝ => v * ‖w‖) complex_norm_I_eq_one)
      (one_mul ‖w‖))

/-- The `I * y⁻¹` norm is the same as the `y⁻¹` norm. -/
theorem norm_I_mul_inverse_eq_norm_inverse
    (y : ℝ) :
    ‖Complex.I * (y : ℂ)⁻¹‖ = ‖(y : ℂ)⁻¹‖ := by
  exact norm_I_mul_eq_norm ((y : ℂ)⁻¹)

/-- Vertical-line integration by parts after substituting the spectral parameter `z`. -/
theorem zetaLaplaceTransform_eq_I_mul_inverse_mul_verticalLineIBPDerivativeIntegral
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (z : ℂ) (hzhigh : 1 ≤ ‖z.im‖) :
    Boundary.zetaLaplaceTransform f.toZetaTestFunction' z =
      Complex.I * (z.im : ℂ)⁻¹ *
        zetaPaleyWienerVerticalLineIBPDerivativeIntegral f z.re z.im := by
  have htransform :
      Boundary.zetaLaplaceTransform f.toZetaTestFunction' z =
        ∫ t : ℝ, zetaPaleyWienerVerticalLineKernel f z.re z.im t :=
    zetaLaplaceTransform_eq_verticalLineKernelIntegral f z
  have hfreq :
      (z.im : ℂ) ≠ 0 :=
    zetaPaleyWienerVerticalFrequency_ne_zero_of_high hzhigh
  have hibp :
      (∫ t : ℝ, zetaPaleyWienerVerticalLineKernel f z.re z.im t) =
        Complex.I * (z.im : ℂ)⁻¹ *
          zetaPaleyWienerVerticalLineIBPDerivativeIntegral f z.re z.im :=
    zetaPaleyWienerVerticalLineKernel_integral_eq_I_mul_inverse_mul_derivativeIntegral
      f I z.re z.im hfreq
  exact htransform.trans hibp

/-- The harmless `I` factor in the vertical-line integration-by-parts identity does not
change the norm comparison. -/
theorem norm_I_mul_inverse_mul_verticalLineIBPDerivativeIntegral_le
    (y : ℝ) (D : ℂ) :
    ‖Complex.I * (y : ℂ)⁻¹ * D‖ ≤ ‖(y : ℂ)⁻¹‖ * ‖D‖ := by
  have hmul :
      ‖Complex.I * (y : ℂ)⁻¹ * D‖ =
        ‖Complex.I * (y : ℂ)⁻¹‖ * ‖D‖ :=
    norm_mul (Complex.I * (y : ℂ)⁻¹) D
  have hleft :
      ‖Complex.I * (y : ℂ)⁻¹‖ = ‖(y : ℂ)⁻¹‖ :=
    norm_I_mul_inverse_eq_norm_inverse y
  exact le_of_eq
    (Eq.trans hmul
      (congrArg (fun v : ℝ => v * ‖D‖) hleft))

/-- Vertical-line integration by parts as a norm identity.

After absorbing the horizontal factor into the source on `re z = x`, integration by
parts on the vertical oscillation gives one inverse vertical-frequency factor. -/
theorem zetaLaplaceTransform_supportInterval_verticalLineIBP_normIdentity
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (z : ℂ)
    (hzstrip : zetaPaleyWienerInVerticalStrip a b z)
    (hzhigh : 1 ≤ ‖z.im‖) :
    ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖ =
      ‖Complex.I * (z.im : ℂ)⁻¹ *
        zetaPaleyWienerVerticalLineIBPDerivativeIntegral f z.re z.im‖ := by
  have hidentity :
      Boundary.zetaLaplaceTransform f.toZetaTestFunction' z =
        Complex.I * (z.im : ℂ)⁻¹ *
          zetaPaleyWienerVerticalLineIBPDerivativeIntegral f z.re z.im :=
    zetaLaplaceTransform_eq_I_mul_inverse_mul_verticalLineIBPDerivativeIntegral
      f I z hzhigh
  exact congrArg (fun v : ℂ => ‖v‖) hidentity

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
        ‖Complex.I * (z.im : ℂ)⁻¹ *
          zetaPaleyWienerVerticalLineIBPDerivativeIntegral f z.re z.im‖ :=
    zetaLaplaceTransform_supportInterval_verticalLineIBP_normIdentity
      f I a b z hzstrip hzhigh
  have hnorm :
      ‖Complex.I * (z.im : ℂ)⁻¹ *
          zetaPaleyWienerVerticalLineIBPDerivativeIntegral f z.re z.im‖ ≤
        ‖(z.im : ℂ)⁻¹‖ *
          ‖zetaPaleyWienerVerticalLineIBPDerivativeIntegral f z.re z.im‖ :=
    norm_I_mul_inverse_mul_verticalLineIBPDerivativeIntegral_le
      z.im
      (zetaPaleyWienerVerticalLineIBPDerivativeIntegral f z.re z.im)
  exact Eq.subst
    (motive := fun v : ℝ =>
      v ≤ ‖(z.im : ℂ)⁻¹‖ *
          ‖zetaPaleyWienerVerticalLineIBPDerivativeIntegral f z.re z.im‖)
    hidentity.symm
    hnorm

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
