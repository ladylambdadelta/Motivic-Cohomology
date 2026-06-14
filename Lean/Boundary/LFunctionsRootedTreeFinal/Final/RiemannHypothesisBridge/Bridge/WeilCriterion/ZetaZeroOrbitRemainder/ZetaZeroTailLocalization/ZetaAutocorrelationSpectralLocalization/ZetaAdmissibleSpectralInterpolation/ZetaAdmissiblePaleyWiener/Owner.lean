import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaTransformCalculusWeighted.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissibleInterpolation.ZetaAdmissibleProbe.Owner
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

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
theorem real_integral_const_indicator_eq_setIntegral_const
    (K : Set ℝ) (hK : MeasurableSet K) (B : ℝ) :
    (∫ t : ℝ, Set.indicator K (fun _ : ℝ => B) t) =
      ∫ t in K, B := by
  exact integral_indicator hK

/-- The set integral of a real constant is the constant times the set volume. -/
theorem real_setIntegral_const_eq_const_mul_volume
    (K : Set ℝ) (B : ℝ) :
    (∫ t in K, B) = B * (volume K).toReal := by
  calc
    (∫ t in K, B) = (volume K).toReal • B := by
      exact integral_const B
    _ = (volume K).toReal * B := by
      rfl
    _ = B * (volume K).toReal := by
      exact mul_comm (volume K).toReal B

/-- The integral of a constant over a compact-set indicator is constant times volume. -/
theorem real_integral_const_indicator_of_isCompact_eq_const_mul_volume
    (K : Set ℝ) (hK : IsCompact K) (B : ℝ) :
    (∫ t : ℝ, Set.indicator K (fun _ : ℝ => B) t) =
      B * (volume K).toReal := by
  exact Eq.trans
    (real_integral_const_indicator_eq_setIntegral_const
      K hK.isClosed.measurableSet B)
    (real_setIntegral_const_eq_const_mul_volume K B)

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

/-- The horizontal twist is smooth in the physical variable. -/
theorem zetaPaleyWienerHorizontalTwist_contDiff
    (f : ZetaAdmissibleFunction) (x : ℝ) :
    ContDiff ℝ ∞ (fun t : ℝ => zetaPaleyWienerHorizontalTwist f x t) := by
  have hsource :
      ContDiff ℝ ∞ (fun t : ℝ => f.toZetaTestFunction' t) := by
    exact f.smooth
  have hlinear :
      ContDiff ℝ ∞ (fun t : ℝ => x * t) :=
    contDiff_const.mul contDiff_id
  have hexp_real :
      ContDiff ℝ ∞ (fun t : ℝ => Real.exp (x * t)) :=
    Real.contDiff_exp.comp hlinear
  have hexp_complex :
      ContDiff ℝ ∞ (fun t : ℝ => (Real.exp (x * t) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hexp_real
  unfold zetaPaleyWienerHorizontalTwist
  exact hsource.mul hexp_complex

/-- The horizontal twist has compact support because the admissible source has compact
support. -/
theorem zetaPaleyWienerHorizontalTwist_hasCompactSupport
    (f : ZetaAdmissibleFunction) (x : ℝ) :
    HasCompactSupport (fun t : ℝ => zetaPaleyWienerHorizontalTwist f x t) := by
  unfold zetaPaleyWienerHorizontalTwist
  exact f.toZetaTestFunction.hasCompactSupport.mul_right

/-- The horizontal twist is continuous in the physical variable. -/
theorem zetaPaleyWienerHorizontalTwist_continuous
    (f : ZetaAdmissibleFunction) (x : ℝ) :
    Continuous (fun t : ℝ => zetaPaleyWienerHorizontalTwist f x t) := by
  exact (zetaPaleyWienerHorizontalTwist_contDiff f x).continuous

/-- The compact parameter-support rectangle used for uniform Paley-Wiener seminorms. -/
def zetaPaleyWienerParameterSupportRectangle
    (I : ZetaPaleyWienerSupportInterval f) (a b : ℝ) : Set (ℝ × ℝ) :=
  Set.Icc a b ×ˢ Set.Icc I.lower I.upper

/-- Membership in the Paley-Wiener parameter-support rectangle is exactly the four endpoint
inequalities. -/
theorem zetaPaleyWienerParameterSupportRectangle_mem
    (I : ZetaPaleyWienerSupportInterval f) (a b : ℝ) (p : ℝ × ℝ) :
    p ∈ zetaPaleyWienerParameterSupportRectangle I a b ↔
      a ≤ p.1 ∧ p.1 ≤ b ∧ I.lower ≤ p.2 ∧ p.2 ≤ I.upper := by
  constructor
  · intro hp
    exact ⟨hp.1.1, hp.1.2, hp.2.1, hp.2.2⟩
  · intro hp
    exact ⟨⟨hp.1, hp.2.1⟩, ⟨hp.2.2.1, hp.2.2.2⟩⟩

/-- The parameter-support rectangle is compact. -/
theorem zetaPaleyWienerParameterSupportRectangle_isCompact
    (I : ZetaPaleyWienerSupportInterval f) (a b : ℝ) :
    IsCompact (zetaPaleyWienerParameterSupportRectangle I a b) := by
  exact isCompact_Icc.prod isCompact_Icc

/-- The two-variable horizontal twist whose vertical-direction jets encode the repeated
integration-by-parts sources. -/
noncomputable def zetaPaleyWienerHorizontalTwistParameter
    (f : ZetaAdmissibleFunction) (p : ℝ × ℝ) : ℂ :=
  zetaPaleyWienerHorizontalTwist f p.1 p.2

/-- The vertical affine line through horizontal coordinate `x` in the parameter plane. -/
def zetaPaleyWienerVerticalLineEmbedding (x : ℝ) (t : ℝ) : ℝ × ℝ :=
  (x, t)

/-- The vertical affine line through `x` is smooth as a map from the physical line to the
parameter plane. -/
theorem zetaPaleyWienerVerticalLineEmbedding_contDiff
    (x : ℝ) :
    ContDiff ℝ ∞ (zetaPaleyWienerVerticalLineEmbedding x) := by
  unfold zetaPaleyWienerVerticalLineEmbedding
  exact contDiff_const.prod contDiff_id

/-- The parameter twist restricted to the vertical line through `x` is the horizontal twist. -/
theorem zetaPaleyWienerHorizontalTwistParameter_verticalLine
    (f : ZetaAdmissibleFunction) (x t : ℝ) :
    zetaPaleyWienerHorizontalTwistParameter f
        (zetaPaleyWienerVerticalLineEmbedding x t) =
      zetaPaleyWienerHorizontalTwist f x t := by
  rfl

/-- The vertical tangent direction in the `(x,t)` parameter plane. -/
def zetaPaleyWienerVerticalParameterDirection : ℝ × ℝ :=
  (0, 1)

/-- The linear part of the vertical affine line in the parameter plane. -/
def zetaPaleyWienerVerticalLinearEmbedding : ℝ →L[ℝ] ℝ × ℝ :=
  (0 : ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℝ)

/-- The vertical linear embedding sends the scalar tangent `1` to the vertical direction. -/
theorem zetaPaleyWienerVerticalLinearEmbedding_one :
    zetaPaleyWienerVerticalLinearEmbedding 1 =
      zetaPaleyWienerVerticalParameterDirection := by
  rfl

/-- The vertical affine line is a translation of its linear vertical embedding. -/
theorem zetaPaleyWienerVerticalLineEmbedding_eq_translate_linear
    (x t : ℝ) :
    zetaPaleyWienerVerticalLineEmbedding x t =
      (x, 0) + zetaPaleyWienerVerticalLinearEmbedding t := by
  rfl

/-- The generic vertical-line compatibility theorem at derivative order zero. -/
theorem iteratedDeriv_verticalLine_eq_iteratedFDeriv_verticalDirection_zero
    (F : ℝ × ℝ → ℂ) (x t : ℝ) :
    iteratedDeriv 0 (fun u : ℝ => F (x, u)) t =
      (iteratedFDeriv ℝ 0 F (x, t) :
          (Fin 0 → ℝ × ℝ) → ℂ)
        (fun _ : Fin 0 => zetaPaleyWienerVerticalParameterDirection) := by
  exact Eq.trans
    (congrFun (iteratedDeriv_zero (f := fun u : ℝ => F (x, u))) t)
    (iteratedFDeriv_zero_apply
      (f := F)
      (x := (x, t))
      (m := fun _ : Fin 0 => zetaPaleyWienerVerticalParameterDirection)).symm

/-- Frechet derivatives of the vertical affine restriction are obtained by precomposing the
ambient Frechet derivative with the vertical linear embedding. -/
theorem iteratedFDeriv_verticalLine_eq_comp_verticalLinearEmbedding
    (F : ℝ × ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (n : ℕ) (x t : ℝ) :
    iteratedFDeriv ℝ n (fun u : ℝ => F (x, u)) t =
      (iteratedFDeriv ℝ n F (x, t)).compContinuousLinearMap
        (fun _ : Fin n => zetaPaleyWienerVerticalLinearEmbedding) := by
  let A : ℝ × ℝ := (x, 0)
  let L : ℝ →L[ℝ] ℝ × ℝ := zetaPaleyWienerVerticalLinearEmbedding
  let G : ℝ × ℝ → ℂ := fun p : ℝ × ℝ => F (A + p)
  have hline :
      (fun u : ℝ => F (x, u)) = G ∘ L := by
    funext u
    exact congrArg F (zetaPaleyWienerVerticalLineEmbedding_eq_translate_linear x u)
  have hG :
      ContDiff ℝ ∞ G := by
    exact hF.comp (contDiff_const.add L.contDiff)
  have hcomp :
      iteratedFDeriv ℝ n (G ∘ L) t =
        (iteratedFDeriv ℝ n G (L t)).compContinuousLinearMap
          (fun _ : Fin n => L) :=
    L.iteratedFDeriv_comp_right hG t le_top
  have htranslate :
      iteratedFDeriv ℝ n G (L t) =
        iteratedFDeriv ℝ n F (x, t) := by
    exact iteratedFDeriv_comp_add_left n A (L t)
  exact Eq.subst
    (motive := fun q : ℝ → ℂ =>
      iteratedFDeriv ℝ n q t =
        (iteratedFDeriv ℝ n F (x, t)).compContinuousLinearMap
          (fun _ : Fin n => zetaPaleyWienerVerticalLinearEmbedding))
    hline.symm
    (Eq.subst
      (motive := fun v : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × ℝ) ℂ =>
        iteratedFDeriv ℝ n (G ∘ L) t =
          v.compContinuousLinearMap
            (fun _ : Fin n => zetaPaleyWienerVerticalLinearEmbedding))
      htranslate
      hcomp)

/-- Applying a vertical-line Frechet derivative to scalar unit directions is applying the
ambient Frechet derivative to vertical parameter directions. -/
theorem iteratedFDeriv_verticalLine_apply_ones_eq_verticalDirections
    (F : ℝ × ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (n : ℕ) (x t : ℝ) :
    (iteratedFDeriv ℝ n (fun u : ℝ => F (x, u)) t :
        (Fin n → ℝ) → ℂ)
      (fun _ : Fin n => 1) =
      (iteratedFDeriv ℝ n F (x, t) :
          (Fin n → ℝ × ℝ) → ℂ)
        (fun _ : Fin n => zetaPaleyWienerVerticalParameterDirection) := by
  have hcomp :
      iteratedFDeriv ℝ n (fun u : ℝ => F (x, u)) t =
        (iteratedFDeriv ℝ n F (x, t)).compContinuousLinearMap
          (fun _ : Fin n => zetaPaleyWienerVerticalLinearEmbedding) :=
    iteratedFDeriv_verticalLine_eq_comp_verticalLinearEmbedding F hF n x t
  exact Eq.trans
    (congrArg
      (fun L : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ) ℂ =>
        L (fun _ : Fin n => 1))
      hcomp)
    (congrArg
      (fun m : Fin n → ℝ × ℝ =>
        (iteratedFDeriv ℝ n F (x, t) :
          (Fin n → ℝ × ℝ) → ℂ) m)
      (funext
        (fun _i : Fin n =>
          zetaPaleyWienerVerticalLinearEmbedding_one)))

/-- Generic vertical-line compatibility between one-variable iterated derivatives and
ambient Frechet derivatives evaluated repeatedly on the vertical parameter direction. -/
theorem iteratedDeriv_verticalLine_eq_iteratedFDeriv_verticalDirection_direct
    (F : ℝ × ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (n : ℕ) (x t : ℝ) :
    iteratedDeriv n (fun u : ℝ => F (x, u)) t =
      (iteratedFDeriv ℝ n F (x, t) :
          (Fin n → ℝ × ℝ) → ℂ)
        (fun _ : Fin n => zetaPaleyWienerVerticalParameterDirection) := by
  exact Eq.trans
    (iteratedDeriv_eq_iteratedFDeriv (𝕜 := ℝ) (n := n)
      (f := fun u : ℝ => F (x, u)) (x := t))
    (iteratedFDeriv_verticalLine_apply_ones_eq_verticalDirections
      F hF n x t)

/-- The successor step for generic vertical-line compatibility between one-variable
iterated derivatives and repeated vertical Frechet derivatives. -/
theorem iteratedDeriv_verticalLine_eq_iteratedFDeriv_verticalDirection_succ
    (F : ℝ × ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (n : ℕ)
    (ih :
      ∀ x t : ℝ,
        iteratedDeriv n (fun u : ℝ => F (x, u)) t =
          (iteratedFDeriv ℝ n F (x, t) :
              (Fin n → ℝ × ℝ) → ℂ)
            (fun _ : Fin n => zetaPaleyWienerVerticalParameterDirection))
    (x t : ℝ) :
    iteratedDeriv (Nat.succ n) (fun u : ℝ => F (x, u)) t =
      (iteratedFDeriv ℝ (Nat.succ n) F (x, t) :
          (Fin (Nat.succ n) → ℝ × ℝ) → ℂ)
        (fun _ : Fin (Nat.succ n) => zetaPaleyWienerVerticalParameterDirection) := by
  exact iteratedDeriv_verticalLine_eq_iteratedFDeriv_verticalDirection_direct
    F hF (Nat.succ n) x t

/-- Generic vertical-line compatibility between one-variable iterated derivatives and
iterated Frechet derivatives evaluated on the repeated vertical direction. -/
theorem iteratedDeriv_verticalLine_eq_iteratedFDeriv_verticalDirection
    (F : ℝ × ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (n : ℕ) (x t : ℝ) :
    iteratedDeriv n (fun u : ℝ => F (x, u)) t =
      (iteratedFDeriv ℝ n F (x, t) :
          (Fin n → ℝ × ℝ) → ℂ)
        (fun _ : Fin n => zetaPaleyWienerVerticalParameterDirection) := by
  exact iteratedDeriv_verticalLine_eq_iteratedFDeriv_verticalDirection_direct
    F hF n x t

/-- The canonical two-variable jet of the horizontal twist in the vertical direction. -/
noncomputable def zetaPaleyWienerHorizontalTwistVerticalJet
    (f : ZetaAdmissibleFunction) (n : ℕ) (x t : ℝ) : ℂ :=
  (iteratedFDeriv ℝ n (zetaPaleyWienerHorizontalTwistParameter f) (x, t) :
      (Fin n → ℝ × ℝ) → ℂ)
    (fun _ : Fin n => zetaPaleyWienerVerticalParameterDirection)

/-- The zero-th vertical parameter jet is the horizontal twist itself. -/
theorem zetaPaleyWienerHorizontalTwistVerticalJet_zero
    (f : ZetaAdmissibleFunction) (x t : ℝ) :
    zetaPaleyWienerHorizontalTwistVerticalJet f 0 x t =
      zetaPaleyWienerHorizontalTwist f x t := by
  exact iteratedFDeriv_zero_apply
    (f := zetaPaleyWienerHorizontalTwistParameter f)
    (x := (x, t))
    (m := fun i : Fin 0 => zetaPaleyWienerVerticalParameterDirection)

/-- The horizontal twist is smooth as a two-variable function of `(x,t)`. -/
theorem zetaPaleyWienerHorizontalTwistParameter_contDiff
    (f : ZetaAdmissibleFunction) :
    ContDiff ℝ ∞ (zetaPaleyWienerHorizontalTwistParameter f) := by
  have hsource :
      ContDiff ℝ ∞ (fun p : ℝ × ℝ => f.toZetaTestFunction' p.2) :=
    f.smooth.comp contDiff_snd
  have hmul :
      ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.1 * p.2) :=
    contDiff_fst.mul contDiff_snd
  have hexp_real :
      ContDiff ℝ ∞ (fun p : ℝ × ℝ => Real.exp (p.1 * p.2)) :=
    Real.contDiff_exp.comp hmul
  have hexp_complex :
      ContDiff ℝ ∞ (fun p : ℝ × ℝ => (Real.exp (p.1 * p.2) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hexp_real
  unfold zetaPaleyWienerHorizontalTwistParameter
  unfold zetaPaleyWienerHorizontalTwist
  exact hsource.mul hexp_complex

/-- The parameter twist restricted to a vertical affine line is smooth. -/
theorem zetaPaleyWienerHorizontalTwistParameter_verticalLine_contDiff
    (f : ZetaAdmissibleFunction) (x : ℝ) :
    ContDiff ℝ ∞
      (fun t : ℝ =>
        zetaPaleyWienerHorizontalTwistParameter f
          (zetaPaleyWienerVerticalLineEmbedding x t)) := by
  exact (zetaPaleyWienerHorizontalTwistParameter_contDiff f).comp
    (zetaPaleyWienerVerticalLineEmbedding_contDiff x)

/-- The vertical parameter jet is continuous on the full parameter plane. -/
theorem zetaPaleyWienerHorizontalTwistVerticalJet_continuous
    (f : ZetaAdmissibleFunction) (n : ℕ) :
    Continuous
      (fun p : ℝ × ℝ =>
        zetaPaleyWienerHorizontalTwistVerticalJet f n p.1 p.2) := by
  have hjet :
      Continuous
        (iteratedFDeriv ℝ n (zetaPaleyWienerHorizontalTwistParameter f)) :=
    (zetaPaleyWienerHorizontalTwistParameter_contDiff f).continuous_iteratedFDeriv
      n le_top
  have hdirection :
      Continuous
        (fun _p : ℝ × ℝ =>
          (fun _i : Fin n => zetaPaleyWienerVerticalParameterDirection)) :=
    continuous_const
  unfold zetaPaleyWienerHorizontalTwistVerticalJet
  exact continuous_eval.comp (hjet.prod_mk hdirection)

/-- The vertical parameter jet is smooth on the full parameter plane. -/
theorem zetaPaleyWienerHorizontalTwistVerticalJet_contDiff
    (f : ZetaAdmissibleFunction) (n : ℕ) :
    ContDiff ℝ ∞
      (fun p : ℝ × ℝ =>
        zetaPaleyWienerHorizontalTwistVerticalJet f n p.1 p.2) := by
  have hjet :
      ContDiff ℝ ∞
        (iteratedFDeriv ℝ n (zetaPaleyWienerHorizontalTwistParameter f)) :=
    (zetaPaleyWienerHorizontalTwistParameter_contDiff f).iteratedFDeriv_right
      le_top
  have happly :
      ContDiff ℝ ∞
        (fun L : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × ℝ) ℂ =>
          L (fun _i : Fin n => zetaPaleyWienerVerticalParameterDirection)) := by
    exact (ContinuousMultilinearMap.apply
      ℝ
      (fun _ : Fin n => ℝ × ℝ)
      ℂ
      (fun _i : Fin n => zetaPaleyWienerVerticalParameterDirection)).contDiff
  unfold zetaPaleyWienerHorizontalTwistVerticalJet
  exact happly.comp hjet

/-- The vertical parameter jet is continuous on the compact parameter-support rectangle. -/
theorem zetaPaleyWienerHorizontalTwistVerticalJet_continuousOn_rectangle
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (n : ℕ) :
    ContinuousOn
      (fun p : ℝ × ℝ =>
        zetaPaleyWienerHorizontalTwistVerticalJet f n p.1 p.2)
      (zetaPaleyWienerParameterSupportRectangle I a b) := by
  exact (zetaPaleyWienerHorizontalTwistVerticalJet_continuous f n).continuousOn

/-- Compact-rectangle boundedness for the vertical parameter jet. -/
theorem exists_zetaPaleyWienerHorizontalTwistVerticalJet_rectangleBound
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (n : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ p : ℝ × ℝ,
        p ∈ zetaPaleyWienerParameterSupportRectangle I a b →
        ‖zetaPaleyWienerHorizontalTwistVerticalJet f n p.1 p.2‖ ≤ C := by
  rcases IsCompact.exists_bound_of_continuousOn
      (zetaPaleyWienerParameterSupportRectangle_isCompact I a b)
      (zetaPaleyWienerHorizontalTwistVerticalJet_continuousOn_rectangle
        f I a b n) with
    ⟨C0, hC0⟩
  refine ⟨max C0 0 + 1, weightedLaplaceKernel_positive_bump C0, ?_⟩
  intro p hp
  have hraw :
      ‖zetaPaleyWienerHorizontalTwistVerticalJet f n p.1 p.2‖ ≤ C0 :=
    hC0 p hp
  exact weightedLaplaceKernel_bound_le_bump C0 hraw

/-- Coordinate form of compact-rectangle boundedness for the vertical parameter jet. -/
theorem exists_zetaPaleyWienerHorizontalTwistVerticalJet_intervalBound
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (n : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ x : ℝ,
        a ≤ x →
        x ≤ b →
        ∀ t : ℝ,
          I.lower ≤ t →
          t ≤ I.upper →
          ‖zetaPaleyWienerHorizontalTwistVerticalJet f n x t‖ ≤ C := by
  rcases exists_zetaPaleyWienerHorizontalTwistVerticalJet_rectangleBound
      f I a b n with ⟨C, hCpos, hCbound⟩
  refine ⟨C, hCpos, ?_⟩
  intro x hx_left hx_right t ht_lower ht_upper
  have hp :
      (x, t) ∈ zetaPaleyWienerParameterSupportRectangle I a b := by
    exact ⟨⟨hx_left, hx_right⟩, ⟨ht_lower, ht_upper⟩⟩
  exact hCbound (x, t) hp

/-- A point of the real line is either inside the certified support interval or strictly
outside one of its two sides. -/
theorem zetaPaleyWienerSupportInterval_inside_or_outside
    (I : ZetaPaleyWienerSupportInterval f) (t : ℝ) :
    (I.lower ≤ t ∧ t ≤ I.upper) ∨ t < I.lower ∨ I.upper < t := by
  by_cases ht_lower : I.lower ≤ t
  · by_cases ht_upper : t ≤ I.upper
    · exact Or.inl ⟨ht_lower, ht_upper⟩
    · exact Or.inr (Or.inr (lt_of_not_ge ht_upper))
  · exact Or.inr (Or.inl (lt_of_not_ge ht_lower))

/-- The pure vertical oscillatory kernel on the line `re z = x`. -/
noncomputable def zetaPaleyWienerVerticalOscillation
    (y t : ℝ) : ℂ :=
  Complex.exp (Complex.I * (y : ℂ) * (t : ℂ))

/-- The imaginary vertical phase can be written as a real scalar times `I`. -/
theorem zetaPaleyWienerVerticalPhase_eq_real_mul_I
    (y t : ℝ) :
    Complex.I * (y : ℂ) * (t : ℂ) = ((y * t : ℝ) : ℂ) * Complex.I := by
  calc
    Complex.I * (y : ℂ) * (t : ℂ)
        = ((y : ℂ) * (t : ℂ)) * Complex.I := by
          exact Eq.trans
            (mul_assoc Complex.I (y : ℂ) (t : ℂ))
            (Eq.trans
              (congrArg (fun v : ℂ => Complex.I * v) (mul_comm (y : ℂ) (t : ℂ)))
              (Eq.trans
                (mul_comm Complex.I ((t : ℂ) * (y : ℂ)))
                (congrArg (fun v : ℂ => v * Complex.I) (mul_comm (t : ℂ) (y : ℂ)))))
    _ = ((y * t : ℝ) : ℂ) * Complex.I := by
          exact congrArg
            (fun v : ℂ => v * Complex.I)
            (Complex.ofReal_mul y t).symm

/-- The vertical phase has zero real part. -/
theorem zetaPaleyWienerVerticalPhase_re_zero
    (y t : ℝ) :
    (Complex.I * (y : ℂ) * (t : ℂ)).re = 0 := by
  exact Eq.trans
    (congrArg Complex.re (zetaPaleyWienerVerticalPhase_eq_real_mul_I y t))
    (paley_ofReal_mul_I_re_zero (y * t))

/-- The vertical oscillatory kernel has norm one. -/
theorem zetaPaleyWienerVerticalOscillation_norm_eq_one
    (y t : ℝ) :
    ‖zetaPaleyWienerVerticalOscillation y t‖ = 1 := by
  unfold zetaPaleyWienerVerticalOscillation
  exact Eq.trans
    (complexExp_norm_eq_realExp_re (Complex.I * (y : ℂ) * (t : ℂ)))
    (Eq.trans
      (congrArg Real.exp (zetaPaleyWienerVerticalPhase_re_zero y t))
      Real.exp_zero)

/-- The vertical oscillatory kernel has norm bounded by one. -/
theorem zetaPaleyWienerVerticalOscillation_norm_le_one
    (y t : ℝ) :
    ‖zetaPaleyWienerVerticalOscillation y t‖ ≤ 1 :=
  le_of_eq (zetaPaleyWienerVerticalOscillation_norm_eq_one y t)

/-- Multiplying by the vertical oscillation does not increase a pointwise norm. -/
theorem norm_mul_zetaPaleyWienerVerticalOscillation_le
    (w : ℂ) (y t : ℝ) :
    ‖w * zetaPaleyWienerVerticalOscillation y t‖ ≤ ‖w‖ := by
  have hmul :
      ‖w * zetaPaleyWienerVerticalOscillation y t‖ =
        ‖w‖ * ‖zetaPaleyWienerVerticalOscillation y t‖ :=
    norm_mul w (zetaPaleyWienerVerticalOscillation y t)
  have hosc :
      ‖zetaPaleyWienerVerticalOscillation y t‖ = 1 :=
    zetaPaleyWienerVerticalOscillation_norm_eq_one y t
  exact le_of_eq
    (Eq.trans hmul
      (Eq.trans
        (congrArg (fun v : ℝ => ‖w‖ * v) hosc)
        (mul_one ‖w‖)))

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

/-- The derivative of the horizontal twist is represented by its named derivative source. -/
theorem hasDerivAt_zetaPaleyWienerHorizontalTwist
    (f : ZetaAdmissibleFunction) (x t : ℝ) :
    HasDerivAt
      (fun u : ℝ => zetaPaleyWienerHorizontalTwist f x u)
      (zetaPaleyWienerVerticalLineIBPDerivative f x t)
      t := by
  exact
    ((zetaPaleyWienerHorizontalTwist_contDiff f x).differentiable le_top t).hasDerivAt

/-- The derivative source of the horizontal twist is continuous. -/
theorem zetaPaleyWienerVerticalLineIBPDerivative_continuous
    (f : ZetaAdmissibleFunction) (x : ℝ) :
    Continuous (fun t : ℝ => zetaPaleyWienerVerticalLineIBPDerivative f x t) := by
  unfold zetaPaleyWienerVerticalLineIBPDerivative
  exact (zetaPaleyWienerHorizontalTwist_contDiff f x).continuous_deriv le_top

/-- The derivative source of the horizontal twist has compact support. -/
theorem zetaPaleyWienerVerticalLineIBPDerivative_hasCompactSupport
    (f : ZetaAdmissibleFunction) (x : ℝ) :
    HasCompactSupport (fun t : ℝ => zetaPaleyWienerVerticalLineIBPDerivative f x t) := by
  unfold zetaPaleyWienerVerticalLineIBPDerivative
  exact (zetaPaleyWienerHorizontalTwist_hasCompactSupport f x).deriv

/-- The vertical-line kernel is integrable. -/
theorem zetaPaleyWienerVerticalLineKernel_integrable
    (f : ZetaAdmissibleFunction) (x y : ℝ) :
    Integrable (fun t : ℝ => zetaPaleyWienerVerticalLineKernel f x y t) := by
  have hcontinuous :
      Continuous (fun t : ℝ => zetaPaleyWienerVerticalLineKernel f x y t) := by
    unfold zetaPaleyWienerVerticalLineKernel
    exact (zetaPaleyWienerHorizontalTwist_continuous f x).mul
      (Complex.continuous_exp.comp
        ((continuous_const.mul continuous_const).mul Complex.continuous_ofReal))
  have hsupport :
      HasCompactSupport (fun t : ℝ => zetaPaleyWienerVerticalLineKernel f x y t) := by
    unfold zetaPaleyWienerVerticalLineKernel
    exact (zetaPaleyWienerHorizontalTwist_hasCompactSupport f x).mul_right
  exact hcontinuous.integrable_of_hasCompactSupport hsupport

/-- The transformed derivative source is integrable. -/
theorem zetaPaleyWienerVerticalLineIBPDerivative_integrable
    (f : ZetaAdmissibleFunction) (x y : ℝ) :
    Integrable
      (fun t : ℝ =>
        zetaPaleyWienerVerticalLineIBPDerivative f x t *
          zetaPaleyWienerVerticalOscillation y t) := by
  have hcontinuous :
      Continuous
        (fun t : ℝ =>
          zetaPaleyWienerVerticalLineIBPDerivative f x t *
            zetaPaleyWienerVerticalOscillation y t) := by
    exact (zetaPaleyWienerVerticalLineIBPDerivative_continuous f x).mul
      (Complex.continuous_exp.comp
        ((continuous_const.mul continuous_const).mul Complex.continuous_ofReal))
  have hsupport :
      HasCompactSupport
        (fun t : ℝ =>
          zetaPaleyWienerVerticalLineIBPDerivative f x t *
            zetaPaleyWienerVerticalOscillation y t) := by
    exact (zetaPaleyWienerVerticalLineIBPDerivative_hasCompactSupport f x).mul_right
  exact hcontinuous.integrable_of_hasCompactSupport hsupport

/-- The iterated `t`-derivatives of the horizontal twist.  This is the source family
produced by repeated integration by parts on the vertical oscillation. -/
noncomputable def zetaPaleyWienerHorizontalTwistIteratedDerivative
    (f : ZetaAdmissibleFunction) (n : ℕ) (x t : ℝ) : ℂ :=
  iteratedDeriv n (fun u : ℝ => zetaPaleyWienerHorizontalTwist f x u) t

/-- The zero-th iterated horizontal-twist derivative is the horizontal twist. -/
theorem zetaPaleyWienerHorizontalTwistIteratedDerivative_zero
    (f : ZetaAdmissibleFunction) (x t : ℝ) :
    zetaPaleyWienerHorizontalTwistIteratedDerivative f 0 x t =
      zetaPaleyWienerHorizontalTwist f x t := by
  exact congrFun
    (iteratedDeriv_zero
      (f := fun u : ℝ => zetaPaleyWienerHorizontalTwist f x u))
    t

/-- The zero-th iterated horizontal-twist derivative agrees with the zero-th vertical
parameter jet. -/
theorem zetaPaleyWienerHorizontalTwistIteratedDerivative_zero_eq_verticalJet_zero
    (f : ZetaAdmissibleFunction) (x t : ℝ) :
    zetaPaleyWienerHorizontalTwistIteratedDerivative f 0 x t =
      zetaPaleyWienerHorizontalTwistVerticalJet f 0 x t := by
  exact Eq.trans
    (zetaPaleyWienerHorizontalTwistIteratedDerivative_zero f x t)
    (zetaPaleyWienerHorizontalTwistVerticalJet_zero f x t).symm

/-- The one-variable iterated vertical derivative of the horizontal twist is the
vertical-direction parameter jet. -/
theorem zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_verticalJet
    (f : ZetaAdmissibleFunction) (n : ℕ) (x t : ℝ) :
    zetaPaleyWienerHorizontalTwistIteratedDerivative f n x t =
      zetaPaleyWienerHorizontalTwistVerticalJet f n x t := by
  unfold zetaPaleyWienerHorizontalTwistIteratedDerivative
  unfold zetaPaleyWienerHorizontalTwistVerticalJet
  exact iteratedDeriv_verticalLine_eq_iteratedFDeriv_verticalDirection
    (zetaPaleyWienerHorizontalTwistParameter f)
    (zetaPaleyWienerHorizontalTwistParameter_contDiff f)
    n x t

/-- The one-variable iterated derivative source is the iterated derivative of the parameter
twist restricted to the vertical affine line. -/
theorem zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_parameterVerticalLine_iteratedDeriv
    (f : ZetaAdmissibleFunction) (n : ℕ) (x t : ℝ) :
    zetaPaleyWienerHorizontalTwistIteratedDerivative f n x t =
      iteratedDeriv n
        (fun u : ℝ =>
          zetaPaleyWienerHorizontalTwistParameter f
            (zetaPaleyWienerVerticalLineEmbedding x u))
        t := by
  rfl

/-- The first iterated derivative of the horizontal twist is the derivative source used in
one vertical-line integration-by-parts step. -/
theorem zetaPaleyWienerHorizontalTwistIteratedDerivative_one
    (f : ZetaAdmissibleFunction) (x t : ℝ) :
    zetaPaleyWienerHorizontalTwistIteratedDerivative f 1 x t =
      zetaPaleyWienerVerticalLineIBPDerivative f x t := by
  exact congrFun
    (iteratedDeriv_one
      (f := fun u : ℝ => zetaPaleyWienerHorizontalTwist f x u))
    t

/-- Successor iterated derivatives are ordinary derivatives of the previous iterated
derivative source. -/
theorem zetaPaleyWienerHorizontalTwistIteratedDerivative_succ
    (f : ZetaAdmissibleFunction) (n : ℕ) (x t : ℝ) :
    zetaPaleyWienerHorizontalTwistIteratedDerivative f (n + 1) x t =
      deriv (fun u : ℝ =>
        zetaPaleyWienerHorizontalTwistIteratedDerivative f n x u) t := by
  exact congrFun
    (iteratedDeriv_succ
      (n := n)
      (f := fun u : ℝ => zetaPaleyWienerHorizontalTwist f x u))
    t

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

/-- The vertical oscillation differentiates by multiplication with `I * y`. -/
theorem hasDerivAt_zetaPaleyWienerVerticalOscillation
    (y t : ℝ) :
    HasDerivAt
      (fun u : ℝ => zetaPaleyWienerVerticalOscillation y u)
      (Complex.I * (y : ℂ) *
        zetaPaleyWienerVerticalOscillation y t)
      t := by
  have hlinear_complex :
      HasDerivAt
        (fun w : ℂ => Complex.I * (y : ℂ) * w)
        (Complex.I * (y : ℂ))
        (t : ℂ) := by
    exact (hasDerivAt_id (t : ℂ)).const_mul (Complex.I * (y : ℂ))
  have hlinear_real :
      HasDerivAt
        (fun u : ℝ => Complex.I * (y : ℂ) * (u : ℂ))
        (Complex.I * (y : ℂ))
        t :=
    hlinear_complex.comp_ofReal
  have hexp :
      HasDerivAt
        (fun u : ℝ => Complex.exp (Complex.I * (y : ℂ) * (u : ℂ)))
        (Complex.exp (Complex.I * (y : ℂ) * (t : ℂ)) *
          (Complex.I * (y : ℂ)))
        t :=
    (Complex.hasDerivAt_exp (Complex.I * (y : ℂ) * (t : ℂ))).comp
      t hlinear_real
  have hcomm :
      Complex.exp (Complex.I * (y : ℂ) * (t : ℂ)) *
          (Complex.I * (y : ℂ)) =
        Complex.I * (y : ℂ) *
          Complex.exp (Complex.I * (y : ℂ) * (t : ℂ)) :=
    mul_comm
      (Complex.exp (Complex.I * (y : ℂ) * (t : ℂ)))
      (Complex.I * (y : ℂ))
  exact Eq.subst
    (motive := fun v : ℂ =>
      HasDerivAt
        (fun u : ℝ => zetaPaleyWienerVerticalOscillation y u)
        v
        t)
    hcomm
    hexp

/-- The horizontal twist vanishes strictly above the certified support interval. -/
theorem zetaPaleyWienerHorizontalTwist_eq_zero_of_supportInterval_lt
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (x t : ℝ) (ht : I.upper < t) :
    zetaPaleyWienerHorizontalTwist f x t = 0 := by
  have hsource :
      f.toZetaTestFunction t = 0 :=
    zetaPaleyWiener_eq_zero_of_supportUpperBound_lt f I ht
  have htest :
      f.toZetaTestFunction' t = f.toZetaTestFunction t :=
    ZetaAdmissibleFunction.toZetaTestFunction'_apply f t
  unfold zetaPaleyWienerHorizontalTwist
  calc
    f.toZetaTestFunction' t * (Real.exp (x * t) : ℂ)
        = f.toZetaTestFunction t * (Real.exp (x * t) : ℂ) := by
          exact congrArg
            (fun v : ℂ => v * (Real.exp (x * t) : ℂ))
            htest
    _ = 0 * (Real.exp (x * t) : ℂ) := by
          exact congrArg
            (fun v : ℂ => v * (Real.exp (x * t) : ℂ))
            hsource
    _ = 0 := zero_mul (Real.exp (x * t) : ℂ)

/-- The horizontal twist vanishes strictly below the certified support interval. -/
theorem zetaPaleyWienerHorizontalTwist_eq_zero_of_lt_supportInterval
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (x t : ℝ) (ht : t < I.lower) :
    zetaPaleyWienerHorizontalTwist f x t = 0 := by
  have hsource :
      f.toZetaTestFunction t = 0 :=
    zetaPaleyWiener_eq_zero_of_lt_supportLowerBound f I ht
  have htest :
      f.toZetaTestFunction' t = f.toZetaTestFunction t :=
    ZetaAdmissibleFunction.toZetaTestFunction'_apply f t
  unfold zetaPaleyWienerHorizontalTwist
  calc
    f.toZetaTestFunction' t * (Real.exp (x * t) : ℂ)
        = f.toZetaTestFunction t * (Real.exp (x * t) : ℂ) := by
          exact congrArg
            (fun v : ℂ => v * (Real.exp (x * t) : ℂ))
            htest
    _ = 0 * (Real.exp (x * t) : ℂ) := by
          exact congrArg
            (fun v : ℂ => v * (Real.exp (x * t) : ℂ))
            hsource
    _ = 0 := zero_mul (Real.exp (x * t) : ℂ)

/-- The zero-th vertical jet vanishes below the certified support interval. -/
theorem zetaPaleyWienerHorizontalTwistVerticalJet_zero_eq_zero_off_supportInterval
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (x t : ℝ) (ht : t < I.lower) :
    zetaPaleyWienerHorizontalTwistVerticalJet f 0 x t = 0 := by
  exact Eq.trans
    (zetaPaleyWienerHorizontalTwistVerticalJet_zero f x t)
    (zetaPaleyWienerHorizontalTwist_eq_zero_of_lt_supportInterval f I x t ht)

/-- The zero-th vertical jet vanishes above the certified support interval. -/
theorem zetaPaleyWienerHorizontalTwistVerticalJet_zero_eq_zero_of_supportInterval_lt
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (x t : ℝ) (ht : I.upper < t) :
    zetaPaleyWienerHorizontalTwistVerticalJet f 0 x t = 0 := by
  exact Eq.trans
    (zetaPaleyWienerHorizontalTwistVerticalJet_zero f x t)
    (zetaPaleyWienerHorizontalTwist_eq_zero_of_supportInterval_lt f I x t ht)

/-- The `ZetaTestFunction` wrapper has the same topological support as the admissible
carrier. -/
theorem zetaPaleyWienerTestFunction_tsupport_eq
    (f : ZetaAdmissibleFunction) :
    tsupport f.toZetaTestFunction' = tsupport f.toZetaTestFunction := by
  exact congrArg tsupport
    (funext
      (fun u : ℝ =>
        ZetaAdmissibleFunction.toZetaTestFunction'_apply f u))

/-- The horizontal twist has no support outside the source support. -/
theorem zetaPaleyWienerHorizontalTwist_tsupport_subset_source
    (f : ZetaAdmissibleFunction) (x : ℝ) :
    tsupport (fun u : ℝ => zetaPaleyWienerHorizontalTwist f x u) ⊆
      tsupport f.toZetaTestFunction := by
  intro t ht
  have hleft :
      t ∈ tsupport (fun u : ℝ => f.toZetaTestFunction' u) := by
    unfold zetaPaleyWienerHorizontalTwist at ht
    exact tsupport_mul_subset_left ht
  exact Eq.subst
    (motive := fun S : Set ℝ => t ∈ S)
    (zetaPaleyWienerTestFunction_tsupport_eq f)
    hleft

/-- Topological support of the derivative is contained in the topological support of the
original one-variable source. -/
theorem zetaPaleyWiener_tsupport_deriv_subset
    (g : ℝ → ℂ) :
    tsupport (deriv g) ⊆ tsupport g := by
  exact closure_minimal support_deriv_subset isClosed_closure

/-- The derivative source produced by the horizontal twist has no support outside the
original admissible source support. -/
theorem zetaPaleyWienerHorizontalTwistDerivative_tsupport_subset_source
    (f : ZetaAdmissibleFunction) (x : ℝ) :
    tsupport (fun t : ℝ => zetaPaleyWienerVerticalLineIBPDerivative f x t) ⊆
      tsupport f.toZetaTestFunction := by
  intro t ht
  have hsupport :
      Function.support
          (deriv (fun u : ℝ => zetaPaleyWienerHorizontalTwist f x u)) ⊆
        tsupport (fun u : ℝ => zetaPaleyWienerHorizontalTwist f x u) :=
    support_deriv_subset
  have htwist :
      t ∈ tsupport (fun u : ℝ => zetaPaleyWienerHorizontalTwist f x u) := by
    unfold zetaPaleyWienerVerticalLineIBPDerivative at ht
    exact hsupport (subset_tsupport _ ht)
  exact zetaPaleyWienerHorizontalTwist_tsupport_subset_source f x htwist

/-- Every iterated derivative of the horizontal twist has support contained in the original
admissible source support. -/
theorem zetaPaleyWienerHorizontalTwistIteratedDerivative_tsupport_subset_source
    (f : ZetaAdmissibleFunction) (n : ℕ) (x : ℝ) :
    tsupport
        (fun t : ℝ =>
          zetaPaleyWienerHorizontalTwistIteratedDerivative f n x t) ⊆
      tsupport f.toZetaTestFunction := by
  induction n with
  | zero =>
      intro t ht
      exact zetaPaleyWienerHorizontalTwist_tsupport_subset_source f x ht
  | succ n ih =>
      intro t ht
      have hderiv :
          t ∈ tsupport
            (deriv
              (fun u : ℝ =>
                zetaPaleyWienerHorizontalTwistIteratedDerivative f n x u)) := by
        exact Eq.subst
          (motive := fun h : ℝ → ℂ => t ∈ tsupport h)
          (funext
            (fun u : ℝ =>
              zetaPaleyWienerHorizontalTwistIteratedDerivative_succ f n x u))
          ht
      have hprev :
          t ∈ tsupport
            (fun u : ℝ =>
              zetaPaleyWienerHorizontalTwistIteratedDerivative f n x u) :=
        zetaPaleyWiener_tsupport_deriv_subset
          (fun u : ℝ =>
            zetaPaleyWienerHorizontalTwistIteratedDerivative f n x u)
          hderiv
      exact ih hprev

/-- Iterated horizontal-twist derivatives vanish away from the original admissible source
support. -/
theorem zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_zero_of_not_mem_source
    (f : ZetaAdmissibleFunction) (n : ℕ) (x t : ℝ)
    (ht : t ∉ tsupport f.toZetaTestFunction) :
    zetaPaleyWienerHorizontalTwistIteratedDerivative f n x t = 0 := by
  exact Function.nmem_support.mp
    (fun hmem =>
      ht
        (zetaPaleyWienerHorizontalTwistIteratedDerivative_tsupport_subset_source
          f n x
          (subset_tsupport _ hmem)))

/-- Iterated horizontal-twist derivatives vanish below the certified support interval. -/
theorem zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_zero_off_supportInterval
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (n : ℕ) (x t : ℝ) (ht_lower : t < I.lower) :
    zetaPaleyWienerHorizontalTwistIteratedDerivative f n x t = 0 := by
  have hsource_not :
      t ∉ tsupport f.toZetaTestFunction := by
    intro ht
    exact (not_lt_of_ge (I.lower_mem t ht)) ht_lower
  exact zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_zero_of_not_mem_source
    f n x t hsource_not

/-- Iterated horizontal-twist derivatives vanish above the certified support interval. -/
theorem zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_zero_of_supportInterval_lt
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (n : ℕ) (x t : ℝ) (ht_upper : I.upper < t) :
    zetaPaleyWienerHorizontalTwistIteratedDerivative f n x t = 0 := by
  have hsource_not :
      t ∉ tsupport f.toZetaTestFunction := by
    intro ht
    exact (not_lt_of_ge (I.upper_mem t ht)) ht_upper
  exact zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_zero_of_not_mem_source
    f n x t hsource_not

/-- The derivative source is zero away from the original admissible source support. -/
theorem zetaPaleyWienerHorizontalTwistDerivative_eq_zero_of_not_mem_source
    (f : ZetaAdmissibleFunction) (x t : ℝ)
    (ht : t ∉ tsupport f.toZetaTestFunction) :
    zetaPaleyWienerVerticalLineIBPDerivative f x t = 0 := by
  exact Eq.subst
    (motive := fun v : ℂ => v = 0)
    (zetaPaleyWienerHorizontalTwistIteratedDerivative_one f x t)
    (zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_zero_of_not_mem_source
      f 1 x t ht)

/-- The compact-support boundary term for the horizontal twist vanishes at any lower and
upper cutoffs chosen strictly outside the certified support interval. -/
theorem zetaPaleyWienerVerticalLineIBP_boundaryTerm_eq_zero_of_strict_bounds
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (x y lower upper : ℝ) (hlower : lower < I.lower) (hupper : I.upper < upper) :
    zetaPaleyWienerHorizontalTwist f x upper *
        zetaPaleyWienerVerticalOscillation y upper -
      zetaPaleyWienerHorizontalTwist f x lower *
        zetaPaleyWienerVerticalOscillation y lower =
      0 := by
  have hupper_zero :
      zetaPaleyWienerHorizontalTwist f x upper = 0 :=
    zetaPaleyWienerHorizontalTwist_eq_zero_of_supportInterval_lt
      f I x upper hupper
  have hlower_zero :
      zetaPaleyWienerHorizontalTwist f x lower = 0 :=
    zetaPaleyWienerHorizontalTwist_eq_zero_of_lt_supportInterval
      f I x lower hlower
  calc
    zetaPaleyWienerHorizontalTwist f x upper *
          zetaPaleyWienerVerticalOscillation y upper -
        zetaPaleyWienerHorizontalTwist f x lower *
          zetaPaleyWienerVerticalOscillation y lower
        = 0 * zetaPaleyWienerVerticalOscillation y upper -
            zetaPaleyWienerHorizontalTwist f x lower *
              zetaPaleyWienerVerticalOscillation y lower := by
          exact congrArg
            (fun v : ℂ =>
              v * zetaPaleyWienerVerticalOscillation y upper -
                zetaPaleyWienerHorizontalTwist f x lower *
                  zetaPaleyWienerVerticalOscillation y lower)
            hupper_zero
    _ = 0 - zetaPaleyWienerHorizontalTwist f x lower *
            zetaPaleyWienerVerticalOscillation y lower := by
          exact congrArg
            (fun v : ℂ =>
              v - zetaPaleyWienerHorizontalTwist f x lower *
                zetaPaleyWienerVerticalOscillation y lower)
            (zero_mul (zetaPaleyWienerVerticalOscillation y upper))
    _ = 0 - 0 * zetaPaleyWienerVerticalOscillation y lower := by
          exact congrArg
            (fun v : ℂ => 0 - v * zetaPaleyWienerVerticalOscillation y lower)
            hlower_zero
    _ = 0 - 0 := by
          exact congrArg
            (fun v : ℂ => 0 - v)
            (zero_mul (zetaPaleyWienerVerticalOscillation y lower))
    _ = 0 := sub_zero 0

/-- The vertical-line integration-by-parts identity before solving for the kernel
integral. -/
theorem zetaPaleyWienerVerticalLineKernel_integral_mul_frequency_eq_neg_derivativeIntegral
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (x y : ℝ) :
    (Complex.I * (y : ℂ)) *
        (∫ t : ℝ, zetaPaleyWienerVerticalLineKernel f x y t) =
      -zetaPaleyWienerVerticalLineIBPDerivativeIntegral f x y := by
  let A : ℂ := Complex.I * (y : ℂ)
  let H : ℝ → ℂ := fun t => zetaPaleyWienerHorizontalTwist f x t
  let V : ℝ → ℂ := fun t => zetaPaleyWienerVerticalOscillation y t
  let D : ℝ → ℂ := fun t => zetaPaleyWienerVerticalLineIBPDerivative f x t
  have hH :
      ∀ t : ℝ, HasDerivAt H (D t) t := by
    intro t
    exact hasDerivAt_zetaPaleyWienerHorizontalTwist f x t
  have hV :
      ∀ t : ℝ, HasDerivAt V (A * V t) t := by
    intro t
    exact hasDerivAt_zetaPaleyWienerVerticalOscillation y t
  have hHV :
      Integrable (fun t : ℝ => H t * V t) := by
    exact zetaPaleyWienerVerticalLineKernel_integrable f x y
  have hHDV :
      Integrable (fun t : ℝ => H t * (A * V t)) := by
    have hcontinuous :
        Continuous (fun t : ℝ => H t * (A * V t)) := by
      exact (zetaPaleyWienerHorizontalTwist_continuous f x).mul
        (continuous_const.mul
          (Complex.continuous_exp.comp
            ((continuous_const.mul continuous_const).mul Complex.continuous_ofReal)))
    have hsupport :
        HasCompactSupport (fun t : ℝ => H t * (A * V t)) := by
      exact (zetaPaleyWienerHorizontalTwist_hasCompactSupport f x).mul_right
    exact hcontinuous.integrable_of_hasCompactSupport hsupport
  have hDV :
      Integrable (fun t : ℝ => D t * V t) := by
    exact zetaPaleyWienerVerticalLineIBPDerivative_integrable f x y
  have hibp :
      (∫ t : ℝ, H t * (A * V t)) =
        -∫ t : ℝ, D t * V t :=
    MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
      hH hV hHDV hDV hHV
  have hleft_integrand :
      (fun t : ℝ => H t * (A * V t)) =
        fun t : ℝ => A * (H t * V t) := by
    funext t
    calc
      H t * (A * V t) = (H t * A) * V t := by
        exact (mul_assoc (H t) A (V t)).symm
      _ = (A * H t) * V t := by
        exact congrArg (fun v : ℂ => v * V t) (mul_comm (H t) A)
      _ = A * (H t * V t) := by
        exact mul_assoc A (H t) (V t)
  have hleft :
      (∫ t : ℝ, H t * (A * V t)) =
        A * (∫ t : ℝ, zetaPaleyWienerVerticalLineKernel f x y t) := by
    calc
      (∫ t : ℝ, H t * (A * V t))
          = ∫ t : ℝ, A * (H t * V t) := by
            exact congrArg
              (fun q : ℝ → ℂ => ∫ t : ℝ, q t)
              hleft_integrand
      _ = A * (∫ t : ℝ, H t * V t) := by
            exact integral_const_mul A (fun t : ℝ => H t * V t)
      _ = A * (∫ t : ℝ, zetaPaleyWienerVerticalLineKernel f x y t) := by
            exact congrArg
              (fun v : ℂ => A * v)
              (complex_integral_congr_of_pointwise_eq
                (fun t : ℝ => H t * V t)
                (fun t : ℝ => zetaPaleyWienerVerticalLineKernel f x y t)
                (fun t : ℝ => rfl))
  have hright :
      (∫ t : ℝ, D t * V t) =
        zetaPaleyWienerVerticalLineIBPDerivativeIntegral f x y := by
    exact complex_integral_congr_of_pointwise_eq
      (fun t : ℝ => D t * V t)
      (fun t : ℝ =>
        zetaPaleyWienerVerticalLineIBPDerivative f x t *
          zetaPaleyWienerVerticalOscillation y t)
      (fun t : ℝ => rfl)
  exact Eq.subst
    (motive := fun v : ℂ =>
      v = -zetaPaleyWienerVerticalLineIBPDerivativeIntegral f x y)
    hleft
    (Eq.subst
      (motive := fun v : ℂ =>
        (∫ t : ℝ, H t * (A * V t)) = -v)
      hright
      hibp)

/-- The negated integration-by-parts identity in derivative-integral-first form. -/
theorem zetaPaleyWienerVerticalLineIBPDerivativeIntegral_eq_neg_frequency_mul_kernelIntegral
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (x y : ℝ) :
    zetaPaleyWienerVerticalLineIBPDerivativeIntegral f x y =
      -(Complex.I * (y : ℂ)) *
        (∫ t : ℝ, zetaPaleyWienerVerticalLineKernel f x y t) := by
  have h :
      (Complex.I * (y : ℂ)) *
          (∫ t : ℝ, zetaPaleyWienerVerticalLineKernel f x y t) =
        -zetaPaleyWienerVerticalLineIBPDerivativeIntegral f x y :=
    zetaPaleyWienerVerticalLineKernel_integral_mul_frequency_eq_neg_derivativeIntegral
      f I x y
  exact neg_eq_iff_eq_neg.mpr h.symm

/-- The frequency multiplier times the displayed inverse factor is `-1`. -/
theorem zetaPaleyWiener_frequency_mul_I_inverse_eq_neg_one
    (y : ℝ) (hy : (y : ℂ) ≠ 0) :
    (Complex.I * (y : ℂ)) * (Complex.I * (y : ℂ)⁻¹) = -1 := by
  calc
    (Complex.I * (y : ℂ)) * (Complex.I * (y : ℂ)⁻¹)
        = (Complex.I * Complex.I) * ((y : ℂ) * (y : ℂ)⁻¹) := by
          exact mul_mul_mul_comm Complex.I (y : ℂ) Complex.I ((y : ℂ)⁻¹)
    _ = (-1 : ℂ) * ((y : ℂ) * (y : ℂ)⁻¹) := by
          exact congrArg
            (fun v : ℂ => v * ((y : ℂ) * (y : ℂ)⁻¹))
            Complex.I_mul_I
    _ = (-1 : ℂ) * 1 := by
          exact congrArg
            (fun v : ℂ => (-1 : ℂ) * v)
            (mul_inv_cancel₀ hy)
    _ = -1 := mul_one (-1 : ℂ)

/-- Multiplying the proposed solved form by the vertical frequency recovers the negated
derivative integral. -/
theorem zetaPaleyWiener_frequency_mul_solvedIntegral
    (y : ℝ) (hy : (y : ℂ) ≠ 0) (D : ℂ) :
    (Complex.I * (y : ℂ)) * (Complex.I * (y : ℂ)⁻¹ * D) =
      -D := by
  calc
    (Complex.I * (y : ℂ)) * (Complex.I * (y : ℂ)⁻¹ * D)
        = ((Complex.I * (y : ℂ)) * (Complex.I * (y : ℂ)⁻¹)) * D := by
          exact (mul_assoc (Complex.I * (y : ℂ)) (Complex.I * (y : ℂ)⁻¹) D).symm
    _ = (-1 : ℂ) * D := by
          exact congrArg
            (fun v : ℂ => v * D)
            (zetaPaleyWiener_frequency_mul_I_inverse_eq_neg_one y hy)
    _ = -D := neg_one_mul D

/-- Solving the vertical-line integration-by-parts identity for the original kernel
integral introduces the factor `I * y⁻¹`. -/
theorem zetaPaleyWienerVerticalLineKernel_integral_solve_frequency
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (x y : ℝ) (hy : (y : ℂ) ≠ 0) :
    (∫ t : ℝ, zetaPaleyWienerVerticalLineKernel f x y t) =
      Complex.I * (y : ℂ)⁻¹ *
        zetaPaleyWienerVerticalLineIBPDerivativeIntegral f x y := by
  let K : ℂ := ∫ t : ℝ, zetaPaleyWienerVerticalLineKernel f x y t
  let D : ℂ := zetaPaleyWienerVerticalLineIBPDerivativeIntegral f x y
  let A : ℂ := Complex.I * (y : ℂ)
  have hA : A ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero hy
  have hibp :
      A * K = -D :=
    zetaPaleyWienerVerticalLineKernel_integral_mul_frequency_eq_neg_derivativeIntegral
      f I x y
  have hcandidate :
      A * (Complex.I * (y : ℂ)⁻¹ * D) = -D :=
    zetaPaleyWiener_frequency_mul_solvedIntegral y hy D
  exact mul_left_cancel₀ hA (hibp.trans hcandidate.symm)

/-- One vertical-line integration-by-parts identity before taking norms.

The oscillatory factor is `exp (I * y * t)`, so differentiating it contributes
`I * y`; the inverse factor is therefore `I * y⁻¹`, not just `y⁻¹`. -/
theorem zetaPaleyWienerVerticalLineKernel_integral_eq_I_mul_inverse_mul_derivativeIntegral
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (x y : ℝ) (hy : (y : ℂ) ≠ 0) :
    (∫ t : ℝ, zetaPaleyWienerVerticalLineKernel f x y t) =
      Complex.I * (y : ℂ)⁻¹ *
        zetaPaleyWienerVerticalLineIBPDerivativeIntegral f x y := by
  exact zetaPaleyWienerVerticalLineKernel_integral_solve_frequency
    f I x y hy

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

/-- The derivative source used after horizontal twisting is supported in the same compact
support interval. -/
theorem zetaPaleyWienerHorizontalTwistDerivative_eq_zero_off_supportInterval
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (x t : ℝ) (ht_lower : t < I.lower) :
    zetaPaleyWienerVerticalLineIBPDerivative f x t = 0 := by
  have hsource_not :
      t ∉ tsupport f.toZetaTestFunction := by
    intro ht
    exact (not_lt_of_ge (I.lower_mem t ht)) ht_lower
  exact zetaPaleyWienerHorizontalTwistDerivative_eq_zero_of_not_mem_source
    f x t hsource_not

/-- The derivative source used after horizontal twisting vanishes above the support
interval. -/
theorem zetaPaleyWienerHorizontalTwistDerivative_eq_zero_of_supportInterval_lt
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (x t : ℝ) (ht_upper : I.upper < t) :
    zetaPaleyWienerVerticalLineIBPDerivative f x t = 0 := by
  have hsource_not :
      t ∉ tsupport f.toZetaTestFunction := by
    intro ht
    exact (not_lt_of_ge (I.upper_mem t ht)) ht_upper
  exact zetaPaleyWienerHorizontalTwistDerivative_eq_zero_of_not_mem_source
    f x t hsource_not

/-- The derivative-source oscillatory kernel used in the post-IBP Fourier integral. -/
noncomputable def zetaPaleyWienerDerivativeOscillatoryKernel
    (f : ZetaAdmissibleFunction) (x y t : ℝ) : ℂ :=
  zetaPaleyWienerVerticalLineIBPDerivative f x t *
    zetaPaleyWienerVerticalOscillation y t

/-- The named derivative-source oscillatory kernel integrates to the post-IBP integral. -/
theorem zetaPaleyWienerDerivativeOscillatoryKernel_integral_eq
    (f : ZetaAdmissibleFunction) (x y : ℝ) :
    (∫ t : ℝ, zetaPaleyWienerDerivativeOscillatoryKernel f x y t) =
      zetaPaleyWienerVerticalLineIBPDerivativeIntegral f x y := by
  rfl

/-- The named derivative-source oscillatory kernel is integrable. -/
theorem zetaPaleyWienerDerivativeOscillatoryKernel_integrable
    (f : ZetaAdmissibleFunction) (x y : ℝ) :
    Integrable
      (fun t : ℝ => zetaPaleyWienerDerivativeOscillatoryKernel f x y t) := by
  exact zetaPaleyWienerVerticalLineIBPDerivative_integrable f x y

/-- The derivative-source oscillatory kernel is zero away from the original source support. -/
theorem zetaPaleyWienerDerivativeOscillatoryKernel_eq_zero_of_not_mem_source
    (f : ZetaAdmissibleFunction) (x y t : ℝ)
    (ht : t ∉ tsupport f.toZetaTestFunction) :
    zetaPaleyWienerDerivativeOscillatoryKernel f x y t = 0 := by
  have hderiv :
      zetaPaleyWienerVerticalLineIBPDerivative f x t = 0 :=
    zetaPaleyWienerHorizontalTwistDerivative_eq_zero_of_not_mem_source
      f x t ht
  unfold zetaPaleyWienerDerivativeOscillatoryKernel
  exact Eq.trans
    (congrArg
      (fun v : ℂ => v * zetaPaleyWienerVerticalOscillation y t)
      hderiv)
    (zero_mul (zetaPaleyWienerVerticalOscillation y t))

/-- A pointwise derivative-source bound on the source support dominates the oscillatory
kernel by the source-support indicator. -/
theorem zetaPaleyWienerDerivativeOscillatoryKernel_norm_le_supportIndicatorBound
    (f : ZetaAdmissibleFunction) (x y B : ℝ)
    (hbound :
      ∀ t : ℝ,
        t ∈ tsupport f.toZetaTestFunction →
        ‖zetaPaleyWienerVerticalLineIBPDerivative f x t‖ ≤ B) :
    ∀ t : ℝ,
      ‖zetaPaleyWienerDerivativeOscillatoryKernel f x y t‖ ≤
        zetaPaleyWienerSupportIndicatorBound f B t := by
  intro t
  by_cases ht : t ∈ tsupport f.toZetaTestFunction
  · have hkernel_le :
        ‖zetaPaleyWienerDerivativeOscillatoryKernel f x y t‖ ≤
          ‖zetaPaleyWienerVerticalLineIBPDerivative f x t‖ := by
      unfold zetaPaleyWienerDerivativeOscillatoryKernel
      exact norm_mul_zetaPaleyWienerVerticalOscillation_le
        (zetaPaleyWienerVerticalLineIBPDerivative f x t) y t
    have hsource_bound :
        ‖zetaPaleyWienerVerticalLineIBPDerivative f x t‖ ≤ B :=
      hbound t ht
    have hindicator :
        zetaPaleyWienerSupportIndicatorBound f B t = B := by
      unfold zetaPaleyWienerSupportIndicatorBound
      exact Set.indicator_of_mem ht
    exact Eq.subst
      (motive := fun v : ℝ =>
        ‖zetaPaleyWienerDerivativeOscillatoryKernel f x y t‖ ≤ v)
      hindicator.symm
      (le_trans hkernel_le hsource_bound)
  · have hkernel_zero :
        zetaPaleyWienerDerivativeOscillatoryKernel f x y t = 0 :=
      zetaPaleyWienerDerivativeOscillatoryKernel_eq_zero_of_not_mem_source
        f x y t ht
    have hnorm_zero :
        ‖zetaPaleyWienerDerivativeOscillatoryKernel f x y t‖ = 0 :=
      (congrArg (fun v : ℂ => ‖v‖) hkernel_zero).trans norm_zero
    have hindicator :
        zetaPaleyWienerSupportIndicatorBound f B t = 0 := by
      unfold zetaPaleyWienerSupportIndicatorBound
      exact Set.indicator_of_not_mem ht
    exact Eq.subst
      (motive := fun v : ℝ =>
        v ≤ zetaPaleyWienerSupportIndicatorBound f B t)
      hnorm_zero.symm
      (Eq.subst
        (motive := fun v : ℝ => 0 ≤ v)
        hindicator.symm
        le_rfl)

/-- Integrating a derivative-source support-indicator majorant bounds the norm of the
post-IBP oscillatory integral. -/
theorem zetaPaleyWienerDerivativeOscillatoryKernel_norm_integral_le_supportIndicatorIntegral
    (f : ZetaAdmissibleFunction) (x y B : ℝ)
    (hindicator :
      ∀ t : ℝ,
        ‖zetaPaleyWienerDerivativeOscillatoryKernel f x y t‖ ≤
          zetaPaleyWienerSupportIndicatorBound f B t) :
    ‖∫ t : ℝ, zetaPaleyWienerDerivativeOscillatoryKernel f x y t‖ ≤
      ∫ t : ℝ, zetaPaleyWienerSupportIndicatorBound f B t := by
  have hnorm :
      ‖∫ t : ℝ, zetaPaleyWienerDerivativeOscillatoryKernel f x y t‖ ≤
        ∫ t : ℝ, ‖zetaPaleyWienerDerivativeOscillatoryKernel f x y t‖ :=
    complex_norm_integral_le_integral_norm_of_integrable
      (fun t : ℝ => zetaPaleyWienerDerivativeOscillatoryKernel f x y t)
      (zetaPaleyWienerDerivativeOscillatoryKernel_integrable f x y)
  have hmajorant :
      (∫ t : ℝ, ‖zetaPaleyWienerDerivativeOscillatoryKernel f x y t‖) ≤
        ∫ t : ℝ, zetaPaleyWienerSupportIndicatorBound f B t :=
    real_integral_mono_of_integrable_pointwise_le
      (fun t : ℝ => ‖zetaPaleyWienerDerivativeOscillatoryKernel f x y t‖)
      (zetaPaleyWienerSupportIndicatorBound f B)
      (zetaPaleyWienerDerivativeOscillatoryKernel_integrable f x y).norm
      (zetaPaleyWienerSupportIndicatorBound_integrable f B)
      hindicator
  exact le_trans hnorm hmajorant

/-- A uniform pointwise derivative-source bound gives a compact-support integral bound for
the derivative-source oscillatory integral. -/
theorem zetaPaleyWienerDerivativeOscillatoryKernel_integral_norm_le_intervalLength_mul_bound
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (x y B : ℝ) (hB_nonneg : 0 ≤ B)
    (hbound :
      ∀ t : ℝ,
        t ∈ tsupport f.toZetaTestFunction →
        ‖zetaPaleyWienerVerticalLineIBPDerivative f x t‖ ≤ B) :
    ‖∫ t : ℝ, zetaPaleyWienerDerivativeOscillatoryKernel f x y t‖ ≤
      B * zetaPaleyWienerSupportIntervalLength I := by
  have hindicator :
      ∀ t : ℝ,
        ‖zetaPaleyWienerDerivativeOscillatoryKernel f x y t‖ ≤
          zetaPaleyWienerSupportIndicatorBound f B t :=
    zetaPaleyWienerDerivativeOscillatoryKernel_norm_le_supportIndicatorBound
      f x y B hbound
  have hintegral :
      ‖∫ t : ℝ, zetaPaleyWienerDerivativeOscillatoryKernel f x y t‖ ≤
        ∫ t : ℝ, zetaPaleyWienerSupportIndicatorBound f B t :=
    zetaPaleyWienerDerivativeOscillatoryKernel_norm_integral_le_supportIndicatorIntegral
      f x y B hindicator
  have hlength :
      (∫ t : ℝ, zetaPaleyWienerSupportIndicatorBound f B t) ≤
        B * zetaPaleyWienerSupportIntervalLength I :=
    zetaPaleyWienerSupportIndicatorIntegral_le_intervalLength_mul_bound
      f I B hB_nonneg
  exact le_trans hintegral hlength

/-- The displayed post-IBP derivative integral is bounded by the compact support length
times any uniform pointwise derivative-source bound. -/
theorem zetaPaleyWienerVerticalLineIBPDerivativeIntegral_norm_le_intervalLength_mul_bound
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (x y B : ℝ) (hB_nonneg : 0 ≤ B)
    (hbound :
      ∀ t : ℝ,
        t ∈ tsupport f.toZetaTestFunction →
        ‖zetaPaleyWienerVerticalLineIBPDerivative f x t‖ ≤ B) :
    ‖zetaPaleyWienerVerticalLineIBPDerivativeIntegral f x y‖ ≤
      B * zetaPaleyWienerSupportIntervalLength I := by
  have hkernel :
      ‖∫ t : ℝ, zetaPaleyWienerDerivativeOscillatoryKernel f x y t‖ ≤
        B * zetaPaleyWienerSupportIntervalLength I :=
    zetaPaleyWienerDerivativeOscillatoryKernel_integral_norm_le_intervalLength_mul_bound
      f I x y B hB_nonneg hbound
  exact Eq.subst
    (motive := fun v : ℂ => ‖v‖ ≤ B * zetaPaleyWienerSupportIntervalLength I)
    (zetaPaleyWienerDerivativeOscillatoryKernel_integral_eq f x y)
    hkernel

/-- The oscillatory kernel attached to an arbitrary iterated horizontal-twist derivative. -/
noncomputable def zetaPaleyWienerIteratedDerivativeOscillatoryKernel
    (f : ZetaAdmissibleFunction) (n : ℕ) (x y t : ℝ) : ℂ :=
  zetaPaleyWienerHorizontalTwistIteratedDerivative f n x t *
    zetaPaleyWienerVerticalOscillation y t

/-- The oscillatory integral attached to an arbitrary iterated horizontal-twist derivative. -/
noncomputable def zetaPaleyWienerIteratedDerivativeOscillatoryIntegral
    (f : ZetaAdmissibleFunction) (n : ℕ) (x y : ℝ) : ℂ :=
  ∫ t : ℝ, zetaPaleyWienerIteratedDerivativeOscillatoryKernel f n x y t

/-- The first iterated-derivative oscillatory kernel is the named post-IBP derivative
oscillatory kernel. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryKernel_one
    (f : ZetaAdmissibleFunction) (x y t : ℝ) :
    zetaPaleyWienerIteratedDerivativeOscillatoryKernel f 1 x y t =
      zetaPaleyWienerDerivativeOscillatoryKernel f x y t := by
  unfold zetaPaleyWienerIteratedDerivativeOscillatoryKernel
  unfold zetaPaleyWienerDerivativeOscillatoryKernel
  exact congrArg
    (fun v : ℂ => v * zetaPaleyWienerVerticalOscillation y t)
    (zetaPaleyWienerHorizontalTwistIteratedDerivative_one f x t)

/-- The first iterated-derivative oscillatory integral is the post-IBP derivative integral. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_one
    (f : ZetaAdmissibleFunction) (x y : ℝ) :
    zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f 1 x y =
      zetaPaleyWienerVerticalLineIBPDerivativeIntegral f x y := by
  have hkernel :
      (∫ t : ℝ, zetaPaleyWienerIteratedDerivativeOscillatoryKernel f 1 x y t) =
        ∫ t : ℝ, zetaPaleyWienerDerivativeOscillatoryKernel f x y t :=
    complex_integral_congr_of_pointwise_eq
      (fun t : ℝ => zetaPaleyWienerIteratedDerivativeOscillatoryKernel f 1 x y t)
      (fun t : ℝ => zetaPaleyWienerDerivativeOscillatoryKernel f x y t)
      (zetaPaleyWienerIteratedDerivativeOscillatoryKernel_one f x y)
  unfold zetaPaleyWienerIteratedDerivativeOscillatoryIntegral
  exact hkernel.trans (zetaPaleyWienerDerivativeOscillatoryKernel_integral_eq f x y)

/-- The arbitrary iterated-derivative oscillatory kernel is zero away from the original
source support. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryKernel_eq_zero_of_not_mem_source
    (f : ZetaAdmissibleFunction) (n : ℕ) (x y t : ℝ)
    (ht : t ∉ tsupport f.toZetaTestFunction) :
    zetaPaleyWienerIteratedDerivativeOscillatoryKernel f n x y t = 0 := by
  have hderiv :
      zetaPaleyWienerHorizontalTwistIteratedDerivative f n x t = 0 :=
    zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_zero_of_not_mem_source
      f n x t ht
  unfold zetaPaleyWienerIteratedDerivativeOscillatoryKernel
  exact Eq.trans
    (congrArg
      (fun v : ℂ => v * zetaPaleyWienerVerticalOscillation y t)
      hderiv)
    (zero_mul (zetaPaleyWienerVerticalOscillation y t))

/-- A pointwise bound for the `n`th derivative source dominates the corresponding
oscillatory kernel by the source-support indicator. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryKernel_norm_le_supportIndicatorBound
    (f : ZetaAdmissibleFunction) (n : ℕ) (x y B : ℝ)
    (hbound :
      ∀ t : ℝ,
        t ∈ tsupport f.toZetaTestFunction →
        ‖zetaPaleyWienerHorizontalTwistIteratedDerivative f n x t‖ ≤ B) :
    ∀ t : ℝ,
      ‖zetaPaleyWienerIteratedDerivativeOscillatoryKernel f n x y t‖ ≤
        zetaPaleyWienerSupportIndicatorBound f B t := by
  intro t
  by_cases ht : t ∈ tsupport f.toZetaTestFunction
  · have hkernel_le :
        ‖zetaPaleyWienerIteratedDerivativeOscillatoryKernel f n x y t‖ ≤
          ‖zetaPaleyWienerHorizontalTwistIteratedDerivative f n x t‖ := by
      unfold zetaPaleyWienerIteratedDerivativeOscillatoryKernel
      exact norm_mul_zetaPaleyWienerVerticalOscillation_le
        (zetaPaleyWienerHorizontalTwistIteratedDerivative f n x t) y t
    have hsource_bound :
        ‖zetaPaleyWienerHorizontalTwistIteratedDerivative f n x t‖ ≤ B :=
      hbound t ht
    have hindicator :
        zetaPaleyWienerSupportIndicatorBound f B t = B := by
      unfold zetaPaleyWienerSupportIndicatorBound
      exact Set.indicator_of_mem ht
    exact Eq.subst
      (motive := fun v : ℝ =>
        ‖zetaPaleyWienerIteratedDerivativeOscillatoryKernel f n x y t‖ ≤ v)
      hindicator.symm
      (le_trans hkernel_le hsource_bound)
  · have hkernel_zero :
        zetaPaleyWienerIteratedDerivativeOscillatoryKernel f n x y t = 0 :=
      zetaPaleyWienerIteratedDerivativeOscillatoryKernel_eq_zero_of_not_mem_source
        f n x y t ht
    have hnorm_zero :
        ‖zetaPaleyWienerIteratedDerivativeOscillatoryKernel f n x y t‖ = 0 :=
      (congrArg (fun v : ℂ => ‖v‖) hkernel_zero).trans norm_zero
    have hindicator :
        zetaPaleyWienerSupportIndicatorBound f B t = 0 := by
      unfold zetaPaleyWienerSupportIndicatorBound
      exact Set.indicator_of_not_mem ht
    exact Eq.subst
      (motive := fun v : ℝ =>
        v ≤ zetaPaleyWienerSupportIndicatorBound f B t)
      hnorm_zero.symm
      (Eq.subst
        (motive := fun v : ℝ => 0 ≤ v)
        hindicator.symm
        le_rfl)

/-- The arbitrary iterated horizontal-twist derivative source is continuous. -/
theorem zetaPaleyWienerHorizontalTwistIteratedDerivative_continuous
    (f : ZetaAdmissibleFunction) (n : ℕ) (x : ℝ) :
    Continuous
      (fun t : ℝ => zetaPaleyWienerHorizontalTwistIteratedDerivative f n x t) := by
  have hjet_plane :
      Continuous
        (fun p : ℝ × ℝ =>
          zetaPaleyWienerHorizontalTwistVerticalJet f n p.1 p.2) :=
    zetaPaleyWienerHorizontalTwistVerticalJet_continuous f n
  have hline :
      Continuous (fun t : ℝ => (x, t)) :=
    continuous_const.prod continuous_id
  have hjet_line :
      Continuous
        (fun t : ℝ => zetaPaleyWienerHorizontalTwistVerticalJet f n x t) :=
    hjet_plane.comp hline
  have hfun :
      (fun t : ℝ => zetaPaleyWienerHorizontalTwistIteratedDerivative f n x t) =
        fun t : ℝ => zetaPaleyWienerHorizontalTwistVerticalJet f n x t :=
    funext
      (fun t : ℝ =>
        zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_verticalJet f n x t)
  exact Eq.subst
    (motive := fun g : ℝ → ℂ => Continuous g)
    hfun.symm
    hjet_line

/-- The arbitrary iterated horizontal-twist derivative source has compact support. -/
theorem zetaPaleyWienerHorizontalTwistIteratedDerivative_hasCompactSupport
    (f : ZetaAdmissibleFunction) (n : ℕ) (x : ℝ) :
    HasCompactSupport
      (fun t : ℝ => zetaPaleyWienerHorizontalTwistIteratedDerivative f n x t) := by
  induction n with
  | zero =>
      have hfun :
          (fun t : ℝ => zetaPaleyWienerHorizontalTwistIteratedDerivative f 0 x t) =
            fun t : ℝ => zetaPaleyWienerHorizontalTwist f x t :=
        funext (fun t : ℝ =>
          zetaPaleyWienerHorizontalTwistIteratedDerivative_zero f x t)
      exact Eq.subst
        (motive := fun g : ℝ → ℂ => HasCompactSupport g)
        hfun.symm
        (zetaPaleyWienerHorizontalTwist_hasCompactSupport f x)
  | succ n ih =>
      have hderiv :
          HasCompactSupport
            (deriv
              (fun t : ℝ =>
                zetaPaleyWienerHorizontalTwistIteratedDerivative f n x t)) :=
        ih.deriv
      have hfun :
          (fun t : ℝ =>
            zetaPaleyWienerHorizontalTwistIteratedDerivative f (Nat.succ n) x t) =
            deriv
              (fun t : ℝ =>
                zetaPaleyWienerHorizontalTwistIteratedDerivative f n x t) :=
        funext (fun t : ℝ =>
          zetaPaleyWienerHorizontalTwistIteratedDerivative_succ f n x t)
      exact Eq.subst
        (motive := fun g : ℝ → ℂ => HasCompactSupport g)
        hfun.symm
        hderiv

/-- The arbitrary iterated-derivative oscillatory kernel is continuous. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryKernel_continuous
    (f : ZetaAdmissibleFunction) (n : ℕ) (x y : ℝ) :
    Continuous
      (fun t : ℝ => zetaPaleyWienerIteratedDerivativeOscillatoryKernel f n x y t) := by
  have hderiv :
      Continuous
        (fun t : ℝ => zetaPaleyWienerHorizontalTwistIteratedDerivative f n x t) :=
    zetaPaleyWienerHorizontalTwistIteratedDerivative_continuous f n x
  have hosc :
      Continuous (fun t : ℝ => zetaPaleyWienerVerticalOscillation y t) :=
    Complex.continuous_exp.comp
      ((continuous_const.mul continuous_const).mul Complex.continuous_ofReal)
  unfold zetaPaleyWienerIteratedDerivativeOscillatoryKernel
  exact hderiv.mul hosc

/-- The arbitrary iterated-derivative oscillatory kernel has compact support. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryKernel_hasCompactSupport
    (f : ZetaAdmissibleFunction) (n : ℕ) (x y : ℝ) :
    HasCompactSupport
      (fun t : ℝ => zetaPaleyWienerIteratedDerivativeOscillatoryKernel f n x y t) := by
  unfold zetaPaleyWienerIteratedDerivativeOscillatoryKernel
  exact (zetaPaleyWienerHorizontalTwistIteratedDerivative_hasCompactSupport
    f n x).mul_right

/-- A uniform pointwise bound for the `n`th derivative source gives a compact-support
integral bound for the corresponding oscillatory integral. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_norm_le_intervalLength_mul_bound
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (n : ℕ) (x y B : ℝ) (hB_nonneg : 0 ≤ B)
    (hintegrable :
      Integrable
        (fun t : ℝ => zetaPaleyWienerIteratedDerivativeOscillatoryKernel f n x y t))
    (hbound :
      ∀ t : ℝ,
        t ∈ tsupport f.toZetaTestFunction →
        ‖zetaPaleyWienerHorizontalTwistIteratedDerivative f n x t‖ ≤ B) :
    ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f n x y‖ ≤
      B * zetaPaleyWienerSupportIntervalLength I := by
  have hindicator :
      ∀ t : ℝ,
        ‖zetaPaleyWienerIteratedDerivativeOscillatoryKernel f n x y t‖ ≤
          zetaPaleyWienerSupportIndicatorBound f B t :=
    zetaPaleyWienerIteratedDerivativeOscillatoryKernel_norm_le_supportIndicatorBound
      f n x y B hbound
  have hnorm :
      ‖∫ t : ℝ, zetaPaleyWienerIteratedDerivativeOscillatoryKernel f n x y t‖ ≤
        ∫ t : ℝ, ‖zetaPaleyWienerIteratedDerivativeOscillatoryKernel f n x y t‖ :=
    complex_norm_integral_le_integral_norm_of_integrable
      (fun t : ℝ => zetaPaleyWienerIteratedDerivativeOscillatoryKernel f n x y t)
      hintegrable
  have hmajorant :
      (∫ t : ℝ, ‖zetaPaleyWienerIteratedDerivativeOscillatoryKernel f n x y t‖) ≤
        ∫ t : ℝ, zetaPaleyWienerSupportIndicatorBound f B t :=
    real_integral_mono_of_integrable_pointwise_le
      (fun t : ℝ => ‖zetaPaleyWienerIteratedDerivativeOscillatoryKernel f n x y t‖)
      (zetaPaleyWienerSupportIndicatorBound f B)
      hintegrable.norm
      (zetaPaleyWienerSupportIndicatorBound_integrable f B)
      hindicator
  have hlength :
      (∫ t : ℝ, zetaPaleyWienerSupportIndicatorBound f B t) ≤
        B * zetaPaleyWienerSupportIntervalLength I :=
    zetaPaleyWienerSupportIndicatorIntegral_le_intervalLength_mul_bound
      f I B hB_nonneg
  unfold zetaPaleyWienerIteratedDerivativeOscillatoryIntegral
  exact le_trans hnorm (le_trans hmajorant hlength)

/-- Uniform compact-strip seminorm control for the zero-th horizontal-twist derivative. -/
theorem exists_zetaPaleyWienerHorizontalTwistIteratedDerivative_zero_uniformSeminorm
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ x : ℝ,
        a ≤ x →
        x ≤ b →
        ∀ t : ℝ,
          ‖zetaPaleyWienerHorizontalTwistIteratedDerivative f 0 x t‖ ≤ C := by
  rcases exists_zetaPaleyWienerHorizontalTwistVerticalJet_intervalBound
      f I a b 0 with ⟨C, hCpos, hCbound⟩
  refine ⟨C, hCpos, ?_⟩
  intro x hx_left hx_right t
  rcases zetaPaleyWienerSupportInterval_inside_or_outside I t with hinside | houtside
  · have hjet :
        ‖zetaPaleyWienerHorizontalTwistVerticalJet f 0 x t‖ ≤ C :=
      hCbound x hx_left hx_right t hinside.1 hinside.2
    exact Eq.subst
      (motive := fun v : ℂ => ‖v‖ ≤ C)
      (zetaPaleyWienerHorizontalTwistIteratedDerivative_zero_eq_verticalJet_zero
        f x t).symm
      hjet
  · rcases houtside with hbelow | habove
    · have hzero :
          zetaPaleyWienerHorizontalTwistIteratedDerivative f 0 x t = 0 :=
        zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_zero_off_supportInterval
          f I 0 x t hbelow
      exact Eq.subst
        (motive := fun v : ℂ => ‖v‖ ≤ C)
        hzero.symm
        (le_of_lt hCpos)
    · have hzero :
          zetaPaleyWienerHorizontalTwistIteratedDerivative f 0 x t = 0 :=
        zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_zero_of_supportInterval_lt
          f I 0 x t habove
      exact Eq.subst
        (motive := fun v : ℂ => ‖v‖ ≤ C)
        hzero.symm
        (le_of_lt hCpos)

/-- Uniform seminorm control for the iterated horizontal-twist derivative family on compact
real-part strips and the fixed compact support interval. -/
theorem exists_zetaPaleyWienerHorizontalTwistIteratedDerivative_uniformSeminorm
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ x : ℝ,
        a ≤ x →
        x ≤ b →
        ∀ t : ℝ,
          ‖zetaPaleyWienerHorizontalTwistIteratedDerivative f N x t‖ ≤ C := by
  rcases exists_zetaPaleyWienerHorizontalTwistVerticalJet_intervalBound
      f I a b N with ⟨C, hCpos, hCbound⟩
  refine ⟨C, hCpos, ?_⟩
  intro x hx_left hx_right t
  rcases zetaPaleyWienerSupportInterval_inside_or_outside I t with hinside | houtside
  · have hjet :
        ‖zetaPaleyWienerHorizontalTwistVerticalJet f N x t‖ ≤ C :=
      hCbound x hx_left hx_right t hinside.1 hinside.2
    exact Eq.subst
      (motive := fun v : ℂ => ‖v‖ ≤ C)
      (zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_verticalJet
        f N x t).symm
      hjet
  · rcases houtside with hbelow | habove
    · have hzero :
          zetaPaleyWienerHorizontalTwistIteratedDerivative f N x t = 0 :=
        zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_zero_off_supportInterval
          f I N x t hbelow
      exact Eq.subst
        (motive := fun v : ℂ => ‖v‖ ≤ C)
        hzero.symm
        (le_of_lt hCpos)
    · have hzero :
          zetaPaleyWienerHorizontalTwistIteratedDerivative f N x t = 0 :=
        zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_zero_of_supportInterval_lt
          f I N x t habove
      exact Eq.subst
        (motive := fun v : ℂ => ‖v‖ ≤ C)
        hzero.symm
        (le_of_lt hCpos)

/-- Uniform seminorm control for the first horizontal-twist derivative family on compact
real-part strips. -/
theorem exists_zetaPaleyWienerHorizontalTwistDerivative_uniformSeminorm
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ x : ℝ,
        a ≤ x →
        x ≤ b →
        ∀ t : ℝ,
          ‖zetaPaleyWienerVerticalLineIBPDerivative f x t‖ ≤ C := by
  rcases exists_zetaPaleyWienerHorizontalTwistIteratedDerivative_uniformSeminorm
      f I a b 1 with ⟨C, hCpos, hCbound⟩
  refine ⟨C, hCpos, ?_⟩
  intro x hx_left hx_right t
  exact Eq.subst
    (motive := fun v : ℂ => ‖v‖ ≤ C)
    (zetaPaleyWienerHorizontalTwistIteratedDerivative_one f x t)
    (hCbound x hx_left hx_right t)

/-- Raw compact-support bound for the post-IBP derivative Fourier integral. -/
theorem zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_le_rawBound
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b C : ℝ)
    (hC_nonneg : 0 ≤ C)
    (hbound :
      ∀ x : ℝ,
        a ≤ x →
        x ≤ b →
        ∀ t : ℝ,
          ‖zetaPaleyWienerVerticalLineIBPDerivative f x t‖ ≤ C) :
    ∀ x y : ℝ,
      a ≤ x →
      x ≤ b →
      ‖∫ t : ℝ,
        zetaPaleyWienerVerticalLineIBPDerivative f x t *
          zetaPaleyWienerVerticalOscillation y t‖ ≤
        C * zetaPaleyWienerSupportIntervalLength I := by
  intro x y hx_left hx_right
  have hsource_bound :
      ∀ t : ℝ,
        t ∈ tsupport f.toZetaTestFunction →
        ‖zetaPaleyWienerVerticalLineIBPDerivative f x t‖ ≤ C := by
    intro t _ht
    exact hbound x hx_left hx_right t
  exact zetaPaleyWienerVerticalLineIBPDerivativeIntegral_norm_le_intervalLength_mul_bound
    f I x y C hC_nonneg hsource_bound

/-- Bumped compact-support bound for the post-IBP derivative Fourier integral. -/
theorem zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_le_bumpedBound
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b C : ℝ)
    (hC_nonneg : 0 ≤ C)
    (hbound :
      ∀ x : ℝ,
        a ≤ x →
        x ≤ b →
        ∀ t : ℝ,
          ‖zetaPaleyWienerVerticalLineIBPDerivative f x t‖ ≤ C) :
    ∀ x y : ℝ,
      a ≤ x →
      x ≤ b →
      ‖∫ t : ℝ,
        zetaPaleyWienerVerticalLineIBPDerivative f x t *
          zetaPaleyWienerVerticalOscillation y t‖ ≤
        C * zetaPaleyWienerSupportIntervalLength I + 1 := by
  intro x y hx_left hx_right
  have hraw :
      ‖∫ t : ℝ,
        zetaPaleyWienerVerticalLineIBPDerivative f x t *
          zetaPaleyWienerVerticalOscillation y t‖ ≤
        C * zetaPaleyWienerSupportIntervalLength I :=
    zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_le_rawBound
      f I a b C hC_nonneg hbound x y hx_left hx_right
  have hle :
      C * zetaPaleyWienerSupportIntervalLength I ≤
        C * zetaPaleyWienerSupportIntervalLength I + 1 :=
    le_add_of_nonneg_right zero_le_one
  exact le_trans hraw hle

/-- Zero-order Fourier bound for the compactly supported horizontal-twist derivative
family. -/
theorem zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_zeroOrder_uniformBound
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ x y : ℝ,
        a ≤ x →
        x ≤ b →
        ‖∫ t : ℝ,
          zetaPaleyWienerVerticalLineIBPDerivative f x t *
            zetaPaleyWienerVerticalOscillation y t‖ ≤ C := by
  rcases exists_zetaPaleyWienerHorizontalTwistDerivative_uniformSeminorm
      f I a b with ⟨C0, hC0pos, hC0bound⟩
  let C : ℝ := C0 * zetaPaleyWienerSupportIntervalLength I + 1
  have hC0_nonneg : 0 ≤ C0 :=
    le_of_lt hC0pos
  have hraw_nonneg :
      0 ≤ C0 * zetaPaleyWienerSupportIntervalLength I :=
    mul_nonneg hC0_nonneg (zetaPaleyWienerSupportIntervalLength_nonnegative I)
  have hCpos : 0 < C :=
    lt_of_le_of_lt hraw_nonneg
      (lt_add_of_pos_right
        (C0 * zetaPaleyWienerSupportIntervalLength I)
        zero_lt_one)
  refine ⟨C, hCpos, ?_⟩
  intro x y hx_left hx_right
  exact zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_le_bumpedBound
    f I a b C0 hC0_nonneg hC0bound x y hx_left hx_right

/-- The zeroth vertical-frequency decay weight is one. -/
theorem zetaPaleyWiener_zeroDecayWeight
    (y : ℝ) :
    (1 + ‖y‖) ^ (-(0 : ℤ)) = (1 : ℝ) := by
  exact zpow_zero (1 + ‖y‖)

/-- The real vertical-frequency decay weight is nonnegative. -/
theorem zetaPaleyWiener_realVerticalDecayWeight_nonnegative
    (y : ℝ) (N : ℕ) :
    0 ≤ (1 + ‖y‖) ^ (-(N : ℤ)) := by
  exact zpow_nonneg
    (add_nonneg zero_le_one (norm_nonneg y))
    (-(N : ℤ))

/-- Low vertical frequency bounds the real decay base by `2`. -/
theorem zetaPaleyWiener_lowFrequency_realDecayBase_le_two
    {y : ℝ} (hy : ‖y‖ ≤ 1) :
    1 + ‖y‖ ≤ (2 : ℝ) := by
  exact Eq.subst
    (motive := fun v : ℝ => 1 + ‖y‖ ≤ v)
    one_add_one_eq_two
    (add_le_add_left hy 1)

/-- The real vertical-frequency decay base is positive. -/
theorem zetaPaleyWiener_realDecayBase_pos
    (y : ℝ) :
    0 < 1 + ‖y‖ :=
  lt_of_lt_of_le zero_lt_one
    (le_add_of_nonneg_right (norm_nonneg y))

/-- The real vertical-frequency decay base is nonzero. -/
theorem zetaPaleyWiener_realDecayBase_ne_zero
    (y : ℝ) :
    1 + ‖y‖ ≠ 0 :=
  ne_of_gt (zetaPaleyWiener_realDecayBase_pos y)

/-- Low vertical frequency bounds every natural power of the real decay base by the
corresponding power of `2`. -/
theorem zetaPaleyWiener_lowFrequency_realDecayBase_pow_le_two_pow
    (m : ℕ) {y : ℝ} (hy : ‖y‖ ≤ 1) :
    (1 + ‖y‖) ^ m ≤ (2 : ℝ) ^ m := by
  exact pow_le_pow_left₀
    (add_nonneg zero_le_one (norm_nonneg y))
    (zetaPaleyWiener_lowFrequency_realDecayBase_le_two hy)
    m

/-- A positive base whose `m`th power is bounded by `A` has reciprocal `m`th z-power
absorbing `A`. -/
theorem zetaPaleyWiener_pow_bound_mul_negative_zpow_ge_one
    (A X : ℝ) (m : ℕ)
    (hX_pos : 0 < X)
    (hpow : X ^ m ≤ A) :
    1 ≤ A * X ^ (-(m : ℤ)) := by
  have hXpow_pos : 0 < X ^ m :=
    pow_pos hX_pos m
  have hdiv :
      1 ≤ A / X ^ m := by
    have hone_mul :
        1 * X ^ m = X ^ m :=
      one_mul (X ^ m)
    exact (le_div_iff₀ hXpow_pos).mpr
      (Eq.subst
        (motive := fun v : ℝ => v ≤ A)
        hone_mul.symm
        hpow)
  have hnegative :
      X ^ (-(m : ℤ)) = (X ^ m)⁻¹ :=
    zpow_neg X m
  have hproduct :
      A * X ^ (-(m : ℤ)) = A / X ^ m :=
    Eq.trans
      (congrArg (fun v : ℝ => A * v) hnegative)
      (div_eq_mul_inv A (X ^ m)).symm
  exact Eq.subst
    (motive := fun v : ℝ => 1 ≤ v)
    hproduct.symm
    hdiv

/-- The low-frequency reciprocal decay weight absorbs the `2 ^ m` renormalization. -/
theorem zetaPaleyWiener_lowFrequency_two_pow_mul_negative_zpow_ge_one
    (m : ℕ) {y : ℝ} (hy : ‖y‖ ≤ 1) :
    1 ≤ (2 : ℝ) ^ m * (1 + ‖y‖) ^ (-(m : ℤ)) := by
  exact zetaPaleyWiener_pow_bound_mul_negative_zpow_ge_one
    ((2 : ℝ) ^ m)
    (1 + ‖y‖)
    m
    (zetaPaleyWiener_realDecayBase_pos y)
    (zetaPaleyWiener_lowFrequency_realDecayBase_pow_le_two_pow m hy)

/-- The positive-order low-frequency decay weight absorbs one bounded constant after
renormalization by `2 ^ (N + 1)`. -/
theorem zetaPaleyWiener_lowFrequency_decayWeight_absorbs_unit
    (N : ℕ) {y : ℝ} (hy : ‖y‖ ≤ 1) :
    1 ≤ (2 : ℝ) ^ (Nat.succ N) *
        (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) := by
  exact zetaPaleyWiener_lowFrequency_two_pow_mul_negative_zpow_ge_one
    (Nat.succ N) hy

/-- A positive constant is absorbed by the low-frequency positive-order decay weight after
renormalization by `2 ^ (N + 1)`. -/
theorem zetaPaleyWiener_lowFrequency_decayWeight_absorbs_constant
    (C0 : ℝ) (hC0_nonneg : 0 ≤ C0) (N : ℕ) {y : ℝ} (hy : ‖y‖ ≤ 1) :
    C0 ≤
      (C0 * (2 : ℝ) ^ (Nat.succ N)) *
        (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) := by
  have hunit :
      1 ≤ (2 : ℝ) ^ (Nat.succ N) *
          (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) :=
    zetaPaleyWiener_lowFrequency_decayWeight_absorbs_unit N hy
  have hscaled :
      C0 * 1 ≤
        C0 *
          ((2 : ℝ) ^ (Nat.succ N) *
            (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ))) :=
    mul_le_mul_of_nonneg_left hunit hC0_nonneg
  have hleft :
      C0 * 1 = C0 :=
    mul_one C0
  have hright :
      C0 *
          ((2 : ℝ) ^ (Nat.succ N) *
            (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ))) =
        (C0 * (2 : ℝ) ^ (Nat.succ N)) *
          (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) := by
    exact (mul_assoc C0 ((2 : ℝ) ^ (Nat.succ N))
      ((1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)))).symm
  exact Eq.subst
    (motive := fun v : ℝ =>
      v ≤
        (C0 * (2 : ℝ) ^ (Nat.succ N)) *
          (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)))
    hleft
    (Eq.subst
      (motive := fun v : ℝ => C0 * 1 ≤ v)
      hright
      hscaled)

/-- Zero-order Fourier decay for the compactly supported horizontal-twist derivative
family. -/
theorem zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_zeroOrder_uniformDecay
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ x y : ℝ,
        a ≤ x →
        x ≤ b →
        ‖∫ t : ℝ,
          zetaPaleyWienerVerticalLineIBPDerivative f x t *
            zetaPaleyWienerVerticalOscillation y t‖
          ≤ C * (1 + ‖y‖) ^ (-(0 : ℤ)) := by
  rcases zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_zeroOrder_uniformBound
      f I a b with ⟨C, hCpos, hCbound⟩
  refine ⟨C, hCpos, ?_⟩
  intro x y hx_left hx_right
  have hweight :
      C * (1 + ‖y‖) ^ (-(0 : ℤ)) = C := by
    exact Eq.trans
      (congrArg (fun v : ℝ => C * v) (zetaPaleyWiener_zeroDecayWeight y))
      (mul_one C)
  exact Eq.subst
    (motive := fun v : ℝ =>
      ‖∫ t : ℝ,
        zetaPaleyWienerVerticalLineIBPDerivative f x t *
          zetaPaleyWienerVerticalOscillation y t‖ ≤ v)
    hweight.symm
    (hCbound x y hx_left hx_right)

/-- Low-frequency positive-order Fourier decay follows from the zero-order bound after
renormalizing the constant on `|y| ≤ 1`. -/
theorem zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrder_lowFrequency
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ x y : ℝ,
        a ≤ x →
        x ≤ b →
        ‖y‖ ≤ 1 →
        ‖∫ t : ℝ,
          zetaPaleyWienerVerticalLineIBPDerivative f x t *
            zetaPaleyWienerVerticalOscillation y t‖
          ≤ C * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) := by
  rcases zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_zeroOrder_uniformBound
      f I a b with ⟨C0, hC0pos, hC0bound⟩
  refine ⟨C0 * (2 : ℝ) ^ (Nat.succ N),
    mul_pos hC0pos (pow_pos zero_lt_two (Nat.succ N)), ?_⟩
  intro x y hx_left hx_right hy
  have hzero :
      ‖∫ t : ℝ,
        zetaPaleyWienerVerticalLineIBPDerivative f x t *
          zetaPaleyWienerVerticalOscillation y t‖ ≤ C0 :=
    hC0bound x y hx_left hx_right
  have habsorb :
      C0 ≤
        (C0 * (2 : ℝ) ^ (Nat.succ N)) *
          (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) :=
    zetaPaleyWiener_lowFrequency_decayWeight_absorbs_constant
      C0 (le_of_lt hC0pos) N hy
  exact le_trans hzero habsorb

/-- The arbitrary iterated-derivative oscillatory kernel is integrable. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryKernel_integrable
    (f : ZetaAdmissibleFunction) (n : ℕ) (x y : ℝ) :
    Integrable
      (fun t : ℝ => zetaPaleyWienerIteratedDerivativeOscillatoryKernel f n x y t) := by
  exact (zetaPaleyWienerIteratedDerivativeOscillatoryKernel_continuous
    f n x y).integrable_of_hasCompactSupport
      (zetaPaleyWienerIteratedDerivativeOscillatoryKernel_hasCompactSupport f n x y)

/-- Zero-order compact-support bound for arbitrary iterated horizontal-twist derivative
oscillatory integrals. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_zeroOrder_uniformBound
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (start : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ x y : ℝ,
        a ≤ x →
        x ≤ b →
        ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f start x y‖ ≤ C := by
  rcases exists_zetaPaleyWienerHorizontalTwistIteratedDerivative_uniformSeminorm
      f I a b start with ⟨C0, hC0pos, hC0bound⟩
  let C : ℝ := C0 * zetaPaleyWienerSupportIntervalLength I + 1
  have hC0_nonneg : 0 ≤ C0 :=
    le_of_lt hC0pos
  have hraw_nonneg :
      0 ≤ C0 * zetaPaleyWienerSupportIntervalLength I :=
    mul_nonneg hC0_nonneg (zetaPaleyWienerSupportIntervalLength_nonnegative I)
  have hCpos : 0 < C :=
    lt_of_le_of_lt hraw_nonneg
      (lt_add_of_pos_right
        (C0 * zetaPaleyWienerSupportIntervalLength I)
        zero_lt_one)
  refine ⟨C, hCpos, ?_⟩
  intro x y hx_left hx_right
  have hsource_bound :
      ∀ t : ℝ,
        t ∈ tsupport f.toZetaTestFunction →
        ‖zetaPaleyWienerHorizontalTwistIteratedDerivative f start x t‖ ≤ C0 := by
    intro t _ht
    exact hC0bound x hx_left hx_right t
  have hraw :
      ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f start x y‖ ≤
        C0 * zetaPaleyWienerSupportIntervalLength I :=
    zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_norm_le_intervalLength_mul_bound
      f I start x y C0 hC0_nonneg
      (zetaPaleyWienerIteratedDerivativeOscillatoryKernel_integrable f start x y)
      hsource_bound
  have hle :
      C0 * zetaPaleyWienerSupportIntervalLength I ≤
        C0 * zetaPaleyWienerSupportIntervalLength I + 1 :=
    le_add_of_nonneg_right zero_le_one
  exact le_trans hraw hle

/-- Zero-order high-frequency decay for arbitrary iterated derivative oscillatory integrals
is just the compact-support bound, since the zeroth decay weight is one. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_highFrequency_zeroOrder_decay
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (start : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ x y : ℝ,
        a ≤ x →
        x ≤ b →
        1 ≤ ‖y‖ →
        ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f start x y‖
          ≤ C * (1 + ‖y‖) ^ (-(0 : ℤ)) := by
  rcases zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_zeroOrder_uniformBound
      f I a b start with ⟨C, hCpos, hCbound⟩
  refine ⟨C, hCpos, ?_⟩
  intro x y hx_left hx_right _hy
  have hweight :
      C * (1 + ‖y‖) ^ (-(0 : ℤ)) = C := by
    exact Eq.trans
      (congrArg (fun v : ℝ => C * v) (zetaPaleyWiener_zeroDecayWeight y))
      (mul_one C)
  exact Eq.subst
    (motive := fun v : ℝ =>
      ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f start x y‖ ≤ v)
    hweight.symm
    (hCbound x y hx_left hx_right)

/-- The arbitrary iterated horizontal-twist derivative source is smooth. -/
theorem zetaPaleyWienerHorizontalTwistIteratedDerivative_contDiff
    (f : ZetaAdmissibleFunction) (start : ℕ) (x : ℝ) :
    ContDiff ℝ ∞
      (fun t : ℝ => zetaPaleyWienerHorizontalTwistIteratedDerivative f start x t) := by
  have hjet_plane :
      ContDiff ℝ ∞
        (fun p : ℝ × ℝ =>
          zetaPaleyWienerHorizontalTwistVerticalJet f start p.1 p.2) :=
    zetaPaleyWienerHorizontalTwistVerticalJet_contDiff f start
  have hline :
      ContDiff ℝ ∞ (fun t : ℝ => (x, t)) :=
    contDiff_const.prod contDiff_id
  have hjet_line :
      ContDiff ℝ ∞
        (fun t : ℝ => zetaPaleyWienerHorizontalTwistVerticalJet f start x t) :=
    hjet_plane.comp hline
  have hfun :
      (fun t : ℝ => zetaPaleyWienerHorizontalTwistIteratedDerivative f start x t) =
        fun t : ℝ => zetaPaleyWienerHorizontalTwistVerticalJet f start x t :=
    funext
      (fun t : ℝ =>
        zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_verticalJet f start x t)
  exact Eq.subst
    (motive := fun g : ℝ → ℂ => ContDiff ℝ ∞ g)
    hfun.symm
    hjet_line

/-- The arbitrary iterated horizontal-twist derivative source is differentiable. -/
theorem zetaPaleyWienerHorizontalTwistIteratedDerivative_differentiableAt
    (f : ZetaAdmissibleFunction) (start : ℕ) (x t : ℝ) :
    DifferentiableAt ℝ
      (fun u : ℝ => zetaPaleyWienerHorizontalTwistIteratedDerivative f start x u)
      t := by
  exact (zetaPaleyWienerHorizontalTwistIteratedDerivative_contDiff
    f start x).differentiable le_top t

/-- The derivative value of the `start`th iterated source is the successor iterated source. -/
theorem deriv_zetaPaleyWienerHorizontalTwistIteratedDerivative
    (f : ZetaAdmissibleFunction) (start : ℕ) (x t : ℝ) :
    deriv
      (fun u : ℝ => zetaPaleyWienerHorizontalTwistIteratedDerivative f start x u)
      t =
      zetaPaleyWienerHorizontalTwistIteratedDerivative f (start + 1) x t := by
  exact (zetaPaleyWienerHorizontalTwistIteratedDerivative_succ f start x t).symm

/-- The derivative of the `start`th iterated source is the successor iterated source. -/
theorem hasDerivAt_zetaPaleyWienerHorizontalTwistIteratedDerivative
    (f : ZetaAdmissibleFunction) (start : ℕ) (x t : ℝ) :
    HasDerivAt
      (fun u : ℝ => zetaPaleyWienerHorizontalTwistIteratedDerivative f start x u)
      (zetaPaleyWienerHorizontalTwistIteratedDerivative f (start + 1) x t)
      t := by
  have hderiv :
      HasDerivAt
        (fun u : ℝ => zetaPaleyWienerHorizontalTwistIteratedDerivative f start x u)
        (deriv
          (fun u : ℝ => zetaPaleyWienerHorizontalTwistIteratedDerivative f start x u)
          t)
        t :=
    (zetaPaleyWienerHorizontalTwistIteratedDerivative_differentiableAt
      f start x t).hasDerivAt
  exact Eq.subst
    (motive := fun v : ℂ =>
      HasDerivAt
        (fun u : ℝ => zetaPaleyWienerHorizontalTwistIteratedDerivative f start x u)
        v
        t)
    (deriv_zetaPaleyWienerHorizontalTwistIteratedDerivative f start x t)
    hderiv

/-- The boundary term for arbitrary iterated derivative oscillatory integration by parts
vanishes at strict cutoffs outside the certified support interval. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_boundaryTerm_eq_zero
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (start : ℕ) (x y lower upper : ℝ)
    (hlower : lower < I.lower) (hupper : I.upper < upper) :
    zetaPaleyWienerHorizontalTwistIteratedDerivative f start x upper *
        zetaPaleyWienerVerticalOscillation y upper -
      zetaPaleyWienerHorizontalTwistIteratedDerivative f start x lower *
        zetaPaleyWienerVerticalOscillation y lower =
      0 := by
  have hupper_zero :
      zetaPaleyWienerHorizontalTwistIteratedDerivative f start x upper = 0 :=
    zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_zero_of_supportInterval_lt
      f I start x upper hupper
  have hlower_zero :
      zetaPaleyWienerHorizontalTwistIteratedDerivative f start x lower = 0 :=
    zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_zero_off_supportInterval
      f I start x lower hlower
  calc
    zetaPaleyWienerHorizontalTwistIteratedDerivative f start x upper *
          zetaPaleyWienerVerticalOscillation y upper -
        zetaPaleyWienerHorizontalTwistIteratedDerivative f start x lower *
          zetaPaleyWienerVerticalOscillation y lower
        = 0 * zetaPaleyWienerVerticalOscillation y upper -
            zetaPaleyWienerHorizontalTwistIteratedDerivative f start x lower *
              zetaPaleyWienerVerticalOscillation y lower := by
          exact congrArg
            (fun v : ℂ =>
              v * zetaPaleyWienerVerticalOscillation y upper -
                zetaPaleyWienerHorizontalTwistIteratedDerivative f start x lower *
                  zetaPaleyWienerVerticalOscillation y lower)
            hupper_zero
    _ = 0 - zetaPaleyWienerHorizontalTwistIteratedDerivative f start x lower *
            zetaPaleyWienerVerticalOscillation y lower := by
          exact congrArg
            (fun v : ℂ =>
              v - zetaPaleyWienerHorizontalTwistIteratedDerivative f start x lower *
                zetaPaleyWienerVerticalOscillation y lower)
            (zero_mul (zetaPaleyWienerVerticalOscillation y upper))
    _ = 0 - 0 * zetaPaleyWienerVerticalOscillation y lower := by
          exact congrArg
            (fun v : ℂ => 0 - v * zetaPaleyWienerVerticalOscillation y lower)
            hlower_zero
    _ = 0 - 0 := by
          exact congrArg
            (fun v : ℂ => 0 - v)
            (zero_mul (zetaPaleyWienerVerticalOscillation y lower))
    _ = 0 := sub_zero 0

/-- The frequency-multiplied oscillatory kernel for an iterated source is integrable. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryKernel_frequency_integrable
    (f : ZetaAdmissibleFunction) (start : ℕ) (x y : ℝ) :
    Integrable
      (fun t : ℝ =>
        zetaPaleyWienerHorizontalTwistIteratedDerivative f start x t *
          ((Complex.I * (y : ℂ)) *
            zetaPaleyWienerVerticalOscillation y t)) := by
  have hcontinuous :
      Continuous
        (fun t : ℝ =>
          zetaPaleyWienerHorizontalTwistIteratedDerivative f start x t *
            ((Complex.I * (y : ℂ)) *
              zetaPaleyWienerVerticalOscillation y t)) := by
    exact (zetaPaleyWienerHorizontalTwistIteratedDerivative_continuous f start x).mul
      (continuous_const.mul
        (Complex.continuous_exp.comp
          ((continuous_const.mul continuous_const).mul Complex.continuous_ofReal)))
  have hsupport :
      HasCompactSupport
        (fun t : ℝ =>
          zetaPaleyWienerHorizontalTwistIteratedDerivative f start x t *
            ((Complex.I * (y : ℂ)) *
              zetaPaleyWienerVerticalOscillation y t)) := by
    exact (zetaPaleyWienerHorizontalTwistIteratedDerivative_hasCompactSupport
      f start x).mul_right
  exact hcontinuous.integrable_of_hasCompactSupport hsupport

/-- The product-rule integration-by-parts identity for the `start`th iterated source. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_integral_mul_frequency_eq_neg_succ
    (f : ZetaAdmissibleFunction) (start : ℕ) (x y : ℝ) :
    (∫ t : ℝ,
        zetaPaleyWienerHorizontalTwistIteratedDerivative f start x t *
          (Complex.I * (y : ℂ) * zetaPaleyWienerVerticalOscillation y t)) =
      -∫ t : ℝ,
        zetaPaleyWienerHorizontalTwistIteratedDerivative f (start + 1) x t *
          zetaPaleyWienerVerticalOscillation y t := by
  let A : ℂ := Complex.I * (y : ℂ)
  let H : ℝ → ℂ :=
    fun t : ℝ => zetaPaleyWienerHorizontalTwistIteratedDerivative f start x t
  let V : ℝ → ℂ :=
    fun t : ℝ => zetaPaleyWienerVerticalOscillation y t
  let D : ℝ → ℂ :=
    fun t : ℝ => zetaPaleyWienerHorizontalTwistIteratedDerivative f (start + 1) x t
  have hH :
      ∀ t : ℝ, HasDerivAt H (D t) t := by
    intro t
    exact hasDerivAt_zetaPaleyWienerHorizontalTwistIteratedDerivative f start x t
  have hV :
      ∀ t : ℝ, HasDerivAt V (A * V t) t := by
    intro t
    exact hasDerivAt_zetaPaleyWienerVerticalOscillation y t
  have hHDV :
      Integrable (fun t : ℝ => H t * (A * V t)) := by
    exact zetaPaleyWienerIteratedDerivativeOscillatoryKernel_frequency_integrable
      f start x y
  have hDV :
      Integrable (fun t : ℝ => D t * V t) := by
    exact zetaPaleyWienerIteratedDerivativeOscillatoryKernel_integrable
      f (start + 1) x y
  have hHV :
      Integrable (fun t : ℝ => H t * V t) := by
    exact zetaPaleyWienerIteratedDerivativeOscillatoryKernel_integrable
      f start x y
  exact MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    hH hV hHDV hDV hHV

/-- Pulling the constant vertical frequency out of the current oscillatory integral. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_frequency_mul_eq_integral
    (f : ZetaAdmissibleFunction) (start : ℕ) (x y : ℝ) :
    (Complex.I * (y : ℂ)) *
        zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f start x y =
      ∫ t : ℝ,
        zetaPaleyWienerHorizontalTwistIteratedDerivative f start x t *
          (Complex.I * (y : ℂ) * zetaPaleyWienerVerticalOscillation y t) := by
  let A : ℂ := Complex.I * (y : ℂ)
  let H : ℝ → ℂ :=
    fun t : ℝ => zetaPaleyWienerHorizontalTwistIteratedDerivative f start x t
  let V : ℝ → ℂ :=
    fun t : ℝ => zetaPaleyWienerVerticalOscillation y t
  have hright_integrand :
      (fun t : ℝ => H t * (A * V t)) =
        fun t : ℝ => A * (H t * V t) := by
    funext t
    calc
      H t * (A * V t) = (H t * A) * V t := by
        exact (mul_assoc (H t) A (V t)).symm
      _ = (A * H t) * V t := by
        exact congrArg (fun v : ℂ => v * V t) (mul_comm (H t) A)
      _ = A * (H t * V t) := by
        exact mul_assoc A (H t) (V t)
  have hintegral :
      (∫ t : ℝ, H t * (A * V t)) =
        A * ∫ t : ℝ, H t * V t := by
    exact Eq.trans
      (congrArg
        (fun q : ℝ → ℂ => ∫ t : ℝ, q t)
        hright_integrand)
      (integral_const_mul A (fun t : ℝ => H t * V t))
  unfold zetaPaleyWienerIteratedDerivativeOscillatoryIntegral
  unfold zetaPaleyWienerIteratedDerivativeOscillatoryKernel
  exact hintegral.symm

/-- The successor iterated source integral is the successor oscillatory integral. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_succ_integral_eq
    (f : ZetaAdmissibleFunction) (start : ℕ) (x y : ℝ) :
    (∫ t : ℝ,
        zetaPaleyWienerHorizontalTwistIteratedDerivative f (start + 1) x t *
          zetaPaleyWienerVerticalOscillation y t) =
      zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f (start + 1) x y := by
  rfl

/-- One integration-by-parts identity for arbitrary iterated derivative oscillatory
integrals, before solving for the current integral. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_mul_frequency_eq_neg_succ
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (start : ℕ) (x y : ℝ) :
    (Complex.I * (y : ℂ)) *
        zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f start x y =
      -zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f (start + 1) x y := by
  have hleft :
      (Complex.I * (y : ℂ)) *
          zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f start x y =
        ∫ t : ℝ,
          zetaPaleyWienerHorizontalTwistIteratedDerivative f start x t *
            (Complex.I * (y : ℂ) * zetaPaleyWienerVerticalOscillation y t) :=
    zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_frequency_mul_eq_integral
      f start x y
  have hibp :
      (∫ t : ℝ,
          zetaPaleyWienerHorizontalTwistIteratedDerivative f start x t *
            (Complex.I * (y : ℂ) * zetaPaleyWienerVerticalOscillation y t)) =
        -∫ t : ℝ,
          zetaPaleyWienerHorizontalTwistIteratedDerivative f (start + 1) x t *
            zetaPaleyWienerVerticalOscillation y t :=
    zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_integral_mul_frequency_eq_neg_succ
      f start x y
  have hright :
      (∫ t : ℝ,
          zetaPaleyWienerHorizontalTwistIteratedDerivative f (start + 1) x t *
            zetaPaleyWienerVerticalOscillation y t) =
        zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f (start + 1) x y :=
    zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_succ_integral_eq
      f start x y
  exact hleft.trans
    (hibp.trans
      (congrArg Neg.neg hright))

/-- Solving the arbitrary iterated integration-by-parts identity for the current integral. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_eq_I_mul_inverse_mul_succ
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (start : ℕ) (x y : ℝ) (hy : (y : ℂ) ≠ 0) :
    zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f start x y =
      Complex.I * (y : ℂ)⁻¹ *
        zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f (start + 1) x y := by
  let K : ℂ := zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f start x y
  let D : ℂ := zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f (start + 1) x y
  let A : ℂ := Complex.I * (y : ℂ)
  have hA : A ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero hy
  have hibp :
      A * K = -D :=
    zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_mul_frequency_eq_neg_succ
      f I start x y
  have hcandidate :
      A * (Complex.I * (y : ℂ)⁻¹ * D) = -D :=
    zetaPaleyWiener_frequency_mul_solvedIntegral y hy D
  exact mul_left_cancel₀ hA (hibp.trans hcandidate.symm)

/-- Norm comparison produced by one arbitrary iterated integration-by-parts step. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_norm_le_inverse_mul_succ
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (start : ℕ) (x y : ℝ) (hy : (y : ℂ) ≠ 0) :
    ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f start x y‖ ≤
      ‖(y : ℂ)⁻¹‖ *
        ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f (start + 1) x y‖ := by
  have hidentity :
      zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f start x y =
        Complex.I * (y : ℂ)⁻¹ *
          zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f (start + 1) x y :=
    zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_eq_I_mul_inverse_mul_succ
      f I start x y hy
  have hnorm :
      ‖Complex.I * (y : ℂ)⁻¹ *
          zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f (start + 1) x y‖ ≤
        ‖(y : ℂ)⁻¹‖ *
          ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f (start + 1) x y‖ :=
    norm_I_mul_inverse_mul_verticalLineIBPDerivativeIntegral_le
      y
      (zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f (start + 1) x y)
  exact Eq.subst
    (motive := fun v : ℝ =>
      v ≤ ‖(y : ℂ)⁻¹‖ *
        ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f (start + 1) x y‖)
    (congrArg (fun v : ℂ => ‖v‖) hidentity).symm
    hnorm

/-- Real-frequency high-frequency inverse weight comparison for one successor step. -/
theorem zetaPaleyWiener_inverseReal_mul_realWeight_le_successor_highFrequency
    (y : ℝ) (N : ℕ) (hy : 1 ≤ ‖y‖) :
    ‖(y : ℂ)⁻¹‖ * (1 + ‖y‖) ^ (-(N : ℤ)) ≤
      2 * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) := by
  let z : ℂ := (y : ℂ) * Complex.I
  have hz_im :
      z.im = y := by
    unfold z
    exact paley_ofReal_mul_I_im y
  have hz_norm :
      ‖z.im‖ = ‖y‖ :=
    congrArg (fun v : ℝ => ‖v‖) hz_im
  have hz_high :
      1 ≤ ‖z.im‖ :=
    Eq.subst
      (motive := fun v : ℝ => 1 ≤ v)
      hz_norm.symm
      hy
  have hbase :
      ‖(z.im : ℂ)⁻¹‖ * zetaPaleyWienerVerticalWeight z N ≤
        2 * zetaPaleyWienerVerticalWeight z (N + 1) :=
    zetaPaleyWiener_inverseIm_mul_weight_le_successor_highFrequency
      z N hz_high
  have hinv :
      ‖(z.im : ℂ)⁻¹‖ = ‖(y : ℂ)⁻¹‖ :=
    congrArg (fun v : ℝ => ‖(v : ℂ)⁻¹‖) hz_im
  have hweightN :
      zetaPaleyWienerVerticalWeight z N =
        (1 + ‖y‖) ^ (-(N : ℤ)) := by
    unfold zetaPaleyWienerVerticalWeight
    exact congrArg (fun v : ℝ => (1 + v) ^ (-(N : ℤ))) hz_norm
  have hweightSucc :
      zetaPaleyWienerVerticalWeight z (N + 1) =
        (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) := by
    unfold zetaPaleyWienerVerticalWeight
    have hsucc :
        (-(N + 1 : ℤ)) = -((Nat.succ N : ℕ) : ℤ) := by
      exact congrArg Neg.neg (Nat.cast_add_one N)
    exact Eq.trans
      (congrArg (fun v : ℝ => (1 + v) ^ (-(N + 1 : ℤ))) hz_norm)
      (congrArg (fun e : ℤ => (1 + ‖y‖) ^ e) hsucc)
  exact Eq.subst
    (motive := fun v : ℝ =>
      v * (1 + ‖y‖) ^ (-(N : ℤ)) ≤
        2 * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)))
    hinv
    (Eq.subst
      (motive := fun v : ℝ =>
        ‖(z.im : ℂ)⁻¹‖ * v ≤
          2 * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)))
      hweightN
      (Eq.subst
        (motive := fun v : ℝ =>
          ‖(z.im : ℂ)⁻¹‖ * zetaPaleyWienerVerticalWeight z N ≤ 2 * v)
        hweightSucc
        hbase))

/-- One high-frequency decay transport step after the arbitrary iterated integration by
parts norm comparison. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_highFrequency_successor_bound
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (start N : ℕ)
    (C : ℝ) (hCpos : 0 < C)
    (hnext :
      ∀ x y : ℝ,
        a ≤ x →
        x ≤ b →
        1 ≤ ‖y‖ →
        ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f (start + 1) x y‖
          ≤ C * (1 + ‖y‖) ^ (-(N : ℤ))) :
    ∀ x y : ℝ,
      a ≤ x →
      x ≤ b →
      1 ≤ ‖y‖ →
      ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f start x y‖
        ≤ (C * 2) * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) := by
  intro x y hx_left hx_right hy
  have hy_ne : (y : ℂ) ≠ 0 :=
    zetaPaleyWienerVerticalFrequency_ne_zero_of_high hy
  have hparts :
      ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f start x y‖ ≤
        ‖(y : ℂ)⁻¹‖ *
          ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f (start + 1) x y‖ :=
    zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_norm_le_inverse_mul_succ
      f I start x y hy_ne
  have hnext_bound :
      ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f (start + 1) x y‖
        ≤ C * (1 + ‖y‖) ^ (-(N : ℤ)) :=
    hnext x y hx_left hx_right hy
  have hinv_nonneg : 0 ≤ ‖(y : ℂ)⁻¹‖ :=
    norm_nonneg ((y : ℂ)⁻¹)
  have hwith_inv :
      ‖(y : ℂ)⁻¹‖ *
          ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f (start + 1) x y‖
        ≤ ‖(y : ℂ)⁻¹‖ *
          (C * (1 + ‖y‖) ^ (-(N : ℤ))) :=
    mul_le_mul_of_nonneg_left hnext_bound hinv_nonneg
  have hC_nonneg : 0 ≤ C :=
    le_of_lt hCpos
  have hweight :
      ‖(y : ℂ)⁻¹‖ * (1 + ‖y‖) ^ (-(N : ℤ)) ≤
        2 * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) :=
    zetaPaleyWiener_inverseReal_mul_realWeight_le_successor_highFrequency
      y N hy
  have hrearrange :
      ‖(y : ℂ)⁻¹‖ * (C * (1 + ‖y‖) ^ (-(N : ℤ))) =
        C * (‖(y : ℂ)⁻¹‖ * (1 + ‖y‖) ^ (-(N : ℤ))) := by
    calc
      ‖(y : ℂ)⁻¹‖ * (C * (1 + ‖y‖) ^ (-(N : ℤ))) =
          (‖(y : ℂ)⁻¹‖ * C) * (1 + ‖y‖) ^ (-(N : ℤ)) := by
        exact (mul_assoc ‖(y : ℂ)⁻¹‖ C ((1 + ‖y‖) ^ (-(N : ℤ)))).symm
      _ = (C * ‖(y : ℂ)⁻¹‖) * (1 + ‖y‖) ^ (-(N : ℤ)) := by
        exact congrArg
          (fun v : ℝ => v * (1 + ‖y‖) ^ (-(N : ℤ)))
          (mul_comm ‖(y : ℂ)⁻¹‖ C)
      _ = C * (‖(y : ℂ)⁻¹‖ * (1 + ‖y‖) ^ (-(N : ℤ))) := by
        exact mul_assoc C ‖(y : ℂ)⁻¹‖ ((1 + ‖y‖) ^ (-(N : ℤ)))
  have hrenorm :
      C * (‖(y : ℂ)⁻¹‖ * (1 + ‖y‖) ^ (-(N : ℤ))) ≤
        C * (2 * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ))) :=
    mul_le_mul_of_nonneg_left hweight hC_nonneg
  have htarget :
      C * (2 * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ))) =
        (C * 2) * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) := by
    exact (mul_assoc C 2 ((1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)))).symm
  exact hparts.trans
    (hwith_inv.trans
      (Eq.subst
        (motive := fun v : ℝ =>
          v ≤ (C * 2) * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)))
        hrearrange.symm
        (hrenorm.trans_eq htarget)))

/-- One high-frequency integration-by-parts step for arbitrary iterated derivative
oscillatory integrals, stated as a recurrence from the next derivative source. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_highFrequency_successor_from_next_decay
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (start N : ℕ)
    (hnext :
      ∃ C : ℝ,
        0 < C ∧
        ∀ x y : ℝ,
          a ≤ x →
          x ≤ b →
          1 ≤ ‖y‖ →
          ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f (start + 1) x y‖
            ≤ C * (1 + ‖y‖) ^ (-(N : ℤ))) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ x y : ℝ,
        a ≤ x →
        x ≤ b →
        1 ≤ ‖y‖ →
        ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f start x y‖
          ≤ C * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) := by
  rcases hnext with ⟨C, hCpos, hCbound⟩
  exact ⟨C * 2, mul_pos hCpos zero_lt_two,
    zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_highFrequency_successor_bound
      f I a b start N C hCpos hCbound⟩

/-- High-frequency decay for arbitrary iterated horizontal-twist derivative oscillatory
integrals.  This is the canonical repeated-integration-by-parts statement: starting from
the `start`th derivative source, `N` further integrations by parts give `N` powers of
vertical-frequency decay. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_highFrequency_decay
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (start N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ x y : ℝ,
        a ≤ x →
        x ≤ b →
        1 ≤ ‖y‖ →
        ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f start x y‖
          ≤ C * (1 + ‖y‖) ^ (-(N : ℤ)) := by
  induction N generalizing start with
  | zero =>
      exact zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_highFrequency_zeroOrder_decay
        f I a b start
  | succ N ih =>
      have hnext :
          ∃ C : ℝ,
            0 < C ∧
            ∀ x y : ℝ,
              a ≤ x →
              x ≤ b →
              1 ≤ ‖y‖ →
              ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f (start + 1) x y‖
                ≤ C * (1 + ‖y‖) ^ (-(N : ℤ)) :=
        ih (start + 1)
      exact
        zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_highFrequency_successor_from_next_decay
          f I a b start N hnext

/-- High-frequency positive-order Fourier decay is the genuine repeated integration by
parts recurrence. -/
theorem zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrder_highFrequency
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ x y : ℝ,
        a ≤ x →
        x ≤ b →
        1 ≤ ‖y‖ →
        ‖∫ t : ℝ,
          zetaPaleyWienerVerticalLineIBPDerivative f x t *
            zetaPaleyWienerVerticalOscillation y t‖
          ≤ C * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) := by
  rcases zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_highFrequency_decay
      f I a b 1 (Nat.succ N) with ⟨C, hCpos, hCbound⟩
  refine ⟨C, hCpos, ?_⟩
  intro x y hx_left hx_right hy
  have hiter :
      ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f 1 x y‖
        ≤ C * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) :=
    hCbound x y hx_left hx_right hy
  exact Eq.subst
    (motive := fun v : ℂ =>
      ‖v‖ ≤ C * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)))
    (zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_one f x y)
    hiter

/-- Low- and high-frequency positive-order estimates combine into the global estimate. -/
theorem zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrder_from_low_high
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ)
    (hlow :
      ∃ C : ℝ,
        0 < C ∧
        ∀ x y : ℝ,
          a ≤ x →
          x ≤ b →
          ‖y‖ ≤ 1 →
          ‖∫ t : ℝ,
            zetaPaleyWienerVerticalLineIBPDerivative f x t *
              zetaPaleyWienerVerticalOscillation y t‖
            ≤ C * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)))
    (hhigh :
      ∃ C : ℝ,
        0 < C ∧
        ∀ x y : ℝ,
          a ≤ x →
          x ≤ b →
          1 ≤ ‖y‖ →
          ‖∫ t : ℝ,
            zetaPaleyWienerVerticalLineIBPDerivative f x t *
              zetaPaleyWienerVerticalOscillation y t‖
            ≤ C * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ))) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ x y : ℝ,
        a ≤ x →
        x ≤ b →
        ‖∫ t : ℝ,
          zetaPaleyWienerVerticalLineIBPDerivative f x t *
            zetaPaleyWienerVerticalOscillation y t‖
          ≤ C * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) := by
  rcases hlow with ⟨Clow, hClow_pos, hClow⟩
  rcases hhigh with ⟨Chigh, hChigh_pos, hChigh⟩
  refine ⟨max Clow Chigh, lt_of_lt_of_le hClow_pos (le_max_left Clow Chigh), ?_⟩
  intro x y hx_left hx_right
  have hweight :
      0 ≤ (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) :=
    zetaPaleyWiener_realVerticalDecayWeight_nonnegative y (Nat.succ N)
  by_cases hlow_region : ‖y‖ ≤ 1
  · have hbound :
        ‖∫ t : ℝ,
          zetaPaleyWienerVerticalLineIBPDerivative f x t *
            zetaPaleyWienerVerticalOscillation y t‖
          ≤ Clow * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) :=
      hClow x y hx_left hx_right hlow_region
    have hconstant :
        Clow * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) ≤
          max Clow Chigh * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) :=
      mul_le_mul_of_nonneg_right (le_max_left Clow Chigh) hweight
    exact hbound.trans hconstant
  · have hhigh_region : 1 ≤ ‖y‖ :=
      le_of_lt (lt_of_not_ge hlow_region)
    have hbound :
        ‖∫ t : ℝ,
          zetaPaleyWienerVerticalLineIBPDerivative f x t *
            zetaPaleyWienerVerticalOscillation y t‖
          ≤ Chigh * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) :=
      hChigh x y hx_left hx_right hhigh_region
    have hconstant :
        Chigh * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) ≤
          max Clow Chigh * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) :=
      mul_le_mul_of_nonneg_right (le_max_right Clow Chigh) hweight
    exact hbound.trans hconstant

/-- Positive-order Fourier decay for the compactly supported horizontal-twist derivative
family is the repeated-integration-by-parts estimate. -/
theorem zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrder_uniformDecay
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ x y : ℝ,
        a ≤ x →
        x ≤ b →
        ‖∫ t : ℝ,
          zetaPaleyWienerVerticalLineIBPDerivative f x t *
            zetaPaleyWienerVerticalOscillation y t‖
          ≤ C * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) := by
  exact zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrder_from_low_high
    f I a b N
    (zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrder_lowFrequency
      f I a b N)
    (zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrder_highFrequency
      f I a b N)

/-- Fourier decay for the compactly supported horizontal-twist derivative family, with
constants uniform over the real-part strip. -/
theorem zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_uniformDecay
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ x y : ℝ,
        a ≤ x →
        x ≤ b →
        ‖∫ t : ℝ,
          zetaPaleyWienerVerticalLineIBPDerivative f x t *
            zetaPaleyWienerVerticalOscillation y t‖
          ≤ C * (1 + ‖y‖) ^ (-(N : ℤ)) := by
  cases N with
  | zero =>
      exact zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_zeroOrder_uniformDecay
        f I a b
  | succ N =>
      exact zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrder_uniformDecay
        f I a b N

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
  rcases zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_uniformDecay
      f I a b N with ⟨C, hCpos, hCbound⟩
  refine ⟨C, hCpos, ?_⟩
  intro x y hx_left hx_right
  unfold zetaPaleyWienerVerticalLineIBPDerivativeIntegral
  exact hCbound x y hx_left hx_right

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

/-- The finite Laplace-transform sample vector of an admissible function. -/
def zetaLaplaceTransformFiniteSample
    (S : Finset ℂ) (f : ZetaAdmissibleFunction) :
    S → ℂ :=
  fun z : S => Boundary.zetaLaplaceTransform f.toZetaTestFunction' (z : ℂ)

/-- The finite target vector induced by a function on the ambient spectral plane. -/
def zetaLaplaceTransformFiniteTarget
    (S : Finset ℂ) (a : ℂ → ℂ) :
    S → ℂ :=
  fun z : S => a (z : ℂ)

/-- The finite Laplace-sample vector of a scalar multiple is the scalar multiple of the
finite Laplace-sample vector. -/
theorem zetaLaplaceTransformFiniteSample_smul
    (S : Finset ℂ) (c : ℂ) (f : ZetaAdmissibleFunction) :
    zetaLaplaceTransformFiniteSample S (c • f) =
      c • zetaLaplaceTransformFiniteSample S f := by
  funext z
  unfold zetaLaplaceTransformFiniteSample
  have hpoint :
      (c • f).toZetaTestFunction' =
        c • f.toZetaTestFunction' := by
    ext t
    calc
      (c • f).toZetaTestFunction' t =
          (c • f) t := by
        exact ZetaAdmissibleFunction.toZetaTestFunction'_apply (c • f) t
      _ = c * f t := by
        exact ZetaAdmissibleFunction.smul_apply c f t
      _ = c * f.toZetaTestFunction' t := by
        exact congrArg (fun u : ℂ => c * u)
          (ZetaAdmissibleFunction.toZetaTestFunction'_apply f t).symm
      _ = (c • f.toZetaTestFunction') t := by
        rfl
  calc
    Boundary.zetaLaplaceTransform (c • f).toZetaTestFunction' (z : ℂ) =
        Boundary.zetaLaplaceTransform (c • f.toZetaTestFunction') (z : ℂ) := by
      exact congrFun (Boundary.zetaLaplaceTransform_congr
        (fun t : ℝ => congrFun hpoint t)) (z : ℂ)
    _ = c * Boundary.zetaLaplaceTransform f.toZetaTestFunction' (z : ℂ) := by
      exact Boundary.zetaLaplaceTransform_smul c f.toZetaTestFunction' (z : ℂ)
    _ = (c • zetaLaplaceTransformFiniteSample S f) z := by
      rfl

/-- The finite Laplace-sample vector of a sum is the sum of the finite Laplace-sample
vectors. -/
theorem zetaLaplaceTransformFiniteSample_add
    (S : Finset ℂ) (f g : ZetaAdmissibleFunction) :
    zetaLaplaceTransformFiniteSample S (f + g) =
      zetaLaplaceTransformFiniteSample S f +
        zetaLaplaceTransformFiniteSample S g := by
  funext z
  unfold zetaLaplaceTransformFiniteSample
  have hpoint :
      (f + g).toZetaTestFunction' =
        f.toZetaTestFunction' + g.toZetaTestFunction' := by
    ext t
    calc
      (f + g).toZetaTestFunction' t =
          (f + g) t := by
        exact ZetaAdmissibleFunction.toZetaTestFunction'_apply (f + g) t
      _ = f t + g t := by
        exact ZetaAdmissibleFunction.add_apply f g t
      _ = f.toZetaTestFunction' t + g.toZetaTestFunction' t := by
        exact congrArg₂ (fun u v : ℂ => u + v)
          (ZetaAdmissibleFunction.toZetaTestFunction'_apply f t).symm
          (ZetaAdmissibleFunction.toZetaTestFunction'_apply g t).symm
      _ = (f.toZetaTestFunction' + g.toZetaTestFunction') t := by
        rfl
  calc
    Boundary.zetaLaplaceTransform (f + g).toZetaTestFunction' (z : ℂ) =
        Boundary.zetaLaplaceTransform
          (f.toZetaTestFunction' + g.toZetaTestFunction') (z : ℂ) := by
      exact congrFun (Boundary.zetaLaplaceTransform_congr
        (fun t : ℝ => congrFun hpoint t)) (z : ℂ)
    _ =
        Boundary.zetaLaplaceTransform f.toZetaTestFunction' (z : ℂ) +
          Boundary.zetaLaplaceTransform g.toZetaTestFunction' (z : ℂ) := by
      exact Boundary.zetaLaplaceTransform_add
        f.toZetaTestFunction'
        g.toZetaTestFunction'
        (z : ℂ)
        (integrable_laplaceKernel_at f (z : ℂ))
        (integrable_laplaceKernel_at g (z : ℂ))
    _ =
        (zetaLaplaceTransformFiniteSample S f +
          zetaLaplaceTransformFiniteSample S g) z := by
      rfl

/-- The finite Laplace-sample map as a bundled linear map. -/
def zetaLaplaceTransformFiniteSampleLinearMap
    (S : Finset ℂ) :
    ZetaAdmissibleFunction →ₗ[ℂ] (S → ℂ) where
  toFun := zetaLaplaceTransformFiniteSample S
  map_add' := fun f g =>
    zetaLaplaceTransformFiniteSample_add S f g
  map_smul' := fun c f =>
    zetaLaplaceTransformFiniteSample_smul S c f

/-- The finite Laplace-sample vector of a finite sum is the finite sum of the sample
vectors. -/
theorem zetaLaplaceTransformFiniteSample_sum
    {α : Type*} [DecidableEq α]
    (S : Finset ℂ) (T : Finset α) (F : α → ZetaAdmissibleFunction) :
    zetaLaplaceTransformFiniteSample S (∑ x in T, F x) =
      ∑ x in T, zetaLaplaceTransformFiniteSample S (F x) := by
  funext z
  unfold zetaLaplaceTransformFiniteSample
  have hpoint :
      (∑ x in T, F x).toZetaTestFunction' =
        ∑ x in T, (F x).toZetaTestFunction' := by
    ext t
    calc
      (∑ x in T, F x).toZetaTestFunction' t =
          (∑ x in T, F x) t := by
        exact ZetaAdmissibleFunction.toZetaTestFunction'_apply (∑ x in T, F x) t
      _ = ∑ x in T, F x t := by
        exact ZetaAdmissibleFunction.sum_apply T F t
      _ = (∑ x in T, (F x).toZetaTestFunction') t := by
        exact (Boundary.zetaLaplaceTransform_sum_apply
          (s := T)
          (f := fun x : α => (F x).toZetaTestFunction')
          t).symm
  calc
    Boundary.zetaLaplaceTransform (∑ x in T, F x).toZetaTestFunction' (z : ℂ) =
        Boundary.zetaLaplaceTransform (∑ x in T, (F x).toZetaTestFunction') (z : ℂ) := by
      exact congrFun (Boundary.zetaLaplaceTransform_congr
        (fun t : ℝ => congrFun hpoint t)) (z : ℂ)
    _ =
        ∑ x in T,
          Boundary.zetaLaplaceTransform (F x).toZetaTestFunction' (z : ℂ) := by
      exact Boundary.zetaLaplaceTransform_sum
        T
        (fun x : α => (F x).toZetaTestFunction')
        (z : ℂ)
        (fun x _hx => integrable_laplaceKernel_at (F x) (z : ℂ))
    _ = (∑ x in T, zetaLaplaceTransformFiniteSample S (F x)) z := by
      exact (T.sum_apply z
        (fun x : α => zetaLaplaceTransformFiniteSample S (F x))).symm

/-- A cardinal family gives the finite linear-combination interpolant for any target
finite sample vector. -/
theorem zetaLaplaceTransformFiniteSample_linearCombination_cardinalFamily
    (S : Finset ℂ) (aS : S → ℂ) (F : S → ZetaAdmissibleFunction)
    (hF :
      ∀ z w : S,
        Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
          if w = z then 1 else 0) :
    zetaLaplaceTransformFiniteSample S (∑ z : S, aS z • F z) = aS := by
  classical
  funext w
  calc
    zetaLaplaceTransformFiniteSample S (∑ z : S, aS z • F z) w =
        (∑ z : S, zetaLaplaceTransformFiniteSample S (aS z • F z)) w := by
      exact congrFun
        (zetaLaplaceTransformFiniteSample_sum
          S Finset.univ (fun z : S => aS z • F z))
        w
    _ =
        ∑ z : S, zetaLaplaceTransformFiniteSample S (aS z • F z) w := by
      exact Finset.univ.sum_apply w
        (fun z : S => zetaLaplaceTransformFiniteSample S (aS z • F z))
    _ =
        ∑ z : S, aS z *
          Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) := by
      exact Finset.sum_congr rfl
        (fun z _hz =>
          congrFun (zetaLaplaceTransformFiniteSample_smul S (aS z) (F z)) w)
    _ =
        ∑ z : S, aS z * (if w = z then 1 else 0) := by
      exact Finset.sum_congr rfl
        (fun z _hz =>
          congrArg (fun u : ℂ => aS z * u) (hF z w))
    _ = aS w := by
      have hsingle :
          ∑ z in (Finset.univ : Finset S),
              aS z * (if w = z then 1 else 0) =
            aS w * (if w = w then 1 else 0) := by
        exact Finset.sum_eq_single
          (a := w)
          (f := fun z : S => aS z * (if w = z then 1 else 0))
          (fun z _hz hzw =>
            have hne : w ≠ z := fun hwz => hzw hwz.symm
            calc
              aS z * (if w = z then 1 else 0) =
                  aS z * 0 := by
                exact congrArg (fun u : ℂ => aS z * u) (if_neg hne)
              _ = 0 := by
                exact mul_zero (aS z))
          (fun hw =>
            False.elim (hw (Finset.mem_univ w)))
      calc
        ∑ z : S, aS z * (if w = z then 1 else 0) =
            aS w * (if w = w then 1 else 0) := by
          exact hsingle
        _ = aS w * 1 := by
          exact congrArg (fun u : ℂ => aS w * u) (if_pos rfl)
        _ = aS w := by
          exact mul_one (aS w)

/-- The Kronecker vector for a cardinal probe at one spectral sample. -/
def zetaLaplaceTransformCardinalVector
    (S : Finset ℂ) (z : S) : S → ℂ :=
  fun w : S => if w = z then 1 else 0

/-- The Kronecker vector has the expected value at each finite sample. -/
theorem zetaLaplaceTransformCardinalVector_apply
    (S : Finset ℂ) (z w : S) :
    zetaLaplaceTransformCardinalVector S z w =
      if w = z then 1 else 0 := by
  rfl

/-- Finite-sample realization of every Kronecker vector is exactly a cardinal family. -/
theorem zetaLaplaceTransformCardinalFamily_of_finiteSample_eq_cardinalVector
    (S : Finset ℂ) (F : S → ZetaAdmissibleFunction)
    (hF :
      ∀ z : S,
        zetaLaplaceTransformFiniteSample S (F z) =
          zetaLaplaceTransformCardinalVector S z) :
    ∀ z w : S,
      Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
        if w = z then 1 else 0 := by
  intro z w
  calc
    Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
        zetaLaplaceTransformFiniteSample S (F z) w := by
      rfl
    _ = zetaLaplaceTransformCardinalVector S z w := by
      exact congrFun (hF z) w
    _ = if w = z then 1 else 0 := by
      exact zetaLaplaceTransformCardinalVector_apply S z w

/-- A pointwise cardinal family gives finite-sample realization of every Kronecker vector. -/
theorem zetaLaplaceTransformFiniteSample_eq_cardinalVector_of_cardinalFamily
    (S : Finset ℂ) (F : S → ZetaAdmissibleFunction)
    (hF :
      ∀ z w : S,
        Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
          if w = z then 1 else 0) :
    ∀ z : S,
      zetaLaplaceTransformFiniteSample S (F z) =
        zetaLaplaceTransformCardinalVector S z := by
  intro z
  funext w
  calc
    zetaLaplaceTransformFiniteSample S (F z) w =
        Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) := by
      rfl
    _ = if w = z then 1 else 0 := by
      exact hF z w
    _ = zetaLaplaceTransformCardinalVector S z w := by
      exact (zetaLaplaceTransformCardinalVector_apply S z w).symm

/-- Finite-sample cardinal-vector realization is equivalent to the pointwise cardinal
matrix identity. -/
theorem zetaLaplaceTransformCardinalFamily_iff_finiteSample_eq_cardinalVector
    (S : Finset ℂ) (F : S → ZetaAdmissibleFunction) :
    (∀ z w : S,
      Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
        if w = z then 1 else 0) ↔
      ∀ z : S,
        zetaLaplaceTransformFiniteSample S (F z) =
          zetaLaplaceTransformCardinalVector S z := by
  exact
    ⟨zetaLaplaceTransformFiniteSample_eq_cardinalVector_of_cardinalFamily S F,
      zetaLaplaceTransformCardinalFamily_of_finiteSample_eq_cardinalVector S F⟩

/-- The Kronecker cardinal vectors form the standard finite-coordinate expansion of every
finite sample vector. -/
theorem zetaLaplaceTransformCardinalVector_linearCombination
    (S : Finset ℂ) (aS : S → ℂ) :
    (∑ z : S, aS z • zetaLaplaceTransformCardinalVector S z) = aS := by
  classical
  funext w
  calc
    (∑ z : S, aS z • zetaLaplaceTransformCardinalVector S z) w =
        ∑ z : S, (aS z • zetaLaplaceTransformCardinalVector S z) w := by
      exact Finset.univ.sum_apply w
        (fun z : S => aS z • zetaLaplaceTransformCardinalVector S z)
    _ = ∑ z : S, aS z * (if w = z then 1 else 0) := by
      exact Finset.sum_congr rfl
        (fun z _hz =>
          congrArg (fun u : ℂ => aS z * u)
            (zetaLaplaceTransformCardinalVector_apply S z w))
    _ = aS w := by
      have hsingle :
          ∑ z in (Finset.univ : Finset S),
              aS z * (if w = z then 1 else 0) =
            aS w * (if w = w then 1 else 0) := by
        exact Finset.sum_eq_single
          (a := w)
          (f := fun z : S => aS z * (if w = z then 1 else 0))
          (fun z _hz hzw =>
            have hne : w ≠ z := fun hwz => hzw hwz.symm
            calc
              aS z * (if w = z then 1 else 0) =
                  aS z * 0 := by
                exact congrArg (fun u : ℂ => aS z * u) (if_neg hne)
              _ = 0 := by
                exact mul_zero (aS z))
          (fun hw =>
            False.elim (hw (Finset.mem_univ w)))
      calc
        ∑ z : S, aS z * (if w = z then 1 else 0) =
            aS w * (if w = w then 1 else 0) := by
          exact hsingle
        _ = aS w * 1 := by
          exact congrArg (fun u : ℂ => aS w * u) (if_pos rfl)
        _ = aS w := by
          exact mul_one (aS w)

/-- The empty spectral sample set has a vacuous cardinal family. -/
theorem exists_zetaLaplaceTransformCardinalFamily_empty_ownerPaleyWiener :
    ∃ F : (∅ : Finset ℂ) → ZetaAdmissibleFunction,
      ∀ z w : (∅ : Finset ℂ),
        Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
          if w = z then 1 else 0 := by
  exact
    ⟨fun z =>
        False.elim (Finset.not_mem_empty (z : ℂ) z.property),
      fun z _w =>
        False.elim (Finset.not_mem_empty (z : ℂ) z.property)⟩

/-- Classical finite exponential-distribution separation by admissible probes.

If a finite coefficient family pairs to zero with the Laplace samples of every admissible
probe, then every coefficient is zero. This is the analytic Paley-Wiener uniqueness
theorem for compactly supported smooth/admissible probes; cardinal probes are downstream
consequences and are not used here. -/
theorem zetaLaplaceTransformFiniteExponentialDistribution_separated_by_admissibleProbes_ownerPaleyWiener
    (S : Finset ℂ) (c : S → ℂ)
    (hc :
      ∀ f : ZetaAdmissibleFunction,
        (∑ z : S, zetaLaplaceTransformFiniteSample S f z * c z) = 0) :
    ∀ z : S, c z = 0 := by
  exact
    zetaLaplaceTransformFiniteExponentialSamples_separated_by_admissibleProbes_ownerAdmissibleProbe
      S c
      (fun f =>
        calc
          (∑ z : S,
              Boundary.zetaLaplaceTransform f.toZetaTestFunction' (z : ℂ) * c z) =
              ∑ z : S, zetaLaplaceTransformFiniteSample S f z * c z := by
            exact Finset.sum_congr rfl
              (fun z _hz => rfl)
          _ = 0 := by
            exact hc f)

/-- Direct Paley-Wiener uniqueness for finite exponential/Laplace samples.

This wrapper keeps the finite-sample separation root upstream of cardinal probes. -/
theorem zetaLaplaceTransformFiniteExponentialSamples_separating_ownerPaleyWiener
    (S : Finset ℂ) (c : S → ℂ)
    (hc :
      ∀ f : ZetaAdmissibleFunction,
        (∑ z : S, zetaLaplaceTransformFiniteSample S f z * c z) = 0) :
    ∀ z : S, c z = 0 := by
  exact
    zetaLaplaceTransformFiniteExponentialDistribution_separated_by_admissibleProbes_ownerPaleyWiener
      S c hc

/-- Analytic separation for finite exponential/Laplace samples by admissible probes.

If a finite dual combination of Laplace samples vanishes on every admissible probe, then
each coefficient against the Kronecker cardinal vector is zero. This is the
Paley-Wiener uniqueness input for finite exponential samples. -/
theorem zetaLaplaceTransformFiniteSample_dualCardinalCoefficients_eq_zero_ownerPaleyWiener
    (S : Finset ℂ)
    (Λ : (S → ℂ) →ₗ[ℂ] ℂ)
    (hΛ :
      ∀ f : ZetaAdmissibleFunction,
        Λ (zetaLaplaceTransformFiniteSample S f) = 0) :
    ∀ z : S,
      Λ (zetaLaplaceTransformCardinalVector S z) = 0 := by
  exact
    zetaLaplaceTransformFiniteExponentialSamples_separating_ownerPaleyWiener
      S
      (fun z : S => Λ (zetaLaplaceTransformCardinalVector S z))
      (fun f =>
        have hmap :
            Λ (∑ z : S,
                zetaLaplaceTransformFiniteSample S f z •
                  zetaLaplaceTransformCardinalVector S z) =
              ∑ z : S,
                zetaLaplaceTransformFiniteSample S f z *
                  Λ (zetaLaplaceTransformCardinalVector S z) := by
          calc
            Λ (∑ z : S,
                zetaLaplaceTransformFiniteSample S f z •
                  zetaLaplaceTransformCardinalVector S z) =
                ∑ z : S,
                  Λ (zetaLaplaceTransformFiniteSample S f z •
                    zetaLaplaceTransformCardinalVector S z) := by
              exact LinearMap.map_sum Λ Finset.univ
                (fun z : S =>
                  zetaLaplaceTransformFiniteSample S f z •
                    zetaLaplaceTransformCardinalVector S z)
            _ =
                ∑ z : S,
                  zetaLaplaceTransformFiniteSample S f z *
                    Λ (zetaLaplaceTransformCardinalVector S z) := by
              exact Finset.sum_congr rfl
                (fun z _hz =>
                  LinearMap.map_smul Λ
                    (zetaLaplaceTransformFiniteSample S f z)
                    (zetaLaplaceTransformCardinalVector S z))
        calc
          (∑ z : S,
              zetaLaplaceTransformFiniteSample S f z *
                Λ (zetaLaplaceTransformCardinalVector S z)) =
              Λ (∑ z : S,
                zetaLaplaceTransformFiniteSample S f z •
                  zetaLaplaceTransformCardinalVector S z) := by
            exact hmap.symm
          _ = Λ (zetaLaplaceTransformFiniteSample S f) := by
            exact congrArg Λ
              (zetaLaplaceTransformCardinalVector_linearCombination
                S (zetaLaplaceTransformFiniteSample S f))
          _ = 0 := by
            exact hΛ f)

/-- Finite-dimensional Paley-Wiener interpolation on a spectral sample set.

This is the finite-dimensional separating-dual form: any linear functional on the finite
sample vector space that vanishes on all admissible Laplace-sample vectors is zero. -/
theorem zetaLaplaceTransformFiniteSample_dual_separating_ownerPaleyWiener
    (S : Finset ℂ)
    (Λ : (S → ℂ) →ₗ[ℂ] ℂ)
    (hΛ :
      ∀ f : ZetaAdmissibleFunction,
        Λ (zetaLaplaceTransformFiniteSample S f) = 0) :
    Λ = 0 := by
  have hcoeff :
      ∀ z : S,
        Λ (zetaLaplaceTransformCardinalVector S z) = 0 :=
    zetaLaplaceTransformFiniteSample_dualCardinalCoefficients_eq_zero_ownerPaleyWiener
      S Λ hΛ
  apply LinearMap.ext
  intro aS
  calc
    Λ aS =
        Λ (∑ z : S, aS z • zetaLaplaceTransformCardinalVector S z) := by
      exact congrArg Λ
        (zetaLaplaceTransformCardinalVector_linearCombination S aS).symm
    _ =
        ∑ z : S, Λ (aS z • zetaLaplaceTransformCardinalVector S z) := by
      exact LinearMap.map_sum Λ Finset.univ
        (fun z : S => aS z • zetaLaplaceTransformCardinalVector S z)
    _ =
        ∑ z : S, aS z * Λ (zetaLaplaceTransformCardinalVector S z) := by
      exact Finset.sum_congr rfl
        (fun z _hz => LinearMap.map_smul Λ (aS z)
          (zetaLaplaceTransformCardinalVector S z))
    _ = ∑ z : S, aS z * 0 := by
      exact Finset.sum_congr rfl
        (fun z _hz =>
          congrArg (fun u : ℂ => aS z * u) (hcoeff z))
    _ = 0 := by
      exact Finset.sum_eq_zero
        (fun z _hz => mul_zero (aS z))
    _ = (0 : (S → ℂ) →ₗ[ℂ] ℂ) aS := by
      rfl

/-- Finite-dimensional linear algebra converts dual separation of the finite
Laplace-evaluation range into surjectivity of the finite Laplace-evaluation map. -/
theorem zetaLaplaceTransformFiniteSample_surjective_of_dual_separating_ownerPaleyWiener
    (S : Finset ℂ)
    (hsep :
      ∀ Λ : (S → ℂ) →ₗ[ℂ] ℂ,
        (∀ f : ZetaAdmissibleFunction,
          Λ (zetaLaplaceTransformFiniteSample S f) = 0) →
          Λ = 0) :
    Function.Surjective (zetaLaplaceTransformFiniteSample S) := by
  have hRangeTop :
      LinearMap.range (zetaLaplaceTransformFiniteSampleLinearMap S) = ⊤ := by
    by_contra hRangeNeTop
    have hRangeProper :
        LinearMap.range (zetaLaplaceTransformFiniteSampleLinearMap S) < ⊤ :=
      lt_of_le_of_ne le_top hRangeNeTop
    rcases Submodule.exists_le_ker_of_lt_top
        (LinearMap.range (zetaLaplaceTransformFiniteSampleLinearMap S))
        hRangeProper with
      ⟨Λ, hΛne, hΛker⟩
    have hΛvanish :
        ∀ f : ZetaAdmissibleFunction,
          Λ (zetaLaplaceTransformFiniteSample S f) = 0 := by
      intro f
      exact LinearMap.mem_ker.mp
        (hΛker
          (LinearMap.mem_range.mpr
            ⟨f, rfl⟩))
    exact hΛne (hsep Λ hΛvanish)
  exact LinearMap.range_eq_top.mp hRangeTop

/-- Finite-dimensional Paley-Wiener interpolation on a spectral sample set.

This is the finite-dimensional Fourier-Laplace/Paley-Wiener range input: every finite
sample vector lies in the range of the admissible Laplace-evaluation map. -/
theorem zetaLaplaceTransformFiniteSample_mem_range_ownerPaleyWiener
    (S : Finset ℂ) (aS : S → ℂ) :
    aS ∈ Set.range (zetaLaplaceTransformFiniteSample S) := by
  exact
    zetaLaplaceTransformFiniteSample_surjective_of_dual_separating_ownerPaleyWiener
      S
      (zetaLaplaceTransformFiniteSample_dual_separating_ownerPaleyWiener S)
      aS

/-- Finite-dimensional Paley-Wiener interpolation on a spectral sample set.

This is the finite-dimensional Fourier-Laplace/Paley-Wiener surjectivity theorem
deduced from the range statement. -/
theorem zetaLaplaceTransformFiniteSample_finiteDimensional_surjective_ownerPaleyWiener
    (S : Finset ℂ) :
    Function.Surjective (zetaLaplaceTransformFiniteSample S) := by
  intro aS
  exact Set.mem_range.mp
    (zetaLaplaceTransformFiniteSample_mem_range_ownerPaleyWiener S aS)

/-- Finite-dimensional Laplace-evaluation separation: each Kronecker vector lies in the
range of the admissible finite Laplace-sample map. -/
theorem zetaLaplaceTransformCardinalVector_mem_range_ownerPaleyWiener
    (S : Finset ℂ) (z : S) :
    zetaLaplaceTransformCardinalVector S z ∈
      Set.range (zetaLaplaceTransformFiniteSample S) := by
  exact zetaLaplaceTransformFiniteSample_finiteDimensional_surjective_ownerPaleyWiener
    S (zetaLaplaceTransformCardinalVector S z)

/-- Nonempty finite Paley-Wiener cardinal interpolation on a spectral sample set.

This constructs one admissible cardinal probe with prescribed Laplace-transform values
against the whole finite sample set from finite-dimensional Laplace-evaluation
surjectivity. -/
theorem exists_zetaLaplaceTransformCardinalVector_ownerPaleyWiener
    (S : Finset ℂ) (z : S) :
    ∃ f : ZetaAdmissibleFunction,
      zetaLaplaceTransformFiniteSample S f =
        zetaLaplaceTransformCardinalVector S z := by
  exact Set.mem_range.mp
    (zetaLaplaceTransformCardinalVector_mem_range_ownerPaleyWiener S z)

/-- A pointwise cardinal-vector realization for every sample can be assembled into a
finite-sample cardinal family over an arbitrary finite index subset of a fixed ambient
sample set. This is constructive finite dependent choice by induction on the index
finset; no global choice operator is used. -/
theorem exists_zetaLaplaceTransformCardinalFiniteSampleFamilyOn_of_forall_cardinalVector
    (S T : Finset ℂ) (hTS : T ⊆ S)
    (hT :
      ∀ z : T,
        ∃ f : ZetaAdmissibleFunction,
          zetaLaplaceTransformFiniteSample S f =
            zetaLaplaceTransformCardinalVector S
              ⟨(z : ℂ), hTS z.property⟩) :
    ∃ F : T → ZetaAdmissibleFunction,
      ∀ z : T,
        zetaLaplaceTransformFiniteSample S (F z) =
          zetaLaplaceTransformCardinalVector S
            ⟨(z : ℂ), hTS z.property⟩ := by
  induction T using Finset.induction_on with
  | empty =>
      exact
        ⟨fun z =>
            False.elim (Finset.not_mem_empty (z : ℂ) z.property),
          fun z =>
            False.elim (Finset.not_mem_empty (z : ℂ) z.property)⟩
  | insert a T ha ih =>
      have hTailSubset : T ⊆ S := by
        intro x hx
        exact hTS (Finset.mem_insert_of_mem hx)
      have hTailExists :
          ∀ z : T,
            ∃ f : ZetaAdmissibleFunction,
              zetaLaplaceTransformFiniteSample S f =
                zetaLaplaceTransformCardinalVector S
                  ⟨(z : ℂ), hTailSubset z.property⟩ := by
        intro z
        rcases hT ⟨(z : ℂ), Finset.mem_insert_of_mem z.property⟩ with
          ⟨f, hf⟩
        exact ⟨f, hf⟩
      rcases ih hTailSubset hTailExists with ⟨Ftail, hFtail⟩
      rcases hT ⟨a, Finset.mem_insert_self a T⟩ with ⟨fa, hfa⟩
      let restrictTail :
          ∀ z : (insert a T : Finset ℂ), (z : ℂ) ≠ a → T :=
        fun z hz =>
          ⟨(z : ℂ), (Finset.mem_insert.mp z.property).resolve_left hz⟩
      let F : (insert a T : Finset ℂ) → ZetaAdmissibleFunction :=
        fun z =>
          if hz : (z : ℂ) = a then
            fa
          else
            Ftail (restrictTail z hz)
      refine ⟨F, ?_⟩
      intro z
      by_cases hz : (z : ℂ) = a
      · have hFz :
            F z = fa := by
          unfold F
          exact dif_pos hz
        calc
          zetaLaplaceTransformFiniteSample S (F z) =
              zetaLaplaceTransformFiniteSample S fa := by
            exact congrArg
              (fun f : ZetaAdmissibleFunction =>
                zetaLaplaceTransformFiniteSample S f)
              hFz
          _ = zetaLaplaceTransformCardinalVector S
              ⟨a, hTS (Finset.mem_insert_self a T)⟩ := by
            exact hfa
          _ = zetaLaplaceTransformCardinalVector S
              ⟨(z : ℂ), hTS z.property⟩ := by
            have hsub :
                (⟨a, hTS (Finset.mem_insert_self a T)⟩ : S) =
                  ⟨(z : ℂ), hTS z.property⟩ := by
              exact Subtype.ext hz.symm
            exact congrArg (fun w : S =>
              zetaLaplaceTransformCardinalVector S w) hsub
      · have hFz :
            F z = Ftail (restrictTail z hz) := by
          unfold F
          exact dif_neg hz
        calc
          zetaLaplaceTransformFiniteSample S (F z) =
              zetaLaplaceTransformFiniteSample S (Ftail (restrictTail z hz)) := by
            exact congrArg
              (fun f : ZetaAdmissibleFunction =>
                zetaLaplaceTransformFiniteSample S f)
              hFz
          _ = zetaLaplaceTransformCardinalVector S
              ⟨((restrictTail z hz) : ℂ),
                hTailSubset (restrictTail z hz).property⟩ := by
            exact hFtail (restrictTail z hz)
          _ = zetaLaplaceTransformCardinalVector S
              ⟨(z : ℂ), hTS z.property⟩ := by
            have hsub :
                (⟨((restrictTail z hz) : ℂ),
                  hTailSubset (restrictTail z hz).property⟩ : S) =
                    ⟨(z : ℂ), hTS z.property⟩ := by
              exact Subtype.ext rfl
            exact congrArg (fun w : S =>
              zetaLaplaceTransformCardinalVector S w) hsub

/-- A pointwise cardinal-vector realization for every sample can be assembled into a
finite-sample cardinal family. -/
theorem exists_zetaLaplaceTransformCardinalFiniteSampleFamily_of_forall_cardinalVector
    (S : Finset ℂ)
    (hS :
      ∀ z : S,
        ∃ f : ZetaAdmissibleFunction,
          zetaLaplaceTransformFiniteSample S f =
            zetaLaplaceTransformCardinalVector S z) :
    ∃ F : S → ZetaAdmissibleFunction,
      ∀ z : S,
        zetaLaplaceTransformFiniteSample S (F z) =
          zetaLaplaceTransformCardinalVector S z := by
  have hSubset : S ⊆ S := by
    intro z hz
    exact hz
  have hExists :
      ∀ z : S,
        ∃ f : ZetaAdmissibleFunction,
          zetaLaplaceTransformFiniteSample S f =
            zetaLaplaceTransformCardinalVector S
              ⟨(z : ℂ), hSubset z.property⟩ := by
    intro z
    exact hS z
  rcases exists_zetaLaplaceTransformCardinalFiniteSampleFamilyOn_of_forall_cardinalVector
      S S hSubset hExists with
    ⟨F, hF⟩
  exact ⟨F, hF⟩

/-- Nonempty finite Paley-Wiener cardinal interpolation on a spectral sample set, in
finite-sample vector form. -/
theorem exists_zetaLaplaceTransformCardinalFiniteSampleFamily_nonempty_ownerPaleyWiener
    (S : Finset ℂ) (_hS : S ≠ ∅) :
    ∃ F : S → ZetaAdmissibleFunction,
      ∀ z : S,
        zetaLaplaceTransformFiniteSample S (F z) =
          zetaLaplaceTransformCardinalVector S z := by
  exact exists_zetaLaplaceTransformCardinalFiniteSampleFamily_of_forall_cardinalVector
    S (fun z => exists_zetaLaplaceTransformCardinalVector_ownerPaleyWiener S z)

/-- Nonempty finite Paley-Wiener cardinal interpolation on a spectral sample set.

This is the pointwise matrix form of the finite-sample cardinal family. -/
theorem exists_zetaLaplaceTransformCardinalFamily_nonempty_ownerPaleyWiener
    (S : Finset ℂ) (hS : S ≠ ∅) :
    ∃ F : S → ZetaAdmissibleFunction,
      ∀ z w : S,
        Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
          if w = z then 1 else 0 := by
  rcases exists_zetaLaplaceTransformCardinalFiniteSampleFamily_nonempty_ownerPaleyWiener
      S hS with
    ⟨F, hF⟩
  exact ⟨F,
    zetaLaplaceTransformCardinalFamily_of_finiteSample_eq_cardinalVector
      S F hF⟩

/-- Paley-Wiener cardinal interpolation on a finite spectral sample set. -/
theorem exists_zetaLaplaceTransformCardinalFamily_ownerPaleyWiener
    (S : Finset ℂ) :
    ∃ F : S → ZetaAdmissibleFunction,
      ∀ z w : S,
        Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
          if w = z then 1 else 0 := by
  by_cases hS : S = ∅
  · subst S
    exact exists_zetaLaplaceTransformCardinalFamily_empty_ownerPaleyWiener
  · exact exists_zetaLaplaceTransformCardinalFamily_nonempty_ownerPaleyWiener S hS

/-- Finite Paley-Wiener interpolation in finite-vector form.

This is the constructive basis/interpolant owner theorem: every target vector on a finite
spectral sample set is realized by the finite Laplace-transform sample vector of an
admissible function. -/
theorem exists_zetaLaplaceTransformFiniteSample_eq_ownerPaleyWiener
    (S : Finset ℂ) (aS : S → ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      zetaLaplaceTransformFiniteSample S f = aS := by
  exact zetaLaplaceTransformFiniteSample_finiteDimensional_surjective_ownerPaleyWiener
    S aS

/-- Finite Paley-Wiener interpolation says the finite Laplace-sample map is surjective. -/
theorem zetaLaplaceTransformFiniteSample_surjective_ownerPaleyWiener
    (S : Finset ℂ) :
    Function.Surjective (zetaLaplaceTransformFiniteSample S) := by
  exact zetaLaplaceTransformFiniteSample_finiteDimensional_surjective_ownerPaleyWiener S

/-- Finite Paley-Wiener interpolation for admissible Laplace transforms on a finite
spectral sample set.

This is the interpolation counterpart to the vertical-strip Paley-Wiener decay theorem:
compactly supported smooth admissible sources can realize arbitrary prescribed Laplace
transform values on a finite set of spectral parameters. -/
theorem exists_zetaLaplaceTransform_sample_on_finset_ownerPaleyWiener
    (S : Finset ℂ) (a : ℂ → ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      ∀ z : ℂ, z ∈ S →
        Boundary.zetaLaplaceTransform f.toZetaTestFunction' z = a z := by
  rcases zetaLaplaceTransformFiniteSample_surjective_ownerPaleyWiener
      S (zetaLaplaceTransformFiniteTarget S a) with
    ⟨f, hf⟩
  exact ⟨f, fun z hz =>
    congrFun hf ⟨z, hz⟩⟩

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
