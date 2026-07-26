import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ProbeInterface.ZetaAdmissibleFunction.ZetaAdmissibleFunctionCore.Owner
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Topology.Order.Bornology

/-!
# Paley-Wiener support intervals

This file owns the low-level compact-support interval certificate used by the
Paley-Wiener decay package. It is copy-first extracted from the current
Paley-Wiener owner file and is not imported by that parent yet, so declaration
names intentionally match the existing owner surface.
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
  match IsCompact.bddAbove f.toZetaTestFunction.hasCompactSupport.isCompact with
  | ⟨B, hB⟩ => exact ⟨B, hB⟩

/-- Compact support gives a lower bound for the admissible source support. -/
theorem exists_zetaPaleyWienerSupportLowerBound
    (f : ZetaAdmissibleFunction) :
    ∃ A : ℝ, ∀ t ∈ tsupport f.toZetaTestFunction, A ≤ t := by
  match IsCompact.bddBelow f.toZetaTestFunction.hasCompactSupport.isCompact with
  | ⟨A, hA⟩ => exact ⟨A, hA⟩

/-- Compact support gives a concrete interval containing the admissible source support, as a
proposition-level existence statement.  This lemma is useful for ordinary support arguments; the
type-level Paley-Wiener constant is produced by the integration-by-parts theorem below rather than
by choosing one of these intervals. -/
theorem exists_zetaPaleyWienerSupportInterval
    (f : ZetaAdmissibleFunction) :
    Nonempty (ZetaPaleyWienerSupportInterval f) := by
  match exists_zetaPaleyWienerSupportLowerBound f with
  | ⟨A, hA⟩ =>
      match exists_zetaPaleyWienerSupportUpperBound f with
      | ⟨B, hB⟩ =>
          exact
            ⟨⟨min A B, max A B,
              le_trans (min_le_left A B) (le_max_left A B),
              (fun t ht => le_trans (min_le_left A B) (hA t ht)),
              (fun t ht => le_trans (hB t ht) (le_max_right A B))⟩⟩

/-- The deterministic compact interval containing the support of an admissible probe. -/
noncomputable def canonicalZetaPaleyWienerSupportInterval
    (f : ZetaAdmissibleFunction) : ZetaPaleyWienerSupportInterval f :=
  let supportSet : Set ℝ := tsupport f.toZetaTestFunction
  let supportBounded : Bornology.IsBounded supportSet :=
    f.toZetaTestFunction.hasCompactSupport.isCompact.isBounded
  { lower := sInf supportSet
    upper := sSup supportSet
    lower_le_upper :=
      Real.sInf_le_sSup supportSet
        supportBounded.bddBelow supportBounded.bddAbove
    lower_mem :=
      fun t ht => (supportBounded.subset_Icc_sInf_sSup ht).1
    upper_mem :=
      fun t ht => (supportBounded.subset_Icc_sInf_sSup ht).2 }

/-- A symmetric nonnegative radius containing the canonical support interval. -/
noncomputable def canonicalZetaPaleyWienerSupportRadius
    (f : ZetaAdmissibleFunction) : ℝ :=
  max |(canonicalZetaPaleyWienerSupportInterval f).lower|
    |(canonicalZetaPaleyWienerSupportInterval f).upper|

/-- The canonical support radius is nonnegative. -/
theorem canonicalZetaPaleyWienerSupportRadius_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ canonicalZetaPaleyWienerSupportRadius f := by
  exact le_trans
    (abs_nonneg (canonicalZetaPaleyWienerSupportInterval f).lower)
    (le_max_left
      |(canonicalZetaPaleyWienerSupportInterval f).lower|
      |(canonicalZetaPaleyWienerSupportInterval f).upper|)

/-- The lower endpoint lies above the negative canonical support radius. -/
theorem canonicalZetaPaleyWienerSupportRadius_neg_le_lower
    (f : ZetaAdmissibleFunction) :
    -canonicalZetaPaleyWienerSupportRadius f ≤
      (canonicalZetaPaleyWienerSupportInterval f).lower := by
  have hlower_abs :
      |(canonicalZetaPaleyWienerSupportInterval f).lower| ≤
        canonicalZetaPaleyWienerSupportRadius f :=
    le_max_left
      |(canonicalZetaPaleyWienerSupportInterval f).lower|
      |(canonicalZetaPaleyWienerSupportInterval f).upper|
  have hneg_abs :
      -|(canonicalZetaPaleyWienerSupportInterval f).lower| ≤
        (canonicalZetaPaleyWienerSupportInterval f).lower :=
    neg_abs_le (canonicalZetaPaleyWienerSupportInterval f).lower
  exact le_trans (neg_le_neg hlower_abs) hneg_abs

/-- The upper endpoint lies below the canonical support radius. -/
theorem canonicalZetaPaleyWienerSupportRadius_upper_le
    (f : ZetaAdmissibleFunction) :
    (canonicalZetaPaleyWienerSupportInterval f).upper ≤
      canonicalZetaPaleyWienerSupportRadius f := by
  have hupper_abs :
      |(canonicalZetaPaleyWienerSupportInterval f).upper| ≤
        canonicalZetaPaleyWienerSupportRadius f :=
    le_max_right
      |(canonicalZetaPaleyWienerSupportInterval f).lower|
      |(canonicalZetaPaleyWienerSupportInterval f).upper|
  exact le_trans
    (le_abs_self (canonicalZetaPaleyWienerSupportInterval f).upper)
    hupper_abs

/-- Every support point lies in the symmetric canonical support interval. -/
theorem mem_symmetricCanonicalZetaPaleyWienerSupportInterval
    (f : ZetaAdmissibleFunction) (t : ℝ)
    (ht : t ∈ tsupport f.toZetaTestFunction) :
    t ∈ Set.Icc
      (-canonicalZetaPaleyWienerSupportRadius f)
      (canonicalZetaPaleyWienerSupportRadius f) := by
  have hlower :
      (canonicalZetaPaleyWienerSupportInterval f).lower ≤ t :=
    (canonicalZetaPaleyWienerSupportInterval f).lower_mem t ht
  have hupper :
      t ≤ (canonicalZetaPaleyWienerSupportInterval f).upper :=
    (canonicalZetaPaleyWienerSupportInterval f).upper_mem t ht
  exact
    ⟨le_trans (canonicalZetaPaleyWienerSupportRadius_neg_le_lower f) hlower,
      le_trans hupper (canonicalZetaPaleyWienerSupportRadius_upper_le f)⟩

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

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
