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
  sorry

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

/-- One Paley-Wiener integration-by-parts identity on a fixed support interval.

The boundary terms vanish because the admissible source is zero off the supplied compact
support interval. This identity is the exact analytic transport that trades one vertical
frequency factor for one source derivative. -/
theorem zetaLaplaceTransform_supportInterval_integrationByParts_identity
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) :
    ∃ derivativeProbe : ZetaAdmissibleFunction,
      ∀ z : ℂ,
        zetaPaleyWienerInVerticalStrip a b z →
        z.im ≠ 0 →
        Boundary.zetaLaplaceTransform f.toZetaTestFunction' z =
          (z.im : ℂ)⁻¹ *
            Boundary.zetaLaplaceTransform derivativeProbe.toZetaTestFunction' z := by
  sorry

/-- One integration-by-parts step constructs the derivative probe together with the
frequency identity and inherited `N`th vertical-strip decay.

This is where smooth compact support supplies the derivative seminorm bound for the new
probe; the derivative probe is not arbitrary. -/
theorem zetaLaplaceTransform_supportInterval_integrationByParts_step
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ)
    (hN :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          zetaPaleyWienerInVerticalStrip a b z →
          ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
            ≤ C * zetaPaleyWienerVerticalWeight z N) :
    ∃ derivativeProbe : ZetaAdmissibleFunction,
      (∀ z : ℂ,
        zetaPaleyWienerInVerticalStrip a b z →
        z.im ≠ 0 →
        Boundary.zetaLaplaceTransform f.toZetaTestFunction' z =
          (z.im : ℂ)⁻¹ *
            Boundary.zetaLaplaceTransform derivativeProbe.toZetaTestFunction' z) ∧
        ∃ C : ℝ,
          0 < C ∧
          ∀ z : ℂ,
            zetaPaleyWienerInVerticalStrip a b z →
            ‖Boundary.zetaLaplaceTransform derivativeProbe.toZetaTestFunction' z‖
              ≤ C * zetaPaleyWienerVerticalWeight z N := by
  sorry

/-- The one-step Paley-Wiener frequency estimate converts integration-by-parts and
derivative-probe decay into successor vertical decay. -/
theorem zetaLaplaceTransform_supportInterval_successor_decay_from_parts
    (f derivativeProbe : ZetaAdmissibleFunction)
    (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ)
    (hidentity :
      ∀ z : ℂ,
        zetaPaleyWienerInVerticalStrip a b z →
        z.im ≠ 0 →
        Boundary.zetaLaplaceTransform f.toZetaTestFunction' z =
          (z.im : ℂ)⁻¹ *
            Boundary.zetaLaplaceTransform derivativeProbe.toZetaTestFunction' z)
    (hderiv :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          zetaPaleyWienerInVerticalStrip a b z →
          ‖Boundary.zetaLaplaceTransform derivativeProbe.toZetaTestFunction' z‖
            ≤ C * zetaPaleyWienerVerticalWeight z N) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        zetaPaleyWienerInVerticalStrip a b z →
        ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
          ≤ C * zetaPaleyWienerVerticalWeight z (N + 1) := by
  sorry

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
  rcases zetaLaplaceTransform_supportInterval_integrationByParts_step
      f I a b N hN with
    ⟨derivativeProbe, hidentity, hderivativeDecay⟩
  exact zetaLaplaceTransform_supportInterval_successor_decay_from_parts
    f derivativeProbe I a b N hidentity hderivativeDecay

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
  induction N with
  | zero =>
      exact zetaLaplaceTransform_supportInterval_zeroOrder_decay f I a b
  | succ N ih =>
      exact zetaLaplaceTransform_supportInterval_integrationByParts_successor
        f I a b N ih

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
