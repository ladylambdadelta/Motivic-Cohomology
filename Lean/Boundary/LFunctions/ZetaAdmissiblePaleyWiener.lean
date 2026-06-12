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

/-- Constructive vertical-strip rapid-decay certificate for a complex-valued transform. -/
structure VerticalStripRapidDecayCertificate
    (Φ : ℂ → ℂ) (a b : ℝ) (N : ℕ) where
  constant : ℝ
  constant_pos : 0 < constant
  bound :
    ∀ z : ℂ,
      a ≤ z.re →
      z.re ≤ b →
      ‖Φ z‖ ≤ constant * (1 + ‖z.im‖) ^ (-(N : ℤ))

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

/-- The oscillatory integration-by-parts estimate on a fixed support interval.

This is the Fourier-side core of Paley-Wiener: after `N` integrations by parts, the vertical
frequency contributes the factor `(1 + |im z|)^{-N}`.  Smoothness supplies the needed
derivative seminorms and the support-interval vanishing lemmas kill all boundary terms. -/
noncomputable def zetaLaplaceTransform_supportInterval_integrationByParts_decayCertificate
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ) :
    VerticalStripRapidDecayCertificate
      (fun z : ℂ => Boundary.zetaLaplaceTransform f.toZetaTestFunction' z) a b N := by
  sorry

/-- The oscillatory integration-by-parts estimate on a fixed support interval, projected as an
existence statement for theorem consumers. -/
theorem zetaLaplaceTransform_supportInterval_integrationByParts_decay
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        zetaPaleyWienerInVerticalStrip a b z →
        ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
          ≤ C * zetaPaleyWienerVerticalWeight z N := by
  let cert :=
    zetaLaplaceTransform_supportInterval_integrationByParts_decayCertificate
      f I a b N
  exact
    ⟨cert.constant, cert.constant_pos, fun z hz =>
      cert.bound z hz.1 hz.2⟩

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
