import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.VerticalWeight.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaTransformCalculusWeighted.Owner

/-!
# Paley-Wiener support envelopes

This file owns the vertical-strip decay predicate, support-interval length, and
compact-support norm/exponential envelopes used by the Paley-Wiener decay
package. It is copy-first extracted from the current Paley-Wiener owner file
and is not imported by that parent yet, so declaration names intentionally
match the existing owner surface.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped ContDiff

namespace ZetaAdmissibleFunction

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

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
