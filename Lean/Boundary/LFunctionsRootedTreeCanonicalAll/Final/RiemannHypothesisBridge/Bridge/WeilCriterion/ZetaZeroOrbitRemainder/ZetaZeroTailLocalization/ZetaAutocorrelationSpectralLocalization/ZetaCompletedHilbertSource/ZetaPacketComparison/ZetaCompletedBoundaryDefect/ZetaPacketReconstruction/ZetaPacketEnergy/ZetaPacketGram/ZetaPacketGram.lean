import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaPacketComparison.ZetaCompletedBoundaryDefect.ZetaPacketReconstruction.ZetaPacketDecomposition.ZetaPacketDecomposition

/-!
# Boundary zeta packet Gram architecture

This file proves the explicit Gram-style identities for the packet kernel:
the family decomposition, the pairwise orthogonality of the packet parts,
and the squared norm split.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaPacketEnsemble

/-- The prime Gram contribution of a packet ensemble. -/
def primePacketGram (x : ZetaPacketEnsemble) : ℝ :=
  ∑ ℓ ∈ x.support, primePart x ℓ * primePart x ℓ

/-- The archimedean Gram contribution of a packet ensemble. -/
def archimedeanPacketGram (x : ZetaPacketEnsemble) : ℝ :=
  ∑ ℓ ∈ x.support, archimedeanPart x ℓ * archimedeanPart x ℓ

/-- The correction Gram contribution of a packet ensemble. -/
def correctionPacketGram (x : ZetaPacketEnsemble) : ℝ :=
  ∑ ℓ ∈ x.support, correctionPart x ℓ * correctionPart x ℓ

/-- A term is equal to its value plus two zero summands. -/
theorem eq_add_zero_add_zero (a : ℝ) : a = a + 0 + 0 := by
  calc
    a = a + 0 := by
      exact (add_zero a).symm
    _ = a + 0 + 0 := by
      exact (add_zero (a + 0)).symm

/-- A term is equal to zero plus its value plus zero. -/
theorem zero_add_eq_zero_add_add_zero (a : ℝ) : a = 0 + a + 0 := by
  calc
    a = 0 + a := by
      exact (zero_add a).symm
    _ = 0 + a + 0 := by
      exact (add_zero _).symm

/-- If a factor is zero, then its square is zero. -/
theorem sq_eq_zero_of_eq_zero {a : ℝ} (h : a = 0) : a * a = 0 := by
  cases h
  exact zero_mul _

/-- If a factor is zero, then zero is its square. -/
theorem zero_eq_sq_of_eq_zero {a : ℝ} (h : a = 0) : 0 = a * a := by
  cases h
  exact (zero_mul _).symm

/-- The support union with itself is itself. -/
theorem support_union_self (x : ZetaPacketEnsemble) : x.support ∪ x.support = x.support := by
  exact Finset.union_self _

/-- A pointwise sum of two terms splits into two finite sums. -/
theorem sum_two_terms (s : Finset ZetaPacketLabel) (f g : ZetaPacketLabel → ℝ) :
    ∑ ℓ in s, (f ℓ + g ℓ) = ∑ ℓ in s, f ℓ + ∑ ℓ in s, g ℓ := by
  exact Finset.sum_add_distrib

/-- A pointwise sum of three terms splits into three finite sums. -/
theorem sum_three_terms (s : Finset ZetaPacketLabel) (f g h : ZetaPacketLabel → ℝ) :
    ∑ ℓ in s, (f ℓ + g ℓ + h ℓ) = ∑ ℓ in s, f ℓ + ∑ ℓ in s, g ℓ + ∑ ℓ in s, h ℓ := by
  calc
    ∑ ℓ in s, (f ℓ + g ℓ + h ℓ)
        = ∑ ℓ in s, ((f ℓ + g ℓ) + h ℓ) := by
            refine Finset.sum_congr rfl ?_
            intro ℓ hℓ
            exact Eq.refl _
    _ = ∑ ℓ in s, (f ℓ + g ℓ) + ∑ ℓ in s, h ℓ := by
          exact sum_two_terms s (fun ℓ => f ℓ + g ℓ) h
    _ = (∑ ℓ in s, f ℓ + ∑ ℓ in s, g ℓ) + ∑ ℓ in s, h ℓ := by
          congr 1
          exact sum_two_terms s f g
    _ = ∑ ℓ in s, f ℓ + ∑ ℓ in s, g ℓ + ∑ ℓ in s, h ℓ := by
          rfl

/-- Transport equality through squaring. -/
theorem square_congr {a b : ℝ} (h : a = b) : a * a = b * b := by
  exact congrArg (fun t => t * t) h

/-- Transport equality by adding a fixed left and right context. -/
theorem add_context_left_right {a b c d : ℝ} (h : a = b) :
    c + a + d = c + b + d := by
  exact congrArg (fun t => c + t + d) h

/-- Transport equality in the first summand with fixed middle and right context. -/
theorem add_context_middle_right {a b c d : ℝ} (h : a = b) :
    a + c + d = b + c + d := by
  exact congrArg (fun t => t + c + d) h

/-- Transport equality by adding a fixed left context. -/
theorem add_context_left {a b c : ℝ} (h : a = b) : c + a = c + b := by
  exact congrArg (fun t => c + t) h

/-- A value is unchanged when the other two packet-family terms vanish. -/
theorem add_vanish_two (a b c : ℝ) (hb : b = 0) (hc : c = 0) :
    a = a + b + c := by
  calc
    a = a + 0 + 0 := by
      exact eq_add_zero_add_zero _
    _ = a + b + 0 := by
      exact add_context_left_right hb.symm
    _ = a + b + c := by
      exact add_context_left hc.symm

/-- A middle value is unchanged when the first and third packet-family terms vanish. -/
theorem add_vanish_one_three (a b c : ℝ) (ha : a = 0) (hc : c = 0) :
    b = a + b + c := by
  calc
    b = 0 + b + 0 := by
      exact zero_add_eq_zero_add_add_zero _
    _ = a + b + 0 := by
      exact add_context_middle_right ha.symm
    _ = a + b + c := by
      exact add_context_left hc.symm

/-- A final value is unchanged when the first two packet-family terms vanish. -/
theorem add_vanish_one_two (a b c : ℝ) (ha : a = 0) (hb : b = 0) :
    c = a + b + c := by
  calc
    c = 0 + c := by
      exact (zero_add c).symm
    _ = 0 + (0 + c) := by
      exact (zero_add (0 + c)).symm
    _ = 0 + 0 + c := by
      exact (add_assoc 0 0 c).symm
    _ = a + 0 + c := by
      exact add_context_middle_right ha.symm
    _ = a + b + c := by
      exact add_context_left_right hb.symm

/-- Pointwise decomposition of the coefficient square across the packet split. -/
theorem pointwise_sq_prime_rewrite (x : ZetaPacketEnsemble) (m n : ℕ) :
    primePart x (ZetaPacketLabel.prime m n) * primePart x (ZetaPacketLabel.prime m n) =
      primePart x (ZetaPacketLabel.prime m n) * primePart x (ZetaPacketLabel.prime m n) +
      archimedeanPart x (ZetaPacketLabel.prime m n) *
        archimedeanPart x (ZetaPacketLabel.prime m n) +
      correctionPart x (ZetaPacketLabel.prime m n) *
        correctionPart x (ZetaPacketLabel.prime m n) := by
  have ha : archimedeanPart x (ZetaPacketLabel.prime m n) = 0 :=
    archimedeanPart_prime x m n
  have hc : correctionPart x (ZetaPacketLabel.prime m n) = 0 :=
    correctionPart_prime x m n
  exact add_vanish_two
    (primePart x (ZetaPacketLabel.prime m n) * primePart x (ZetaPacketLabel.prime m n))
    (archimedeanPart x (ZetaPacketLabel.prime m n) *
      archimedeanPart x (ZetaPacketLabel.prime m n))
    (correctionPart x (ZetaPacketLabel.prime m n) *
      correctionPart x (ZetaPacketLabel.prime m n))
    (sq_eq_zero_of_eq_zero ha) (sq_eq_zero_of_eq_zero hc)

theorem pointwise_sq_prime (x : ZetaPacketEnsemble) (m n : ℕ) :
    x (ZetaPacketLabel.prime m n) * x (ZetaPacketLabel.prime m n) =
      primePart x (ZetaPacketLabel.prime m n) * primePart x (ZetaPacketLabel.prime m n) +
      archimedeanPart x (ZetaPacketLabel.prime m n) *
        archimedeanPart x (ZetaPacketLabel.prime m n) +
      correctionPart x (ZetaPacketLabel.prime m n) *
        correctionPart x (ZetaPacketLabel.prime m n) := by
  have hp : primePart x (ZetaPacketLabel.prime m n) = x (ZetaPacketLabel.prime m n) :=
    primePart_prime x m n
  calc
    x (ZetaPacketLabel.prime m n) * x (ZetaPacketLabel.prime m n)
        = primePart x (ZetaPacketLabel.prime m n) * primePart x (ZetaPacketLabel.prime m n) := by
          exact square_congr hp
    _ = primePart x (ZetaPacketLabel.prime m n) * primePart x (ZetaPacketLabel.prime m n) +
        archimedeanPart x (ZetaPacketLabel.prime m n) *
          archimedeanPart x (ZetaPacketLabel.prime m n) +
        correctionPart x (ZetaPacketLabel.prime m n) *
          correctionPart x (ZetaPacketLabel.prime m n) := by
          exact pointwise_sq_prime_rewrite x m n

theorem pointwise_sq_archimedean_rewrite (x : ZetaPacketEnsemble) :
    archimedeanPart x ZetaPacketLabel.archimedean *
        archimedeanPart x ZetaPacketLabel.archimedean =
      primePart x ZetaPacketLabel.archimedean * primePart x ZetaPacketLabel.archimedean +
      archimedeanPart x ZetaPacketLabel.archimedean *
        archimedeanPart x ZetaPacketLabel.archimedean +
      correctionPart x ZetaPacketLabel.archimedean *
        correctionPart x ZetaPacketLabel.archimedean := by
  have hp : primePart x ZetaPacketLabel.archimedean = 0 :=
    primePart_archimedean x
  have hc : correctionPart x ZetaPacketLabel.archimedean = 0 :=
    correctionPart_archimedean x
  exact add_vanish_one_three
    (primePart x ZetaPacketLabel.archimedean *
      primePart x ZetaPacketLabel.archimedean)
    (archimedeanPart x ZetaPacketLabel.archimedean *
      archimedeanPart x ZetaPacketLabel.archimedean)
    (correctionPart x ZetaPacketLabel.archimedean *
      correctionPart x ZetaPacketLabel.archimedean)
    (sq_eq_zero_of_eq_zero hp) (sq_eq_zero_of_eq_zero hc)

theorem pointwise_sq_archimedean (x : ZetaPacketEnsemble) :
    x ZetaPacketLabel.archimedean * x ZetaPacketLabel.archimedean =
      primePart x ZetaPacketLabel.archimedean * primePart x ZetaPacketLabel.archimedean +
      archimedeanPart x ZetaPacketLabel.archimedean *
        archimedeanPart x ZetaPacketLabel.archimedean +
      correctionPart x ZetaPacketLabel.archimedean *
        correctionPart x ZetaPacketLabel.archimedean := by
  have ha : archimedeanPart x ZetaPacketLabel.archimedean = x ZetaPacketLabel.archimedean :=
    archimedeanPart_archimedean x
  calc
    x ZetaPacketLabel.archimedean * x ZetaPacketLabel.archimedean
        = archimedeanPart x ZetaPacketLabel.archimedean *
            archimedeanPart x ZetaPacketLabel.archimedean := by
          exact square_congr ha.symm
    _ = primePart x ZetaPacketLabel.archimedean * primePart x ZetaPacketLabel.archimedean +
        archimedeanPart x ZetaPacketLabel.archimedean *
          archimedeanPart x ZetaPacketLabel.archimedean +
        correctionPart x ZetaPacketLabel.archimedean *
          correctionPart x ZetaPacketLabel.archimedean := by
          exact pointwise_sq_archimedean_rewrite x

theorem pointwise_sq_correction_rewrite (x : ZetaPacketEnsemble) :
    correctionPart x ZetaPacketLabel.correction *
        correctionPart x ZetaPacketLabel.correction =
      primePart x ZetaPacketLabel.correction * primePart x ZetaPacketLabel.correction +
      archimedeanPart x ZetaPacketLabel.correction *
        archimedeanPart x ZetaPacketLabel.correction +
      correctionPart x ZetaPacketLabel.correction *
        correctionPart x ZetaPacketLabel.correction := by
  have hp : primePart x ZetaPacketLabel.correction = 0 :=
    primePart_correction x
  have ha : archimedeanPart x ZetaPacketLabel.correction = 0 :=
    archimedeanPart_correction x
  exact add_vanish_one_two
    (primePart x ZetaPacketLabel.correction *
      primePart x ZetaPacketLabel.correction)
    (archimedeanPart x ZetaPacketLabel.correction *
      archimedeanPart x ZetaPacketLabel.correction)
    (correctionPart x ZetaPacketLabel.correction *
      correctionPart x ZetaPacketLabel.correction)
    (sq_eq_zero_of_eq_zero hp) (sq_eq_zero_of_eq_zero ha)

theorem pointwise_sq_correction (x : ZetaPacketEnsemble) :
    x ZetaPacketLabel.correction * x ZetaPacketLabel.correction =
      primePart x ZetaPacketLabel.correction * primePart x ZetaPacketLabel.correction +
      archimedeanPart x ZetaPacketLabel.correction *
        archimedeanPart x ZetaPacketLabel.correction +
      correctionPart x ZetaPacketLabel.correction *
        correctionPart x ZetaPacketLabel.correction := by
  have hp : primePart x ZetaPacketLabel.correction = 0 :=
    primePart_correction x
  have ha : archimedeanPart x ZetaPacketLabel.correction = 0 :=
    archimedeanPart_correction x
  have hc : correctionPart x ZetaPacketLabel.correction = x ZetaPacketLabel.correction :=
    correctionPart_correction x
  calc
    x ZetaPacketLabel.correction * x ZetaPacketLabel.correction
        = correctionPart x ZetaPacketLabel.correction *
            correctionPart x ZetaPacketLabel.correction := by
          exact square_congr hc.symm
    _ = primePart x ZetaPacketLabel.correction * primePart x ZetaPacketLabel.correction +
        archimedeanPart x ZetaPacketLabel.correction *
          archimedeanPart x ZetaPacketLabel.correction +
        correctionPart x ZetaPacketLabel.correction *
          correctionPart x ZetaPacketLabel.correction := by
          exact pointwise_sq_correction_rewrite x

theorem pointwise_sq_decompose (x : ZetaPacketEnsemble) (ℓ : ZetaPacketLabel) :
    x ℓ * x ℓ =
      primePart x ℓ * primePart x ℓ +
      archimedeanPart x ℓ * archimedeanPart x ℓ +
      correctionPart x ℓ * correctionPart x ℓ := by
  cases ℓ with
  | prime m n => exact pointwise_sq_prime x m n
  | archimedean => exact pointwise_sq_archimedean x
  | correction => exact pointwise_sq_correction x

theorem dotProduct_prime_archimedean_prime (x : ZetaPacketEnsemble) (m n : ℕ) :
    primePart x (ZetaPacketLabel.prime m n) * archimedeanPart x (ZetaPacketLabel.prime m n) = 0 := by
  have hp := primePart_prime x m n
  have ha := archimedeanPart_prime x m n
  cases hp
  cases ha
  exact mul_zero _

theorem dotProduct_prime_archimedean_archimedean (x : ZetaPacketEnsemble) :
    primePart x ZetaPacketLabel.archimedean *
        archimedeanPart x ZetaPacketLabel.archimedean = 0 := by
  have hp := primePart_archimedean x
  have ha := archimedeanPart_archimedean x
  cases hp
  cases ha
  exact zero_mul _

theorem dotProduct_prime_archimedean_correction (x : ZetaPacketEnsemble) :
    primePart x ZetaPacketLabel.correction *
        archimedeanPart x ZetaPacketLabel.correction = 0 := by
  have hp := primePart_correction x
  have ha := archimedeanPart_correction x
  cases hp
  cases ha
  exact zero_mul _

/-- Helper: the prime and archimedean packet parts are orthogonal. -/
theorem dotProduct_prime_archimedean_helper (x : ZetaPacketEnsemble) :
    ZetaPacketEnsemble.dotProduct (primePart x) (archimedeanPart x) = 0 := by
  unfold ZetaPacketEnsemble.dotProduct
  refine Finset.sum_eq_zero ?_
  intro ℓ hℓ
  cases ℓ with
  | prime m n => exact dotProduct_prime_archimedean_prime x m n
  | archimedean => exact dotProduct_prime_archimedean_archimedean x
  | correction => exact dotProduct_prime_archimedean_correction x

/-- Prime and archimedean packet parts are orthogonal for the packet kernel. -/
theorem dotProduct_prime_archimedean (x : ZetaPacketEnsemble) :
    ZetaPacketEnsemble.dotProduct (primePart x) (archimedeanPart x) = 0 := by
  exact dotProduct_prime_archimedean_helper x

theorem dotProduct_prime_correction_prime (x : ZetaPacketEnsemble) (m n : ℕ) :
    primePart x (ZetaPacketLabel.prime m n) * correctionPart x (ZetaPacketLabel.prime m n) = 0 := by
  have hp := primePart_prime x m n
  have hc := correctionPart_prime x m n
  cases hp
  cases hc
  exact mul_zero _

theorem dotProduct_prime_correction_archimedean (x : ZetaPacketEnsemble) :
    primePart x ZetaPacketLabel.archimedean * correctionPart x ZetaPacketLabel.archimedean = 0 := by
  have hp := primePart_archimedean x
  have hc := correctionPart_archimedean x
  cases hp
  cases hc
  exact zero_mul _

theorem dotProduct_prime_correction_correction (x : ZetaPacketEnsemble) :
    primePart x ZetaPacketLabel.correction * correctionPart x ZetaPacketLabel.correction = 0 := by
  have hp := primePart_correction x
  have hc := correctionPart_correction x
  cases hp
  cases hc
  exact zero_mul _

/-- Helper: the prime and correction packet parts are orthogonal. -/
theorem dotProduct_prime_correction_helper (x : ZetaPacketEnsemble) :
    ZetaPacketEnsemble.dotProduct (primePart x) (correctionPart x) = 0 := by
  unfold ZetaPacketEnsemble.dotProduct
  refine Finset.sum_eq_zero ?_
  intro ℓ hℓ
  cases ℓ with
  | prime m n => exact dotProduct_prime_correction_prime x m n
  | archimedean => exact dotProduct_prime_correction_archimedean x
  | correction => exact dotProduct_prime_correction_correction x

/-- Prime and correction packet parts are orthogonal for the packet kernel. -/
theorem dotProduct_prime_correction (x : ZetaPacketEnsemble) :
    ZetaPacketEnsemble.dotProduct (primePart x) (correctionPart x) = 0 := by
  exact dotProduct_prime_correction_helper x

theorem dotProduct_archimedean_correction_prime (x : ZetaPacketEnsemble) (m n : ℕ) :
    archimedeanPart x (ZetaPacketLabel.prime m n) * correctionPart x (ZetaPacketLabel.prime m n) = 0 := by
  have ha := archimedeanPart_prime x m n
  have hc := correctionPart_prime x m n
  cases ha
  cases hc
  exact zero_mul _

theorem dotProduct_archimedean_correction_archimedean (x : ZetaPacketEnsemble) :
    archimedeanPart x ZetaPacketLabel.archimedean * correctionPart x ZetaPacketLabel.archimedean = 0 := by
  have ha := archimedeanPart_archimedean x
  have hc := correctionPart_archimedean x
  cases ha
  cases hc
  exact mul_zero _

theorem dotProduct_archimedean_correction_correction (x : ZetaPacketEnsemble) :
    archimedeanPart x ZetaPacketLabel.correction * correctionPart x ZetaPacketLabel.correction = 0 := by
  have ha := archimedeanPart_correction x
  have hc := correctionPart_correction x
  cases ha
  cases hc
  exact zero_mul _

/-- Helper: the archimedean and correction packet parts are orthogonal. -/
theorem dotProduct_archimedean_correction_helper (x : ZetaPacketEnsemble) :
    ZetaPacketEnsemble.dotProduct (archimedeanPart x) (correctionPart x) = 0 := by
  unfold ZetaPacketEnsemble.dotProduct
  refine Finset.sum_eq_zero ?_
  intro ℓ hℓ
  cases ℓ with
  | prime m n => exact dotProduct_archimedean_correction_prime x m n
  | archimedean => exact dotProduct_archimedean_correction_archimedean x
  | correction => exact dotProduct_archimedean_correction_correction x

/-- Archimedean and correction packet parts are orthogonal for the packet kernel. -/
theorem dotProduct_archimedean_correction (x : ZetaPacketEnsemble) :
    ZetaPacketEnsemble.dotProduct (archimedeanPart x) (correctionPart x) = 0 := by
  exact dotProduct_archimedean_correction_helper x

/-- Helper: the packet norm square splits into familywise Gram sums. -/
theorem normSq_eq_prime_add_archimedean_add_correction_helper (x : ZetaPacketEnsemble) :
    normSq x = primePacketGram x + archimedeanPacketGram x + correctionPacketGram x := by
  unfold normSq dotProduct primePacketGram archimedeanPacketGram correctionPacketGram
  rw [support_union_self x]
  calc
    ∑ ℓ ∈ x.support, x ℓ * x ℓ
        = ∑ ℓ ∈ x.support,
            (primePart x ℓ * primePart x ℓ +
              archimedeanPart x ℓ * archimedeanPart x ℓ +
              correctionPart x ℓ * correctionPart x ℓ) := by
            refine Finset.sum_congr rfl ?_
            intro ℓ hℓ
            exact pointwise_sq_decompose x ℓ
    _ = ∑ ℓ ∈ x.support, primePart x ℓ * primePart x ℓ +
          ∑ ℓ ∈ x.support, archimedeanPart x ℓ * archimedeanPart x ℓ +
          ∑ ℓ ∈ x.support, correctionPart x ℓ * correctionPart x ℓ := by
            exact sum_three_terms x.support
              (fun ℓ => primePart x ℓ * primePart x ℓ)
              (fun ℓ => archimedeanPart x ℓ * archimedeanPart x ℓ)
              (fun ℓ => correctionPart x ℓ * correctionPart x ℓ)
    _ = primePacketGram x + archimedeanPacketGram x + correctionPacketGram x := by
            rfl

/-- The squared norm splits into the three packet-family Gram sums. -/
theorem normSq_eq_prime_add_archimedean_add_correction (x : ZetaPacketEnsemble) :
    normSq x = primePacketGram x + archimedeanPacketGram x + correctionPacketGram x := by
  exact normSq_eq_prime_add_archimedean_add_correction_helper x

theorem normSq_eq_primePacketGram_add_archimedeanPacketGram_add_correctionPacketGram
    (x : ZetaPacketEnsemble) :
    normSq x = primePacketGram x + archimedeanPacketGram x + correctionPacketGram x := by
  exact normSq_eq_prime_add_archimedean_add_correction x

/-- The packet norm-square identity on the finite packet ensemble. -/
theorem zetaPacketNormSquare (x : ZetaPacketEnsemble) :
    normSq x = primePacketGram x + archimedeanPacketGram x + correctionPacketGram x := by
  exact normSq_eq_primePacketGram_add_archimedeanPacketGram_add_correctionPacketGram x

end ZetaPacketEnsemble

end
end LFunctions
end Boundary
