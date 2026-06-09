import Boundary.LFunctions.ZetaPacketDecomposition

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
  have harch_sq : 0 =
      archimedeanPart x (ZetaPacketLabel.prime m n) *
        archimedeanPart x (ZetaPacketLabel.prime m n) := by
    rw [ha]
    exact (zero_mul _).symm
  have hcorr_sq : 0 =
      correctionPart x (ZetaPacketLabel.prime m n) *
        correctionPart x (ZetaPacketLabel.prime m n) := by
    rw [hc]
    exact (zero_mul _).symm
  calc
    primePart x (ZetaPacketLabel.prime m n) * primePart x (ZetaPacketLabel.prime m n)
        = primePart x (ZetaPacketLabel.prime m n) * primePart x (ZetaPacketLabel.prime m n) + 0 + 0 := by
          rw [add_zero, add_zero]
    _ = primePart x (ZetaPacketLabel.prime m n) * primePart x (ZetaPacketLabel.prime m n) +
        archimedeanPart x (ZetaPacketLabel.prime m n) *
          archimedeanPart x (ZetaPacketLabel.prime m n) + 0 := by
          rw [harch_sq]
    _ = primePart x (ZetaPacketLabel.prime m n) * primePart x (ZetaPacketLabel.prime m n) +
        archimedeanPart x (ZetaPacketLabel.prime m n) *
          archimedeanPart x (ZetaPacketLabel.prime m n) +
        correctionPart x (ZetaPacketLabel.prime m n) *
          correctionPart x (ZetaPacketLabel.prime m n) := by
          rw [hcorr_sq]

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
          exact congrArg (fun t => t * t) hp
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
  have hprime_sq : 0 =
      primePart x ZetaPacketLabel.archimedean *
        primePart x ZetaPacketLabel.archimedean := by
    rw [hp]
    exact (zero_mul _).symm
  have hcorr_sq : 0 =
      correctionPart x ZetaPacketLabel.archimedean *
        correctionPart x ZetaPacketLabel.archimedean := by
    rw [hc]
    exact (zero_mul _).symm
  calc
    archimedeanPart x ZetaPacketLabel.archimedean *
        archimedeanPart x ZetaPacketLabel.archimedean
        = 0 + archimedeanPart x ZetaPacketLabel.archimedean *
            archimedeanPart x ZetaPacketLabel.archimedean + 0 := by
          rw [zero_add, add_zero]
    _ = primePart x ZetaPacketLabel.archimedean * primePart x ZetaPacketLabel.archimedean +
        archimedeanPart x ZetaPacketLabel.archimedean *
          archimedeanPart x ZetaPacketLabel.archimedean + 0 := by
          rw [hprime_sq]
    _ = primePart x ZetaPacketLabel.archimedean * primePart x ZetaPacketLabel.archimedean +
        archimedeanPart x ZetaPacketLabel.archimedean *
          archimedeanPart x ZetaPacketLabel.archimedean +
        correctionPart x ZetaPacketLabel.archimedean *
          correctionPart x ZetaPacketLabel.archimedean := by
          rw [hcorr_sq]

theorem pointwise_sq_archimedean (x : ZetaPacketEnsemble) :
    x ZetaPacketLabel.archimedean * x ZetaPacketLabel.archimedean =
      primePart x ZetaPacketLabel.archimedean * primePart x ZetaPacketLabel.archimedean +
      archimedeanPart x ZetaPacketLabel.archimedean *
        archimedeanPart x ZetaPacketLabel.archimedean +
      correctionPart x ZetaPacketLabel.archimedean *
        correctionPart x ZetaPacketLabel.archimedean := by
  have hp : primePart x ZetaPacketLabel.archimedean = 0 :=
    primePart_archimedean x
  have ha : archimedeanPart x ZetaPacketLabel.archimedean = x ZetaPacketLabel.archimedean :=
    archimedeanPart_archimedean x
  calc
    x ZetaPacketLabel.archimedean * x ZetaPacketLabel.archimedean
        = archimedeanPart x ZetaPacketLabel.archimedean *
            archimedeanPart x ZetaPacketLabel.archimedean := by
          exact congrArg (fun t => t * t) ha.symm
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
  have hprime_sq : 0 =
      primePart x ZetaPacketLabel.correction *
        primePart x ZetaPacketLabel.correction := by
    rw [hp]
    exact (zero_mul _).symm
  have harch_sq : 0 =
      archimedeanPart x ZetaPacketLabel.correction *
        archimedeanPart x ZetaPacketLabel.correction := by
    rw [ha]
    exact (zero_mul _).symm
  calc
    correctionPart x ZetaPacketLabel.correction *
        correctionPart x ZetaPacketLabel.correction
        = 0 + 0 + correctionPart x ZetaPacketLabel.correction *
            correctionPart x ZetaPacketLabel.correction := by
          rw [zero_add, zero_add]
    _ = primePart x ZetaPacketLabel.correction * primePart x ZetaPacketLabel.correction +
        0 + correctionPart x ZetaPacketLabel.correction *
          correctionPart x ZetaPacketLabel.correction := by
          rw [hprime_sq]
    _ = primePart x ZetaPacketLabel.correction * primePart x ZetaPacketLabel.correction +
        archimedeanPart x ZetaPacketLabel.correction *
          archimedeanPart x ZetaPacketLabel.correction +
        correctionPart x ZetaPacketLabel.correction *
          correctionPart x ZetaPacketLabel.correction := by
          rw [harch_sq]

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
          exact congrArg (fun t => t * t) hc.symm
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
  calc
    primePart x (ZetaPacketLabel.prime m n) * archimedeanPart x (ZetaPacketLabel.prime m n)
        = x (ZetaPacketLabel.prime m n) * 0 := by
          rw [hp, ha]
    _ = 0 := by
          exact mul_zero _

theorem dotProduct_prime_archimedean_archimedean (x : ZetaPacketEnsemble) :
    primePart x ZetaPacketLabel.archimedean *
        archimedeanPart x ZetaPacketLabel.archimedean = 0 := by
  have hp := primePart_archimedean x
  have ha := archimedeanPart_archimedean x
  calc
    primePart x ZetaPacketLabel.archimedean *
        archimedeanPart x ZetaPacketLabel.archimedean
        = 0 * x ZetaPacketLabel.archimedean := by
          rw [hp, ha]
    _ = 0 := by
          exact zero_mul _

theorem dotProduct_prime_archimedean_correction (x : ZetaPacketEnsemble) :
    primePart x ZetaPacketLabel.correction *
        archimedeanPart x ZetaPacketLabel.correction = 0 := by
  have hp := primePart_correction x
  have ha := archimedeanPart_correction x
  calc
    primePart x ZetaPacketLabel.correction *
        archimedeanPart x ZetaPacketLabel.correction
        = 0 * 0 := by
          rw [hp, ha]
    _ = 0 := by
          exact zero_mul _

/-- Prime and archimedean packet parts are orthogonal for the packet kernel. -/
theorem dotProduct_prime_archimedean (x : ZetaPacketEnsemble) :
    ZetaPacketEnsemble.dotProduct (primePart x) (archimedeanPart x) = 0 := by
  unfold ZetaPacketEnsemble.dotProduct
  refine Finset.sum_eq_zero ?_
  intro ℓ hℓ
  cases ℓ with
  | prime m n => exact dotProduct_prime_archimedean_prime x m n
  | archimedean => exact dotProduct_prime_archimedean_archimedean x
  | correction => exact dotProduct_prime_archimedean_correction x

theorem dotProduct_prime_correction_prime (x : ZetaPacketEnsemble) (m n : ℕ) :
    primePart x (ZetaPacketLabel.prime m n) * correctionPart x (ZetaPacketLabel.prime m n) = 0 := by
  have hp := primePart_prime x m n
  have hc := correctionPart_prime x m n
  calc
    primePart x (ZetaPacketLabel.prime m n) * correctionPart x (ZetaPacketLabel.prime m n)
        = x (ZetaPacketLabel.prime m n) * 0 := by
          rw [hp, hc]
    _ = 0 := by
          exact mul_zero _

theorem dotProduct_prime_correction_archimedean (x : ZetaPacketEnsemble) :
    primePart x ZetaPacketLabel.archimedean * correctionPart x ZetaPacketLabel.archimedean = 0 := by
  have hp := primePart_archimedean x
  have hc := correctionPart_archimedean x
  calc
    primePart x ZetaPacketLabel.archimedean * correctionPart x ZetaPacketLabel.archimedean
        = 0 * 0 := by
          rw [hp, hc]
    _ = 0 := by
          exact zero_mul _

theorem dotProduct_prime_correction_correction (x : ZetaPacketEnsemble) :
    primePart x ZetaPacketLabel.correction * correctionPart x ZetaPacketLabel.correction = 0 := by
  have hp := primePart_correction x
  have hc := correctionPart_correction x
  calc
    primePart x ZetaPacketLabel.correction * correctionPart x ZetaPacketLabel.correction
        = 0 * x ZetaPacketLabel.correction := by
          rw [hp, hc]
    _ = 0 := by
          exact zero_mul _

/-- Prime and correction packet parts are orthogonal for the packet kernel. -/
theorem dotProduct_prime_correction (x : ZetaPacketEnsemble) :
    ZetaPacketEnsemble.dotProduct (primePart x) (correctionPart x) = 0 := by
  unfold ZetaPacketEnsemble.dotProduct
  refine Finset.sum_eq_zero ?_
  intro ℓ hℓ
  cases ℓ with
  | prime m n => exact dotProduct_prime_correction_prime x m n
  | archimedean => exact dotProduct_prime_correction_archimedean x
  | correction => exact dotProduct_prime_correction_correction x

theorem dotProduct_archimedean_correction_prime (x : ZetaPacketEnsemble) (m n : ℕ) :
    archimedeanPart x (ZetaPacketLabel.prime m n) * correctionPart x (ZetaPacketLabel.prime m n) = 0 := by
  have ha := archimedeanPart_prime x m n
  have hc := correctionPart_prime x m n
  calc
    archimedeanPart x (ZetaPacketLabel.prime m n) * correctionPart x (ZetaPacketLabel.prime m n)
        = 0 * 0 := by
          rw [ha, hc]
    _ = 0 := by
          exact zero_mul _

theorem dotProduct_archimedean_correction_archimedean (x : ZetaPacketEnsemble) :
    archimedeanPart x ZetaPacketLabel.archimedean * correctionPart x ZetaPacketLabel.archimedean = 0 := by
  have ha := archimedeanPart_archimedean x
  have hc := correctionPart_archimedean x
  calc
    archimedeanPart x ZetaPacketLabel.archimedean * correctionPart x ZetaPacketLabel.archimedean
        = x ZetaPacketLabel.archimedean * 0 := by
          rw [ha, hc]
    _ = 0 := by
          exact mul_zero _

theorem dotProduct_archimedean_correction_correction (x : ZetaPacketEnsemble) :
    archimedeanPart x ZetaPacketLabel.correction * correctionPart x ZetaPacketLabel.correction = 0 := by
  have ha := archimedeanPart_correction x
  have hc := correctionPart_correction x
  calc
    archimedeanPart x ZetaPacketLabel.correction * correctionPart x ZetaPacketLabel.correction
        = 0 * x ZetaPacketLabel.correction := by
          rw [ha, hc]
    _ = 0 := by
          exact zero_mul _

/-- Archimedean and correction packet parts are orthogonal for the packet kernel. -/
theorem dotProduct_archimedean_correction (x : ZetaPacketEnsemble) :
    ZetaPacketEnsemble.dotProduct (archimedeanPart x) (correctionPart x) = 0 := by
  unfold ZetaPacketEnsemble.dotProduct
  refine Finset.sum_eq_zero ?_
  intro ℓ hℓ
  cases ℓ with
  | prime m n => exact dotProduct_archimedean_correction_prime x m n
  | archimedean => exact dotProduct_archimedean_correction_archimedean x
  | correction => exact dotProduct_archimedean_correction_correction x

/-- The squared norm splits into the three packet-family Gram sums. -/
theorem normSq_eq_prime_add_archimedean_add_correction (x : ZetaPacketEnsemble) :
    normSq x = primePacketGram x + archimedeanPacketGram x + correctionPacketGram x := by
  unfold normSq dotProduct primePacketGram archimedeanPacketGram correctionPacketGram
  rw [Finset.union_self]
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
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = primePacketGram x + archimedeanPacketGram x + correctionPacketGram x := by
            rfl

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
