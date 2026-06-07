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
theorem pointwise_sq_decompose (x : ZetaPacketEnsemble) (ℓ : ZetaPacketLabel) :
    x ℓ * x ℓ =
      primePart x ℓ * primePart x ℓ +
      archimedeanPart x ℓ * archimedeanPart x ℓ +
      correctionPart x ℓ * correctionPart x ℓ := by
  cases ℓ with
  | prime m n =>
      have hp : primePart x (ZetaPacketLabel.prime m n) = x (ZetaPacketLabel.prime m n) := by
        rw [primePart_apply, if_pos (ZetaPacketLabel.isPrime_prime m n)]
      have ha : archimedeanPart x (ZetaPacketLabel.prime m n) = 0 := by
        rw [archimedeanPart_apply, if_neg (ZetaPacketLabel.isArchimedean_prime m n)]
      have hc : correctionPart x (ZetaPacketLabel.prime m n) = 0 := by
        rw [correctionPart_apply, if_neg (ZetaPacketLabel.isCorrection_prime m n)]
      rw [hp, ha, hc]
      ring
  | archimedean =>
      have hp : primePart x ZetaPacketLabel.archimedean = 0 := by
        rw [primePart_apply, if_neg ZetaPacketLabel.isPrime_archimedean]
      have ha : archimedeanPart x ZetaPacketLabel.archimedean = x ZetaPacketLabel.archimedean := by
        rw [archimedeanPart_apply, if_pos ZetaPacketLabel.isArchimedean_archimedean]
      have hc : correctionPart x ZetaPacketLabel.archimedean = 0 := by
        rw [correctionPart_apply, if_neg ZetaPacketLabel.isCorrection_archimedean]
      rw [hp, ha, hc]
      ring
  | correction =>
      have hp : primePart x ZetaPacketLabel.correction = 0 := by
        rw [primePart_apply, if_neg ZetaPacketLabel.isPrime_correction]
      have ha : archimedeanPart x ZetaPacketLabel.correction = 0 := by
        rw [archimedeanPart_apply, if_neg ZetaPacketLabel.isArchimedean_correction]
      have hc : correctionPart x ZetaPacketLabel.correction = x ZetaPacketLabel.correction := by
        rw [correctionPart_apply, if_pos ZetaPacketLabel.isCorrection_correction]
      rw [hp, ha, hc]
      ring

/-- Prime and archimedean packet parts are orthogonal for the packet kernel. -/
theorem dotProduct_prime_archimedean (x : ZetaPacketEnsemble) :
    ZetaPacketEnsemble.dotProduct (primePart x) (archimedeanPart x) = 0 := by
  unfold ZetaPacketEnsemble.dotProduct
  refine Finset.sum_eq_zero ?_
  intro ℓ hℓ
  cases ℓ with
  | prime m n =>
      rw [primePart_apply, archimedeanPart_apply]
      rw [if_pos (ZetaPacketLabel.isPrime_prime m n)]
      rw [if_neg (ZetaPacketLabel.isArchimedean_prime m n)]
      ring
  | archimedean =>
      rw [primePart_apply, archimedeanPart_apply]
      rw [if_neg ZetaPacketLabel.isPrime_archimedean]
      rw [if_pos ZetaPacketLabel.isArchimedean_archimedean]
      ring
  | correction =>
      rw [primePart_apply, archimedeanPart_apply]
      rw [if_neg ZetaPacketLabel.isPrime_correction]
      rw [if_neg ZetaPacketLabel.isArchimedean_correction]
      ring

/-- Prime and correction packet parts are orthogonal for the packet kernel. -/
theorem dotProduct_prime_correction (x : ZetaPacketEnsemble) :
    ZetaPacketEnsemble.dotProduct (primePart x) (correctionPart x) = 0 := by
  unfold ZetaPacketEnsemble.dotProduct
  refine Finset.sum_eq_zero ?_
  intro ℓ hℓ
  cases ℓ with
  | prime m n =>
      rw [primePart_apply, correctionPart_apply]
      rw [if_pos (ZetaPacketLabel.isPrime_prime m n)]
      rw [if_neg (ZetaPacketLabel.isCorrection_prime m n)]
      ring
  | archimedean =>
      rw [primePart_apply, correctionPart_apply]
      rw [if_neg ZetaPacketLabel.isPrime_archimedean]
      rw [if_neg ZetaPacketLabel.isCorrection_archimedean]
      ring
  | correction =>
      rw [primePart_apply, correctionPart_apply]
      rw [if_neg ZetaPacketLabel.isPrime_correction]
      rw [if_pos ZetaPacketLabel.isCorrection_correction]
      ring

/-- Archimedean and correction packet parts are orthogonal for the packet kernel. -/
theorem dotProduct_archimedean_correction (x : ZetaPacketEnsemble) :
    ZetaPacketEnsemble.dotProduct (archimedeanPart x) (correctionPart x) = 0 := by
  unfold ZetaPacketEnsemble.dotProduct
  refine Finset.sum_eq_zero ?_
  intro ℓ hℓ
  cases ℓ with
  | prime m n =>
      rw [archimedeanPart_apply, correctionPart_apply]
      rw [if_neg (ZetaPacketLabel.isArchimedean_prime m n)]
      rw [if_neg (ZetaPacketLabel.isCorrection_prime m n)]
      ring
  | archimedean =>
      rw [archimedeanPart_apply, correctionPart_apply]
      rw [if_pos ZetaPacketLabel.isArchimedean_archimedean]
      rw [if_neg ZetaPacketLabel.isCorrection_archimedean]
      ring
  | correction =>
      rw [archimedeanPart_apply, correctionPart_apply]
      rw [if_neg ZetaPacketLabel.isArchimedean_correction]
      rw [if_pos ZetaPacketLabel.isCorrection_correction]
      ring

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

/-- The packet norm-square identity on the finite packet ensemble. -/
theorem zetaPacketNormSquare (x : ZetaPacketEnsemble) :
    normSq x = primePacketGram x + archimedeanPacketGram x + correctionPacketGram x := by
  exact normSq_eq_prime_add_archimedean_add_correction x

end ZetaPacketEnsemble

end
end LFunctions
end Boundary
