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
      have hp : primePart x (ZetaPacketLabel.prime m n) = x (ZetaPacketLabel.prime m n) :=
        primePart_prime x m n
      have ha : archimedeanPart x (ZetaPacketLabel.prime m n) = 0 :=
        archimedeanPart_prime x m n
      have hc : correctionPart x (ZetaPacketLabel.prime m n) = 0 :=
        correctionPart_prime x m n
      calc
        x (ZetaPacketLabel.prime m n) * x (ZetaPacketLabel.prime m n)
            = primePart x (ZetaPacketLabel.prime m n) * primePart x (ZetaPacketLabel.prime m n) := by
              exact congrArg (fun t => t * t) hp
        _ = primePart x (ZetaPacketLabel.prime m n) * primePart x (ZetaPacketLabel.prime m n) +
            archimedeanPart x (ZetaPacketLabel.prime m n) *
              archimedeanPart x (ZetaPacketLabel.prime m n) +
            correctionPart x (ZetaPacketLabel.prime m n) *
              correctionPart x (ZetaPacketLabel.prime m n) := by
              rw [ha, hc]
              simp
  | archimedean =>
      have hp : primePart x ZetaPacketLabel.archimedean = 0 :=
        primePart_archimedean x
      have ha : archimedeanPart x ZetaPacketLabel.archimedean = x ZetaPacketLabel.archimedean :=
        archimedeanPart_archimedean x
      have hc : correctionPart x ZetaPacketLabel.archimedean = 0 :=
        correctionPart_archimedean x
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
              rw [hp, hc]
              simp
  | correction =>
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
              rw [hp, ha]
              simp

/-- Prime and archimedean packet parts are orthogonal for the packet kernel. -/
theorem dotProduct_prime_archimedean (x : ZetaPacketEnsemble) :
    ZetaPacketEnsemble.dotProduct (primePart x) (archimedeanPart x) = 0 := by
  unfold ZetaPacketEnsemble.dotProduct
  refine Finset.sum_eq_zero ?_
  intro ℓ hℓ
  cases ℓ with
  | prime m n =>
      have hp := primePart_prime x m n
      have ha := archimedeanPart_prime x m n
      exact by
        calc
          primePart x (ZetaPacketLabel.prime m n) * archimedeanPart x (ZetaPacketLabel.prime m n)
              = x (ZetaPacketLabel.prime m n) * 0 := by
                rw [hp, ha]
          _ = 0 := by
                exact mul_zero _
  | archimedean =>
      have hp := primePart_archimedean x
      have ha := archimedeanPart_archimedean x
      exact by
        calc
          primePart x ZetaPacketLabel.archimedean *
              archimedeanPart x ZetaPacketLabel.archimedean
              = 0 * x ZetaPacketLabel.archimedean := by
                rw [hp, ha]
          _ = 0 := by
                exact zero_mul _
  | correction =>
      have hp := primePart_correction x
      have ha := archimedeanPart_correction x
      exact by
        calc
          primePart x ZetaPacketLabel.correction *
              archimedeanPart x ZetaPacketLabel.correction
              = 0 * 0 := by
                rw [hp, ha]
          _ = 0 := by
                exact zero_mul _

/-- Prime and correction packet parts are orthogonal for the packet kernel. -/
theorem dotProduct_prime_correction (x : ZetaPacketEnsemble) :
    ZetaPacketEnsemble.dotProduct (primePart x) (correctionPart x) = 0 := by
  unfold ZetaPacketEnsemble.dotProduct
  refine Finset.sum_eq_zero ?_
  intro ℓ hℓ
  cases ℓ with
  | prime m n =>
      have hp := primePart_prime x m n
      have hc := correctionPart_prime x m n
      exact by
        calc
          primePart x (ZetaPacketLabel.prime m n) * correctionPart x (ZetaPacketLabel.prime m n)
              = x (ZetaPacketLabel.prime m n) * 0 := by
                rw [hp, hc]
          _ = 0 := by
                exact mul_zero _
  | archimedean =>
      have hp := primePart_archimedean x
      have hc := correctionPart_archimedean x
      exact by
        calc
          primePart x ZetaPacketLabel.archimedean * correctionPart x ZetaPacketLabel.archimedean
              = 0 * 0 := by
                rw [hp, hc]
          _ = 0 := by
                exact zero_mul _
  | correction =>
      have hp := primePart_correction x
      have hc := correctionPart_correction x
      exact by
        calc
          primePart x ZetaPacketLabel.correction * correctionPart x ZetaPacketLabel.correction
              = 0 * x ZetaPacketLabel.correction := by
                rw [hp, hc]
          _ = 0 := by
                exact zero_mul _

/-- Archimedean and correction packet parts are orthogonal for the packet kernel. -/
theorem dotProduct_archimedean_correction (x : ZetaPacketEnsemble) :
    ZetaPacketEnsemble.dotProduct (archimedeanPart x) (correctionPart x) = 0 := by
  unfold ZetaPacketEnsemble.dotProduct
  refine Finset.sum_eq_zero ?_
  intro ℓ hℓ
  cases ℓ with
  | prime m n =>
      have ha := archimedeanPart_prime x m n
      have hc := correctionPart_prime x m n
      exact by
        calc
          archimedeanPart x (ZetaPacketLabel.prime m n) *
              correctionPart x (ZetaPacketLabel.prime m n)
              = 0 * 0 := by
                rw [ha, hc]
          _ = 0 := by
                exact zero_mul _
  | archimedean =>
      have ha := archimedeanPart_archimedean x
      have hc := correctionPart_archimedean x
      exact by
        calc
          archimedeanPart x ZetaPacketLabel.archimedean *
              correctionPart x ZetaPacketLabel.archimedean
              = x ZetaPacketLabel.archimedean * 0 := by
                rw [ha, hc]
          _ = 0 := by
                exact mul_zero _
  | correction =>
      have ha := archimedeanPart_correction x
      have hc := correctionPart_correction x
      exact by
        calc
          archimedeanPart x ZetaPacketLabel.correction *
              correctionPart x ZetaPacketLabel.correction
              = 0 * x ZetaPacketLabel.correction := by
                rw [ha, hc]
          _ = 0 := by
                exact zero_mul _

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
