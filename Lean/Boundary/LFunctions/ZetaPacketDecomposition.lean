import Boundary.LFunctions.ZetaPacketKernel

/-!
# Boundary zeta packet decomposition

This file makes the packet-family split explicit at the level of finite-support
ensembles. The construction is intentionally direct: it uses `Finsupp.filter`
to isolate the prime, archimedean, and correction components.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Classical

namespace ZetaPacketLabel

/-- Predicate selecting prime packet labels. -/
def IsPrime : ZetaPacketLabel → Prop
  | .prime _ _ => True
  | _ => False

/-- Predicate selecting the archimedean packet. -/
def IsArchimedean : ZetaPacketLabel → Prop
  | .archimedean => True
  | _ => False

/-- Predicate selecting the correction packet. -/
def IsCorrection : ZetaPacketLabel → Prop
  | .correction => True
  | _ => False

theorem isPrime_prime (m n : ℕ) : IsPrime (.prime m n) := by
  trivial

theorem isPrime_archimedean : ¬ IsPrime (.archimedean) := by
  intro h
  cases h

theorem isPrime_correction : ¬ IsPrime (.correction) := by
  intro h
  cases h

theorem isArchimedean_archimedean : IsArchimedean .archimedean := by
  trivial

theorem isArchimedean_prime (m n : ℕ) : ¬ IsArchimedean (.prime m n) := by
  intro h
  cases h

theorem isArchimedean_correction : ¬ IsArchimedean (.correction) := by
  intro h
  cases h

theorem isCorrection_correction : IsCorrection .correction := by
  trivial

theorem isCorrection_prime (m n : ℕ) : ¬ IsCorrection (.prime m n) := by
  intro h
  cases h

theorem isCorrection_archimedean : ¬ IsCorrection .archimedean := by
  intro h
  cases h

end ZetaPacketLabel

namespace ZetaPacketEnsemble

/-- The prime part of a packet ensemble. -/
def primePart (x : ZetaPacketEnsemble) : ZetaPacketEnsemble :=
  x.filter ZetaPacketLabel.IsPrime

/-- The archimedean part of a packet ensemble. -/
def archimedeanPart (x : ZetaPacketEnsemble) : ZetaPacketEnsemble :=
  x.filter ZetaPacketLabel.IsArchimedean

/-- The correction part of a packet ensemble. -/
def correctionPart (x : ZetaPacketEnsemble) : ZetaPacketEnsemble :=
  x.filter ZetaPacketLabel.IsCorrection

theorem primePart_apply (x : ZetaPacketEnsemble) (ℓ : ZetaPacketLabel) :
    primePart x ℓ = if ZetaPacketLabel.IsPrime ℓ then x ℓ else 0 := by
  rfl

theorem archimedeanPart_apply (x : ZetaPacketEnsemble) (ℓ : ZetaPacketLabel) :
    archimedeanPart x ℓ = if ZetaPacketLabel.IsArchimedean ℓ then x ℓ else 0 := by
  rfl

theorem correctionPart_apply (x : ZetaPacketEnsemble) (ℓ : ZetaPacketLabel) :
    correctionPart x ℓ = if ZetaPacketLabel.IsCorrection ℓ then x ℓ else 0 := by
  rfl

/-- The packet decomposition as a literal sum of the three filtered parts. -/
theorem add_prime_archimedean_correction (x : ZetaPacketEnsemble) :
    primePart x + archimedeanPart x + correctionPart x = x := by
  ext ℓ
  cases ℓ with
  | prime m n =>
      change primePart x (ZetaPacketLabel.prime m n) +
          archimedeanPart x (ZetaPacketLabel.prime m n) +
          correctionPart x (ZetaPacketLabel.prime m n) =
        x (ZetaPacketLabel.prime m n)
      rw [primePart_apply, archimedeanPart_apply, correctionPart_apply]
      rw [if_pos (ZetaPacketLabel.isPrime_prime m n)]
      rw [if_neg (ZetaPacketLabel.isArchimedean_prime m n)]
      rw [if_neg (ZetaPacketLabel.isCorrection_prime m n)]
      simp
  | archimedean =>
      change primePart x ZetaPacketLabel.archimedean +
          archimedeanPart x ZetaPacketLabel.archimedean +
          correctionPart x ZetaPacketLabel.archimedean =
        x ZetaPacketLabel.archimedean
      rw [primePart_apply, archimedeanPart_apply, correctionPart_apply]
      rw [if_neg ZetaPacketLabel.isPrime_archimedean]
      rw [if_pos ZetaPacketLabel.isArchimedean_archimedean]
      rw [if_neg ZetaPacketLabel.isCorrection_archimedean]
      simp
  | correction =>
      change primePart x ZetaPacketLabel.correction +
          archimedeanPart x ZetaPacketLabel.correction +
          correctionPart x ZetaPacketLabel.correction =
        x ZetaPacketLabel.correction
      rw [primePart_apply, archimedeanPart_apply, correctionPart_apply]
      rw [if_neg ZetaPacketLabel.isPrime_correction]
      rw [if_neg ZetaPacketLabel.isArchimedean_correction]
      rw [if_pos ZetaPacketLabel.isCorrection_correction]
      simp

/-- Prime and archimedean packet parts have disjoint support. -/
theorem support_primePart_disjoint_archimedeanPart (x : ZetaPacketEnsemble) :
    Disjoint x.primePart.support x.archimedeanPart.support := by
  classical
  refine Finset.disjoint_left.2 ?_
  intro ℓ h₁ h₂
  cases ℓ with
  | prime m n =>
      have h₂nz : x.archimedeanPart (ZetaPacketLabel.prime m n) ≠ 0 := by
        exact Finsupp.mem_support_iff.mp h₂
      have h₂eq : x.archimedeanPart (ZetaPacketLabel.prime m n) = 0 := by
        rw [archimedeanPart_apply]
        rw [if_neg (ZetaPacketLabel.isArchimedean_prime m n)]
      exact h₂nz h₂eq
  | archimedean =>
      have h₁nz : x.primePart ZetaPacketLabel.archimedean ≠ 0 := by
        exact Finsupp.mem_support_iff.mp h₁
      have h₁eq : x.primePart ZetaPacketLabel.archimedean = 0 := by
        rw [primePart_apply]
        rw [if_neg ZetaPacketLabel.isPrime_archimedean]
      exact h₁nz h₁eq
  | correction =>
      have h₁nz : x.primePart ZetaPacketLabel.correction ≠ 0 := by
        exact Finsupp.mem_support_iff.mp h₁
      have h₁eq : x.primePart ZetaPacketLabel.correction = 0 := by
        rw [primePart_apply]
        rw [if_neg ZetaPacketLabel.isPrime_correction]
      exact h₁nz h₁eq

/-- Prime and correction packet parts have disjoint support. -/
theorem support_primePart_disjoint_correctionPart (x : ZetaPacketEnsemble) :
    Disjoint x.primePart.support x.correctionPart.support := by
  classical
  refine Finset.disjoint_left.2 ?_
  intro ℓ h₁ h₂
  cases ℓ with
  | prime m n =>
      have h₂nz : x.correctionPart (ZetaPacketLabel.prime m n) ≠ 0 := by
        exact Finsupp.mem_support_iff.mp h₂
      have h₂eq : x.correctionPart (ZetaPacketLabel.prime m n) = 0 := by
        rw [correctionPart_apply]
        rw [if_neg (ZetaPacketLabel.isCorrection_prime m n)]
      exact h₂nz h₂eq
  | archimedean =>
      have h₁nz : x.primePart ZetaPacketLabel.archimedean ≠ 0 := by
        exact Finsupp.mem_support_iff.mp h₁
      have h₁eq : x.primePart ZetaPacketLabel.archimedean = 0 := by
        rw [primePart_apply]
        rw [if_neg ZetaPacketLabel.isPrime_archimedean]
      exact h₁nz h₁eq
  | correction =>
      have h₁nz : x.primePart ZetaPacketLabel.correction ≠ 0 := by
        exact Finsupp.mem_support_iff.mp h₁
      have h₁eq : x.primePart ZetaPacketLabel.correction = 0 := by
        rw [primePart_apply]
        rw [if_neg ZetaPacketLabel.isPrime_correction]
      exact h₁nz h₁eq

/-- Archimedean and correction packet parts have disjoint support. -/
theorem support_archimedeanPart_disjoint_correctionPart (x : ZetaPacketEnsemble) :
    Disjoint x.archimedeanPart.support x.correctionPart.support := by
  classical
  refine Finset.disjoint_left.2 ?_
  intro ℓ h₁ h₂
  cases ℓ with
  | prime m n =>
      have h₁nz : x.archimedeanPart (ZetaPacketLabel.prime m n) ≠ 0 := by
        exact Finsupp.mem_support_iff.mp h₁
      have h₁eq : x.archimedeanPart (ZetaPacketLabel.prime m n) = 0 := by
        rw [archimedeanPart_apply]
        rw [if_neg (ZetaPacketLabel.isArchimedean_prime m n)]
      exact h₁nz h₁eq
  | archimedean =>
      have h₂nz : x.correctionPart ZetaPacketLabel.archimedean ≠ 0 := by
        exact Finsupp.mem_support_iff.mp h₂
      have h₂eq : x.correctionPart ZetaPacketLabel.archimedean = 0 := by
        rw [correctionPart_apply]
        rw [if_neg ZetaPacketLabel.isCorrection_archimedean]
      exact h₂nz h₂eq
  | correction =>
      have h₁nz : x.archimedeanPart ZetaPacketLabel.correction ≠ 0 := by
        exact Finsupp.mem_support_iff.mp h₁
      have h₁eq : x.archimedeanPart ZetaPacketLabel.correction = 0 := by
        rw [archimedeanPart_apply]
        rw [if_neg ZetaPacketLabel.isArchimedean_correction]
      exact h₁nz h₁eq

end ZetaPacketEnsemble

end
end LFunctions
end Boundary
