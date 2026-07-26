import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaPacketComparison.ZetaCompletedBoundaryDefect.ZetaPacketReconstruction.ZetaPacketDecomposition.ZetaPacketKernel.Owner

/-!
# Boundary zeta packet decomposition

This file makes the packet-family split explicit at the level of finite-support
ensembles. The construction is intentionally direct: it uses `Finsupp.filter`
to isolate the prime, archimedean, and correction components.
-/

namespace Boundary
namespace LFunctions

noncomputable section

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
  exact True.intro

theorem isPrime_archimedean : ¬ IsPrime (.archimedean) := by
  intro h
  cases h

theorem isPrime_correction : ¬ IsPrime (.correction) := by
  intro h
  cases h

theorem isArchimedean_archimedean : IsArchimedean .archimedean := by
  exact True.intro

theorem isArchimedean_prime (m n : ℕ) : ¬ IsArchimedean (.prime m n) := by
  intro h
  cases h

theorem isArchimedean_correction : ¬ IsArchimedean (.correction) := by
  intro h
  cases h

theorem isCorrection_correction : IsCorrection .correction := by
  exact True.intro

theorem isCorrection_prime (m n : ℕ) : ¬ IsCorrection (.prime m n) := by
  intro h
  cases h

theorem isCorrection_archimedean : ¬ IsCorrection .archimedean := by
  intro h
  cases h

end ZetaPacketLabel

namespace ZetaPacketEnsemble

instance : DecidablePred ZetaPacketLabel.IsPrime := by
  intro ℓ
  cases ℓ with
  | prime m n => exact isTrue True.intro
  | archimedean => exact isFalse (by intro h; cases h)
  | correction => exact isFalse (by intro h; cases h)

instance : DecidablePred ZetaPacketLabel.IsArchimedean := by
  intro ℓ
  cases ℓ with
  | prime m n => exact isFalse (by intro h; cases h)
  | archimedean => exact isTrue True.intro
  | correction => exact isFalse (by intro h; cases h)

instance : DecidablePred ZetaPacketLabel.IsCorrection := by
  intro ℓ
  cases ℓ with
  | prime m n => exact isFalse (by intro h; cases h)
  | archimedean => exact isFalse (by intro h; cases h)
  | correction => exact isTrue True.intro

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

theorem primePart_prime (x : ZetaPacketEnsemble) (m n : ℕ) :
    primePart x (ZetaPacketLabel.prime m n) = x (ZetaPacketLabel.prime m n) := by
  unfold primePart
  exact Finsupp.filter_apply_pos (f := x) (p := ZetaPacketLabel.IsPrime)
    (a := ZetaPacketLabel.prime m n) (ZetaPacketLabel.isPrime_prime m n)

theorem archimedeanPart_prime (x : ZetaPacketEnsemble) (m n : ℕ) :
    archimedeanPart x (ZetaPacketLabel.prime m n) = 0 := by
  unfold archimedeanPart
  exact Finsupp.filter_apply_neg (f := x) (p := ZetaPacketLabel.IsArchimedean)
    (a := ZetaPacketLabel.prime m n) (ZetaPacketLabel.isArchimedean_prime m n)

theorem correctionPart_prime (x : ZetaPacketEnsemble) (m n : ℕ) :
    correctionPart x (ZetaPacketLabel.prime m n) = 0 := by
  unfold correctionPart
  exact Finsupp.filter_apply_neg (f := x) (p := ZetaPacketLabel.IsCorrection)
    (a := ZetaPacketLabel.prime m n) (ZetaPacketLabel.isCorrection_prime m n)

theorem primePart_archimedean (x : ZetaPacketEnsemble) :
    primePart x ZetaPacketLabel.archimedean = 0 := by
  unfold primePart
  exact Finsupp.filter_apply_neg (f := x) (p := ZetaPacketLabel.IsPrime)
    (a := ZetaPacketLabel.archimedean) ZetaPacketLabel.isPrime_archimedean

theorem archimedeanPart_archimedean (x : ZetaPacketEnsemble) :
    archimedeanPart x ZetaPacketLabel.archimedean = x ZetaPacketLabel.archimedean := by
  unfold archimedeanPart
  exact Finsupp.filter_apply_pos (f := x) (p := ZetaPacketLabel.IsArchimedean)
    (a := ZetaPacketLabel.archimedean) ZetaPacketLabel.isArchimedean_archimedean

theorem correctionPart_archimedean (x : ZetaPacketEnsemble) :
    correctionPart x ZetaPacketLabel.archimedean = 0 := by
  unfold correctionPart
  exact Finsupp.filter_apply_neg (f := x) (p := ZetaPacketLabel.IsCorrection)
    (a := ZetaPacketLabel.archimedean) ZetaPacketLabel.isCorrection_archimedean

theorem primePart_correction (x : ZetaPacketEnsemble) :
    primePart x ZetaPacketLabel.correction = 0 := by
  unfold primePart
  exact Finsupp.filter_apply_neg (f := x) (p := ZetaPacketLabel.IsPrime)
    (a := ZetaPacketLabel.correction) ZetaPacketLabel.isPrime_correction

theorem archimedeanPart_correction (x : ZetaPacketEnsemble) :
    archimedeanPart x ZetaPacketLabel.correction = 0 := by
  unfold archimedeanPart
  exact Finsupp.filter_apply_neg (f := x) (p := ZetaPacketLabel.IsArchimedean)
    (a := ZetaPacketLabel.correction) ZetaPacketLabel.isArchimedean_correction

theorem correctionPart_correction (x : ZetaPacketEnsemble) :
    correctionPart x ZetaPacketLabel.correction = x ZetaPacketLabel.correction := by
  unfold correctionPart
  exact Finsupp.filter_apply_pos (f := x) (p := ZetaPacketLabel.IsCorrection)
    (a := ZetaPacketLabel.correction) ZetaPacketLabel.isCorrection_correction

/-- Prime-label decomposition helper. -/
theorem add_prime_archimedean_correction_prime (x : ZetaPacketEnsemble) :
    primePart x + archimedeanPart x + correctionPart x = x := by
  ext ℓ
  cases ℓ with
  | prime m' n' =>
      change primePart x (ZetaPacketLabel.prime m' n') +
          archimedeanPart x (ZetaPacketLabel.prime m' n') +
          correctionPart x (ZetaPacketLabel.prime m' n') =
        x (ZetaPacketLabel.prime m' n')
      have hprime := primePart_prime x m' n'
      have harch := archimedeanPart_prime x m' n'
      have hcorr := correctionPart_prime x m' n'
      calc
        primePart x (ZetaPacketLabel.prime m' n') +
            archimedeanPart x (ZetaPacketLabel.prime m' n') +
            correctionPart x (ZetaPacketLabel.prime m' n')
            = x (ZetaPacketLabel.prime m' n') + 0 + 0 := by
              exact Eq.trans
                (congrArg (fun t => t + archimedeanPart x (ZetaPacketLabel.prime m' n') +
                  correctionPart x (ZetaPacketLabel.prime m' n')) hprime)
                (Eq.trans
                  (congrArg (fun t => x (ZetaPacketLabel.prime m' n') + t +
                    correctionPart x (ZetaPacketLabel.prime m' n')) harch)
                  (congrArg (fun t => x (ZetaPacketLabel.prime m' n') + 0 + t) hcorr))
        _ = x (ZetaPacketLabel.prime m' n') := by
              calc
                x (ZetaPacketLabel.prime m' n') + 0 + 0 = x (ZetaPacketLabel.prime m' n') + 0 := by
                  exact add_zero (x (ZetaPacketLabel.prime m' n') + 0)
                _ = x (ZetaPacketLabel.prime m' n') := by
                  exact add_zero _
  | archimedean =>
      change primePart x ZetaPacketLabel.archimedean +
          archimedeanPart x ZetaPacketLabel.archimedean +
          correctionPart x ZetaPacketLabel.archimedean =
        x ZetaPacketLabel.archimedean
      have hprime := primePart_archimedean x
      have harch := archimedeanPart_archimedean x
      have hcorr := correctionPart_archimedean x
      calc
        primePart x ZetaPacketLabel.archimedean +
            archimedeanPart x ZetaPacketLabel.archimedean +
            correctionPart x ZetaPacketLabel.archimedean
            = 0 + x ZetaPacketLabel.archimedean + 0 := by
              exact Eq.trans
                (congrArg (fun t => t + archimedeanPart x ZetaPacketLabel.archimedean +
                  correctionPart x ZetaPacketLabel.archimedean) hprime)
                (Eq.trans
                  (congrArg (fun t => 0 + t + correctionPart x ZetaPacketLabel.archimedean) harch)
                  (congrArg (fun t => 0 + x ZetaPacketLabel.archimedean + t) hcorr))
        _ = x ZetaPacketLabel.archimedean := by
              calc
                0 + x ZetaPacketLabel.archimedean + 0 = 0 + x ZetaPacketLabel.archimedean := by
                  exact add_zero (0 + x ZetaPacketLabel.archimedean)
                _ = x ZetaPacketLabel.archimedean := by
                  exact zero_add _
  | correction =>
      change primePart x ZetaPacketLabel.correction +
          archimedeanPart x ZetaPacketLabel.correction +
          correctionPart x ZetaPacketLabel.correction =
        x ZetaPacketLabel.correction
      have hprime := primePart_correction x
      have harch := archimedeanPart_correction x
      have hcorr := correctionPart_correction x
      calc
        primePart x ZetaPacketLabel.correction +
            archimedeanPart x ZetaPacketLabel.correction +
            correctionPart x ZetaPacketLabel.correction
            = 0 + 0 + x ZetaPacketLabel.correction := by
              exact Eq.trans
                (congrArg (fun t => t + archimedeanPart x ZetaPacketLabel.correction +
                  correctionPart x ZetaPacketLabel.correction) hprime)
                (Eq.trans
                  (congrArg (fun t => 0 + t + correctionPart x ZetaPacketLabel.correction) harch)
                  (congrArg (fun t => 0 + 0 + t) hcorr))
        _ = x ZetaPacketLabel.correction := by
              calc
                0 + 0 + x ZetaPacketLabel.correction = 0 + (0 + x ZetaPacketLabel.correction) := by
                  exact add_assoc _ _ _
                _ = 0 + x ZetaPacketLabel.correction := by
                  exact zero_add _
                _ = x ZetaPacketLabel.correction := by
                  exact zero_add _

/-- The packet decomposition as a literal sum of the three filtered parts. -/
theorem add_prime_archimedean_correction (x : ZetaPacketEnsemble) :
    primePart x + archimedeanPart x + correctionPart x = x := by
  ext ℓ
  cases ℓ with
  | prime m n =>
      exact congrArg (fun f => f (ZetaPacketLabel.prime m n))
        (add_prime_archimedean_correction_prime x)
  | archimedean =>
      exact congrArg (fun f => f ZetaPacketLabel.archimedean)
        (add_prime_archimedean_correction_prime x)
  | correction =>
      exact congrArg (fun f => f ZetaPacketLabel.correction)
        (add_prime_archimedean_correction_prime x)

/-- Prime and archimedean packet parts have disjoint support. -/
theorem support_primePart_disjoint_archimedeanPart (x : ZetaPacketEnsemble) :
    Disjoint x.primePart.support x.archimedeanPart.support := by
  exact Finset.disjoint_left.2
    (fun ℓ h₁ h₂ =>
      match ℓ with
      | ZetaPacketLabel.prime m n =>
          have h₂nz : x.archimedeanPart (ZetaPacketLabel.prime m n) ≠ 0 :=
            Finsupp.mem_support_iff.mp h₂
          have h₂eq := archimedeanPart_prime x m n
          h₂nz h₂eq
      | ZetaPacketLabel.archimedean =>
          have h₁nz : x.primePart ZetaPacketLabel.archimedean ≠ 0 :=
            Finsupp.mem_support_iff.mp h₁
          have h₁eq := primePart_archimedean x
          h₁nz h₁eq
      | ZetaPacketLabel.correction =>
          have h₁nz : x.primePart ZetaPacketLabel.correction ≠ 0 :=
            Finsupp.mem_support_iff.mp h₁
          have h₁eq := primePart_correction x
          h₁nz h₁eq)

/-- Prime and correction packet parts have disjoint support. -/
theorem support_primePart_disjoint_correctionPart (x : ZetaPacketEnsemble) :
    Disjoint x.primePart.support x.correctionPart.support := by
  exact Finset.disjoint_left.2
    (fun ℓ h₁ h₂ =>
      match ℓ with
      | ZetaPacketLabel.prime m n =>
          have h₂nz : x.correctionPart (ZetaPacketLabel.prime m n) ≠ 0 :=
            Finsupp.mem_support_iff.mp h₂
          have h₂eq := correctionPart_prime x m n
          h₂nz h₂eq
      | ZetaPacketLabel.archimedean =>
          have h₁nz : x.primePart ZetaPacketLabel.archimedean ≠ 0 :=
            Finsupp.mem_support_iff.mp h₁
          have h₁eq := primePart_archimedean x
          h₁nz h₁eq
      | ZetaPacketLabel.correction =>
          have h₁nz : x.primePart ZetaPacketLabel.correction ≠ 0 :=
            Finsupp.mem_support_iff.mp h₁
          have h₁eq := primePart_correction x
          h₁nz h₁eq)

/-- Archimedean and correction packet parts have disjoint support. -/
theorem support_archimedeanPart_disjoint_correctionPart (x : ZetaPacketEnsemble) :
    Disjoint x.archimedeanPart.support x.correctionPart.support := by
  exact Finset.disjoint_left.2
    (fun ℓ h₁ h₂ =>
      match ℓ with
      | ZetaPacketLabel.prime m n =>
          have h₁nz : x.archimedeanPart (ZetaPacketLabel.prime m n) ≠ 0 :=
            Finsupp.mem_support_iff.mp h₁
          have h₁eq := archimedeanPart_prime x m n
          h₁nz h₁eq
      | ZetaPacketLabel.archimedean =>
          have h₂nz : x.correctionPart ZetaPacketLabel.archimedean ≠ 0 :=
            Finsupp.mem_support_iff.mp h₂
          have h₂eq := correctionPart_archimedean x
          h₂nz h₂eq
      | ZetaPacketLabel.correction =>
          have h₁nz : x.archimedeanPart ZetaPacketLabel.correction ≠ 0 :=
            Finsupp.mem_support_iff.mp h₁
          have h₁eq := archimedeanPart_correction x
          h₁nz h₁eq)

end ZetaPacketEnsemble

end
end LFunctions
end Boundary
