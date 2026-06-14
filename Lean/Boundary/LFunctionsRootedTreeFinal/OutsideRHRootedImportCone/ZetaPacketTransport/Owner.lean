import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissibleInterpolation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaPacketComparison.ZetaCompletedBoundaryDefect.ZetaPacketReconstruction.ZetaPacketEnergy.Owner

/-!
# Boundary zeta packet transport

This file packages the admissible-side transport surface that will eventually
feed the packet-energy comparison theorems. It only records the canonical
spectral/probe pair already available on the admissible side.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The admissible transport data: spectral model together with the probe. -/
def packetTransportSurface (f : ZetaAdmissibleFunction) :
    ZetaTestFunction.zetaExplicitFormulaTransform × ZetaTestFunction :=
  interpolationSurface f

/-- The admissible packet transport surface has the spectral model as first component. -/
theorem packetTransportSurface_fst (f : ZetaAdmissibleFunction) :
    (packetTransportSurface f).1 = spectralModel f := by
  rfl

/-- The admissible packet transport surface has the probe as second component. -/
theorem packetTransportSurface_snd (f : ZetaAdmissibleFunction) :
    (packetTransportSurface f).2 = separatingProbe f := by
  rfl

/-- The admissible packet transport surface is the interpolation surface. -/
theorem packetTransportSurface_eq (f : ZetaAdmissibleFunction) :
    packetTransportSurface f = interpolationSurface f := by
  rfl

/-- The admissible packet transport surface is the spectral model together with
the autocorrelation probe. -/
theorem packetTransportSurface_eq_spectralModel_autocorrelation (f : ZetaAdmissibleFunction) :
    packetTransportSurface f = (spectralModel f, autocorrelation f) := by
  exact interpolationSurface_eq_spectralModel_autocorrelation f

/-- The admissible packet transport surface is the spectral-model/probe pair. -/
theorem packetTransportSurface_pair (f : ZetaAdmissibleFunction) :
    packetTransportSurface f = (spectralModel f, separatingProbe f) := by
  rfl

/-- The spectral-model component of a finite transport sum is the finite sum of spectral models. -/
theorem packetTransportSurface_fst_sum {α : Type*} (s : Finset α)
    (f : α → ZetaAdmissibleFunction) :
    (packetTransportSurface (∑ a in s, f a)).1 = ∑ a in s, spectralModel (f a) := by
  exact ZetaAdmissibleFunction.spectralModel_sum s f

/-- The transport surface of a finite sum exposes the finite spectral sum in the first
component and the probe of the sum in the second component. -/
theorem packetTransportSurface_sum {α : Type*} (s : Finset α)
    (f : α → ZetaAdmissibleFunction) :
    packetTransportSurface (∑ a in s, f a) =
      (∑ a in s, spectralModel (f a), separatingProbe (∑ a in s, f a)) := by
  ext
  · exact packetTransportSurface_fst_sum s f
  · exact packetTransportSurface_snd (∑ a in s, f a)

/-- A finite sample can be realized by an admissible packet transport surface. -/
theorem exists_packetTransportSurface_eval_sample_with_support
    (S : ZetaAdmissibleFunction.FiniteSample) (a : Fin S.n → ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      (∀ i, f (S.x i) = a i) ∧
      HasCompactSupport f ∧
      (packetTransportSurface f).1 = spectralModel f ∧
      (packetTransportSurface f).2 = separatingProbe f := by
  rcases exists_interpolationSurface_eval_sample_with_support S a with
    ⟨f, hf, hfc, _hfst, _hsnd⟩
  exact ⟨f, hf, hfc, packetTransportSurface_fst f, packetTransportSurface_snd f⟩

/-- A finite sample can be realized by a packet transport surface whose delta basis has controlled
support. -/
theorem exists_packetTransportSurface_eval_sample_with_basis_support
    (S : ZetaAdmissibleFunction.FiniteSample) (a : Fin S.n → ℂ) :
    ∃ F : ∀ _i, ZetaAdmissibleFunction,
      (∀ i, F i (S.x i) = (1 : ℂ)) ∧
      (∀ i j, j ≠ i → F i (S.x j) = 0) ∧
      (∀ i, HasCompactSupport (F i)) ∧
      ∃ f : ZetaAdmissibleFunction,
        (∀ i, f (S.x i) = a i) ∧
        HasCompactSupport f ∧
        Function.support f ⊆ Set.iUnion fun i => Function.support (F i) ∧
        (packetTransportSurface f).1 = spectralModel f ∧
        (packetTransportSurface f).2 = separatingProbe f := by
  rcases exists_interpolationSurface_eval_sample_with_basis_support S a with
    ⟨F, hF1, hF0, hFc, f, hf, hfc, hfs, _hfst, _hsnd⟩
  exact ⟨F, hF1, hF0, hFc, f, hf, hfc, hfs,
    packetTransportSurface_fst f, packetTransportSurface_snd f⟩

/-- A finite sample can be realized by a packet transport surface whose delta basis is controlled by
closed balls. -/
theorem exists_packetTransportSurface_eval_sample_with_basis_closedBall_support
    (S : ZetaAdmissibleFunction.FiniteSample) (a : Fin S.n → ℂ) :
    ∃ F : ∀ _i, ZetaAdmissibleFunction,
      (∀ i, F i (S.x i) = (1 : ℂ)) ∧
      (∀ i j, j ≠ i → F i (S.x j) = 0) ∧
      (∀ i, ∃ rOut : ℝ, 0 < rOut ∧
        Function.support (F i) ⊆ Metric.closedBall (S.x i) rOut) ∧
      ∃ f : ZetaAdmissibleFunction,
        (∀ i, f (S.x i) = a i) ∧
        HasCompactSupport f ∧
        Function.support f ⊆ Set.iUnion fun i => Function.support (F i) ∧
        (packetTransportSurface f).1 = spectralModel f ∧
        (packetTransportSurface f).2 = separatingProbe f := by
  rcases exists_interpolationSurface_eval_sample_with_basis_closedBall_support S a with
    ⟨F, hF1, hF0, hFr, f, hf, hfc, hfs, _hfst, _hsnd⟩
  exact ⟨F, hF1, hF0, hFr, f, hf, hfc, hfs,
    packetTransportSurface_fst f, packetTransportSurface_snd f⟩

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
