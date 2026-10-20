module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812g4
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Subsystem

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}











/-- **Universality transports along isomorphism.** If `W` is universal and `W ≅ᴰ W'`, then `W'` is
universal too: every countable `D` embeds in `W` (`D ⊴ W`), and `W ⊴ W'` (take `D' := W'` in `⊴`'s
definition, using `Subsystem.refl` and the given isomorphism), so `trianglelefteq_trans` finishes. -/
theorem isUniversal_of_isomorphic {W : NeighborhoodSystem β} {W' : NeighborhoodSystem γ}
    (hW : IsUniversal.{u} W) (hWW' : W ≅ᴰ W') : IsUniversal.{u} W' := by
  have hWW'_tri : W ⊴ W' := hWW'.elim fun e => ⟨W', Subsystem.refl W', ⟨e⟩⟩
  intro α D _
  exact trianglelefteq_trans (hW D) hWW'_tri

end DomainTheory.NeighbourhoodSystems
