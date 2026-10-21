/-ai
When every neighbourhood of the generating system is its master, the colimit algebra admits a unique strict homomorphism into every T-algebra whose structure map is strict.

Existence supplies one strict homomorphism. Any other strict homomorphism equals it by uniqueness of strict homomorphisms out of the colimit.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.nonempty_strict_algHom
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.algHom_unique

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

namespace Theorem614


variable {α : Type w}


/-- **Theorem 6.14 (Scott 1981, PRG-19) — initial `T`-algebra.** When `{Γ}` is the one-point
generating system, the canonical solution `𝒟 = ⋃ₙ Tⁿ({Γ})` is the **initial** `T`-algebra among the
strict algebras: for every `T`-algebra `B` with a strict structure map there is a *unique* strict
homomorphism `𝒟 → B`. (Existence is Theorem 6.9; uniqueness is the `ρₙ` projection-chain argument.) -/
theorem exists_unique_strict_algHom (s : Setup.{w}) (hΓ : ∀ X, s.Γ.mem X → X = s.Γ.master)
    (B : TAlgebra s.T) (hk : IsStrict B.str) :
    ∃ g : AlgHom (colimAlg s) B, IsStrict g.hom ∧
      ∀ g' : AlgHom (colimAlg s) B, IsStrict g'.hom → g' = g := by
  obtain ⟨⟨g, hg⟩⟩ := nonempty_strict_algHom s B hk
  exact ⟨g, hg, fun g' hg' => algHom_unique s hΓ B g' g hg' hg⟩

end Theorem614
end DomainTheory.NeighbourhoodSystems
