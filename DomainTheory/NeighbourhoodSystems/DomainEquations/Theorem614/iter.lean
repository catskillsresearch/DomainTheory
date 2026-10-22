module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Setup
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.subsystem_cast
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.rec_trans

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

namespace Theorem614

variable {α : Type w}

/-- The iterated tower, as data: at level `n`, the system `Tⁿ({Γ})` over `Tok`, the carrier
identification `(T.obj Tⁿ({Γ})).carrier = Tok`, and the subdomain relation `Tⁿ({Γ}) ◁ Tⁿ⁺¹({Γ})`
(where `Tⁿ⁺¹({Γ})` is the carrier-transport of `T(Tⁿ({Γ}))`). The successor step uses
*monotone on domains* (`MonotoneAt`) to obtain the next carrier identification and subdomain
relation. Choice-free. -/
def iter (s : Setup.{w}) : (n : ℕ) →
    Σ' (S : NeighborhoodSystem s.Tok), Σ' (ceq : (s.T.obj ⟨s.Tok, S⟩).carrier = s.Tok),
      S ◁ (ceq ▸ (s.T.obj ⟨s.Tok, S⟩).sys : NeighborhoodSystem s.Tok)
  | 0 => ⟨s.Γ, s.ceq, s.hsub⟩
  | (n + 1) =>
      let p := iter s n
      ⟨p.2.1 ▸ (s.T.obj ⟨s.Tok, p.1⟩).sys,
        (s.hmono p.2.2).carrier_eq.trans p.2.1,
        by
          have hsub := subsystem_cast p.2.1 (s.hmono p.2.2).sub
          rwa [rec_trans] at hsub⟩

end Theorem614

end DomainTheory.NeighbourhoodSystems
