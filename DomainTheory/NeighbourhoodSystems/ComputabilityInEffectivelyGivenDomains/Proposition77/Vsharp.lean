module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.unpair_fst_le

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

/-- **Proposition 7.7 (Scott 1981, PRG-19).** Scott's enumeration of `D^§`:
`V₀ = Γ`, `V_{2n+1} = 0·Xₙ`, `V_{2n+2} = 1·V_{p n} ∪ 2·V_{q n}` (`p = unpair.1`, `q = unpair.2`). -/
def Vsharp (D : NeighborhoodSystem α) (P : ComputablePresentation D) :
    ℕ → Set (List Bool × α)
  | 0 => Gamma D
  | (k + 1) =>
      if (k + 1) % 2 = 1 then
        embZero (P.X (k / 2))
      else
        embPair (Vsharp D P ((k - 1) / 2).unpair.1) (Vsharp D P ((k - 1) / 2).unpair.2)
  termination_by k => k
  decreasing_by
    · have := unpair_fst_le ((k - 1) / 2); omega
    · have := unpair_snd_le ((k - 1) / 2); omega

end Proposition77

end DomainTheory.NeighbourhoodSystems
