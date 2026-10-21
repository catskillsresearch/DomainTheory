/-ai
Scott's enumeration of the section domain sends 0 to the master neighbourhood, and sends a successor index to the zero embedding of the enumerated neighbourhood of half the predecessor when the index is odd, and otherwise to the paired embedding of the two earlier values at the components of the unpairing of half the predecessor of the predecessor. The recursion is well-founded because each component of an unpairing is at most its argument.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.unpair_fst_le

@[expose] public section

set_option linter.unusedSectionVars false

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
