/-ai
If an approximable map j after a map i is the identity, then j sends the bottom of the codomain to the bottom of the domain.

The two inequalities give equality. Bottom lies below the image of bottom under i, so monotonicity of j and the elementwise form of the left-inverse identity put the image of bottom below bottom. Bottom lies below every element, so the other inequality holds.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.toElementMap_of_comp_eq_idMap

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326


variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}




/-- **`j₊` sends `𝒰`'s bottom to `𝒰+𝒰`'s bottom.** General fact: if `j ∘ i = I_D`, then `j(E.bot)`
is a global lower bound of `|D|` (via `D.bot ≤ i(v)` monotone through `j`, landing on
`j(i(D.bot)) = D.bot` for `v := D.bot`), hence equals `D.bot` by antisymmetry with `bot_le`. -/
theorem toElementMap_bot_eq_bot_of_comp_eq_idMap {i : ApproximableMap D E} {j : ApproximableMap E D}
    (hji : j.comp i = idMap D) : j.toElementMap E.bot = D.bot := by
  apply le_antisymm
  · have h2 := j.toElementMap_mono (E.bot_le (i.toElementMap D.bot))
    rwa [toElementMap_of_comp_eq_idMap hji] at h2
  · exact D.bot_le _

end DomainTheory.NeighbourhoodSystems
