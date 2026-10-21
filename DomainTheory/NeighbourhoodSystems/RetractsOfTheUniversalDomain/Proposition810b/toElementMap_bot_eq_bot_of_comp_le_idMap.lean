/-ai
If i composed with j lies below the identity on the codomain, then i sends the bottom of the domain to the bottom of the codomain.

Antisymmetry compares the two bottoms. Monotonicity of i and the fact that the domain bottom lies below the image of the codomain bottom under j give one inequality, and the hypothesis on the composition puts that image below the codomain bottom. The codomain bottom lies below the image of the domain bottom.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u

variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-- If `i ∘ j ≤ I_E`, then `i` sends `D`'s bottom to `E`'s bottom: `i(⊥_D) ≤ i(j(⊥_E)) ≤ ⊥_E`
(the first step by monotonicity, since `⊥_D ≤ j(⊥_E)`; the second is `toElementMap_le_of_comp_le_idMap`
at `x := ⊥_E`), and `⊥_E ≤ i(⊥_D)` always. -/
theorem toElementMap_bot_eq_bot_of_comp_le_idMap {i : ApproximableMap D E} {j : ApproximableMap E D}
    (hij : i.comp j ≤ idMap E) : i.toElementMap D.bot = E.bot := by
  apply le_antisymm
  · calc i.toElementMap D.bot ≤ i.toElementMap (j.toElementMap E.bot) :=
          i.toElementMap_mono (D.bot_le _)
      _ ≤ E.bot := toElementMap_le_of_comp_le_idMap hij E.bot
  · exact E.bot_le _

end DomainTheory.NeighbourhoodSystems
