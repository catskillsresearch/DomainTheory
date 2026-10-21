/-ai
If the false tag of the product neighbourhood of X' and Y' is a neighbourhood of the lift of the product, then X' is a neighbourhood of D and Y' is a neighbourhood of E.

The inverse tagging lemma supplies neighbourhoods A and B of the product whose product neighbourhood equals that of X' and Y'. Injectivity of product neighbourhoods identifies the pairs, so the memberships of A and B are the required memberships.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.lift
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.liftTok_mem_embF_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.mem_liftBot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.mem_liftUp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.toSumLift_mem_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.toSumLift_mem_embT
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.fromSumLift_mem_embFF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.fromSumLift_mem_embTF

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {A B C : ScottSys}

variable {D E : ScottSys}

theorem lp_prod_inv {X' Y' : Set Str}
    (h : (D.prod E).lift.sys.mem (embBit false (prodTokNbhd X' Y'))) :
    D.sys.mem X' ∧ E.sys.mem Y' := by
  obtain ⟨A, B, hA, hB, heq⟩ := liftTok_mem_embF_inv (hD := (D.prod E).ne) h
  obtain ⟨rfl, rfl⟩ := prodTokNbhd_injective heq
  exact ⟨hA, hB⟩

end Exercise619

end DomainTheory.NeighbourhoodSystems
