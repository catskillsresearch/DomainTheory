/-ai
If an endomap a of the universal domain lies below the identity, then its sharp lies below the identity.

The leaf embedding composed with a lies below the leaf embedding. The inner sharp therefore lies below the catamorphism of the leaf embedding and the pairing, which is the identity on the tree algebra. Conjugating by the projection pair, and using that the embedding after the projection lies below the identity, gives the inequality for the sharp.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.gMap_mono
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.iSharp_comp_jSharp_le

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}



variable {hD : ∀ X, D.mem X → X.Nonempty}








variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}











/-- **`a ≤ I ⟹ a§ ≤ I`** (half of "`a` a projection ⟹ `a§` a projection", Proposition 8.10's
proof recipe transcribed to `§`). -/
theorem aSharp_le_idMap_of_le {a : ApproximableMap U U} (ha : a ≤ idMap U) :
    aSharp a ≤ idMap U := by
  have h1 : (inSharpMap U_mem_nonempty).comp a ≤ inSharpMap U_mem_nonempty := by
    calc (inSharpMap U_mem_nonempty).comp a
        ≤ (inSharpMap U_mem_nonempty).comp (idMap U) := comp_mono_gen le_rfl ha
      _ = inSharpMap U_mem_nonempty := comp_idMap _
  have h2 : aSharpInner a ≤ idMap (Dsharp U U_mem_nonempty) := by
    calc aSharpInner a
        ≤ gMap (inSharpMap U_mem_nonempty) (pairSharpMap U_mem_nonempty) U_mem_nonempty :=
          gMap_mono U_mem_nonempty h1 le_rfl
      _ = idMap (Dsharp U U_mem_nonempty) := gMap_inSharp_pairSharp_eq_idMap
  calc aSharp a = iSharp.comp ((aSharpInner a).comp jSharp) := aSharp_eq a
    _ ≤ iSharp.comp ((idMap (Dsharp U U_mem_nonempty)).comp jSharp) :=
        comp_mono_gen le_rfl (comp_mono_gen h2 le_rfl)
    _ = iSharp.comp jSharp := by rw [idMap_comp]
    _ ≤ idMap U := iSharp_comp_jSharp_le

end DomainTheory.NeighbourhoodSystems
