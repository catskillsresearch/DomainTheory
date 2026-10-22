module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Combinators77
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)


/-- The index characterization of `pairSharpMap` against the product/`Vsharp` enumerations:
`(V⁰_{p t} ∪ V¹_{q t}) pair V_k ↔ V_{2·t+2} ⊆ V_k` (since `V_{2t+2} = 1·V_{p t} ∪ 2·V_{q t}`). -/
theorem pairSharp_rel_Vsharp_iff (P : ComputablePresentation D) (t k : ℕ) :
    (pairSharpMap hD).rel
        ((prodPresentation (dsharpPresentation P hD) (dsharpPresentation P hD)).X t)
        ((dsharpPresentation P hD).X k) ↔
      Vsharp D P (2 * t + 2) ⊆ Vsharp D P k := by
  rw [pairSharpMap_rel, prodPresentation_X, Vsharp_even]
  constructor
  · rintro ⟨-, -, A, B, -, -, heq, hsub⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    exact hsub
  · intro hsub
    exact ⟨prod_mem_prodNbhd (Vsharp_mem P _) (Vsharp_mem P _), Vsharp_mem P k,
      _, _, Vsharp_mem P _, Vsharp_mem P _, rfl, hsub⟩

end Proposition77
end DomainTheory.NeighbourhoodSystems
