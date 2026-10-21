/-ai
The universal strict map sends the sharp pairing of two elements to the image, under the node algebra map, of the pair of the images of those elements.

A neighbourhood of the image comes from a neighbourhood of the pairing. The master case forces the target to be the master, which the node map reaches from the master of the product. A paired neighbourhood inverts to relations of the two factors and a relation of the node map on their product. Conversely, a neighbourhood of the pair of the images is a product of neighbourhoods of those images, and the node clause relates the paired embedding of their sources to the target.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717



variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}















/-- **`g(pair y z) = v(⟨g y, g z⟩)`.** The product summand folds via `v` applied to the recursive
results — the defining recursion of the catamorphism. -/
theorem gMap_pair (hD : ∀ X, D.mem X → X.Nonempty) (y z : (Dsharp D hD).Element) :
    (gMap u v hD).toElementMap (pairSharp D hD y z)
      = v.toElementMap (pair ((gMap u v hD).toElementMap y) ((gMap u v hD).toElementMap z)) := by
  apply Element.ext
  intro Z
  simp only [mem_toElementMap, gMap_rel]
  constructor
  · rintro ⟨W, hWmem, hrel⟩
    rcases hWmem with rfl | ⟨P, Q, hPy, hQz, rfl⟩
    · have hZ := gRel_gamma_inv hD hrel; subst hZ
      exact ⟨(prod E E).master, (pair _ _).master_mem, v.master_rel⟩
    · obtain ⟨Z₁, Z₂, hP1, hQ2, hvrel⟩ := gRel_embPair_inv hD hrel
      exact ⟨prodNbhd Z₁ Z₂,
        mem_pair.mpr ⟨Z₁, Z₂, ⟨P, hPy, hP1⟩, ⟨Q, hQz, hQ2⟩, rfl⟩, hvrel⟩
  · rintro ⟨V, hVmem, hvrel⟩
    obtain ⟨Z₁, Z₂, ⟨P, hPy, hP1⟩, ⟨Q, hQz, hQ2⟩, rfl⟩ := mem_pair.mp hVmem
    exact ⟨embPair P Q, Or.inr ⟨P, Q, hPy, hQz, rfl⟩, GRel.node hP1 hQ2 hvrel⟩

end Exercise717
end DomainTheory.NeighbourhoodSystems
