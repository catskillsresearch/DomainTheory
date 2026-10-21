/-ai
The universal strict map sends the injection of an element to the image of that element under the leaf algebra map.

A neighbourhood of the image comes from a neighbourhood of the injection. The master case forces the target to be the master, which the leaf map reaches from the master of the element. A zero embedding yields a relation of the leaf map by inversion. Conversely, a relation of the leaf map on a neighbourhood of the element is the leaf clause on the zero embedding of that neighbourhood.
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















/-- **`g(in x) = u(x)`.** The injection summand of `D^§ ≅ D + (D^§×D^§)` folds via `u`. -/
theorem gMap_in (hD : ∀ X, D.mem X → X.Nonempty) (x : D.Element) :
    (gMap u v hD).toElementMap (inSharp D hD x) = u.toElementMap x := by
  apply Element.ext
  intro Z
  simp only [mem_toElementMap, gMap_rel]
  constructor
  · rintro ⟨W, hWmem, hrel⟩
    rcases hWmem with rfl | ⟨X, hXx, rfl⟩
    · have hZ := gRel_gamma_inv hD hrel; subst hZ
      exact ⟨D.master, x.master_mem, u.master_rel⟩
    · exact ⟨X, hXx, gRel_embZero_inv hD hrel⟩
  · rintro ⟨X, hXx, hrel⟩
    exact ⟨embZero X, Or.inr ⟨X, hXx, rfl⟩, GRel.leaf hrel⟩

end Exercise717
end DomainTheory.NeighbourhoodSystems
