module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

















theorem graph_funOf_ext {f g : Pomega}
    (hf : f = graph (fun x => funOf f x))
    (hg : g = graph (fun x => funOf g x))
    (h : ∀ x, funOf f x = funOf g x) : f = g := by
  rw [hf, hg]
  exact graph_ext h

end DomainTheory.DataTypesAsLattices
