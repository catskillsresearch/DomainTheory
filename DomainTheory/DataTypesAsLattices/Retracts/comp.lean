module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.5).** Composition `u ∘ v = λx. u(v(x))`. -/
def comp (u v : Pomega) : Pomega :=
  graph (fun x => funOf u (funOf v x))

end DomainTheory.DataTypesAsLattices
