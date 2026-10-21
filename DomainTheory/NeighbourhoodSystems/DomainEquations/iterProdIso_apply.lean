/-ai
The product isomorphism sends an element of the infinite iterate to the pair of its component at zero and the sequence of its later components.

This equality is the definition of the isomorphism.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510


namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

/-- **The forward iso reads off head and tail.** `iterProdIso z = ⟨z₀, ⟨z₁,z₂,…⟩⟩`: the first
component is the `0`-coordinate `component z 0`, the second is the shifted sequence. -/
theorem iterProdIso_apply (z : (iterSys V).Element) :
    iterProdIso V z = pair (component z 0) (ofSeq (fun n => component z (n + 1))) := rfl

end Exercise618

end DomainTheory.NeighbourhoodSystems
