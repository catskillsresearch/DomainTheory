/-ai
The exponential of an approximable map h into the domain of a function space and an approximable map k out of its codomain is the currying of k composed after evaluation composed after the product of the identity on the function space with h. On elements it sends a map f to k composed after f composed after h.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u v

variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

variable {a b : ApproximableMap U U}

section ExpMap

variable {γ δ γ' δ' γ'' δ'' : Type*}

variable {V0 : NeighborhoodSystem γ} {V1 : NeighborhoodSystem δ}

variable {V0' : NeighborhoodSystem γ'} {V1' : NeighborhoodSystem δ'}

variable {V0'' : NeighborhoodSystem γ''} {V1'' : NeighborhoodSystem δ''}

/-- **The Hom-functor's action on maps**, `f ↦ k∘f∘h`, transported to the function-space
neighbourhood systems via `curry`/`evalMap`/`prodMap`, exactly as `lamComb` (`Definition89.lean`)
does for the self-map case. -/
noncomputable def expMap (h : ApproximableMap V0' V0) (k : ApproximableMap V1 V1') :
    ApproximableMap (funSpace V0 V1) (funSpace V0' V1') :=
  curry (k.comp ((evalMap V0 V1).comp (prodMap (idMap (funSpace V0 V1)) h)))

end ExpMap

end DomainTheory.NeighbourhoodSystems
