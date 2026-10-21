/-ai
pathAppend concatenates two paths that meet at a common middle state, yielding a path on the concatenated word. A trivial path on the empty word is dropped, and a one-step path is rebuilt on the appended word with the recursively appended continuation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Cat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Words
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.PathSplit
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.instFintypeAutState
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.instDecidableEqAutState
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.pathStateAt_zero

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability

open Sum Set

variable {σ₁ σ₂ : Type}

variable {σ : Type}

section ShortWord

variable {σ : Type} [Fintype σ] {M : NFA Bool σ}

/-- Append two paths meeting at the middle state. -/
def pathAppend {s u t : σ} {a b : List Bool} (p : M.Path s u a) (p' : M.Path u t b) :
    M.Path s t (a ++ b) :=
  match p with
  | .nil _ => p'
  | .cons sMid s' _ a' xs hstep p'' =>
      .cons sMid s' _ a' (xs ++ b) hstep (pathAppend p'' p')

end ShortWord

end Exercise722

end DomainTheory.NeighbourhoodSystems
