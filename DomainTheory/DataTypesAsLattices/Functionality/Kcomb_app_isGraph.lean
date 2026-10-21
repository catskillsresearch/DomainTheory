/-ai
Applying the K combinator to an element equals the graph of its further applications.

Rewrite by the one-argument application, then use extensionality of graphs. At each argument the equality is the symmetric form of beta reduction for the constant function with that value.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.Kcomb_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






















theorem Kcomb_app_isGraph (x : Pomega) :
    funOf Kcomb x = graph (fun y => funOf (funOf Kcomb x) y) := by
  rw [Kcomb_app]
  apply graph_ext
  intro y
  exact (beta (const_isScottContinuous x) y).symm

end DomainTheory.DataTypesAsLattices
