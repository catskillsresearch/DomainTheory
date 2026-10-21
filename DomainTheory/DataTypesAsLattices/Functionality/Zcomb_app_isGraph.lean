/-ai
Applying the combinator Z at a stage to a function equals the graph of its further applications.

Rewrite by the one-argument application, then use extensionality of graphs. At each value the equality is the symmetric form of beta reduction for continuity of the iterator in the value.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.Z_isScottContinuous_right
public import DomainTheory.DataTypesAsLattices.Functionality.Zcomb_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Zcomb_app_isGraph (n : ℕ) (f : Pomega) :
    funOf (Zcomb n) f = graph (fun x => funOf (funOf (Zcomb n) f) x) := by
  rw [Zcomb_app]
  apply graph_ext
  intro x
  exact (beta (Z_isScottContinuous_right n f) x).symm

end DomainTheory.DataTypesAsLattices
