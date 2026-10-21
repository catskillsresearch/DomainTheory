/-ai
Applying the S combinator to a function equals the graph of its further applications.

Rewrite by the one-argument application, then use extensionality of graphs. At each argument the equality is the symmetric form of beta reduction for continuity of the middle map.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.Scomb_mid_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Functionality.Scomb_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Scomb_app_isGraph (f : Pomega) :
    funOf Scomb f = graph (fun g => funOf (funOf Scomb f) g) := by
  rw [Scomb_app]
  apply graph_ext
  intro g
  exact (beta (Scomb_mid_isScottContinuous f) g).symm

end DomainTheory.DataTypesAsLattices
