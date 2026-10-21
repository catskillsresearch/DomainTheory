/-ai
The map sending a function to the graph of its iterator at a fixed stage is Scott continuous.

The constant-graph lemma, using continuity of the iterator in the function argument.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.Z_isScottContinuous_left

@[expose] public section


namespace DomainTheory.DataTypesAsLattices
























theorem Zcomb_map_isScottContinuous (n : ℕ) :
    IsScottContinuous (fun f => graph (fun x => Z n f x)) :=
  graph_const_isScottContinuous (fun f x => Z n f x)
    (fun x => Z_isScottContinuous_left n x)

end DomainTheory.DataTypesAsLattices
