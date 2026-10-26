module

public import DomainTheory.DataTypesAsLattices.Enumeration.Rcomb
public import DomainTheory.DataTypesAsLattices.Enumeration.Rterm_interp
public import DomainTheory.DataTypesAsLattices.Enumeration.Rterm
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_4_closed
public import DomainTheory.DataTypesAsLattices.Enumeration.graph_mem_FUN

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

namespace Rcomb

theorem combinatory : IsCombinatory Rcomb := by
  rw [← Rterm_interp]
  exact theorem_2_4_closed Rterm

theorem mem_FUN : Rcomb ∈ FUN :=
  graph_mem_FUN (seq2_right_isScottContinuous (ofNat 0))

end Rcomb

end DomainTheory.DataTypesAsLattices
