module

public import DomainTheory.DataTypesAsLattices.Lambda.Ycomb
public import DomainTheory.DataTypesAsLattices.Lambda.omega_first_recursion

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem theorem_2_5 {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    funOf Ycomb (graph f) = fix f := by
  rw [Ycomb.app]
  exact omega_first_recursion hf

end DomainTheory.DataTypesAsLattices
