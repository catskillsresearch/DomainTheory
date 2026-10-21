/-ai
For fixed x and n, the environment update of t by x at n is Scott continuous in t.

It is the graph of a pointwise continuous family. At the numeral n the component is the constant map with value x, and at every other argument it is application in the function place.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






































theorem updateEnv_isScottContinuous_t (x : Pomega) (n : ℕ) :
    IsScottContinuous (fun t => updateEnv t x n) :=
  graph_const_isScottContinuous
    (fun t m => if m = ofNat n then x else funOf t m)
    (fun m => by
      by_cases h : m = ofNat n
      · simpa [h] using const_isScottContinuous (c := x)
      · simpa [h] using funOf_isScottContinuous_left m)

end DomainTheory.DataTypesAsLattices
