/-ai
Every numeral is combinatory.

The numeral zero is the zero combinator. The numeral of a successor is the application of the successor combinator to the preceding numeral, rewritten by the successor application law and the equation for the successor of a numeral.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.sucC_app
public import DomainTheory.DataTypesAsLattices.Lambda.succSet_ofNat

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






















































theorem ofNat_combinatory : ∀ n, IsCombinatory (ofNat n)
  | 0 => by
    simpa [zeroC] using IsCombinatory.zero
  | n + 1 => by
    have h := IsCombinatory.app IsCombinatory.suc (ofNat_combinatory n)
    simpa [sucC_app, succSet_ofNat] using h

end DomainTheory.DataTypesAsLattices
