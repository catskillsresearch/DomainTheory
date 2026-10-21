/-ai
If the characteristic and the consistency test are primitive recursive, then the code-level qChar-gated fold is primitive recursive.

Apply primitive recursion of code folding to the primitive-recursive code-level step, the constant zero, the constant master index, and the identity, and match the resulting function with the fold by reflexivity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88h.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88h.diagFixed_iff_fixedNbhd_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88h.diagFixed_isREPred
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88h.diagFixed_exists_qChar
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88i.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88i.primrec_myStepCode

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)





variable {P qChar cons}

variable (P qChar cons)




/-- **`myFoldCode` is primitive recursive** (Part 2's headline `Nat.Primrec` claim). -/
theorem primrec_myFoldCode (hqCharp : Nat.Primrec qChar) (hconsp : Nat.Primrec cons) :
    Nat.Primrec (myFoldCode P qChar cons) :=
  (primrec_foldCode (primrec_myStepCode P qChar cons hqCharp hconsp)
    (Nat.Primrec.const 0) (Nat.Primrec.const P.masterIdx) primrec_id).of_eq
    fun _ => rfl

end DomainTheory.NeighbourhoodSystems
