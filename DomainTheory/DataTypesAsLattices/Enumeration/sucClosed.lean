module

public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import DomainTheory.DataTypesAsLattices.Lambda.sucC
public import DomainTheory.DataTypesAsLattices.Lambda.envSet
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Graph.lam
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Enumeration.Avoids
public import Mathlib.Computability.Halting

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

def sucClosed : Term := .lam 4 (.succ (.var 4))

namespace sucClosed

theorem avoids8 : sucClosed.Avoids 8 := by
  simp[sucClosed, Term.Avoids]

theorem interp (ρ : ℕ → Pomega) : interp sucClosed ρ = sucC := by
  simp[sucClosed, sucC, envSet, Function.update, _root_.DomainTheory.DataTypesAsLattices.interp]

end sucClosed

end DomainTheory.DataTypesAsLattices
