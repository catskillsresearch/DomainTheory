module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConN_mono

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]


variable (A : InfoSys α)


/-- Inserting an entailed bot or atom preserves stage-`n` consistency.
Function-token `ent_con` (FunCon on `insert`) remains. -/
theorem LamConN_insert_of_ent_atom {n : ℕ} {u : Finset (RawLamToken α)} {x : α}
    (ht : LamEntN A n u (.atom x)) : LamConN A n (insert (.atom x) u) := by
  induction n generalizing u with
  | zero =>
    rcases ht with ⟨⟨_, hF⟩, _, hEnt⟩
    exact ⟨by rw [lamAtomFinset_insert_atom]; exact A.ent_con hEnt,
      by rw [lamFunFinset_insert_atom]; exact hF⟩
  | succ n ih =>
    rcases ht with ht | ⟨_, hF, _, hEnt⟩
    · exact Or.inl (ih ht)
    · exact LamConN_mono A (Nat.zero_le (n + 1))
        ⟨by rw [lamAtomFinset_insert_atom]; exact A.ent_con hEnt,
          by rw [lamFunFinset_insert_atom]; exact hF⟩

end InfoSys
end DomainTheory.InformationSystems
