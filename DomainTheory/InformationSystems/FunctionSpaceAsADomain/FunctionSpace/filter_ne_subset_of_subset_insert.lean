module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.BasicInst7
public import Mathlib.Data.Finset.Filter

@[expose] public section

namespace DomainTheory.InformationSystems

namespace InfoSys

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem filter_ne_subset_of_subset_insert {p : FunToken A B}
    {t w : Finset (FunToken A B)} (ht : t ⊆ insert p w) :
    t.filter (· ≠ p) ⊆ w := by
  intro q hq
  have ⟨hqt, hne⟩ := Finset.mem_filter.mp hq
  have : q ∈ insert p w := ht hqt
  rcases Finset.mem_insert.mp this with rfl | hqW
  · exact False.elim (hne rfl)
  · exact hqW

end InfoSys

end DomainTheory.InformationSystems
