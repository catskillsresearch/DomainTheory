module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.SumToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instDecidableEqSumToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.rhtInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instLeftCommutativeLftInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instLeftCommutativeRhtInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.mem_foldr_rht

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
variable (A : InfoSys α) (B : InfoSys β)

/-- Right projection `rht u` (Scott 6.3). -/
def rhtFinset (u : Finset (SumToken α β)) : Finset β :=
  Multiset.foldr rhtInsert (∅ : Finset β) u.1

omit [DecidableEq α] in

theorem mem_rhtFinset {u : Finset (SumToken α β)} {y : β} :
    y ∈ rhtFinset u ↔ SumToken.right y ∈ u := by
  unfold rhtFinset
  rw [mem_foldr_rht]
  constructor
  · rintro ⟨p, hp, hp'⟩
    rwa [← hp']
  · intro hy
    exact ⟨.right y, hy, rfl⟩

omit [DecidableEq α] in


theorem rhtFinset.empty : rhtFinset (∅ : Finset (SumToken α β)) = ∅ := by
  ext y
  constructor
  · intro hy
    exact False.elim (Finset.notMem_empty _ ((mem_rhtFinset).1 hy))
  · intro hy
    exact False.elim (Finset.notMem_empty y hy)

theorem rhtFinset.funion (u v : Finset (SumToken α β)) :
    rhtFinset (u ∪' v) = rhtFinset u ∪' rhtFinset v := by
  ext y
  constructor
  · intro hy
    have : SumToken.right y ∈ u ∪' v := (mem_rhtFinset).1 hy
    rcases mem_funion.mp this with h | h
    · exact mem_funion.mpr (Or.inl ((mem_rhtFinset).2 h))
    · exact mem_funion.mpr (Or.inr ((mem_rhtFinset).2 h))
  · intro hy
    rcases mem_funion.mp hy with h | h
    · exact (mem_rhtFinset).2 (mem_funion.mpr (Or.inl ((mem_rhtFinset).1 h)))
    · exact (mem_rhtFinset).2 (mem_funion.mpr (Or.inr ((mem_rhtFinset).1 h)))

theorem rhtFinset.insert_bot (u : Finset (SumToken α β)) :
    rhtFinset (insert (.bot : SumToken α β) u) = rhtFinset u := by
  ext y
  constructor
  · intro hy
    have : SumToken.right y ∈ insert .bot u := (mem_rhtFinset).1 hy
    rcases Finset.mem_insert.mp this with h | h
    · exact False.elim (nomatch h)
    · exact (mem_rhtFinset).2 h
  · intro hy
    exact (mem_rhtFinset).2 (Finset.mem_insert.mpr (Or.inr ((mem_rhtFinset).1 hy)))

theorem rhtFinset.insert_left (u : Finset (SumToken α β)) (x : α) :
    rhtFinset (insert (.left x) u) = rhtFinset u := by
  ext y
  constructor
  · intro hy
    have : SumToken.right y ∈ insert (.left x) u := (mem_rhtFinset).1 hy
    rcases Finset.mem_insert.mp this with h | h
    · exact False.elim (nomatch h)
    · exact (mem_rhtFinset).2 h
  · intro hy
    exact (mem_rhtFinset).2 (Finset.mem_insert.mpr (Or.inr ((mem_rhtFinset).1 hy)))

theorem rhtFinset.insert_right (u : Finset (SumToken α β)) (y : β) :
    rhtFinset (insert (.right y) u) = insert y (rhtFinset u) := by
  ext z
  constructor
  · intro hz
    have : SumToken.right z ∈ insert (.right y) u := (mem_rhtFinset).1 hz
    rcases Finset.mem_insert.mp this with h | h
    · injection h with hz'
      exact Finset.mem_insert.mpr (Or.inl hz')
    · exact Finset.mem_insert.mpr (Or.inr ((mem_rhtFinset).2 h))
  · intro hz
    rcases Finset.mem_insert.mp hz with hz' | hz'
    · exact (mem_rhtFinset).2 (Finset.mem_insert.mpr (Or.inl (congrArg SumToken.right hz')))
    · exact (mem_rhtFinset).2 (Finset.mem_insert.mpr (Or.inr ((mem_rhtFinset).1 hz')))

omit [DecidableEq α] in

theorem rhtFinset.mono {u v : Finset (SumToken α β)} (h : v ⊆ u) :
    rhtFinset v ⊆ rhtFinset u := by
  intro y hy
  exact (mem_rhtFinset).2 (h ((mem_rhtFinset).1 hy))

omit [DecidableEq α] in

theorem rhtFinset.singleton_bot :
    rhtFinset ({.bot} : Finset (SumToken α β)) = ∅ := by
  ext y
  constructor
  · intro hy
    have : SumToken.right y ∈ ({.bot} : Finset _) := (mem_rhtFinset).1 hy
    exact False.elim (nomatch Finset.mem_singleton.mp this)
  · intro hy
    exact False.elim (Finset.notMem_empty y hy)

omit [DecidableEq α] in

theorem rhtFinset.singleton_right (y : β) :
    rhtFinset ({.right y} : Finset (SumToken α β)) = {y} := by
  ext z
  simp only [mem_rhtFinset, Finset.mem_singleton]
  exact ⟨SumToken.right.inj, fun h => h ▸ rfl⟩

end InfoSys


end DomainTheory.InformationSystems
