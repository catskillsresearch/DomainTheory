module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.BasicInst5
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.ProdToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.BasicInst7
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.instLeftCommutativeFstInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.instLeftCommutativeSndInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.mem_foldr_snd

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
variable (A : InfoSys α) (B : InfoSys β)

/-- Right projection of a finite set of product tokens (Scott 6.1). -/
def sndFinset (u : Finset (ProdToken A B)) : Finset β :=
  Multiset.foldr (fun p : ProdToken A B => insert p.val.2) (∅ : Finset β)
    (u.filter (fun p => p.val.1 = A.bot)).1

theorem mem_sndFinset {u : Finset (ProdToken A B)} {y : β} :
    y ∈ sndFinset A B u ↔ ∃ p ∈ u, p.val.1 = A.bot ∧ p.val.2 = y := by
  unfold sndFinset
  rw [mem_foldr_snd]
  constructor
  · rintro ⟨p, hp, hy⟩
    have hp' := Finset.mem_filter.mp hp
    exact ⟨p, hp'.1, hp'.2, hy⟩
  · rintro ⟨p, hp, hbot, hy⟩
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, hbot⟩, hy⟩

theorem sndFinset.empty : sndFinset A B (∅ : Finset (ProdToken A B)) = ∅ := by
  ext y
  constructor
  · intro hy
    rcases (mem_sndFinset A B).1 hy with ⟨_, hp, _, _⟩
    exact False.elim (Finset.notMem_empty _ hp)
  · intro hy
    exact False.elim (Finset.notMem_empty y hy)

theorem sndFinset.funion (u v : Finset (ProdToken A B)) :
    sndFinset A B (u ∪' v) = sndFinset A B u ∪' sndFinset A B v := by
  ext y
  constructor
  · intro hy
    rcases (mem_sndFinset A B).1 hy with ⟨p, hp, hbot, hy'⟩
    rcases mem_funion.mp hp with hp | hp
    · exact mem_funion.mpr (Or.inl ((mem_sndFinset A B).2 ⟨p, hp, hbot, hy'⟩))
    · exact mem_funion.mpr (Or.inr ((mem_sndFinset A B).2 ⟨p, hp, hbot, hy'⟩))
  · intro hy
    rcases mem_funion.mp hy with hy | hy
    · rcases (mem_sndFinset A B).1 hy with ⟨p, hp, hbot, hy'⟩
      exact (mem_sndFinset A B).2 ⟨p, mem_funion.mpr (Or.inl hp), hbot, hy'⟩
    · rcases (mem_sndFinset A B).1 hy with ⟨p, hp, hbot, hy'⟩
      exact (mem_sndFinset A B).2 ⟨p, mem_funion.mpr (Or.inr hp), hbot, hy'⟩

theorem sndFinset.insert_not_right (u : Finset (ProdToken A B)) (p : ProdToken A B)
    (hp : p.val.1 ≠ A.bot) :
    sndFinset A B (insert p u) = sndFinset A B u := by
  ext y
  constructor
  · intro hy
    rcases (mem_sndFinset A B).1 hy with ⟨q, hq, hbot, hy'⟩
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact False.elim (hp hbot)
    · exact (mem_sndFinset A B).2 ⟨q, hq, hbot, hy'⟩
  · intro hy
    rcases (mem_sndFinset A B).1 hy with ⟨q, hq, hbot, hy'⟩
    exact (mem_sndFinset A B).2 ⟨q, Finset.mem_insert_of_mem hq, hbot, hy'⟩

theorem sndFinset.insert_right (u : Finset (ProdToken A B)) (p : ProdToken A B)
    (hp : p.val.1 = A.bot) :
    sndFinset A B (insert p u) = insert p.val.2 (sndFinset A B u) := by
  ext y
  constructor
  · intro hy
    rcases (mem_sndFinset A B).1 hy with ⟨q, hq, hbot, hy'⟩
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Finset.mem_insert.mpr (Or.inl hy'.symm)
    · exact Finset.mem_insert.mpr (Or.inr ((mem_sndFinset A B).2 ⟨q, hq, hbot, hy'⟩))
  · intro hy
    rcases Finset.mem_insert.mp hy with hy' | hy'
    · exact (mem_sndFinset A B).2 ⟨p, Finset.mem_insert_self p u, hp, hy'.symm⟩
    · rcases (mem_sndFinset A B).1 hy' with ⟨q, hq, hbot, hyq⟩
      exact (mem_sndFinset A B).2 ⟨q, Finset.mem_insert_of_mem hq, hbot, hyq⟩

theorem sndFinset.mono {u v : Finset (ProdToken A B)} (h : v ⊆ u) :
    sndFinset A B v ⊆ sndFinset A B u := by
  intro y hy
  rcases (mem_sndFinset A B).1 hy with ⟨p, hp, hbot, hy'⟩
  exact (mem_sndFinset A B).2 ⟨p, h hp, hbot, hy'⟩

theorem sndFinset.singleton_right (p : ProdToken A B) (hp : p.val.1 = A.bot) :
    sndFinset A B {p} = {p.val.2} := by
  rw [show ({p} : Finset _) = insert p ∅ from rfl, sndFinset.insert_right A B ∅ p hp,
    sndFinset.empty]
  rfl

end InfoSys


end DomainTheory.InformationSystems
