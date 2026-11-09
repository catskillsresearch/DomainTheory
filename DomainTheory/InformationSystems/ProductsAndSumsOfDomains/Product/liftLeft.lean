module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.mkLeft

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β)

def liftLeft (v : Finset α) : Finset (ProdToken A B) :=
  Multiset.foldr (fun x : α => insert (mkLeft A B x)) (∅ : Finset (ProdToken A B)) v.1

namespace liftLeft

theorem mem_foldr (s : Multiset α) (p : ProdToken A B) :
    p ∈ Multiset.foldr (fun x : α => insert (mkLeft A B x)) (∅ : Finset (ProdToken A B)) s ↔
      ∃ x ∈ s, p = mkLeft A B x := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro hp
      exact False.elim (Finset.notMem_empty p hp)
    · rintro ⟨_, hx, _⟩
      exact False.elim (by cases hx)
  · intro x t ih
    simp only [Multiset.foldr_cons, Finset.mem_insert, ih, Multiset.mem_cons]
    constructor
    · rintro (hp | ⟨y, hy, hp⟩)
      · exact ⟨x, Or.inl rfl, hp⟩
      · exact ⟨y, Or.inr hy, hp⟩
    · rintro ⟨y, hy, hp⟩
      rcases hy with rfl | hy
      · exact Or.inl hp
      · exact Or.inr ⟨y, hy, hp⟩

theorem mem {v : Finset α} {p : ProdToken A B} :
    p ∈ liftLeft A B v ↔ ∃ x ∈ v, p = mkLeft A B x := by
  unfold liftLeft
  exact mem_foldr A B v.1 p

theorem fstFinset_eq (v : Finset α) : fstFinset A B (liftLeft A B v) = v := by
  ext x
  constructor
  · intro hx
    rcases (mem_fstFinset A B).1 hx with ⟨p, hp, hbot, hx'⟩
    rcases (liftLeft.mem A B).1 hp with ⟨y, hy, hp'⟩
    subst hp'
    exact (show y = x from hx').symm ▸ hy
  · intro hx
    exact (mem_fstFinset A B).2
      ⟨mkLeft A B x, (liftLeft.mem A B).2 ⟨x, hx, rfl⟩, rfl, rfl⟩

theorem sndFinset_eq (v : Finset α) :
    sndFinset A B (liftLeft A B v) ⊆ ({B.bot} : Finset β) := by
  intro y hy
  rcases (mem_sndFinset A B).1 hy with ⟨p, hp, hbot, hy'⟩
  rcases (liftLeft.mem A B).1 hp with ⟨x, _, hp'⟩
  subst hp'
  have : y = B.bot := hy'.symm
  exact Finset.mem_singleton.mpr this

theorem con {v : Finset α} (hv : v ∈ A.Con) :
    ProdCon A B (liftLeft A B v) := by
  refine ⟨?_, ?_⟩
  · rw [fstFinset_eq]
    exact hv
  · exact B.con_subset (B.con_sing B.bot) (sndFinset_eq A B v)

end liftLeft

end InfoSys

end DomainTheory.InformationSystems
